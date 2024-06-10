open! Core
open Parse_tree
open Typed_tree

type env = det some_texp Id.Map.t

let gen_vertex =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    [%string "X%{!cnt#Int}"]

let rec peval : type a. (a, det) texp -> (a, det) texp =
 fun ({ ty; exp } as texp) ->
  match exp with
  | Value _ | Rvar _ -> texp
  | Bop (bop, te1, te2, ms) -> (
      match (peval te1, peval te2, ms) with
      | { exp = Value v1; _ }, { exp = Value v2; _ }, Both_val _ ->
          { ty; exp = Value (bop.op v1 v2) }
      | te1, te2, ms -> { ty; exp = Bop (bop, te1, te2, ms) })
  | Uop (uop, te) -> (
      match peval te with
      | { exp = Value v; _ } -> { ty; exp = Value (uop.op v) }
      | e -> { ty; exp = Uop (uop, e) })
  | If_pred (te_pred, te_con, te_alt) -> (
      match peval te_pred with
      | { exp = Value true; _ } -> peval { ty; exp = If_just te_con }
      | { exp = Value false; _ } -> peval { ty; exp = If_just te_alt }
      | p -> { ty; exp = If_pred (p, peval te_con, peval te_alt) })
  | Call (f, args) -> (
      match peval_args args with
      | args, None -> { ty; exp = Call (f, args) }
      | _, Some vargs ->
          (* All arguments are fully evaluated;
             Go ahead and fully evaluate the (primitive) call.
             It is a primitive call as this is a deterministic expression. *)
          let f_dist =
            {
              ret = f.ret;
              name = f.name;
              params = [];
              sampler = (fun [] -> f.sampler vargs);
              log_pmdf = (fun [] -> f.log_pmdf vargs);
            }
          in
          { ty; exp = Call (f_dist, []) })
  | If_pred_dist (p, de) -> (
      match peval p with
      | { exp = Value true; _ } -> peval de
      | { exp = Value false; _ } ->
          { ty; exp = Call (Dist.one (dty_of_dist_ty ty), []) }
      | p -> { ty; exp = If_pred_dist (p, peval de) })
  | If_just de -> { ty; exp = If_just (peval de) }

and peval_args : type a. (a, det) args -> (a, det) args * a vargs option =
  function
  | [] -> ([], Some [])
  | te :: tl -> (
      match (peval te, peval_args tl) with
      | { ty; exp = Value v }, (tl, Some vargs) ->
          ({ ty; exp = Value v } :: tl, Some ((dty_of_dat_ty ty, v) :: vargs))
      | te, (tl, _) -> (te :: tl, None))

let ( &&& ) p1 p2 : bool some_dat_det_texp =
  let { ty = Dat_ty (Tyb, s1); _ } = p1 and { ty = Dat_ty (Tyb, s2); _ } = p2 in
  let (Ex (ms, s)) = merge_stamps s1 s2 in
  Ex
    (peval
       {
         ty = Dat_ty (Tyb, s);
         exp = Bop ({ name = "&&"; op = ( && ) }, p1, p2, ms);
       })

let ( &&! ) p1 p2 =
  p1 &&& { ty = p2.ty; exp = Uop ({ name = "not"; op = not }, p2) }

let rec score : type a. (a dist_ty, det) texp -> (a dist_ty, det) texp =
  function
  | { exp = If_pred_dist (p, de); _ } ->
      { ty = de.ty; exp = If_pred_dist (p, score de) }
  | { exp = Call _; _ } as e -> e

let rec compile :
    type a s.
    env:env ->
    pred:((bool, s) dat_ty, det) texp ->
    (a, ndet) texp ->
    Graph.t * (a, det) texp =
 fun ~env ~pred { ty; exp } ->
  match exp with
  | Value _ as exp -> (Graph.empty, { ty; exp })
  | Var x -> (
      let (Ex { ty = tyx; exp }) = Map.find_exn env x in
      match eq_tys tyx ty with
      | Some Refl -> (Graph.empty, { ty; exp })
      | None -> failwith "[Bug] Type mismatch")
  | Bop (op, e1, e2, ms) ->
      let g1, te1 = compile ~env ~pred e1 in
      let g2, te2 = compile ~env ~pred e2 in
      Graph.(g1 @| g2, peval { ty; exp = Bop (op, te1, te2, ms) })
  | Uop (op, e) ->
      let g, te = compile ~env ~pred e in
      (g, peval { ty; exp = Uop (op, te) })
  | If (e_pred, e_con, e_alt, _, _) ->
      let g1, de_pred = compile ~env ~pred e_pred in
      let (Ex pred_con) = pred &&& de_pred in
      let (Ex pred_alt) = pred &&! de_pred in
      let g2, de_con = compile ~env ~pred:pred_con e_con in
      let g3, de_alt = compile ~env ~pred:pred_alt e_alt in
      let g = Graph.(g1 @| g2 @| g3) in
      (g, peval { ty; exp = If_pred (pred_con, de_con, de_alt) })
  | Let (x, e, body) ->
      let g1, det_exp1 = compile ~env ~pred e in
      let g2, det_exp2 =
        compile ~env:(Map.set env ~key:x ~data:(Ex det_exp1)) ~pred body
      in
      Graph.(g1 @| g2, det_exp2)
  | Call (f, args) ->
      let g, args = compile_args env pred args in
      (g, { ty; exp = Call (f, args) })
  | Sample e ->
      let g, de = compile ~env ~pred e in
      let v = gen_vertex () in
      let de_fvs = fv de.exp in
      let f = score de in
      let g' =
        Graph.
          {
            vertices = [ v ];
            arcs = List.map (Set.to_list de_fvs) ~f:(fun z -> (z, v));
            pmdf_map = Id.Map.singleton v (Ex f : pmdf);
            obs_map = Id.Map.empty;
          }
      in
      Graph.(g @| g', { ty; exp = Rvar v })
  | Observe (e1, e2) ->
      let g1, de1 = compile ~env ~pred e1 in
      let g2, de2 = compile ~env ~pred e2 in
      let v = gen_vertex () in
      let f1 = score de1 in
      let f = { ty = f1.ty; exp = If_pred_dist (pred, f1) } in
      let fvs = Id.(fv de1.exp @| fv pred.exp) in
      if not (Set.is_empty (fv de2.exp)) then
        failwith "[Bug] Not closed observation";
      let g' =
        Graph.
          {
            vertices = [ v ];
            arcs = List.map (Set.to_list fvs) ~f:(fun z -> (z, v));
            pmdf_map = Id.Map.singleton v (Ex f : pmdf);
            obs_map = Id.Map.singleton v (Ex de2 : obs);
          }
      in
      Graph.(g1 @| g2 @| g', { ty = Dat_ty (Tyu, Val); exp = Value () })

and compile_args :
    type a s.
    env ->
    ((bool, s) dat_ty, det) texp ->
    (a, ndet) args ->
    Graph.t * (a, det) args =
 fun env pred args ->
  match args with
  | [] -> (Graph.empty, [])
  | arg :: args ->
      let g, arg = compile ~env ~pred arg in
      let g', args = compile_args env pred args in
      Graph.(g @| g', arg :: args)

exception Query_not_found

let compile_program (prog : program) : Graph.t * Evaluator.query =
  Logs.debug (fun m ->
      m "Inlining program %a" Sexp.pp_hum [%sexp (prog : Parse_tree.program)]);
  let exp = Preprocessor.inline prog in
  Logs.debug (fun m ->
      m "Inlined program %a" Sexp.pp_hum [%sexp (exp : Parse_tree.exp)]);

  let (Ex e) = Typing.check exp in
  let g, { ty; exp } =
    compile ~env:Id.Map.empty
      ~pred:{ ty = Dat_ty (Tyb, Val); exp = Value true }
      e
  in
  match ty with
  | Dat_ty (_, Rv) -> (g, Ex { ty; exp })
  | _ -> raise Query_not_found

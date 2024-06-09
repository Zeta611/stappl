open! Core
open Parse_tree
open Typed_tree

type env = some_det Id.Map.t

let gen_vertex =
  let cnt = ref 0 in
  fun () ->
    let v = "X" ^ string_of_int !cnt in
    incr cnt;
    v

exception Score_invalid_arguments
exception Not_closed_observation

let rec peval : type a. (a, det) texp -> (a, det) texp =
 fun { ty; exp } ->
  (* TODO: consider other cases *)
  let exp =
    match exp with
    | Value _ -> exp
    | Var _ -> exp
    | Bop (op, te1, te2) -> (
        match (peval te1, peval te2) with
        (*| { ty = ty1; exp = Value v1 }, { ty = ty2; exp = Value v2 } ->*)
        (*    Value (op.op v1 v2)*)
        | te1, te2 -> Bop (op, te1, te2))
    | Uop (op, te) -> (
        match peval te with
        (*| { exp = Value v; _ } -> Value (op.op v)*)
        | e -> Uop (op, e))
    | If (te_pred, te_cons, te_alt) -> (
        match peval te_pred with
        (*| { exp = Value true; _ } -> (peval te_cons).exp*)
        (*| { exp = Value false; _ } -> (peval te_alt).exp*)
        | te_pred -> If (te_pred, peval te_cons, peval te_alt))
    | Call (f, args) -> (
        match peval_args args with
        | args, None -> Call (f, args)
        | _, Some vargs ->
            (* All arguments are fully evaluated;
               Go ahead and fully evaluate the (primitive) call.
               It is a primitive call as this is a deterministic expression. *)
            Call
              ( {
                  ret = f.ret;
                  name = f.name;
                  params = [];
                  sampler = (fun [] -> f.sampler vargs);
                  log_pmdf = (fun [] -> f.log_pmdf vargs);
                },
                [] ))
    | If_pred (p, de) -> (
        let p = peval_pred p and de = peval de in
        match p with (* TODO: *) _ -> If_pred (p, de))
    | If_con de -> If_con (peval de)
    | If_alt de -> If_alt (peval de)
  in

  { ty; exp }

and peval_args : type a. (a, det) args -> (a, det) args * a vargs option =
  function
  | [] -> ([], Some [])
  | te :: tl -> (
      match (peval te, peval_args tl) with
      | { ty; exp = Value v }, (tl, Some vargs) ->
          ({ ty; exp = Value v } :: tl, Some ((dty_of_ty ty, v) :: vargs))
      | te, (tl, _) -> (te :: tl, None))

and peval_pred : pred -> pred = function
  | Empty -> failwith "[Bug] Empty predicate"
  | True -> True
  | False -> False
  | And (p, de) -> (
      match peval de with
      | { exp = Value true; _ } -> peval_pred p
      | { exp = Value false; _ } -> False
      | de -> And (p, de))
  | And_not (p, de) -> (
      match peval de with
      | { exp = Value true; _ } -> False
      | { exp = Value false; _ } -> peval_pred p
      | de -> And_not (p, de))

let ( &&& ) p de = peval_pred (And (p, de))
let ( &&! ) p de = peval_pred (And_not (p, de))

let rec score : type a. (a, det) texp -> (a, det) texp = function
  (* TODO: consider other cases *)
  | { ty; exp = If (e_pred, e_con, e_alt) } ->
      let s_con = score e_con and s_alt = score e_alt in
      { ty; exp = If (e_pred, s_con, s_alt) }
  | { exp = Call _; _ } as e -> e
  | _ -> raise Score_invalid_arguments

let rec compile :
    type a s.
    env:env -> ?pred:pred -> (a, non_det) texp -> Graph.t * (a, det) texp =
 fun ~env ?(pred = Empty) { ty; exp } ->
  match exp with
  | Value _ as exp -> (Graph.empty, { ty; exp })
  | Var x -> (
      let (Ex { ty = tyx; exp }) = Map.find_exn env x in
      match (tyx, ty) with
      | Dat_ty (Tyu, Val), Dat_ty (Tyu, Val) -> (Graph.empty, { ty; exp })
      | Dat_ty (Tyb, Val), Dat_ty (Tyb, Val) -> (Graph.empty, { ty; exp })
      | Dat_ty (Tyi, Val), Dat_ty (Tyi, Val) -> (Graph.empty, { ty; exp })
      | Dat_ty (Tyr, Val), Dat_ty (Tyr, Val) -> (Graph.empty, { ty; exp })
      | Dat_ty (Tyu, Rv), Dat_ty (Tyu, Rv) -> (Graph.empty, { ty; exp })
      | Dat_ty (Tyb, Rv), Dat_ty (Tyb, Rv) -> (Graph.empty, { ty; exp })
      | Dat_ty (Tyi, Rv), Dat_ty (Tyi, Rv) -> (Graph.empty, { ty; exp })
      | Dat_ty (Tyr, Rv), Dat_ty (Tyr, Rv) -> (Graph.empty, { ty; exp })
      | Dist_ty Tyu, Dist_ty Tyu -> (Graph.empty, { ty; exp })
      | Dist_ty Tyb, Dist_ty Tyb -> (Graph.empty, { ty; exp })
      | Dist_ty Tyi, Dist_ty Tyi -> (Graph.empty, { ty; exp })
      | Dist_ty Tyr, Dist_ty Tyr -> (Graph.empty, { ty; exp })
      | _, _ -> failwith "[Bug] Type mismatch")
  | Bop (op, e1, e2) ->
      let g1, te1 = compile ~env ~pred e1 in
      let g2, te2 = compile ~env ~pred e2 in
      Graph.(g1 @| g2, { ty; exp = Bop (op, te1, te2) })
  | Uop (op, e) ->
      let g, te = compile ~env ~pred e in
      (g, { ty; exp = Uop (op, te) })
  | If (e_pred, e_con, e_alt) -> (
      let g1, de_pred = compile ~env ~pred e_pred in
      let pred_con = pred &&& de_pred in
      let pred_alt = pred &&! de_pred in
      let g2, de_con = compile ~env ~pred:pred_con e_con in
      let g3, de_alt = compile ~env ~pred:pred_alt e_alt in
      let g = Graph.(g1 @| g2 @| g3) in
      match pred_con with
      | True -> (g, { ty; exp = If_con de_con })
      | False -> (g, { ty; exp = If_alt de_alt })
      | _ -> (g, { ty; exp = If (de_pred, de_con, de_alt) }))
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
            pmdf_map = Id.Map.singleton v (Ex f : some_dist_texp);
            obs_map = Id.Map.empty;
          }
      in
      Graph.(g @| g', { ty; exp = Var v })
  | Observe (e1, e2) ->
      let g1, de1 = compile ~env ~pred e1 in
      let g2, de2 = compile ~env ~pred e2 in
      let v = gen_vertex () in
      let f1 = score de1 in
      let f = { ty = f1.ty; exp = If_pred (pred, f1) } in
      let fvs = Id.(fv de1.exp @| fv_pred pred) in
      if not (Set.is_empty (fv de2.exp)) then
        failwith "[Bug] Not closed observation";
      let g' =
        Graph.
          {
            vertices = [ v ];
            arcs = List.map (Set.to_list fvs) ~f:(fun z -> (z, v));
            pmdf_map = Id.Map.singleton v (Ex f : some_dist_texp);
            obs_map = Id.Map.singleton v (Ex de2 : some_dat_texp);
          }
      in
      Graph.(g1 @| g2 @| g', { ty = Dat_ty (Tyu, Val); exp = Value () })

and compile_args :
    type a. env -> pred -> (a, non_det) args -> Graph.t * (a, det) args =
 fun env pred args ->
  match args with
  | [] -> (Graph.empty, [])
  | arg :: args ->
      let g, arg = compile ~env ~pred arg in
      let g', args = compile_args env pred args in
      Graph.(g @| g', arg :: args)

exception Query_not_found

let compile_program (prog : program) : Graph.t * some_rv_texp =
  Logs.debug (fun m ->
      m "Inlining program %a" Sexp.pp_hum [%sexp (prog : Parse_tree.program)]);
  let exp = Preprocessor.inline prog in
  Logs.debug (fun m ->
      m "Inlined program %a" Sexp.pp_hum [%sexp (exp : Parse_tree.exp)]);

  let (Ex e) = Typing.check exp in
  let g, { ty; exp } = compile ~env:Id.Map.empty e in
  match ty with
  | Dat_ty (_, Rv) -> (g, Ex { ty; exp })
  | _ -> raise Query_not_found

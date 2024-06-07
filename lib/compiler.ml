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
  let exp =
    match exp with
    | (Value _ | Var _) as e -> e
    | Bop (op, te1, te2) -> (
        match (peval te1, peval te2) with
        | { exp = Value v1; _ }, { exp = Value v2; _ } -> Value (op.f v1 v2)
        | te1, te2 -> Bop (op, te1, te2))
    | Uop (op, te) -> (
        match peval te with
        | { exp = Value v; _ } -> Value (op.f v)
        | e -> Uop (op, e))
    | If (te_pred, te_cons, te_alt) -> (
        match peval te_pred with
        | { exp = Value true; _ } -> (peval te_cons).exp
        | { exp = Value false; _ } -> (peval te_alt).exp
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
  in
  { ty; exp }

and peval_args : type a. (a, det) args -> (a, det) args * a vargs option =
  function
  | [] -> ([], Some [])
  | te :: tl -> (
      match (peval te, peval_args tl) with
      | { ty; exp = Value v }, (tl, Some vargs) ->
          ({ ty; exp = Value v } :: tl, Some ((ty, v) :: vargs))
      | te, (tl, _) -> (te :: tl, None))

let rec score : type a. (a, det) texp -> Id.t -> (a, det) texp =
 fun e var ->
  match e.exp with
  | If (e_pred, e_con, e_alt) ->
      let s_con = score e_con var in
      let s_alt = score e_alt var in
      { ty = e.ty; exp = If (e_pred, s_con, s_alt) }
  | Call _ -> e
  | _ -> raise Score_invalid_arguments

let rec compile :
    type a.
    env -> (bool, det) texp -> (a, non_det) texp -> Graph.t * (a, det) texp =
 fun env pred e ->
  let { ty; exp } = e in
  match exp with
  | Value v -> (Graph.empty, { ty; exp = Value v })
  | Var x -> (
      let (Ex { ty = tx; exp }) = Map.find_exn env x in
      match (tx, ty) with
      | Tyi, Tyi -> (Graph.empty, { ty; exp })
      | Tyr, Tyr -> (Graph.empty, { ty; exp })
      | Tyb, Tyb -> (Graph.empty, { ty; exp })
      | _, _ -> assert false)
  | Bop (op, e1, e2) ->
      let g1, te1 = compile env pred e1 in
      let g2, te2 = compile env pred e2 in
      Graph.(g1 @| g2, { ty; exp = Bop (op, te1, te2) })
  | Uop (op, e) ->
      let g, te = compile env pred e in
      (g, { ty; exp = Uop (op, te) })
  | If (e_pred, e_con, e_alt) -> (
      let g1, de_pred = compile env pred e_pred in
      let pred_con =
        peval
          { ty = Tyb; exp = Bop ({ f = ( && ); name = "&&" }, pred, de_pred) }
      in
      let pred_alt =
        peval
          {
            ty = Tyb;
            exp =
              Bop
                ( { f = ( && ); name = "&&" },
                  pred,
                  { ty = Tyb; exp = Uop ({ f = not; name = "!" }, de_pred) } );
          }
      in
      let g2, de_con = compile env pred_con e_con in
      let g3, de_alt = compile env pred_alt e_alt in
      let g = Graph.(g1 @| g2 @| g3) in
      match pred_con.exp with
      | Value true -> (g, de_con)
      | Value false -> (g, de_alt)
      | _ -> (g, { ty; exp = If (de_pred, de_con, de_alt) }))
  | Let (x, e, body) ->
      let g1, det_exp1 = compile env pred e in
      let g2, det_exp2 =
        compile (Map.set env ~key:x ~data:(Ex det_exp1)) pred body
      in
      Graph.(g1 @| g2, det_exp2)
  | Call (f, args) ->
      let g, args = compile_args env pred args in
      (g, { ty; exp = Call (f, args) })
  | Sample e ->
      let g, de = compile env pred e in
      let v = gen_vertex () in
      let de_fvs = fv de.exp in
      let f : some_det = Ex (score de v) in
      let g' =
        Graph.
          {
            vertices = [ v ];
            arcs = List.map (Set.to_list de_fvs) ~f:(fun z -> (z, v));
            pmdf_map = Id.Map.singleton v f;
            obs_map = Id.Map.empty;
          }
      in
      Graph.(g @| g', { ty; exp = Var v })
  | Observe (e1, e2) ->
      let g1, de1 = compile env pred e1 in
      let g2, de2 = compile env pred e2 in
      let v = gen_vertex () in
      let f1 = score de1 v in
      let one : type a. a ty -> (a, unit) dist =
       fun ty ->
        match ty with
        | Tyi ->
            {
              ret = ty;
              name = "one";
              params = [];
              sampler = (fun _ -> 1);
              log_pmdf = (fun [] _ -> 0.0);
            }
        | Tyr ->
            {
              ret = ty;
              name = "one";
              params = [];
              sampler = (fun _ -> 1.0);
              log_pmdf = (fun [] _ -> 0.0);
            }
        | Tyb ->
            {
              ret = Tyb;
              name = "one";
              params = [];
              sampler = (fun _ -> true);
              log_pmdf = (fun [] _ -> 0.0);
            }
      in
      let f = { ty; exp = If (pred, f1, { ty; exp = Call (one ty, []) }) } in
      let fvs = Id.(fv de1.exp @| fv pred.exp) in
      if not (Set.is_empty (fv de2.exp)) then raise Not_closed_observation;
      let g' =
        Graph.
          {
            vertices = [ v ];
            arcs = List.map (Set.to_list fvs) ~f:(fun z -> (z, v));
            pmdf_map = Id.Map.singleton v (Ex f : some_det);
            obs_map = Id.Map.singleton v (Ex de2 : some_det);
          }
      in
      Graph.(g1 @| g2 @| g', de2)

and compile_args :
    type a.
    env -> (bool, det) texp -> (a, non_det) args -> Graph.t * (a, det) args =
 fun env pred args ->
  match args with
  | [] -> (Graph.empty, [])
  | arg :: args ->
      let g, arg = compile env pred arg in
      let g', args = compile_args env pred args in
      Graph.(g @| g', arg :: args)

let compile_program (prog : program) : Graph.t * some_det =
  let open Typing in
  let (Ex e) = convert Id.Map.empty (inline prog) in
  let g, e = compile Id.Map.empty { ty = Tyb; exp = Value true } e in
  (g, Ex e)

open! Core
open Program

let gen_sym =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    Printf.sprintf "#%d" !cnt

let gen_vertex =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    Printf.sprintf "X%d" !cnt

let rec sub (x : Id.t) (de : Det_exp.t) : Exp.t -> Exp.t =
  let s1 ctor e = ctor ((x |-> de) e)
  and s2 ctor e1 e2 = ctor ((x |-> de) e1) ((x |-> de) e2) in

  let open Exp in
  function
  | Var y when Id.(x = y) -> Exp.of_det_exp de
  | (Int _ | Real _ | Var _ | Bool _) as e -> e
  | Add (e1, e2) -> s2 add e1 e2
  | Radd (e1, e2) -> s2 radd e1 e2
  | Minus (e1, e2) -> s2 minus e1 e2
  | Rminus (e1, e2) -> s2 rminus e1 e2
  | Neg e -> s1 neg e
  | Rneg e -> s1 rneg e
  | Mult (e1, e2) -> s2 mult e1 e2
  | Rmult (e1, e2) -> s2 rmult e1 e2
  | Div (e1, e2) -> s2 div e1 e2
  | Rdiv (e1, e2) -> s2 rdiv e1 e2
  | Eq (e1, e2) -> s2 eq e1 e2
  | Req (e1, e2) -> s2 req e1 e2
  | Noteq (e1, e2) -> s2 noteq e1 e2
  | Less (e1, e2) -> s2 less e1 e2
  | Rless (e1, e2) -> s2 rless e1 e2
  | And (e1, e2) -> s2 and_ e1 e2
  | Or (e1, e2) -> s2 or_ e1 e2
  | Seq (e1, e2) -> s2 seq e1 e2
  | Not e -> s1 not e
  | List es -> List (List.map es ~f:(x |-> de))
  | Record fs -> Record (List.map fs ~f:(fun (f, e) -> (f, (x |-> de) e)))
  | Assign (y, e, body) when Id.(x = y) -> Assign (y, (x |-> de) e, body)
  | Assign (y, e, body) when Core.not (Set.mem (Det_exp.fv de) y) ->
      Assign (y, (x |-> de) e, (x |-> de) body)
  | Assign (y, e, body) ->
      let z = gen_sym () in
      Assign (z, (x |-> de) e, (x |-> de) @@ (y |-> Var z) body)
  | If (e_pred, e_con, e_alt) ->
      If ((x |-> de) e_pred, (x |-> de) e_con, (x |-> de) e_alt)
  | Call (f, es) -> Call (f, List.map es ~f:(x |-> de))
  | Sample e -> s1 sample e
  | Observe (e1, e2) -> s2 observe e1 e2

and ( |-> ) x de = sub x de

let gather_functions (prog : program) : Env.t =
  List.fold prog.funs ~init:Env.empty ~f:(fun env f ->
      Env.add_exn env ~name:f.name ~fn:f)

exception Not_closed_observation

let compile (program : program) : Graph.t * Det_exp.t =
  let env = gather_functions program in

  let rec compile (pred : Pred.t) : Exp.t -> Graph.t * Det_exp.t =
    let compile' e = compile pred e in

    let c0 x = (Graph.empty, x) in
    let c1 e ctor =
      let g, de = compile' e in
      (g, ctor de)
    in
    let c2 e1 e2 ctor =
      let g1, de1 = compile' e1 in
      let g2, de2 = compile' e2 in
      Graph.(g1 @| g2, ctor de1 de2)
    in

    let open Det_exp in
    let open Graph in
    function
    | Int n -> c0 (Int n)
    | Real r -> c0 (Real r)
    | Bool b -> c0 (Bool b)
    | Var x -> c0 (Var x)
    | Sample e ->
        let g, de = compile' e in
        let v = gen_vertex () in
        let de_fvs = fv de in
        let f = Dist.score de v in
        let g' =
          {
            vertices = [ v ];
            arcs = List.map (Set.to_list de_fvs) ~f:(fun z -> (z, v));
            pmdf_map = Id.Map.singleton v f;
            obs_map = Id.Map.empty;
          }
        in
        (g @| g', Var v)
    | Observe (e1, e2) ->
        let g1, de1 = compile' e1 in
        let g2, de2 = compile' e2 in
        let v = gen_vertex () in
        let f1 = Dist.score de1 v in
        let f = Dist.(If_pred (pred, f1, One)) in
        let fvs = Id.(fv de1 @| Pred.fv pred) in
        if Core.not @@ Set.is_empty (fv de2) then raise Not_closed_observation;
        let g' =
          {
            vertices = [ v ];
            arcs = List.map (Set.to_list fvs) ~f:(fun z -> (z, v));
            pmdf_map = Id.Map.singleton v f;
            obs_map = Id.Map.singleton v de2;
          }
        in
        (g1 @| g2 @| g', de2)
    | Assign (x, e, body) ->
        let g1, det_exp1 = compile' e in
        let sub_body = (x |-> det_exp1) body in
        let g2, det_exp2 = compile' sub_body in
        (g1 @| g2, det_exp2)
    | If (e_pred, e_con, e_alt) -> (
        let g1, de_pred = compile' e_pred in
        let pred_con = Pred.(eval (pred &&& de_pred)) in
        let pred_alt = Pred.(eval (pred &&! de_pred)) in
        let g2, de_con = compile pred_con e_con in
        let g3, de_alt = compile pred_alt e_alt in
        let g = Graph.(g1 @| g2 @| g3) in
        match pred_con with
        | True -> (g, de_con)
        | False -> (g, de_alt)
        | _ -> (g, If (de_pred, de_con, de_alt)))
    | Call (c, params) -> (
        let g, det_exps =
          List.fold_map params ~init:Graph.empty ~f:(fun g e ->
              let g', de = compile' e in
              let evaled_de = eval de in
              (g @| g', evaled_de))
        in
        match Env.find env ~name:c with
        | Some f ->
            let { params; body; _ } = f in
            let param_det_pairs = List.zip_exn params det_exps in
            let sub_body =
              List.fold param_det_pairs ~init:body
                ~f:(fun acc (param_name, det_exp) ->
                  (param_name |-> det_exp) acc)
            in
            let g_body, det_exp_body = compile' sub_body in
            (g @| g_body, det_exp_body)
        | None -> (g, Prim_call (c, det_exps)))
    | Add (e1, e2) -> c2 e1 e2 add
    | Radd (e1, e2) -> c2 e1 e2 radd
    | Minus (e1, e2) -> c2 e1 e2 minus
    | Rminus (e1, e2) -> c2 e1 e2 rminus
    | Neg e -> c1 e neg
    | Rneg e -> c1 e rneg
    | Mult (e1, e2) -> c2 e1 e2 mult
    | Rmult (e1, e2) -> c2 e1 e2 rmult
    | Div (e1, e2) -> c2 e1 e2 div
    | Rdiv (e1, e2) -> c2 e1 e2 rdiv
    | Eq (e1, e2) -> c2 e1 e2 eq
    | Req (e1, e2) -> c2 e1 e2 req
    | Noteq (e1, e2) -> c2 e1 e2 noteq
    | Less (e1, e2) -> c2 e1 e2 less
    | Rless (e1, e2) -> c2 e1 e2 rless
    | And (e1, e2) -> c2 e1 e2 and_
    | Or (e1, e2) -> c2 e1 e2 or_
    | Seq (e1, e2) -> c2 e1 e2 (fun _ de -> de)
    | Not e -> c1 e not
    | List es ->
        let g, des =
          List.fold_map es ~init:Graph.empty ~f:(fun g e ->
              let g', de = compile' e in
              (g @| g', de))
        in
        (g, List des)
    | Record fields ->
        let g, des =
          List.fold_map fields ~init:Graph.empty ~f:(fun g (k, v) ->
              let g_k, de_k = compile' k in
              let g_v, de_v = compile' v in
              (g @| g_k @| g_v, (de_k, de_v)))
        in
        (g, Record des)
  in
  compile Pred.Empty program.exp

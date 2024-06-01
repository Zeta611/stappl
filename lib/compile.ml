open Core
open Program

type number = Int of int | Float of float

module Env = struct
  type t = (Id.t, fn, Id.comparator_witness) Map.t

  let empty : t = Map.empty (module Id)
  let add (env : t) ~(name : Id.t) ~(fn : fn) = Map.add env ~key:name ~data:fn
  let find_exn (env : t) ~(name : Id.t) : fn = Map.find_exn env name
end

module Pred = struct
  type t
end

module Graph = struct
  type vertex = Id.t
  type arc = vertex * vertex
  type det_map = (Id.t, Det_exp.t, Id.comparator_witness) Map.t
  type obs_map = (Id.t, number, Id.comparator_witness) Map.t

  type t = {
    vertices : vertex list;
    arcs : arc list;
    det_map : det_map;
    obs_map : obs_map;
  }

  let empty =
    {
      vertices = [];
      arcs = [];
      det_map = Map.empty (module Id);
      obs_map = Map.empty (module Id);
    }
end

let gen_sym =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    Printf.sprintf "X_%d" !cnt

let rec sub (exp : Exp.t) (x : Id.t) (det_exp : Det_exp.t) : Exp.t =
  let sub' exp = sub exp x det_exp in
  match exp with
  | Int n -> Int n
  | Real r -> Real r
  | Var y when Id.(x = y) -> Det_exp.to_exp det_exp
  | Var y -> Var y
  | Add (e1, e2) -> Add (sub' e1, sub' e2)
  | Radd (e1, e2) -> Radd (sub' e1, sub' e2)
  | Minus (e1, e2) -> Minus (sub' e1, sub' e2)
  | Rminus (e1, e2) -> Rminus (sub' e1, sub' e2)
  | Neg e -> Neg (sub' e)
  | Rneg e -> Rneg (sub' e)
  | Mult (e1, e2) -> Mult (sub' e1, sub' e2)
  | Rmult (e1, e2) -> Rmult (sub' e1, sub' e2)
  | Div (e1, e2) -> Div (sub' e1, sub' e2)
  | Rdiv (e1, e2) -> Rdiv (sub' e1, sub' e2)
  | Eq (e1, e2) -> Eq (sub' e1, sub' e2)
  | Noteq (e1, e2) -> Noteq (sub' e1, sub' e2)
  | Less (e1, e2) -> Less (sub' e1, sub' e2)
  | And (e1, e2) -> And (sub' e1, sub' e2)
  | Or (e1, e2) -> Or (sub' e1, sub' e2)
  | Seq (e1, e2) -> Seq (sub' e1, sub' e2)
  | Not e -> Not (sub' e)
  | List es -> List (List.map es ~f:sub')
  | Record fs -> Record (List.map fs ~f:(fun (f, e) -> (f, sub' e)))
  | Assign (y, e, body) when Id.(x = y) -> Assign (y, sub' e, body)
  | Assign (y, e, body) when not (Set.mem (Det_exp.fv det_exp) y) ->
      Assign (y, sub' e, sub' body)
  | Assign (y, e, body) ->
      let z = gen_sym () in
      Assign (z, sub' e, sub' @@ sub body y (Det_exp.Var z))
  | If (e_pred, e_con, e_alt) -> If (sub' e_pred, sub' e_con, sub' e_alt)
  | Call (f, es) -> Call (f, List.map es ~f:sub')
  | Sample e -> Sample (sub' e)
  | Observe (e1, e2) -> Observe (sub' e1, sub' e2)

let compile (env : Env.t) (pred : Pred.t) (exp : Exp.t) : Graph.t * Det_exp.t =
  ignore env;
  ignore pred;
  match exp with
  | Int n -> (Graph.empty, Det_exp.Int n)
  | Real r -> (Graph.empty, Det_exp.Real r)
  | Var x -> (Graph.empty, Det_exp.Var x)
  | _ -> failwith "Not implemented"

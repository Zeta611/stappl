open Core
module Id = String

module Exp = struct
  type t =
    | Int of int
    | Real of float
    | Var of Id.t
    | Add of t * t
    | Radd of t * t
    | Minus of t * t
    | Rminus of t * t
    | Neg of t
    | Rneg of t
    | Mult of t * t
    | Rmult of t * t
    | Div of t * t
    | Rdiv of t * t
    | Eq of t * t
    | Noteq of t * t
    | Less of t * t
    | And of t * t
    | Or of t * t
    | Seq of t * t
    | Not of t
    | List of t list
    | Record of (t * t) list
    | Assign of Id.t * t * t
    | If of t * t * t
    | Call of Id.t * t list
    | Sample of t
    | Observe of t * t
  [@@deriving sexp]
end

type fn = { name : Id.t; params : Id.t list; body : Exp.t } [@@deriving sexp]
type program = { funs : fn list; exp : Exp.t } [@@deriving sexp]

module Det_exp = struct
  type t =
    | Int of int
    | Real of float
    | Var of Id.t
    | Add of t * t
    | Radd of t * t
    | Minus of t * t
    | Rminus of t * t
    | Neg of t
    | Rneg of t
    | Mult of t * t
    | Rmult of t * t
    | Div of t * t
    | Rdiv of t * t
    | Eq of t * t
    | Noteq of t * t
    | Less of t * t
    | And of t * t
    | Or of t * t
    | Not of t
    | List of t list
    | Record of (t * t) list
    | If of t * t * t
    | Prim_call of Id.t * t list
  [@@deriving sexp]

  let rec to_exp = function
    | Int i -> Exp.Int i
    | Real f -> Exp.Real f
    | Var x -> Exp.Var x
    | Add (e1, e2) -> Exp.Add (to_exp e1, to_exp e2)
    | Radd (e1, e2) -> Exp.Radd (to_exp e1, to_exp e2)
    | Minus (e1, e2) -> Exp.Minus (to_exp e1, to_exp e2)
    | Rminus (e1, e2) -> Exp.Rminus (to_exp e1, to_exp e2)
    | Neg e -> Exp.Neg (to_exp e)
    | Rneg e -> Exp.Rneg (to_exp e)
    | Mult (e1, e2) -> Exp.Mult (to_exp e1, to_exp e2)
    | Rmult (e1, e2) -> Exp.Rmult (to_exp e1, to_exp e2)
    | Div (e1, e2) -> Exp.Div (to_exp e1, to_exp e2)
    | Rdiv (e1, e2) -> Exp.Rdiv (to_exp e1, to_exp e2)
    | Eq (e1, e2) -> Exp.Eq (to_exp e1, to_exp e2)
    | Noteq (e1, e2) -> Exp.Noteq (to_exp e1, to_exp e2)
    | Less (e1, e2) -> Exp.Less (to_exp e1, to_exp e2)
    | And (e1, e2) -> Exp.And (to_exp e1, to_exp e2)
    | Or (e1, e2) -> Exp.Or (to_exp e1, to_exp e2)
    | Not e -> Exp.Not (to_exp e)
    | List es -> Exp.List (List.map ~f:to_exp es)
    | Record fields ->
        Exp.Record (List.map ~f:(fun (k, v) -> (to_exp k, to_exp v)) fields)
    | If (cond, e1, e2) -> Exp.If (to_exp cond, to_exp e1, to_exp e2)
    | Prim_call (id, es) -> Exp.Call (id, List.map ~f:to_exp es)

  let rec fv : t -> (Id.t, Id.comparator_witness) Set.t = function
    | Int _ | Real _ -> Set.empty (module Id)
    | Var x -> Set.singleton (module Id) x
    | Add (e1, e2)
    | Radd (e1, e2)
    | Minus (e1, e2)
    | Rminus (e1, e2)
    | Mult (e1, e2)
    | Rmult (e1, e2)
    | Div (e1, e2)
    | Rdiv (e1, e2)
    | Eq (e1, e2)
    | Noteq (e1, e2)
    | Less (e1, e2)
    | And (e1, e2)
    | Or (e1, e2) ->
        Set.union (fv e1) (fv e2)
    | Neg e | Rneg e | Not e -> fv e
    | List es ->
        List.fold es
          ~init:(Set.empty (module Id))
          ~f:(fun acc e -> Set.union acc (fv e))
    | Record fields ->
        List.fold fields
          ~init:(Set.empty (module Id))
          ~f:(fun acc (k, v) -> Set.(union acc (union (fv k) (fv v))))
    | If (cond, e1, e2) -> Set.(union (fv cond) (union (fv e1) (fv e2)))
    | Prim_call (id, es) ->
        List.fold es
          ~init:(Set.singleton (module Id) id)
          ~f:(fun acc e -> Set.union acc (fv e))
end

let pp pgm = print_endline (sexp_of_program pgm |> Sexp.to_string_hum)

open Core

type id = string [@@deriving sexp]

module Exp = struct
  type t =
    | Int of int
    | Real of float
    | Var of id
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
    | Assign of id * t * t
    | If of t * t * t
    | Call of id * t list
    | Sample of t
    | Observe of t * t
  [@@deriving sexp]
end

type fn = { name : id; params : id list; body : Exp.t } [@@deriving sexp]
type program = { funs : fn list; exp : Exp.t } [@@deriving sexp]

module Det_exp = struct
  type t =
    | Int of int
    | Real of float
    | Var of id
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
    | Prim_call of id * t list
  [@@deriving sexp]
end

let pp pgm = print_endline (sexp_of_program pgm |> Sexp.to_string_hum)

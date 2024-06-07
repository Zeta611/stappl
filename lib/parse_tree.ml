open! Core

type exp =
  | Int of int
  | Real of float
  | Bool of bool
  | Var of Id.t
  | Add of exp * exp
  | Radd of exp * exp
  | Minus of exp * exp
  | Rminus of exp * exp
  | Neg of exp
  | Rneg of exp
  | Mult of exp * exp
  | Rmult of exp * exp
  | Div of exp * exp
  | Rdiv of exp * exp
  | Eq of exp * exp
  | Req of exp * exp
  | Noteq of exp * exp
  | Less of exp * exp
  | Rless of exp * exp
  | And of exp * exp
  | Or of exp * exp
  | Seq of exp * exp
  | Not of exp
  | List of exp list
  | Record of (exp * exp) list
  | Assign of Id.t * exp * exp
  | If of exp * exp * exp
  | Call of Id.t * exp list
  | Sample of exp
  | Observe of exp * exp
[@@deriving sexp]

type fn = { name : Id.t; params : Id.t list; body : exp } [@@deriving sexp]
type program = { funs : fn list; exp : exp } [@@deriving sexp]

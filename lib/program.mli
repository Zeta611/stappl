module Id = Core.String

module Exp : sig
  type t =
    | Int of int
    | Real of float
    | Var of string
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
    | Assign of string * t * t
    | If of t * t * t
    | Call of string * t list
    | Sample of t
    | Observe of t * t

  val t_of_sexp : Sexplib0.Sexp.t -> t
  val sexp_of_t : t -> Sexplib0.Sexp.t
end

type fn = { name : string; params : string list; body : Exp.t }

val fn_of_sexp : Sexplib0.Sexp.t -> fn
val sexp_of_fn : fn -> Sexplib0.Sexp.t

type program = { funs : fn list; exp : Exp.t }

val program_of_sexp : Sexplib0.Sexp.t -> program
val sexp_of_program : program -> Sexplib0.Sexp.t

module Det_exp : sig
  type t =
    | Int of int
    | Real of float
    | Var of string
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
    | Prim_call of string * t list

  val t_of_sexp : Sexplib0.Sexp.t -> t
  val sexp_of_t : t -> Sexplib0.Sexp.t
  val to_exp : t -> Exp.t
  val fv : t -> (string, Id.comparator_witness) Base.Set.t
end

val pp : program -> unit

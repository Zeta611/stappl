type t

val t_of_sexp : Sexplib0.Sexp.t -> t
val sexp_of_t : t -> Sexplib0.Sexp.t

type one = One

val one_of_sexp : Sexplib0.Sexp.t -> one
val sexp_of_one : one -> Sexplib0.Sexp.t

type exp =
  | If_de of Program.Det_exp.t * exp * exp
  | If_pred of Pred.t * exp * one
  | Dist_obj of { dist : t; var : string; args : Program.Det_exp.t list }

val exp_of_sexp : Sexplib0.Sexp.t -> exp
val sexp_of_exp : exp -> Sexplib0.Sexp.t

exception Score_invalid_arguments

val prim_to_dist : string -> t
val score : Program.Det_exp.t -> string -> exp

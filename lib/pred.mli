type t =
  | Empty
  | And of Program.Det_exp.t * t
  | And_not of Program.Det_exp.t * t

val t_of_sexp : Sexplib0.Sexp.t -> t
val sexp_of_t : t -> Sexplib0.Sexp.t
val fv : t -> Base.Set.M(Program.Id).t

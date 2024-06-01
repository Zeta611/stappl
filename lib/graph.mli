type vertex = string

val vertex_of_sexp : Sexplib0.Sexp.t -> vertex
val sexp_of_vertex : vertex -> Sexplib0.Sexp.t

type arc = vertex * vertex

val arc_of_sexp : Sexplib0.Sexp.t -> arc
val sexp_of_arc : arc -> Sexplib0.Sexp.t

type det_map = Dist.exp Base.Map.M(Program.Id).t

val det_map_of_sexp : Sexplib0.Sexp.t -> det_map
val sexp_of_det_map : det_map -> Sexplib0.Sexp.t

type obs_map = Program.Det_exp.t Base.Map.M(Program.Id).t

val obs_map_of_sexp : Sexplib0.Sexp.t -> obs_map
val sexp_of_obs_map : obs_map -> Sexplib0.Sexp.t

type t = {
  vertices : vertex list;
  arcs : arc list;
  det_map : det_map;
  obs_map : obs_map;
}

val t_of_sexp : Sexplib0.Sexp.t -> t
val sexp_of_t : t -> Sexplib0.Sexp.t
val empty : t
val union : t -> t -> t
val pp : t -> string
val ( @+ ) : t -> t -> t

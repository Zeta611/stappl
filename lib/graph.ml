open Core
open Program

type vertex = Id.t [@@deriving sexp]
type arc = vertex * vertex [@@deriving sexp]
type det_map = Dist.exp Map.M(Id).t [@@deriving sexp]
type obs_map = Det_exp.t Map.M(Id).t [@@deriving sexp]

type t = {
  vertices : vertex list;
  arcs : arc list;
  det_map : det_map;
  obs_map : obs_map;
}
[@@deriving sexp]

let empty =
  {
    vertices = [];
    arcs = [];
    det_map = Map.empty (module Id);
    obs_map = Map.empty (module Id);
  }

let union g1 g2 =
  {
    vertices = g1.vertices @ g2.vertices;
    arcs = g1.arcs @ g2.arcs;
    det_map =
      Map.merge g1.det_map g2.det_map ~f:(fun ~key:_ v ->
          match v with
          | `Left det | `Right det -> Some det
          | `Both _ ->
              failwith "Graph.union: duplicate deterministic expression");
    obs_map =
      Map.merge g1.obs_map g2.obs_map ~f:(fun ~key:_ v ->
          match v with
          | `Left obs | `Right obs -> Some obs
          | `Both _ -> failwith "Graph.union: duplicate observation");
  }

let pp (graph : t) : string = graph |> sexp_of_t |> Sexp.to_string_hum
let ( @+ ) = union

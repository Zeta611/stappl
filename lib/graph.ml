open! Core
open Program
open Typed_tree

type vertex = Id.t
type arc = vertex * vertex
type pmdf_map = any_det Id.Map.t
type obs_map = any_det Id.Map.t

type t = {
  vertices : vertex list;
  arcs : arc list;
  pmdf_map : pmdf_map;
  obs_map : obs_map;
}

let empty =
  { vertices = []; arcs = []; pmdf_map = Id.Map.empty; obs_map = Id.Map.empty }

let union g1 g2 =
  {
    vertices = g1.vertices @ g2.vertices;
    arcs = g1.arcs @ g2.arcs;
    pmdf_map =
      Map.merge g1.pmdf_map g2.pmdf_map ~f:(fun ~key:_ v ->
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

let ( @| ) = union

let unobserved_vertices_pmdfs ({ vertices; pmdf_map; obs_map; _ } : t) :
    (vertex * any_det) list =
  List.filter_map vertices ~f:(fun v ->
      if Map.mem obs_map v then None
      else
        let pmdf = Map.find_exn pmdf_map v in
        Some (v, pmdf))

open Core

type number = Int of int | Float of float
type det_exp

module Env = struct
  type t = (Program.id, Program.fn, String.comparator_witness) Map.t

  let empty : t = Map.empty (module String)

  let add (env : t) ~(name : Program.id) ~(fn : Program.fn) =
    Map.add env ~key:name ~data:fn

  let find_exn (env : t) ~(name : Program.id) : Program.fn =
    Map.find_exn env name
end

module Graphical_model = struct
  type vertex = Program.id
  type arc = vertex * vertex
  type det_map = (Program.id, det_exp, String.comparator_witness) Map.t
  type obs_map = (Program.id, number, String.comparator_witness) Map.t

  type t = {
    vertices : vertex list;
    arcs : arc list;
    det_map : det_map;
    obs_map : obs_map;
  }
end

let compile (exp : Program.exp) =
  match exp with _ -> failwith "Not implemented"

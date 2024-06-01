open Core

type number = Int of int | Float of float

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

  type det_map =
    (Program.id, Program.Det_exp.t, String.comparator_witness) Map.t

  type obs_map = (Program.id, number, String.comparator_witness) Map.t

  type t = {
    vertices : vertex list;
    arcs : arc list;
    det_map : det_map;
    obs_map : obs_map;
  }

  let empty =
    {
      vertices = [];
      arcs = [];
      det_map = Map.empty (module String);
      obs_map = Map.empty (module String);
    }
end

let compile (env : Env.t) (exp : Program.Exp.t) :
    Graphical_model.t * Program.Det_exp.t =
  match exp with
  | Int n -> (Graphical_model.empty, Program.Det_exp.Int n)
  | _ -> failwith "Not implemented"

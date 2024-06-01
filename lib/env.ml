open! Core
open Program

type t = fn Id.Map.t

let empty : t = Id.Map.empty

let add_exn (env : t) ~(name : Id.t) ~(fn : fn) =
  Map.add_exn env ~key:name ~data:fn

let find (env : t) ~(name : Id.t) : fn option = Map.find env name

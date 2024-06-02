open! Core
open Program

type t = float Id.Map.t [@@deriving sexp]

let empty : t = Id.Map.empty

let set (env : t) ~(name : Id.t) ~(value : float) : t =
  Map.set env ~key:name ~data:value

let find (env : t) ~(name : Id.t) : float option = Map.find env name

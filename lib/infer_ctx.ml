open! Core
open Program

type t = float Id.Table.t [@@deriving sexp]

let create : unit -> t = Id.Table.create

let set (env : t) ~(name : Id.t) ~(value : float) : unit =
  Hashtbl.set env ~key:name ~data:value

let find (env : t) ~(name : Id.t) : float option = Hashtbl.find env name

open! Core
open Program

type t = float Id.Table.t [@@deriving sexp]

let create : unit -> t = Id.Table.create

let set (env : t) ~(name : Id.t) ~(value : float) : unit =
  Hashtbl.set env ~key:name ~data:value

let find_exn (env : t) ~(name : Id.t) : float = Hashtbl.find_exn env name

open! Core
open Program

type t = (Id.t, float, Id.comparator_witness) Map.t

let empty : t = Map.empty (module Id)

let add (env : t) (x : Id.t) (value : float) : t =
  Map.add_exn env ~key:x ~data:value

let find (env : t) (x : Id.t) : float option = Map.find env x

open! Core
open Program

type t = (Id.t, float, Id.comparator_witness) Map.t

let empty : t = Map.empty (module Id)

let add (env : t) (x : Id.t) (value : float) : t =
  Map.set env ~key:x ~data:value

let find (env : t) (x : Id.t) : float option = Map.find env x

let to_string (env : t) : string =
  Map.to_alist env
  |> List.map ~f:(fun (x, value) ->
         Id.to_string x ^ " = " ^ Float.to_string value)
  |> String.concat ~sep:", " |> Printf.sprintf "{ %s }"

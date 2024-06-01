open! Core
open Program

type t = Empty | And of Det_exp.t * t | And_not of Det_exp.t * t
[@@deriving sexp]

let ( &&& ) p de = And (de, p)
let ( &&! ) p de = And_not (de, p)

let rec fv : t -> Id.Set.t = function
  | Empty -> Id.Set.empty
  | And (de, p) | And_not (de, p) -> Id.(Det_exp.fv de @| fv p)

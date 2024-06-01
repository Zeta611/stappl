open Core
open Program

type t = Empty | And of Det_exp.t * t | And_not of Det_exp.t * t
[@@deriving sexp]

let ( &&& ) p de = And (de, p)
let ( &&! ) p de = And_not (de, p)

let rec fv : t -> Set.M(Id).t = function
  | Empty -> Set.empty (module Id)
  | And (de, p) | And_not (de, p) -> Set.union (Det_exp.fv de) (fv p)

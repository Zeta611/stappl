open! Core
open Program

type t =
  | Empty
  | True
  | False
  | And of Det_exp.t * t
  | And_not of Det_exp.t * t
[@@deriving sexp]

let ( &&& ) p de = And (de, p)
let ( &&! ) p de = And_not (de, p)

let rec fv : t -> Id.Set.t = function
  | Empty | True | False -> Id.Set.empty
  | And (de, p) | And_not (de, p) -> Id.(Det_exp.fv de @| fv p)

exception Eval_empty_predicate

let rec eval (pred : t) : t =
  match pred with
  | Empty -> raise Eval_empty_predicate
  | True | False -> pred
  | And (de, p) -> (
      match Det_exp.eval de with
      | Bool true -> eval p
      | Bool false -> False
      | _ -> pred)
  | And_not (de, p) -> (
      match Det_exp.eval de with
      | Bool true -> False
      | Bool false -> eval p
      | _ -> pred)

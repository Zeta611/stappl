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
  | Empty -> Id.Set.empty
  | True -> Id.Set.empty
  | False -> Id.Set.empty
  | And (de, p) | And_not (de, p) -> Id.(Det_exp.fv de @| fv p)

let rec to_string : t -> string = function
  | Empty -> "Empty"
  | True -> "True"
  | False -> "False"
  | And (de, p) ->
      Printf.sprintf "%s &&& %s" (Det_exp.to_string de) (to_string p)
  | And_not (de, p) ->
      Printf.sprintf "%s &&! %s" (Det_exp.to_string de) (to_string p)

let rec eval (exp : t) : t =
  match exp with
  | Empty | True | False -> exp
  | And (de, p) -> (
      match Det_exp.eval de with
      | Bool true -> eval p
      | Bool false -> False
      | _ -> exp)
  | And_not (de, p) -> (
      match Det_exp.eval de with
      | Bool true -> False
      | Bool false -> eval p
      | _ -> exp)

open! Core
open Program

type t = Empty | And of Det_exp.t * t | And_not of Det_exp.t * t
[@@deriving sexp]

let ( &&& ) p de = And (de, p)
let ( &&! ) p de = And_not (de, p)

let rec fv : t -> Id.Set.t = function
  | Empty -> Id.Set.empty
  | And (de, p) | And_not (de, p) -> Id.(Det_exp.fv de @| fv p)

let rec eval (exp : t) : bool option =
  let de_eval de =
    match Det_exp.eval de with
    | Bool true -> Some true
    | Bool false -> Some false
    | _ -> None
  in
  match exp with
  | Empty -> Some true
  | And (de, p) -> (
      match de_eval de with
      | Some true -> eval p
      | Some false -> Some false
      | None -> None)
  | And_not (de, p) -> (
      match de_eval de with
      | Some true -> Some false
      | Some false -> eval p
      | None -> None)

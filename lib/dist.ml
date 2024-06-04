open! Core
open Program

type t = string [@@deriving sexp]
type one = One [@@deriving sexp]

type exp =
  | If_de of Det_exp.t * exp * exp
  | If_pred of Pred.t * exp * one
  | Dist_obj of { dist : t; var : Id.t; args : Det_exp.t list }
[@@deriving sexp]

exception Score_invalid_arguments

let prim_to_dist : Id.t -> t = function a -> a

let rec score (det_exp : Det_exp.t) (var : Id.t) =
  match det_exp with
  | If (e_pred, e_con, e_alt) ->
      let s_con = score e_con var in
      let s_alt = score e_alt var in
      If_de (e_pred, s_con, s_alt)
  | Prim_call (c, es) -> Dist_obj { dist = prim_to_dist c; var; args = es }
  | _ -> raise Score_invalid_arguments

let rec fv : exp -> Id.Set.t = function
  | If_de (de, e1, e2) -> Id.(Det_exp.fv de @| fv e1 @| fv e2)
  | If_pred (pred, e1, One) -> Id.(Pred.fv pred @| fv e1)
  | Dist_obj { args; _ } ->
      List.fold args ~init:Id.Set.empty ~f:(fun acc e ->
          Id.(Det_exp.fv e @| acc))

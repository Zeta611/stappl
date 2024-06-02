open! Core

module Id = struct
  let ( @| ) = Set.union

  include String
end

module Det_exp = struct
  type t =
    | Int of int
    | Real of float
    | Bool of bool
    | Var of Id.t
    | Add of t * t
    | Radd of t * t
    | Minus of t * t
    | Rminus of t * t
    | Neg of t
    | Rneg of t
    | Mult of t * t
    | Rmult of t * t
    | Div of t * t
    | Rdiv of t * t
    | Eq of t * t
    | Req of t * t
    | Noteq of t * t
    | Less of t * t
    | Rless of t * t
    | And of t * t
    | Or of t * t
    | Not of t
    | List of t list
    | Record of (t * t) list
    | If of t * t * t
    | Prim_call of Id.t * t list
  [@@deriving sexp, variants, stable_variant]

  let to_string (de : t) : string = de |> sexp_of_t |> Sexp.to_string_hum

  let rec fv : t -> Id.Set.t =
    let open Id in
    function
    | Int _ | Real _ | Bool _ -> Id.Set.empty
    | Var x -> Id.Set.singleton x
    | Add (e1, e2)
    | Radd (e1, e2)
    | Minus (e1, e2)
    | Rminus (e1, e2)
    | Mult (e1, e2)
    | Rmult (e1, e2)
    | Div (e1, e2)
    | Rdiv (e1, e2)
    | Eq (e1, e2)
    | Req (e1, e2)
    | Noteq (e1, e2)
    | Less (e1, e2)
    | Rless (e1, e2)
    | And (e1, e2)
    | Or (e1, e2) ->
        fv e1 @| fv e2
    | Neg e | Rneg e | Not e -> fv e
    | List es -> List.fold es ~init:Id.Set.empty ~f:(fun acc e -> acc @| fv e)
    | Record fields ->
        List.fold fields ~init:Id.Set.empty ~f:(fun acc (k, v) ->
            acc @| fv k @| fv v)
    | If (cond, e1, e2) -> fv cond @| fv e1 @| fv e2
    | Prim_call (_, es) ->
        List.fold es ~init:Id.Set.empty ~f:(fun acc e -> acc @| fv e)

  let rec eval (exp : t) : t =
    let evi dom ctor op e1 e2 =
      match (eval e1, eval e2) with
      | Int i1, Int i2 -> dom (op i1 i2)
      | ee1, ee2 -> ctor ee1 ee2
    and evr dom ctor op e1 e2 =
      match (eval e1, eval e2) with
      | Real r1, Real r2 -> dom (op r1 r2)
      | ee1, ee2 -> ctor ee1 ee2
    and evb dom ctor op e1 e2 =
      match (eval e1, eval e2) with
      | Bool b1, Bool b2 -> dom (op b1 b2)
      | ee1, ee2 -> ctor ee1 ee2
    in
    let evii = evi int
    and evib = evi bool
    and evrr = evr real
    and evrb = evr bool
    and evbb = evb bool in

    match exp with
    | Int _ | Real _ | Var _ | Bool _ -> exp
    | Add (e1, e2) -> evii add ( + ) e1 e2
    | Radd (e1, e2) -> evrr radd ( +. ) e1 e2
    | Minus (e1, e2) -> evii minus ( - ) e1 e2
    | Rminus (e1, e2) -> evrr rminus ( -. ) e1 e2
    | Neg e -> ( match eval e with Int i -> Int (-i) | e -> e)
    | Rneg e -> ( match eval e with Real r -> Real (-.r) | e -> e)
    | Mult (e1, e2) -> evii mult ( * ) e1 e2
    | Rmult (e1, e2) -> evrr rmult ( *. ) e1 e2
    | Div (e1, e2) -> evii div ( / ) e1 e2
    | Rdiv (e1, e2) -> evrr rdiv ( /. ) e1 e2
    | Eq (e1, e2) -> evib eq ( = ) e1 e2
    | Req (e1, e2) -> evrb req Float.( = ) e1 e2
    | Noteq (e1, e2) -> evib noteq ( <> ) e1 e2
    | Less (e1, e2) -> evib less ( < ) e1 e2
    | Rless (e1, e2) -> evrb rless Float.( < ) e1 e2
    | And (e1, e2) -> evbb and_ ( && ) e1 e2
    | Or (e1, e2) -> evbb or_ ( || ) e1 e2
    | Not e -> ( match eval e with Bool b -> Bool (Core.not b) | e -> e)
    | List es -> List (List.map es ~f:eval)
    | Record fields ->
        Record (List.map fields ~f:(fun (k, v) -> (eval k, eval v)))
    | If (cond, e1, e2) -> (
        match eval cond with
        | Bool true -> eval e1
        | Bool false -> eval e2
        | cond -> If (cond, eval e1, eval e2))
    | Prim_call (f, es) ->
        (* Evaluate arguments while checking if all arguments are fully evaluated *)
        let all_const, ev_args =
          List.fold_map es ~init:true ~f:(fun full_ev e ->
              match eval e with
              | (Int _ | Real _ | Bool _) as e -> (full_ev, e)
              | e -> (false, e))
        in
        if all_const then
          (* TODO Return an evaluated distribution object *)
          Prim_call (f, ev_args)
        else Prim_call (f, ev_args)
end

module Exp = struct
  type t =
    | Int of int
    | Real of float
    | Bool of bool
    | Var of Id.t
    | Add of t * t
    | Radd of t * t
    | Minus of t * t
    | Rminus of t * t
    | Neg of t
    | Rneg of t
    | Mult of t * t
    | Rmult of t * t
    | Div of t * t
    | Rdiv of t * t
    | Eq of t * t
    | Req of t * t
    | Noteq of t * t
    | Less of t * t
    | Rless of t * t
    | And of t * t
    | Or of t * t
    | Seq of t * t
    | Not of t
    | List of t list
    | Record of (t * t) list
    | Assign of Id.t * t * t
    | If of t * t * t
    | Call of Id.t * t list
    | Sample of t
    | Observe of t * t
  [@@deriving
    sexp,
      variants,
      stable_variant ~version:Det_exp.t
        ~remove:[ Call; Seq; Assign; Sample; Observe ]
        ~add:[ Prim_call ]]

  let rec of_det_exp (de : Det_exp.t) : t =
    of_Det_exp_t
      ~remove_Prim_call:(fun f es -> Call (f, List.map es ~f:of_det_exp))
      de
end

type fn = { name : Id.t; params : Id.t list; body : Exp.t } [@@deriving sexp]
type program = { funs : fn list; exp : Exp.t } [@@deriving sexp]

let pretty (prog : program) : string =
  prog |> sexp_of_program |> Sexp.to_string_hum

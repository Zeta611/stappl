open! Core

module Id = struct
  let ( @| ) = Set.union

  include String
end

module Type_safe = struct
  type real = float

  type _ value =
    | Int : int -> int value
    | Real : real -> real value
    | Bool : bool -> bool value

  type _ ty = Tyi : int ty | Tyr : real ty | Tyb : bool ty
  type ('a, 'b, 'c) bop = ('a ty * 'b ty * 'c ty) * ('a -> 'b -> 'c)
  type ('a, 'b) uop = ('a ty * 'b ty) * ('a -> 'b)
  type det = Det
  type non_det = Non_det

  type (_, _) exp =
    | Value : 'a value -> ('a, _) exp
    | Var : Id.t -> _ exp
    | Bop : ('a, 'b, 'c) bop * ('a, 'd) exp * ('b, 'd) exp -> ('c, 'd) exp
    | Uop : ('a, 'b) uop * ('a, 'd) exp -> ('b, 'd) exp
    (* TODO: Add list and record constructors *)
    (*| List : ('a, 'd) exp list -> ('a list, 'd) exp*)
    (*| Record : ('k * 'v, 'd) exp list -> ('k * 'v, 'd) exp*)
    | If : (bool, 'd) exp * ('a, 'd) exp * ('a, 'd) exp -> ('a, 'd) exp
    | Let : Id.t * ('a, non_det) exp * ('b, non_det) exp -> ('b, non_det) exp
    | Call : ('a -> 'b, 'd) exp * ('a, 'd) exp -> ('b, 'd) exp
    | Sample : ('a, non_det) exp -> ('a, non_det) exp
    | Observe : ('a, non_det) exp * ('a, non_det) exp -> ('a, non_det) exp

  let rec fv : type a. (a, det) exp -> Id.Set.t = function
    | Value _ -> Id.Set.empty
    | Var x -> Id.Set.singleton x
    | Bop (_, e1, e2) -> Id.(fv e1 @| fv e2)
    | Uop (_, e) -> fv e
    | If (e_pred, e_cons, e_alt) -> Id.(fv e_pred @| fv e_cons @| fv e_alt)
    | Call (f, e) -> Id.(fv f @| fv e)

  let bop (type a b c) (op : (a, b, c) bop) (v1 : a value) (v2 : b value) :
      c value =
    match (op, v1, v2) with
    | ((Tyi, Tyi, Tyi), op), Int i1, Int i2 -> Int (op i1 i2)
    | ((Tyi, Tyi, Tyr), op), Int i1, Int i2 -> Real (op i1 i2)
    | ((Tyi, Tyi, Tyb), op), Int i1, Int i2 -> Bool (op i1 i2)
    | ((Tyi, Tyr, Tyi), op), Int i, Real r -> Int (op i r)
    | ((Tyi, Tyr, Tyr), op), Int i, Real r -> Real (op i r)
    | ((Tyi, Tyr, Tyb), op), Int i, Real r -> Bool (op i r)
    | ((Tyi, Tyb, Tyr), op), Int i, Bool b -> Real (op i b)
    | ((Tyi, Tyb, Tyi), op), Int i, Bool b -> Int (op i b)
    | ((Tyi, Tyb, Tyb), op), Int i, Bool b -> Bool (op i b)
    | ((Tyr, Tyi, Tyi), op), Real r, Int i -> Int (op r i)
    | ((Tyr, Tyi, Tyr), op), Real r, Int i -> Real (op r i)
    | ((Tyr, Tyi, Tyb), op), Real r, Int i -> Bool (op r i)
    | ((Tyr, Tyr, Tyi), op), Real r1, Real r2 -> Int (op r1 r2)
    | ((Tyr, Tyr, Tyr), op), Real r1, Real r2 -> Real (op r1 r2)
    | ((Tyr, Tyr, Tyb), op), Real r1, Real r2 -> Bool (op r1 r2)
    | ((Tyr, Tyb, Tyi), op), Real r, Bool b -> Int (op r b)
    | ((Tyr, Tyb, Tyr), op), Real r, Bool b -> Real (op r b)
    | ((Tyr, Tyb, Tyb), op), Real r, Bool b -> Bool (op r b)
    | ((Tyb, Tyi, Tyr), op), Bool b, Int i -> Real (op b i)
    | ((Tyb, Tyi, Tyi), op), Bool b, Int i -> Int (op b i)
    | ((Tyb, Tyi, Tyb), op), Bool b, Int i -> Bool (op b i)
    | ((Tyb, Tyr, Tyi), op), Bool b, Real r -> Int (op b r)
    | ((Tyb, Tyr, Tyr), op), Bool b, Real r -> Real (op b r)
    | ((Tyb, Tyr, Tyb), op), Bool b, Real r -> Bool (op b r)
    | ((Tyb, Tyb, Tyi), op), Bool b1, Bool b2 -> Int (op b1 b2)
    | ((Tyb, Tyb, Tyr), op), Bool b1, Bool b2 -> Real (op b1 b2)
    | ((Tyb, Tyb, Tyb), op), Bool b1, Bool b2 -> Bool (op b1 b2)

  let uop (type a b) (op : (a, b) uop) (v : a value) : b value =
    match (op, v) with
    | ((Tyi, Tyi), op), Int i -> Int (op i)
    | ((Tyi, Tyr), op), Int i -> Real (op i)
    | ((Tyi, Tyb), op), Int i -> Bool (op i)
    | ((Tyr, Tyi), op), Real r -> Int (op r)
    | ((Tyr, Tyr), op), Real r -> Real (op r)
    | ((Tyr, Tyb), op), Real r -> Bool (op r)
    | ((Tyb, Tyi), op), Bool b -> Int (op b)
    | ((Tyb, Tyr), op), Bool b -> Real (op b)
    | ((Tyb, Tyb), op), Bool b -> Bool (op b)

  let rec eval : type a. (a, det) exp -> (a, det) exp = function
    | (Value _ | Var _) as e -> e
    | Bop (op, e1, e2) -> (
        match (eval e1, eval e2) with
        | Value v1, Value v2 -> Value (bop op v1 v2)
        | e1, e2 -> Bop (op, e1, e2))
    | Uop (op, e) -> (
        match eval e with Value v -> Value (uop op v) | e -> Uop (op, e))
    | If (e_pred, e_cons, e_alt) -> (
        match eval e_pred with
        | Value (Bool true) -> eval e_cons
        | Value (Bool false) -> eval e_alt
        | e_pred -> If (e_pred, eval e_cons, eval e_alt))
    | Call (f, e) -> Call (f, eval e)
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

  exception Type_error of string

  (* Remove this ugly crap *)
  let to_float (de : t) : float =
    match de with
    | Real r -> r
    | Int i -> Float.of_int i
    | Bool b -> if b then 1.0 else 0.0
    | _ -> raise (Type_error ("Float conversion failed: " ^ to_string de))

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
    | Int _ | Real _ | Bool _ | Var _ -> exp
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

  let%expect_test _ =
    let exp = Add (If (Bool true, Mult (Int 2, Int 3), Int 4), Int 5) in
    print_s [%sexp (eval exp : t)];
    [%expect {| (Int 11) |}]

  let%expect_test _ =
    let exp = Add (If (Bool false, Mult (Int 2, Int 3), Int 4), Int 5) in
    print_s [%sexp (eval exp : t)];
    [%expect {| (Int 9) |}]

  (* TODO: Prim_call conversion *)
  (*let%expect_test _ =*)
  (*  let exp = Prim_call ("bernoulli", [ Real 0.5 ]) in*)
  (*  print_s [%sexp (eval exp : t)];*)
  (*  [%expect {| (Dist_obj (dist bernoulli) (var X) (args ((Real 0.5)))) |}]*)
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

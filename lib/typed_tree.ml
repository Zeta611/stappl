open! Core

type real = float
type ('a, 'b) uop = { name : Id.t; op : 'a -> 'b }
type ('a, 'b, 'c) bop = { name : Id.t; op : 'a -> 'b -> 'c }
type _ dty = Tyu : unit dty | Tyi : int dty | Tyr : real dty | Tyb : bool dty
type value = Val_ph
type rv = Rv_ph
type _ stamp = Val : value stamp | Rv : rv stamp

type (_, _, _) merge_stamp =
  | Both_val : value stamp * value stamp -> (value, value, value) merge_stamp
  | Right_rv : value stamp * rv stamp -> (value, rv, rv) merge_stamp
  | Left_rv : rv stamp * value stamp -> (rv, value, rv) merge_stamp
  | Both_rv : rv stamp * rv stamp -> (rv, rv, rv) merge_stamp

type ('a, 'b) dat_ty = Dat_ty_ph
type 'a dist_ty = Dist_ty_ph

type _ ty =
  | Dat_ty : 'a dty * 'b stamp -> ('a, 'b) dat_ty ty
  | Dist_ty : 'a dty -> 'a dist_ty ty

type det = Det_ph
type ndet = Ndet_ph

type _ params =
  | [] : unit params
  | ( :: ) : 'a dty * 'b params -> ('a * 'b) params

type _ vargs =
  | [] : unit vargs
  | ( :: ) : ('a dty * 'a) * 'b vargs -> ('a * 'b) vargs

type ('a, 'b) dist = {
  ret : 'a dty;
  name : Id.t;
  params : 'b params;
  sampler : 'b vargs -> 'a;
  log_pmdf : 'b vargs -> 'a -> real;
}

(* TODO: Why args should also be det? *)
type (_, _) args =
  | [] : (unit, _) args
  | ( :: ) : (('a, _) dat_ty, 'd) texp * ('b, 'd) args -> ('a * 'b, 'd) args

and pred =
  | Empty : pred
  | True : pred
  | False : pred
  | And : pred * ((bool, _) dat_ty, det) texp -> pred
  | And_not : pred * ((bool, _) dat_ty, det) texp -> pred

and ('a, 'd) texp = { ty : 'a ty; exp : ('a, 'd) exp }

and (_, _) exp =
  | Value : 'a -> (('a, value) dat_ty, _) exp
  | Var : Id.t -> (_, ndet) exp
  | Rvar : Id.t -> (('a, rv) dat_ty, det) exp
  | Bop :
      ('a1, 'a2, 'a) bop
      * (('a1, 's1) dat_ty, 'd) texp
      * (('a2, 's2) dat_ty, 'd) texp
      * ('s1, 's2, 's) merge_stamp
      -> (('a, 's) dat_ty, 'd) exp
  | Uop : ('a, 'b) uop * (('a, 's) dat_ty, 'd) texp -> (('b, 's) dat_ty, 'd) exp
  | If :
      ((bool, 's_pred) dat_ty, ndet) texp
      * (('a, 's_con) dat_ty, ndet) texp
      * (('a, 's_alt) dat_ty, ndet) texp
      * ('s_con, 's_alt, 's_ca) merge_stamp
      * ('s_pred, 's_ca, 's) merge_stamp
      -> (('a, 's) dat_ty, ndet) exp
  | If_pred :
      pred * (('a, _) dat_ty, det) texp * (('a, _) dat_ty, det) texp
      -> (('a, _) dat_ty, det) exp
  | If_pred_dist : pred * ('a dist_ty, det) texp -> ('a dist_ty, det) exp
  | If_just : (('a, _) dat_ty, det) texp -> (('a, _) dat_ty, det) exp
  | Let : Id.t * ('a, ndet) texp * ('b, ndet) texp -> ('b, ndet) exp
  | Call : ('a, 'b) dist * ('b, 'd) args -> ('a dist_ty, 'd) exp
  | Sample : ('a dist_ty, ndet) texp -> (('a, rv) dat_ty, ndet) exp
  | Observe :
      ('a dist_ty, ndet) texp * (('a, value) dat_ty, ndet) texp
      -> ((unit, value) dat_ty, ndet) exp

type some_dty = Ex : _ dty -> some_dty
type some_val = Ex : ('a dty * 'a) -> some_val
type some_ty = Ex : _ ty -> some_ty
type _ some_texp = Ex : (_, 'd) texp -> 'd some_texp

type _ some_dat_ndet_texp =
  | Ex : (('a, _) dat_ty, ndet) texp -> 'a some_dat_ndet_texp

type _ some_val_texp = Ex : ((_, value) dat_ty, 'd) texp -> 'd some_val_texp
type _ some_rv_texp = Ex : ((_, rv) dat_ty, 'd) texp -> 'd some_rv_texp
type _ some_dat_texp = Ex : (_ dat_ty, 'd) texp -> 'd some_dat_texp
type _ some_dist_texp = Ex : (_ dist_ty, 'd) texp -> 'd some_dist_texp
type (_, _) eq = Refl : ('a, 'a) eq

type (_, _) some_merge_stamp =
  | Ex : ('s1, 's2, 's) merge_stamp * 's stamp -> ('s1, 's2) some_merge_stamp

let dty_of_dat_ty : type a. (a, _) dat_ty ty -> a dty = function
  | Dat_ty (dty, _) -> dty

let dty_of_dist_ty : type a. a dist_ty ty -> a dty = function
  | Dist_ty dty -> dty

let some_dist_of_texp : type a d. (a, d) texp -> d some_dist_texp option =
 fun texp -> match texp.ty with Dist_ty _ -> Some (Ex texp) | _ -> None

let some_dat_of_texp : type a d. (a, d) texp -> d some_dat_texp option =
 fun texp -> match texp.ty with Dat_ty _ -> Some (Ex texp) | _ -> None

let some_dty_of_ty : type a. a ty -> some_dty option = function
  | Dat_ty (dty, _) -> Some (Ex dty)
  | Dist_ty _ -> None

let eq_dtys : type a1 a2. a1 dty -> a2 dty -> (a1, a2) eq option =
 fun t1 t2 ->
  match (t1, t2) with
  | Tyu, Tyu -> Some Refl
  | Tyb, Tyb -> Some Refl
  | Tyi, Tyi -> Some Refl
  | Tyr, Tyr -> Some Refl
  | _, _ -> None

let unify_dtys : type a1 a2. a1 dty -> a2 dty -> (a1, a2) eq -> a1 dty =
 fun t _ Refl -> t

let merge_stamps : type s1 s2. s1 stamp -> s2 stamp -> (s1, s2) some_merge_stamp
    =
 fun s1 s2 ->
  match (s1, s2) with
  | Val, Val -> Ex (Both_val (Val, Val), Val)
  | Val, Rv -> Ex (Right_rv (Val, Rv), Rv)
  | Rv, Val -> Ex (Left_rv (Rv, Val), Rv)
  | Rv, Rv -> Ex (Both_rv (Rv, Rv), Rv)

let eq_dat_tys :
    type a1 a2. (a1, _) dat_ty ty -> (a2, _) dat_ty ty -> (a1, a2) eq option =
 fun t1 t2 -> eq_dtys (dty_of_dat_ty t1) (dty_of_dat_ty t2)

let eq_tys : type a1 a2. a1 ty -> a2 ty -> (a1, a2) eq option =
 fun t1 t2 ->
  match (t1, t2) with
  | Dat_ty (Tyu, Val), Dat_ty (Tyu, Val) -> Some Refl
  | Dat_ty (Tyb, Val), Dat_ty (Tyb, Val) -> Some Refl
  | Dat_ty (Tyi, Val), Dat_ty (Tyi, Val) -> Some Refl
  | Dat_ty (Tyr, Val), Dat_ty (Tyr, Val) -> Some Refl
  | Dat_ty (Tyu, Rv), Dat_ty (Tyu, Rv) -> Some Refl
  | Dat_ty (Tyb, Rv), Dat_ty (Tyb, Rv) -> Some Refl
  | Dat_ty (Tyi, Rv), Dat_ty (Tyi, Rv) -> Some Refl
  | Dat_ty (Tyr, Rv), Dat_ty (Tyr, Rv) -> Some Refl
  | Dist_ty Tyu, Dist_ty Tyu -> Some Refl
  | Dist_ty Tyb, Dist_ty Tyb -> Some Refl
  | Dist_ty Tyi, Dist_ty Tyi -> Some Refl
  | Dist_ty Tyr, Dist_ty Tyr -> Some Refl
  | _, _ -> None

let string_of_dty : type a. a dty -> string = function
  | Tyu -> "unit"
  | Tyi -> "int"
  | Tyr -> "real"
  | Tyb -> "bool"

let string_of_ty : type a. a ty -> string = function
  | Dat_ty (Tyu, Val) -> "unit val"
  | Dat_ty (Tyi, Val) -> "int val"
  | Dat_ty (Tyr, Val) -> "real val"
  | Dat_ty (Tyb, Val) -> "bool val"
  | Dat_ty (Tyu, Rv) -> "unit rv"
  | Dat_ty (Tyi, Rv) -> "int rv"
  | Dat_ty (Tyr, Rv) -> "real rv"
  | Dat_ty (Tyb, Rv) -> "bool rv"
  | Dist_ty Tyu -> "unit dist"
  | Dist_ty Tyi -> "int dist"
  | Dist_ty Tyr -> "real dist"
  | Dist_ty Tyb -> "bool dist"

let rec fv : type a. (a, det) exp -> Id.Set.t = function
  | Value _ -> Id.Set.empty
  | Rvar x -> Id.Set.singleton x
  | Bop (_, { exp = e1; _ }, { exp = e2; _ }, _) -> Id.(fv e1 @| fv e2)
  | Uop (_, { exp; _ }) -> fv exp
  | If_pred (pred, { exp = e_con; _ }, { exp = e_alt; _ }) ->
      Id.(fv_pred pred @| fv e_con @| fv e_alt)
  | If_pred_dist (pred, { exp = e_con; _ }) -> Id.(fv_pred pred @| fv e_con)
  | If_just { exp; _ } -> fv exp
  | Call (_, args) -> fv_args args

and fv_args : type a. (a, det) args -> Id.Set.t = function
  | [] -> Id.Set.empty
  | { exp; _ } :: es -> Id.(fv exp @| fv_args es)

and fv_pred : pred -> Id.Set.t = function
  | Empty | True | False -> Id.Set.empty
  | And (p, { exp = de; _ }) -> Id.(fv de @| fv_pred p)
  | And_not (p, { exp = de; _ }) -> Id.(fv de @| fv_pred p)

module Erased = struct
  type exp =
    | Value : string -> exp
    | Var : Id.t -> exp
    | Bop : Id.t * exp * exp -> exp
    | Uop : Id.t * exp -> exp
    (* TODO: Add list and record constructors *)
    (*| List : ('a, 'd) exp list -> ('a list, 'd) exp*)
    (*| Record : ('k * 'v, 'd) exp list -> ('k * 'v, 'd) exp*)
    | If : exp * exp * exp -> exp
    | If_just : exp -> exp
    | Let : Id.t * exp * exp -> exp
    | Call : Id.t * exp list -> exp
    | Sample : exp -> exp
    | Observe : exp * exp -> exp
  [@@deriving sexp]

  let rec of_exp : type a d. (a, d) texp -> exp =
   fun { ty; exp } ->
    match exp with
    | If (pred, con, alt, _, _) -> If (of_exp pred, of_exp con, of_exp alt)
    | If_pred (pred, con, alt) -> If (of_pred pred, of_exp con, of_exp alt)
    | If_pred_dist (pred, con) -> If (of_pred pred, of_exp con, Value "1")
    | If_just exp -> If_just (of_exp exp)
    | Value v -> (
        match ty with
        | Dat_ty (Tyu, _) -> Value "()"
        | Dat_ty (Tyi, _) -> Value (string_of_int v)
        | Dat_ty (Tyr, _) -> Value (string_of_float v)
        | Dat_ty (Tyb, _) -> Value (string_of_bool v))
    | Var v | Rvar v -> Var v
    | Bop (op, e1, e2, _) -> Bop (op.name, of_exp e1, of_exp e2)
    | Uop (op, e) -> Uop (op.name, of_exp e)
    | Let (x, e1, e2) -> Let (x, of_exp e1, of_exp e2)
    | Call (f, args) -> Call (f.name, of_args args)
    | Sample e -> Sample (of_exp e)
    | Observe (d, e) -> Observe (of_exp d, of_exp e)

  and of_args : type a d. (a, d) args -> exp list = function
    | [] -> []
    | arg :: args -> of_exp arg :: of_args args

  and of_pred : pred -> exp = function
    | Empty -> Value ""
    | True -> Value "true"
    | False -> Value "false"
    | And (pred, exp) -> Bop ("&&", of_pred pred, of_exp exp)
    | And_not (pred, exp) -> Bop ("&&", of_pred pred, Uop ("not", of_exp exp))

  let of_rv (Ex rv : _ some_rv_texp) = rv |> of_exp
end

open! Core

type real = float
type ('a, 'b) uop = { name : Id.t; op : 'a -> 'b }
type ('a, 'b, 'c) bop = { name : Id.t; op : 'a -> 'b -> 'c }
type _ dty = Tyu : unit dty | Tyi : int dty | Tyr : real dty | Tyb : bool dty
type value = Val_ph
type rv = Rv_ph
type _ stamp = Val : value stamp | Rv : rv stamp
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
  | Var : Id.t -> _ exp
  | Bop :
      ('a, 'b, 'c) bop * (('a, _) dat_ty, 'd) texp * (('b, _) dat_ty, 'd) texp
      -> (('c, _) dat_ty, 'd) exp
  | Uop : ('a, 'b) uop * (('a, _) dat_ty, 'd) texp -> (('b, _) dat_ty, 'd) exp
  | If :
      ((bool, _) dat_ty, 'd) texp
      * (('a, _) dat_ty, 'd) texp
      * (('a, _) dat_ty, 'd) texp
      -> (('a, _) dat_ty, 'd) exp
  | If_pred : pred * ('a dist_ty, det) texp -> ('a dist_ty, det) exp
  | If_just : (('a, 's) dat_ty, det) texp -> (('a, _) dat_ty, det) exp
  | Let : Id.t * ('a, ndet) texp * ('b, ndet) texp -> ('b, ndet) exp
  | Call : ('a, 'b) dist * ('b, 'd) args -> ('a dist_ty, 'd) exp
  | Sample : ('a dist_ty, ndet) texp -> (('a, rv) dat_ty, ndet) exp
  | Observe :
      ('a dist_ty, ndet) texp * (('a, value) dat_ty, ndet) texp
      -> ((unit, value) dat_ty, ndet) exp

type some_dty = Ex : _ dty -> some_dty
type some_stamp = Ex : _ stamp -> some_stamp
type some_ty = Ex : _ ty -> some_ty
type some_ndet_texp = Ex : (_, ndet) texp -> some_ndet_texp
type some_det_texp = Ex : (_, det) texp -> some_det_texp
type some_dat_ndet_texp = Ex : (_ dat_ty, ndet) texp -> some_dat_ndet_texp

type _ some_dat_ndet_texp1 =
  | Ex : (('a, _) dat_ty, ndet) texp -> 'a some_dat_ndet_texp1

type some_val_det_texp =
  | Ex : ((_, value) dat_ty, det) texp -> some_val_det_texp

type some_rv_det_texp = Ex : ((_, rv) dat_ty, det) texp -> some_rv_det_texp
type some_dist_det_texp = Ex : (_ dist_ty, det) texp -> some_dist_det_texp
type (_, _) eq = Refl : ('a, 'a) eq

let dty_of_ty : type a. (a, _) dat_ty ty -> a dty = function
  | Dat_ty (dty, _) -> dty

let some_dat_ndet_texp_of_ndet_texp :
    type a. (a, ndet) texp -> some_dat_ndet_texp option =
 fun texp ->
  match texp.ty with
  | Dat_ty (Tyu, _) -> Some (Ex texp)
  | Dat_ty (Tyb, _) -> Some (Ex texp)
  | Dat_ty (Tyi, _) -> Some (Ex texp)
  | Dat_ty (Tyr, _) -> Some (Ex texp)
  | _ -> None

let eq_dat_ndet_texps :
    type a1 a2.
    ((a1, _) dat_ty, ndet) texp ->
    ((a2, _) dat_ty, ndet) texp ->
    (a1, a2) eq option =
 fun te_con te_alt ->
  match (dty_of_ty te_con.ty, dty_of_ty te_alt.ty) with
  | Tyu, Tyu -> Some Refl
  | Tyb, Tyb -> Some Refl
  | Tyi, Tyi -> Some Refl
  | Tyr, Tyr -> Some Refl
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
  | Var x -> Id.Set.singleton x
  | Bop (_, { exp = e1; _ }, { exp = e2; _ }) -> Id.(fv e1 @| fv e2)
  | Uop (_, { exp; _ }) -> fv exp
  | If ({ exp = e_pred; _ }, { exp = e_cons; _ }, { exp = e_alt; _ }) ->
      Id.(fv e_pred @| fv e_cons @| fv e_alt)
  | If_pred (pred, { exp = e_cons; _ }) -> Id.(fv_pred pred @| fv e_cons)
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
    | If (pred, cons, alt) -> If (of_exp pred, of_exp cons, of_exp alt)
    | If_pred (pred, cons) -> If (of_pred pred, of_exp cons, Value "1")
    | If_just exp -> If_just (of_exp exp)
    | Value v -> (
        match ty with
        | Dat_ty (Tyu, _) -> Value "()"
        | Dat_ty (Tyi, _) -> Value (string_of_int v)
        | Dat_ty (Tyr, _) -> Value (string_of_float v)
        | Dat_ty (Tyb, _) -> Value (string_of_bool v))
    | Var v -> Var v
    | Bop (op, e1, e2) -> Bop (op.name, of_exp e1, of_exp e2)
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

  let of_rv (Ex rv : some_rv_det_texp) = rv |> of_exp
end

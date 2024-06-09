open! Core

type real = float
type _ dty = Tyu : unit dty | Tyi : int dty | Tyr : real dty | Tyb : bool dty
type value = Val_ph
type rv = Rv_ph
type _ stamp = Val : value stamp | Rv : rv stamp
type ('a, 'b) dat_ty = Dat_ty_ph
type 'a dist_ty = Dist_ty_ph

type _ ty =
  | Dat_ty : 'a dty * 'b stamp -> ('a, 'b) dat_ty ty
  | Dist_ty : 'a dty -> 'a dist_ty ty

type _ params =
  | [] : unit params
  | ( :: ) : 'a dty * 'b params -> ('a * 'b) params

type det = Det_ph
type non_det = Non_det_ph

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

type ('a, 'b, 'c) bop = { name : Id.t; op : 'a -> 'b -> 'c }
type ('a, 'b) uop = { name : Id.t; op : 'a -> 'b }

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
  | If_con : (('a, 's) dat_ty, det) texp -> (('a, _) dat_ty, det) exp
  | If_alt : (('a, 's) dat_ty, det) texp -> (('a, _) dat_ty, det) exp
  | Let : Id.t * ('a, non_det) texp * ('b, non_det) texp -> ('b, non_det) exp
  | Call : ('a, 'b) dist * ('b, 'd) args -> ('a dist_ty, 'd) exp
  | Sample : ('a dist_ty, non_det) texp -> (('a, rv) dat_ty, non_det) exp
  | Observe :
      ('a dist_ty, non_det) texp * (('a, value) dat_ty, non_det) texp
      -> ((unit, value) dat_ty, non_det) exp

type some_non_det_texp = Ex : (_, non_det) texp -> some_non_det_texp
type some_det = Ex : (_, det) texp -> some_det
type some_rv_texp = Ex : ((_, rv) dat_ty, det) texp -> some_rv_texp
type some_dat_texp = Ex : ((_, value) dat_ty, det) texp -> some_dat_texp
type some_dist_texp = Ex : (_ dist_ty, det) texp -> some_dist_texp
type some_dty = Ex : _ dty -> some_dty
type some_ty = Ex : _ ty -> some_ty
type some_stamp = Ex : _ stamp -> some_stamp

type _ some_dat_non_det_texp =
  | Ex : (('a, _) dat_ty, non_det) texp -> 'a some_dat_non_det_texp

type 'a dist_non_det_texp = ('a dist_ty, non_det) texp
(*  | Ex : ('a dist_ty ty, non_det) texp -> 'a some_dist_non_det_texp*)

(*type _ some_dist_texp = Ex : ('a dist_ty, non_det) texp -> 'a some_dist_texp*)

let dty_of_ty : type a. (a, _) dat_ty ty -> a dty = function
  | Dat_ty (dty, _) -> dty

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
  | If_con { exp; _ } -> fv exp
  | If_alt { exp; _ } -> fv exp
  | Call (_, args) -> fv_args args

and fv_args : type a. (a, det) args -> Id.Set.t = function
  | [] -> Id.Set.empty
  | { exp; _ } :: es -> Id.(fv exp @| fv_args es)

and fv_pred : pred -> Id.Set.t = function
  | Empty | True | False -> Id.Set.empty
  | And (p, { exp = de; _ }) -> Id.(fv de @| fv_pred p)
  | And_not (p, { exp = de; _ }) -> Id.(fv de @| fv_pred p)

open! Core

type real = float
type _ ty = Tyi : int ty | Tyr : real ty | Tyb : bool ty

type _ params =
  | [] : unit params
  | ( :: ) : 'a ty * 'b params -> ('a * 'b) params

type det = Det
type non_det = Non_det

type _ vargs =
  | [] : unit vargs
  | ( :: ) : ('a ty * 'a) * 'b vargs -> ('a * 'b) vargs

type ('a, 'b) dist = {
  ret : 'a ty;
  name : Id.t;
  params : 'b params;
  sampler : 'b vargs -> 'a;
  log_pmdf : 'b vargs -> 'a -> real;
}

type ('a, 'b, 'c) bop = { name : Id.t; f : 'a -> 'b -> 'c }
type ('a, 'b) uop = { name : Id.t; f : 'a -> 'b }

type (_, _) args =
  | [] : (unit, _) args
  | ( :: ) : ('a, 'd) texp * ('b, 'd) args -> ('a * 'b, 'd) args

and (_, _) exp =
  | Value : 'a -> ('a, _) exp
  | Var : Id.t -> _ exp
  | Bop : ('a, 'b, 'c) bop * ('a, 'd) texp * ('b, 'd) texp -> ('c, 'd) exp
  | Uop : ('a, 'b) uop * ('a, 'd) texp -> ('b, 'd) exp
  (* TODO: Add list and record constructors *)
  (*| List : ('a, 'd) exp list -> ('a list, 'd) exp*)
  (*| Record : ('k * 'v, 'd) exp list -> ('k * 'v, 'd) exp*)
  | If : (bool, 'd) texp * ('a, 'd) texp * ('a, 'd) texp -> ('a, 'd) exp
  | Let : Id.t * ('a, non_det) texp * ('b, non_det) texp -> ('b, non_det) exp
  | Call : ('a, 'b) dist * ('b, 'd) args -> ('a, 'd) exp
  | Sample : ('a, non_det) texp -> ('a, non_det) exp
  | Observe : ('a, non_det) texp * ('a, non_det) texp -> ('a, non_det) exp

and ('a, 'd) texp = { ty : 'a ty; exp : ('a, 'd) exp }

let rec fv : type a. (a, det) exp -> Id.Set.t = function
  | Value _ -> Id.Set.empty
  | Var x -> Id.Set.singleton x
  | Bop (_, { exp = e1; _ }, { exp = e2; _ }) -> Id.(fv e1 @| fv e2)
  | Uop (_, { exp; _ }) -> fv exp
  | If ({ exp = e_pred; _ }, { exp = e_cons; _ }, { exp = e_alt; _ }) ->
      Id.(fv e_pred @| fv e_cons @| fv e_alt)
  | Call (_, args) -> fv_args args

and fv_args : type a. (a, det) args -> Id.Set.t = function
  | [] -> Id.Set.empty
  | { exp; _ } :: es -> Id.(fv exp @| fv_args es)

type any_ndet = Any : (_, non_det) texp -> any_ndet
type any_det = Any : (_, det) texp -> any_det
type any_ty = Any : _ ty -> any_ty
type any_params = Any : _ params -> any_params
type any_v = Any : ('a ty * 'a) -> any_v
type any_dist = Any : _ dist -> any_dist
type tyenv = any_ty Id.Map.t

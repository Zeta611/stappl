open! Core
open Program

type real = float
type _ ty = Tyi : int ty | Tyr : real ty | Tyb : bool ty

type _ params =
  | [] : unit params
  | ( :: ) : 'a ty * 'b params -> ('a * 'b) params

type det = Det
type non_det = Non_det
type 'a sampler = unit -> 'a
type 'a log_pmdf = 'a -> real

type 'a dist = {
  name : Id.t;
  ty : 'a ty;
  sampler : 'a sampler;
  log_pmdf : 'a log_pmdf;
}

type any_dist = Any_dist : 'a dist -> any_dist

type (_, _) args =
  | [] : (unit, _) args
  | ( :: ) : ('a, 'd) texp * ('b, 'd) args -> ('a * 'b, 'd) args

and (_, _) exp =
  | Value : 'a -> ('a, _) exp
  | Var : Id.t -> _ exp
  | Bop : ('a -> 'b -> 'c) * ('a, 'd) texp * ('b, 'd) texp -> ('c, 'd) exp
  | Uop : ('a -> 'b) * ('a, 'd) texp -> ('b, 'd) exp
  (* TODO: Add list and record constructors *)
  (*| List : ('a, 'd) exp list -> ('a list, 'd) exp*)
  (*| Record : ('k * 'v, 'd) exp list -> ('k * 'v, 'd) exp*)
  | If : (bool, 'd) texp * ('a, 'd) texp * ('a, 'd) texp -> ('a, 'd) exp
  | Let : Id.t * ('a, non_det) texp * ('b, non_det) texp -> ('b, non_det) exp
  | Call : Id.t * ('a, 'd) args -> ('b, 'd) exp
  | Sample : ('a, non_det) texp -> ('a, non_det) exp
  | Observe : ('a, non_det) texp * ('a, non_det) texp -> ('a, non_det) exp
  | Dist : 'b dist -> ('b, det) exp

and ('a, 'd) texp = { ty : 'a ty; exp : ('a, 'd) exp }

let rec fv : type a. (a, det) exp -> Id.Set.t = function
  | Value _ | Dist _ -> Id.Set.empty
  | Var x -> Id.Set.singleton x
  | Bop (_, { exp = e1; _ }, { exp = e2; _ }) -> Id.(fv e1 @| fv e2)
  | Uop (_, { exp; _ }) -> fv exp
  | If ({ exp = e_pred; _ }, { exp = e_cons; _ }, { exp = e_alt; _ }) ->
      Id.(fv e_pred @| fv e_cons @| fv e_alt)
  | Call (_, args) -> fv_args args

and fv_args : type a. (a, det) args -> Id.Set.t = function
  | [] -> Id.Set.empty
  | { exp; _ } :: es -> Id.(fv exp @| fv_args es)

type _ vargs =
  | [] : unit vargs
  | ( :: ) : ('a ty * 'a) * 'b vargs -> ('a * 'b) vargs

exception Dist_type_error of string

let get_bernoulli (type a b) (ret : a ty) (vargs : b vargs) : a dist =
  let open Owl.Stats in
  match (ret, vargs) with
  | Tyb, [ (Tyr, p) ] ->
      {
        name = "bernoulli";
        ty = Tyb;
        sampler = (fun () -> binomial_rvs ~p ~n:1 = 1);
        log_pmdf = (fun b -> binomial_logpdf ~p ~n:1 (Bool.to_int b));
      }
  | Tyb, [] -> raise (Dist_type_error "Bernoulli: too few args")
  | Tyb, [ (Tyi, i) ] ->
      raise (Dist_type_error (sprintf "Bernoulli: got %i expected real" i))
  | Tyb, [ (Tyb, b) ] ->
      raise (Dist_type_error (sprintf "Bernoulli: got %b expected real" b))
  | Tyb, _ -> raise (Dist_type_error "Bernoulli: too many arguments")
  | _, _ -> raise (Dist_type_error "Bernoulli: should return bool")

let get_normal (type a b) (ret : a ty) (vargs : b vargs) : a dist =
  let open Owl.Stats in
  match (ret, vargs) with
  | Tyr, [ (Tyr, mu); (Tyr, sigma) ] ->
      {
        name = "normal";
        ty = Tyr;
        sampler = (fun () -> gaussian_rvs ~mu ~sigma);
        log_pmdf = gaussian_logpdf ~mu ~sigma;
      }
  | Tyr, [] | Tyr, [ _ ] -> raise (Dist_type_error "Normal: too few args")
  | Tyr, [ (Tyi, i); _ ] ->
      raise (Dist_type_error (sprintf "Normal: got %i expected real" i))
  | Tyr, [ (Tyr, _); (Tyi, i) ] ->
      raise (Dist_type_error (sprintf "Normal: got %i expected real" i))
  | Tyr, [ (Tyb, b); _ ] ->
      raise (Dist_type_error (sprintf "Normal: got %b expected real" b))
  | Tyr, [ (Tyr, _); (Tyb, b) ] ->
      raise (Dist_type_error (sprintf "Normal: got %b expected real" b))
  | Tyr, _ -> raise (Dist_type_error "Normal: too many arguments")
  | _, _ -> raise (Dist_type_error "Normal: should return real")

type ('arg, 'k) cont_dist_box = {
  k : 'a 'b. ('a params * 'b ty) * ('arg vargs -> 'b dist) -> 'k;
}

let dist_lookup (name : Id.t) (ret : 'a ty) (vargs : 'b vargs) : 'a dist =
  match name with
  | "bernoulli" -> get_bernoulli ret vargs
  | "normal" -> get_normal ret vargs
  (* TODO: Add more distributions *)
  | _ -> raise (Invalid_argument "Distribution not found")

let rec peval : type a. (a, det) texp -> (a, det) texp =
 fun { ty; exp } ->
  let exp =
    match exp with
    | (Value _ | Var _) as e -> e
    | Bop (op, te1, te2) -> (
        match (peval te1, peval te2) with
        | { exp = Value v1; _ }, { exp = Value v2; _ } -> Value (op v1 v2)
        | te1, te2 -> Bop (op, te1, te2))
    | Uop (op, te) -> (
        match peval te with
        | { exp = Value v; _ } -> Value (op v)
        | e -> Uop (op, e))
    | If (te_pred, te_cons, te_alt) -> (
        match peval te_pred with
        | { exp = Value true; _ } -> (peval te_cons).exp
        | { exp = Value false; _ } -> (peval te_alt).exp
        | te_pred -> If (te_pred, peval te_cons, peval te_alt))
    | Call (f, args) -> (
        match peval_args args with
        | args, None -> Call (f, args)
        | _, Some vargs ->
            (* All arguments are fully evaluated;
               Go ahead and fully evaluate the (primitive) call.
               It is a primitive call as this is a deterministic expression. *)
            Dist (dist_lookup f ty vargs))
    | Dist _ as e -> e (* TODO: probably should not be encountered *)
  in
  { ty; exp }

and peval_args : type a. (a, det) args -> (a, det) args * a vargs option =
  function
  | [] -> ([], Some [])
  | te :: tl -> (
      match (peval te, peval_args tl) with
      | { ty; exp = Value v }, (tl, Some vargs) ->
          ({ ty; exp = Value v } :: tl, Some ((ty, v) :: vargs))
      | te, (tl, _) -> (te :: tl, None))

(*let rec convert (exp : Exp.t) : (float, non_det) exp =*)

open! Core
open Typed_tree

type t =
  | Value : string -> t
  | Var : Id.t -> t
  | Bop : Id.t * t * t -> t
  | Uop : Id.t * t -> t
  (* TODO: Add list and record constructors *)
  (*| List : ('a, 'd) exp list -> ('a list, 'd) exp*)
  (*| Record : ('k * 'v, 'd) exp list -> ('k * 'v, 'd) exp*)
  | If : t * t * t -> t
  | If_con : t -> t
  | If_alt : t -> t
  | Let : Id.t * t * t -> t
  | Call : Id.t * t list -> t
  | Sample : t -> t
  | Observe : t * t -> t
[@@deriving sexp]

type graph = {
  vertices : Id.t list;
  arcs : (Id.t * Id.t) list;
  pmdf_map : t Id.Map.t;
  obs_map : t Id.Map.t;
}
[@@deriving sexp]

let rec of_exp : type a d. (a, d) texp -> t =
 fun { ty; exp } ->
  match exp with
  | If (pred, cons, alt) -> If (of_exp pred, of_exp cons, of_exp alt)
  | If_pred (pred, cons) -> If (of_pred pred, of_exp cons, Value "1")
  | If_con exp -> If_con (of_exp exp)
  | If_alt exp -> If_alt (of_exp exp)
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

and of_args : type a d. (a, d) args -> t list = function
  | [] -> []
  | arg :: args -> of_exp arg :: of_args args

and of_pred : pred -> t = function
  | Empty -> Value ""
  | True -> Value "true"
  | False -> Value "false"
  | And (pred, exp) -> Bop ("&&", of_pred pred, of_exp exp)
  | And_not (pred, exp) -> Bop ("&&", of_pred pred, Uop ("not", of_exp exp))

let of_graph ({ vertices; arcs; pmdf_map; obs_map } : Graph.t) : graph =
  {
    vertices;
    arcs;
    pmdf_map = Map.map pmdf_map ~f:(fun (Ex e) -> of_exp e);
    obs_map = Map.map obs_map ~f:(fun (Ex e) -> of_exp e);
  }

let of_rv (Ex rv : some_rv_texp) =
  rv |> of_exp |> sexp_of_t |> Sexp.to_string_hum

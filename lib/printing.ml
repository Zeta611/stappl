open! Core
open Typed_tree

type t =
  | Value : Id.t -> t
  | Var : Id.t -> t
  | Bop : Id.t * t * t -> t
  | Uop : Id.t * t -> t
  (* TODO: Add list and record constructors *)
  (*| List : ('a, 'd) exp list -> ('a list, 'd) exp*)
  (*| Record : ('k * 'v, 'd) exp list -> ('k * 'v, 'd) exp*)
  | If : t * t * t -> t
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
  | Value v -> (
      match ty with
      | Tyi -> Value (string_of_int v)
      | Tyr -> Value (string_of_float v)
      | Tyb -> Value (string_of_bool v))
  | Var v -> Var v
  | Bop (op, e1, e2) -> Bop (op.name, of_exp e1, of_exp e2)
  | Uop (op, e) -> Uop (op.name, of_exp e)
  | If (pred, cons, alt) -> If (of_exp pred, of_exp cons, of_exp alt)
  | Let (x, e1, e2) -> Let (x, of_exp e1, of_exp e2)
  | Call (f, args) -> Call (f.name, of_args args)
  | Sample e -> Sample (of_exp e)
  | Observe (d, e) -> Observe (of_exp d, of_exp e)

and of_args : type a d. (a, d) args -> t list = function
  | [] -> []
  | arg :: args -> of_exp arg :: of_args args

let of_graph ({ vertices; arcs; pmdf_map; obs_map } : Graph.t) : graph =
  {
    vertices;
    arcs;
    pmdf_map = Map.map pmdf_map ~f:(fun (Any e) -> of_exp e);
    obs_map = Map.map obs_map ~f:(fun (Any e) -> of_exp e);
  }

let to_string (Any e : any_det) = e |> of_exp |> sexp_of_t |> Sexp.to_string_hum

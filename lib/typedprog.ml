open! Core
open Program

module Syntax = struct
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
end

module Typing = struct
  open Syntax

  let gen_args =
    let cnt = ref 0 in
    fun () ->
      let arg = "$arg" ^ string_of_int !cnt in
      incr cnt;
      arg

  let rec subst (env : Id.t Id.Map.t) (e : Exp.t) =
    let subst' = subst env in
    match e with
    | Int _ | Real _ | Bool _ -> e
    | Var x -> (
        match Map.find env x with
        | None -> failwith ("Unbound variable " ^ x)
        | Some v -> Var v)
    | Add (e1, e2) -> Add (subst' e1, subst' e2)
    | Radd (e1, e2) -> Radd (subst' e1, subst' e2)
    | Minus (e1, e2) -> Minus (subst' e1, subst' e2)
    | Rminus (e1, e2) -> Rminus (subst' e1, subst' e2)
    | Neg e -> Neg (subst' e)
    | Rneg e -> Rneg (subst' e)
    | Mult (e1, e2) -> Mult (subst' e1, subst' e2)
    | Rmult (e1, e2) -> Rmult (subst' e1, subst' e2)
    | Div (e1, e2) -> Div (subst' e1, subst' e2)
    | Rdiv (e1, e2) -> Rdiv (subst' e1, subst' e2)
    | Eq (e1, e2) -> Eq (subst' e1, subst' e2)
    | Req (e1, e2) -> Req (subst' e1, subst' e2)
    | Noteq (e1, e2) -> Noteq (subst' e1, subst' e2)
    | Less (e1, e2) -> Less (subst' e1, subst' e2)
    | Rless (e1, e2) -> Rless (subst' e1, subst' e2)
    | And (e1, e2) -> And (subst' e1, subst' e2)
    | Or (e1, e2) -> Or (subst' e1, subst' e2)
    | Seq (e1, e2) -> Seq (subst' e1, subst' e2)
    | Not e -> Not (subst' e)
    | Assign (x, e1, e2) ->
        Assign (x, subst' e1, subst (Map.set env ~key:x ~data:x) e2)
    | If (cond, yes, no) -> If (subst' cond, subst' yes, subst' no)
    | Call (f, args) ->
        let args = List.map ~f:subst' args in
        Call (f, args)
    | Sample e -> Sample (subst' e)
    | Observe (d, e) -> Observe (subst' d, subst' e)
    | List _ -> failwith "List not implemented"
    | Record _ -> failwith "Record not implemented"

  let rec inline_one (fn : fn) (prog : program) =
    let rec inline_exp scope (e : Exp.t) =
      let inline_exp' = inline_exp scope in
      match e with
      | Int _ | Real _ | Bool _ -> e
      | Var x ->
          if Set.mem scope x then e else failwith ("Unbound variable " ^ x)
      | Add (e1, e2) -> Add (inline_exp' e1, inline_exp' e2)
      | Radd (e1, e2) -> Radd (inline_exp' e1, inline_exp' e2)
      | Minus (e1, e2) -> Minus (inline_exp' e1, inline_exp' e2)
      | Rminus (e1, e2) -> Rminus (inline_exp' e1, inline_exp' e2)
      | Neg e -> Neg (inline_exp' e)
      | Rneg e -> Rneg (inline_exp' e)
      | Mult (e1, e2) -> Mult (inline_exp' e1, inline_exp' e2)
      | Rmult (e1, e2) -> Rmult (inline_exp' e1, inline_exp' e2)
      | Div (e1, e2) -> Div (inline_exp' e1, inline_exp' e2)
      | Rdiv (e1, e2) -> Rdiv (inline_exp' e1, inline_exp' e2)
      | Eq (e1, e2) -> Eq (inline_exp' e1, inline_exp' e2)
      | Req (e1, e2) -> Req (inline_exp' e1, inline_exp' e2)
      | Noteq (e1, e2) -> Noteq (inline_exp' e1, inline_exp' e2)
      | Less (e1, e2) -> Less (inline_exp' e1, inline_exp' e2)
      | Rless (e1, e2) -> Rless (inline_exp' e1, inline_exp' e2)
      | And (e1, e2) -> And (inline_exp' e1, inline_exp' e2)
      | Or (e1, e2) -> Or (inline_exp' e1, inline_exp' e2)
      | Seq (e1, e2) -> Seq (inline_exp' e1, inline_exp' e2)
      | Not e -> Not (inline_exp' e)
      | Assign (x, e1, e2) ->
          Assign (x, inline_exp' e1, inline_exp (Set.add scope x) e2)
      | If (cond, yes, no) ->
          If (inline_exp' cond, inline_exp' yes, inline_exp' no)
      | Call (f, args) ->
          let args = List.map ~f:inline_exp' args in
          if Id.(equal f fn.name) then
            let kvpair =
              try List.zip_exn fn.params args
              with _ ->
                failwith
                  ("Argument length mismatch when calling function " ^ fn.name)
            in
            let kvpair =
              List.map ~f:(fun (k, v) -> (k, gen_args (), v)) kvpair
            in
            let env =
              List.fold kvpair ~init:Id.Map.empty ~f:(fun acc (k, v, _) ->
                  Map.set acc ~key:k ~data:v)
            in
            List.fold kvpair ~init:(subst env fn.body)
              ~f:(fun acc (_, v, arg) -> Exp.Assign (v, arg, acc))
          else Call (f, args)
      | Sample e -> Sample (inline_exp' e)
      | Observe (d, e) -> Observe (inline_exp' d, inline_exp' e)
      | List _ -> failwith "List not implemented"
      | Record _ -> failwith "Record not implemented"
    in
    let { funs; exp } = prog in
    match funs with
    | [] -> { funs = []; exp = inline_exp Id.Set.empty exp }
    | { name; params; body } :: funs ->
        let body = inline_exp (Id.Set.of_list params) body in
        if Id.(equal name fn.name) then
          { funs = { name; params; body } :: funs; exp }
        else
          let { funs; exp } = inline_one fn { funs; exp } in
          { funs = { name; params; body } :: funs; exp }

  let rec inline (prog : program) =
    let { funs; exp } = prog in
    match funs with
    | [] -> exp
    | fn :: funs -> inline (inline_one fn { funs; exp })

  let get_dist (name : Id.t) : any_dist =
    let open Owl.Stats in
    match name with
    | "bernoulli" ->
        Any
          {
            ret = Tyb;
            name = "bernoulli";
            params = [ Tyr ];
            sampler = (fun [ (Tyr, p) ] -> binomial_rvs ~p ~n:1 = 1);
            log_pmdf =
              (fun [ (Tyr, p) ] b -> binomial_logpdf ~p ~n:1 (Bool.to_int b));
          }
    | "normal" ->
        Any
          {
            ret = Tyr;
            name = "normal";
            params = [ Tyr; Tyr ];
            sampler =
              (fun [ (Tyr, mu); (Tyr, sigma) ] -> gaussian_rvs ~mu ~sigma);
            log_pmdf =
              (fun [ (Tyr, mu); (Tyr, sigma) ] -> gaussian_logpdf ~mu ~sigma);
          }
    | _ -> failwith "Unknown primitive function"

  let rec check : type a. tyenv -> Exp.t -> a ty -> (a, non_det) texp =
   fun tyenv e ty ->
    match e with
    | Var x -> (
        match Map.find tyenv x with
        | None -> failwith ("Unbound variable " ^ x)
        | Some (Any t) -> (
            match (t, ty) with
            | Tyi, Tyi -> { ty; exp = Var x }
            | Tyr, Tyr -> { ty; exp = Var x }
            | Tyb, Tyb -> { ty; exp = Var x }
            | _, _ -> failwith ("Variable " ^ x ^ " type mismatch")))
    | Int i -> (
        match ty with
        | Tyi -> { ty; exp = Value i }
        | _ -> failwith "Expected something other than int")
    | Add (e1, e2) -> (
        match ty with
        | Tyi -> check_bop tyenv "+" ( + ) Tyi Tyi Tyi e1 e2
        | _ -> failwith "Expected something other than int")
    | Minus (e1, e2) -> (
        match ty with
        | Tyi -> check_bop tyenv "-" ( - ) Tyi Tyi Tyi e1 e2
        | _ -> failwith "Expected something other than int")
    | Neg e -> (
        match ty with
        | Tyi -> check_uop tyenv "-" Int.neg Tyi Tyi e
        | _ -> failwith "Expected something other than int")
    | Mult (e1, e2) -> (
        match ty with
        | Tyi -> check_bop tyenv "*" ( * ) Tyi Tyi Tyi e1 e2
        | _ -> failwith "Expected something other than int")
    | Div (e1, e2) -> (
        match ty with
        | Tyi -> check_bop tyenv "/" ( / ) Tyi Tyi Tyi e1 e2
        | _ -> failwith "Expected something other than int")
    | Real r -> (
        match ty with
        | Tyr -> { ty; exp = Value r }
        | _ -> failwith "Expected something other than float")
    | Radd (e1, e2) -> (
        match ty with
        | Tyr -> check_bop tyenv "+" ( +. ) Tyr Tyr Tyr e1 e2
        | _ -> failwith "Expected something other than float")
    | Rminus (e1, e2) -> (
        match ty with
        | Tyr -> check_bop tyenv "-" ( -. ) Tyr Tyr Tyr e1 e2
        | _ -> failwith "Expected something other than float")
    | Rneg e -> (
        match ty with
        | Tyr -> check_uop tyenv "-" Float.neg Tyr Tyr e
        | _ -> failwith "Expected something other than float")
    | Rmult (e1, e2) -> (
        match ty with
        | Tyr -> check_bop tyenv "*" ( *. ) Tyr Tyr Tyr e1 e2
        | _ -> failwith "Expected something other than float")
    | Rdiv (e1, e2) -> (
        match ty with
        | Tyr -> check_bop tyenv "/" ( /. ) Tyr Tyr Tyr e1 e2
        | _ -> failwith "Expected something other than float")
    | Bool b -> (
        match ty with
        | Tyb -> { ty; exp = Value b }
        | _ -> failwith "Expected something other than bool")
    | Eq (e1, e2) -> (
        match ty with
        | Tyb -> check_bop tyenv "=" Int.( = ) Tyi Tyi Tyb e1 e2
        | _ -> failwith "Expected something other than bool")
    | Req (e1, e2) -> (
        match ty with
        | Tyb -> check_bop tyenv "=" Float.( = ) Tyr Tyr Tyb e1 e2
        | _ -> failwith "Expected something other than bool")
    | Noteq (e1, e2) -> (
        match ty with
        | Tyb -> check_bop tyenv "<>" Int.( <> ) Tyi Tyi Tyb e1 e2
        | _ -> failwith "Expected something other than bool")
    | Less (e1, e2) -> (
        match ty with
        | Tyb -> check_bop tyenv "<" Int.( < ) Tyi Tyi Tyb e1 e2
        | _ -> failwith "Expected something other than bool")
    | Rless (e1, e2) -> (
        match ty with
        | Tyb -> check_bop tyenv "<" Float.( < ) Tyr Tyr Tyb e1 e2
        | _ -> failwith "Expected something other than bool")
    | And (e1, e2) -> (
        match ty with
        | Tyb -> check_bop tyenv "&&" ( && ) Tyb Tyb Tyb e1 e2
        | _ -> failwith "Expected something other than bool")
    | Or (e1, e2) -> (
        match ty with
        | Tyb -> check_bop tyenv "||" ( || ) Tyb Tyb Tyb e1 e2
        | _ -> failwith "Expected something other than bool")
    | Not e -> (
        match ty with
        | Tyb -> check_uop tyenv "!" not Tyb Tyb e
        | _ -> failwith "Expected something other than bool")
    | Observe (d, e) -> (
        let (Any td) = convert tyenv d in
        let (Any te) = convert tyenv e in
        match (ty, td.ty, te.ty) with
        | Tyi, Tyi, Tyi -> { ty; exp = Observe (td, te) }
        | Tyr, Tyr, Tyr -> { ty; exp = Observe (td, te) }
        | Tyb, Tyb, Tyb -> { ty; exp = Observe (td, te) }
        | _, _, _ -> failwith "Argument to observe has different types")
    | Seq (e1, e2) ->
        let (Any te1) = convert tyenv e1 in
        let te2 = check tyenv e2 ty in
        { ty; exp = Let ("_", te1, te2) }
    | Assign (x, e1, e2) ->
        let (Any ({ ty = ty1; exp = _ } as te1)) = convert tyenv e1 in
        let tyenv = Map.set tyenv ~key:x ~data:(Any ty1) in
        let te2 = check tyenv e2 ty in
        { ty; exp = Let (x, te1, te2) }
    | If (pred, conseq, alt) ->
        let tpred = check tyenv pred Tyb in
        let tconseq = check tyenv conseq ty in
        let talt = check tyenv alt ty in
        { ty; exp = If (tpred, tconseq, talt) }
    | Call (prim, args) -> (
        let (Any dist) = get_dist prim in
        let args = check_args tyenv args dist.params in
        match (dist.ret, ty) with
        | Tyi, Tyi -> { ty; exp = Call (dist, args) }
        | Tyr, Tyr -> { ty; exp = Call (dist, args) }
        | Tyb, Tyb -> { ty; exp = Call (dist, args) }
        | _, _ -> failwith "No")
    | Sample e ->
        let te = check tyenv e ty in
        { ty; exp = Sample te }
    | List _ -> failwith "List not implemented"
    | Record _ -> failwith "Record not implemented"

  and check_uop :
      type arg ret.
      tyenv ->
      Id.t ->
      (arg -> ret) ->
      arg ty ->
      ret ty ->
      Exp.t ->
      (ret, non_det) texp =
   fun tyenv name f t ty e ->
    let te = check tyenv e t in
    { ty; exp = Uop ({ name; f }, te) }

  and check_bop :
      type arg1 arg2 ret.
      tyenv ->
      Id.t ->
      (arg1 -> arg2 -> ret) ->
      arg1 ty ->
      arg2 ty ->
      ret ty ->
      Exp.t ->
      Exp.t ->
      (ret, non_det) texp =
   fun tyenv name f t1 t2 ty e1 e2 ->
    let te1 = check tyenv e1 t1 in
    let te2 = check tyenv e2 t2 in
    { ty; exp = Bop ({ name; f }, te1, te2) }

  and check_args : type a. tyenv -> Exp.t list -> a params -> (a, non_det) args
      =
   fun tyenv el tyl ->
    match tyl with
    | [] -> []
    | argty :: argtys -> (
        match el with
        | [] -> failwith "Primitive call failed"
        | arg :: args ->
            let arg = check tyenv arg argty in
            let args = check_args tyenv args argtys in
            arg :: args)

  and convert (tyenv : tyenv) (e : Exp.t) : any_ndet =
    match e with
    | Var x -> (
        match Map.find tyenv x with
        | None -> failwith ("Unbound variable " ^ x)
        | Some (Any t) -> Any { ty = t; exp = Var x })
    | Int _ | Add _ | Minus _ | Neg _ | Mult _ | Div _ ->
        Any (check tyenv e Tyi)
    | Real _ | Radd _ | Rminus _ | Rneg _ | Rmult _ | Rdiv _ ->
        Any (check tyenv e Tyr)
    | Bool _ | Eq _ | Req _ | Noteq _ | Less _ | Rless _ | And _ | Or _ | Not _
      ->
        Any (check tyenv e Tyb)
    | Observe (d, e) -> (
        let (Any td) = convert tyenv d in
        let (Any te) = convert tyenv e in
        match (td.ty, te.ty) with
        | Tyi, Tyi -> Any { ty = Tyi; exp = Observe (td, te) }
        | Tyr, Tyr -> Any { ty = Tyr; exp = Observe (td, te) }
        | Tyb, Tyb -> Any { ty = Tyb; exp = Observe (td, te) }
        | _, _ -> failwith "Argument to observe has different types.")
    | Seq (e1, e2) ->
        let (Any te1) = convert tyenv e1 in
        let (Any ({ ty = ty2; exp = _ } as te2)) = convert tyenv e2 in
        Any { ty = ty2; exp = Let ("_", te1, te2) }
    | Assign (x, e1, e2) ->
        let (Any ({ ty = ty1; exp = _ } as te1)) = convert tyenv e1 in
        let tyenv = Map.set tyenv ~key:x ~data:(Any ty1) in
        let (Any ({ ty = ty2; exp = _ } as te2)) = convert tyenv e2 in
        Any { ty = ty2; exp = Let (x, te1, te2) }
    | If (pred, conseq, alt) -> (
        let tpred = check tyenv pred Tyb in
        let (Any tconseq) = convert tyenv conseq in
        let (Any talt) = convert tyenv alt in
        match (tconseq.ty, talt.ty) with
        | Tyi, Tyi -> Any { ty = Tyi; exp = If (tpred, tconseq, talt) }
        | Tyr, Tyr -> Any { ty = Tyr; exp = If (tpred, tconseq, talt) }
        | Tyb, Tyb -> Any { ty = Tyb; exp = If (tpred, tconseq, talt) }
        | _, _ ->
            failwith "Branches of an if statement must return the same type")
    | Call (prim, args) ->
        let (Any dist) = get_dist prim in
        let args = check_args tyenv args dist.params in
        Any { ty = dist.ret; exp = Call (dist, args) }
    | Sample e ->
        let (Any te) = convert tyenv e in
        Any { ty = te.ty; exp = Sample te }
    | List _ -> failwith "List not implemented"
    | Record _ -> failwith "Record not implemented"
end

module Graph = struct
  open Syntax

  type vertex = Id.t
  type arc = vertex * vertex
  type pmdf_map = any_det Id.Map.t
  type obs_map = any_det Id.Map.t

  type t = {
    vertices : vertex list;
    arcs : arc list;
    pmdf_map : pmdf_map;
    obs_map : obs_map;
  }

  let empty =
    {
      vertices = [];
      arcs = [];
      pmdf_map = Id.Map.empty;
      obs_map = Id.Map.empty;
    }

  let union g1 g2 =
    {
      vertices = g1.vertices @ g2.vertices;
      arcs = g1.arcs @ g2.arcs;
      pmdf_map =
        Map.merge g1.pmdf_map g2.pmdf_map ~f:(fun ~key:_ v ->
            match v with
            | `Left det | `Right det -> Some det
            | `Both _ ->
                failwith "Graph.union: duplicate deterministic expression");
      obs_map =
        Map.merge g1.obs_map g2.obs_map ~f:(fun ~key:_ v ->
            match v with
            | `Left obs | `Right obs -> Some obs
            | `Both _ -> failwith "Graph.union: duplicate observation");
    }

  let ( @| ) = union

  let unobserved_vertices_pmdfs ({ vertices; pmdf_map; obs_map; _ } : t) :
      (vertex * any_det) list =
    List.filter_map vertices ~f:(fun v ->
        if Map.mem obs_map v then None
        else
          let pmdf = Map.find_exn pmdf_map v in
          Some (v, pmdf))
end

module Compiler = struct
  open Syntax

  type env = any_det Id.Map.t

  let gen_vertex =
    let cnt = ref 0 in
    fun () ->
      let v = "X" ^ string_of_int !cnt in
      incr cnt;
      v

  exception Score_invalid_arguments
  exception Not_closed_observation

  let rec peval : type a. (a, det) texp -> (a, det) texp =
   fun { ty; exp } ->
    let exp =
      match exp with
      | (Value _ | Var _) as e -> e
      | Bop (op, te1, te2) -> (
          match (peval te1, peval te2) with
          | { exp = Value v1; _ }, { exp = Value v2; _ } -> Value (op.f v1 v2)
          | te1, te2 -> Bop (op, te1, te2))
      | Uop (op, te) -> (
          match peval te with
          | { exp = Value v; _ } -> Value (op.f v)
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
              Call
                ( {
                    ret = f.ret;
                    name = f.name;
                    params = [];
                    sampler = (fun [] -> f.sampler vargs);
                    log_pmdf = (fun [] -> f.log_pmdf vargs);
                  },
                  [] ))
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

  let rec score : type a. (a, det) texp -> Id.t -> (a, det) texp =
   fun e var ->
    match e.exp with
    | If (e_pred, e_con, e_alt) ->
        let s_con = score e_con var in
        let s_alt = score e_alt var in
        { ty = e.ty; exp = If (e_pred, s_con, s_alt) }
    | Call _ -> e
    | _ -> raise Score_invalid_arguments

  let rec compile :
      type a.
      env -> (bool, det) texp -> (a, non_det) texp -> Graph.t * (a, det) texp =
   fun env pred e ->
    let { ty; exp } = e in
    match exp with
    | Value v -> (Graph.empty, { ty; exp = Value v })
    | Var x -> (
        let (Any { ty = tx; exp }) = Map.find_exn env x in
        match (tx, ty) with
        | Tyi, Tyi -> (Graph.empty, { ty; exp })
        | Tyr, Tyr -> (Graph.empty, { ty; exp })
        | Tyb, Tyb -> (Graph.empty, { ty; exp })
        | _, _ -> assert false)
    | Bop (op, e1, e2) ->
        let g1, te1 = compile env pred e1 in
        let g2, te2 = compile env pred e2 in
        Graph.(g1 @| g2, { ty; exp = Bop (op, te1, te2) })
    | Uop (op, e) ->
        let g, te = compile env pred e in
        (g, { ty; exp = Uop (op, te) })
    | If (e_pred, e_con, e_alt) -> (
        let g1, de_pred = compile env pred e_pred in
        let pred_con =
          peval
            { ty = Tyb; exp = Bop ({ f = ( && ); name = "&&" }, pred, de_pred) }
        in
        let pred_alt =
          peval
            {
              ty = Tyb;
              exp =
                Bop
                  ( { f = ( && ); name = "&&" },
                    pred,
                    { ty = Tyb; exp = Uop ({ f = not; name = "!" }, de_pred) }
                  );
            }
        in
        let g2, de_con = compile env pred_con e_con in
        let g3, de_alt = compile env pred_alt e_alt in
        let g = Graph.(g1 @| g2 @| g3) in
        match pred_con.exp with
        | Value true -> (g, de_con)
        | Value false -> (g, de_alt)
        | _ -> (g, { ty; exp = If (de_pred, de_con, de_alt) }))
    | Let (x, e, body) ->
        let g1, det_exp1 = compile env pred e in
        let g2, det_exp2 =
          compile (Map.set env ~key:x ~data:(Any det_exp1)) pred body
        in
        Graph.(g1 @| g2, det_exp2)
    | Call (f, args) ->
        let g, args = compile_args env pred args in
        (g, { ty; exp = Call (f, args) })
    | Sample e ->
        let g, de = compile env pred e in
        let v = gen_vertex () in
        let de_fvs = fv de.exp in
        let f : any_det = Any (score de v) in
        let g' =
          Graph.
            {
              vertices = [ v ];
              arcs = List.map (Set.to_list de_fvs) ~f:(fun z -> (z, v));
              pmdf_map = Id.Map.singleton v f;
              obs_map = Id.Map.empty;
            }
        in
        Graph.(g @| g', { ty; exp = Var v })
    | Observe (e1, e2) ->
        let g1, de1 = compile env pred e1 in
        let g2, de2 = compile env pred e2 in
        let v = gen_vertex () in
        let f1 = score de1 v in
        let one : type a. a ty -> (a, unit) dist =
         fun ty ->
          match ty with
          | Tyi ->
              {
                ret = ty;
                name = "one";
                params = [];
                sampler = (fun _ -> 1);
                log_pmdf = (fun [] _ -> 0.0);
              }
          | Tyr ->
              {
                ret = ty;
                name = "one";
                params = [];
                sampler = (fun _ -> 1.0);
                log_pmdf = (fun [] _ -> 0.0);
              }
          | Tyb ->
              {
                ret = Tyb;
                name = "one";
                params = [];
                sampler = (fun _ -> true);
                log_pmdf = (fun [] _ -> 0.0);
              }
        in
        let f = { ty; exp = If (pred, f1, { ty; exp = Call (one ty, []) }) } in
        let fvs = Id.(fv de1.exp @| fv pred.exp) in
        if not (Set.is_empty (fv de2.exp)) then raise Not_closed_observation;
        let g' =
          Graph.
            {
              vertices = [ v ];
              arcs = List.map (Set.to_list fvs) ~f:(fun z -> (z, v));
              pmdf_map = Id.Map.singleton v (Any f : any_det);
              obs_map = Id.Map.singleton v (Any de2 : any_det);
            }
        in
        Graph.(g1 @| g2 @| g', de2)

  and compile_args :
      type a.
      env -> (bool, det) texp -> (a, non_det) args -> Graph.t * (a, det) args =
   fun env pred args ->
    match args with
    | [] -> (Graph.empty, [])
    | arg :: args ->
        let g, arg = compile env pred arg in
        let g', args = compile_args env pred args in
        Graph.(g @| g', arg :: args)

  let compile_program (prog : program) : Graph.t * any_det =
    let open Typing in
    let (Any e) = convert Id.Map.empty (inline prog) in
    let g, e = compile Id.Map.empty { ty = Tyb; exp = Value true } e in
    (g, Any e)
end

module Printing = struct
  open Syntax

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

  let to_string (Any e : any_det) =
    e |> of_exp |> sexp_of_t |> Sexp.to_string_hum
end

module Evaluator = struct
  open Syntax

  type env = any_v Id.Table.t

  let rec eval : type a. env -> (a, det) texp -> a =
   fun env { ty; exp } ->
    match exp with
    | Value v -> v
    | Var x -> (
        let (Any (tv, v)) = Hashtbl.find_exn env x in
        match (ty, tv) with
        | Tyi, Tyi -> v
        | Tyr, Tyr -> v
        | Tyb, Tyb -> v
        | _ -> assert false)
    | Bop (op, te1, te2) -> op.f (eval env te1) (eval env te2)
    | Uop (op, te) -> op.f (eval env te)
    | If (te_pred, te_cons, te_alt) ->
        if eval env te_pred then eval env te_cons else eval env te_alt
    | Call (f, args) -> f.sampler (eval_args env args)

  and eval_args : type a. env -> (a, det) args -> a vargs =
   fun env -> function
    | [] -> []
    | te :: tl -> (te.ty, eval env te) :: eval_args env tl

  let rec eval_pmdf (env : env) (Any { ty; exp } : any_det) :
      (any_v -> float) * any_v =
    match exp with
    | If (te_pred, te_cons, te_alt) ->
        if eval env te_pred then eval_pmdf env (Any te_cons)
        else eval_pmdf env (Any te_alt)
    | Call (f, args) ->
        let pmdf (Any (ty', v) : any_v) =
          match (ty, ty') with
          | Tyi, Tyi -> f.log_pmdf (eval_args env args) v
          | Tyr, Tyr -> f.log_pmdf (eval_args env args) v
          | Tyb, Tyb -> f.log_pmdf (eval_args env args) v
          | _, _ -> assert false
        in
        (pmdf, Any (ty, eval env { ty; exp }))
    | _ -> (* not reachable *) assert false

  let gibbs_sampling ~(num_samples : int) (graph : Graph.t) (query : any_det) :
      float array =
    (* Initialize the context with the observed values. Float conversion must
       succeed as observed variables do not contain free variables *)
    let default : type a. a ty -> a = function
      | Tyi -> 0
      | Tyr -> 0.0
      | Tyb -> false
    in
    let ctx = Id.Table.create () in
    let () =
      Map.iteri graph.obs_map ~f:(fun ~key ~data:(Any { ty; exp }) ->
          let data : any_v = Any (ty, eval ctx { ty; exp }) in
          Hashtbl.set ctx ~key ~data)
    in
    let unobserved = Graph.unobserved_vertices_pmdfs graph in
    let () =
      List.iter unobserved ~f:(fun (key, Any { ty; _ }) ->
          let data : any_v = Any (ty, default ty) in
          Hashtbl.set ctx ~key ~data)
    in

    (* Adapted from gibbs_sampling of Owl *)
    let a, b = (1000, 10) in
    let num_iter = a + (b * num_samples) in
    let samples = Array.create ~len:num_samples 0. in
    for i = 0 to num_iter - 1 do
      (* Gibbs step *)
      List.iter unobserved ~f:(fun (key, exp) ->
          let curr = Hashtbl.find_exn ctx key in
          let log_pmdf, cand = eval_pmdf ctx exp in

          (* metropolis-hastings update logic *)
          Hashtbl.set ctx ~key ~data:cand;
          let log_pmdf', _ = eval_pmdf ctx exp in
          let log_alpha = log_pmdf' curr -. log_pmdf cand in

          (* variables influenced by "name" *)
          let name_infl =
            Map.filteri graph.pmdf_map
              ~f:(fun ~key:name ~data:(Any { exp; _ }) ->
                Id.(name = key) || Set.mem (fv exp) key)
          in
          let log_alpha =
            Map.fold name_infl ~init:log_alpha
              ~f:(fun ~key:name ~data:exp acc ->
                let prob_w_cand =
                  (fst (eval_pmdf ctx exp)) (Hashtbl.find_exn ctx name)
                in
                Hashtbl.set ctx ~key ~data:curr;
                let prob_wo_cand =
                  (fst (eval_pmdf ctx exp)) (Hashtbl.find_exn ctx name)
                in
                Hashtbl.set ctx ~key ~data:cand;
                acc +. prob_w_cand -. prob_wo_cand)
          in

          let alpha = Float.exp log_alpha in
          let uniform = Owl.Stats.std_uniform_rvs () in
          if Float.(uniform > alpha) then Hashtbl.set ctx ~key ~data:curr);

      if i >= a && i mod b = 0 then
        let (Any query) = query in
        let query =
          match (query.ty, eval ctx query) with
          | Tyi, i -> float_of_int i
          | Tyr, r -> r
          | Tyb, b -> if b then 1.0 else 0.0
        in
        samples.((i - a) / b) <- query
    done;

    samples

  let infer ?(filename : string = "out") ?(num_samples : int = 100_000)
      (graph : Graph.t) (query : any_det) : string =
    let samples = gibbs_sampling graph ~num_samples query in

    let filename = String.chop_suffix_if_exists filename ~suffix:".stp" in
    let plot_path = filename ^ ".png" in

    let open Owl_plplot in
    let h = Plot.create plot_path in
    Plot.set_title h (Printing.to_string query);
    let mat = Owl.Mat.of_array samples 1 num_samples in
    Plot.histogram ~h ~bin:50 mat;
    Plot.output h;
    plot_path
end

open! Core
open Typed_tree

type tyenv = some_ty Id.Map.t

exception Arity_mismatch of string
exception Unbound_variable of string
exception Type_mismatch of string

let gen_args =
  let cnt = ref 0 in
  fun () ->
    let arg = "$arg" ^ string_of_int !cnt in
    incr cnt;
    arg

let rec subst (env : Id.t Id.Map.t) : Parse_tree.exp -> Parse_tree.exp =
  let subst' = subst env in
  function
  | (Int _ | Real _ | Bool _) as e -> e
  | Var x -> (
      match Map.find env x with
      | None -> raise (Unbound_variable x)
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

let rec inline_one (fn : Parse_tree.fn) (prog : Parse_tree.program) =
  let open Parse_tree in
  let rec inline_exp scope (e : exp) =
    let inline_exp' = inline_exp scope in
    match e with
    | Int _ | Real _ | Bool _ -> e
    | Var x -> if Set.mem scope x then e else raise (Unbound_variable x)
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
    | Call (f, args) as e ->
        (* A-Normalize the arguments. For example, f(sample(e)) should only evaluate sample(e) once. *)
        let args = List.map ~f:inline_exp' args in
        if Id.(f <> fn.name) then e
        else
          let param_args =
            try List.zip_exn fn.params args
            with _ -> raise (Arity_mismatch fn.name)
          in
          let param_args =
            List.map ~f:(fun (p, a) -> (p, gen_args (), a)) param_args
          in
          let env =
            List.fold param_args ~init:Id.Map.empty ~f:(fun env (p, p', _a) ->
                Map.set env ~key:p ~data:p')
          in
          List.fold param_args ~init:(subst env fn.body)
            ~f:(fun body (_p, p', a) -> Assign (p', a, body))
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
      if Id.(name = fn.name) then { funs = { name; params; body } :: funs; exp }
      else
        let { funs; exp } = inline_one fn { funs; exp } in
        { funs = { name; params; body } :: funs; exp }

let rec inline (prog : Parse_tree.program) =
  let open Parse_tree in
  let { funs; exp } = prog in
  match funs with
  | [] -> exp
  | fn :: funs -> inline (inline_one fn { funs; exp })

let rec check : type a. tyenv -> Parse_tree.exp -> a ty -> (a, non_det) texp =
 fun tyenv e ty ->
  match e with
  | Var x -> (
      match Map.find tyenv x with
      | None -> raise (Unbound_variable x)
      | Some (Ex t) -> (
          match (t, ty) with
          | Tyi, Tyi -> { ty; exp = Var x }
          | Tyr, Tyr -> { ty; exp = Var x }
          | Tyb, Tyb -> { ty; exp = Var x }
          | t1, t2 ->
              raise
                (Type_mismatch
                   (sprintf "Variable %s: expected %s, got %s" x
                      (string_of_ty t2) (string_of_ty t1)))))
  | Int i -> (
      match ty with
      | Tyi -> { ty; exp = Value i }
      | t ->
          raise
            (Type_mismatch (sprintf "Expected int, got %s" (string_of_ty t))))
  | Add (e1, e2) -> (
      match ty with
      | Tyi -> check_bop tyenv "+" ( + ) Tyi Tyi Tyi e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected int for Add, got %s" (string_of_ty t))))
  | Minus (e1, e2) -> (
      match ty with
      | Tyi -> check_bop tyenv "-" ( - ) Tyi Tyi Tyi e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected int for Minus, got %s" (string_of_ty t))))
  | Neg e -> (
      match ty with
      | Tyi -> check_uop tyenv "-" Int.neg Tyi Tyi e
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected int for Neg, got %s" (string_of_ty t))))
  | Mult (e1, e2) -> (
      match ty with
      | Tyi -> check_bop tyenv "*" ( * ) Tyi Tyi Tyi e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected int for Mult, got %s" (string_of_ty t))))
  | Div (e1, e2) -> (
      match ty with
      | Tyi -> check_bop tyenv "/" ( / ) Tyi Tyi Tyi e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected int for Div, got %s" (string_of_ty t))))
  | Real r -> (
      match ty with
      | Tyr -> { ty; exp = Value r }
      | t ->
          raise
            (Type_mismatch (sprintf "Expected float, got %s" (string_of_ty t))))
  | Radd (e1, e2) -> (
      match ty with
      | Tyr -> check_bop tyenv "+" ( +. ) Tyr Tyr Tyr e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected float for Radd, got %s" (string_of_ty t))))
  | Rminus (e1, e2) -> (
      match ty with
      | Tyr -> check_bop tyenv "-" ( -. ) Tyr Tyr Tyr e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected float for Rminus, got %s" (string_of_ty t))))
  | Rneg e -> (
      match ty with
      | Tyr -> check_uop tyenv "-" Float.neg Tyr Tyr e
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected float for Rneg, got %s" (string_of_ty t))))
  | Rmult (e1, e2) -> (
      match ty with
      | Tyr -> check_bop tyenv "*" ( *. ) Tyr Tyr Tyr e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected float for Rmult, got %s" (string_of_ty t))))
  | Rdiv (e1, e2) -> (
      match ty with
      | Tyr -> check_bop tyenv "/" ( /. ) Tyr Tyr Tyr e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected float for Rdiv, got %s" (string_of_ty t))))
  | Bool b -> (
      match ty with
      | Tyb -> { ty; exp = Value b }
      | t ->
          raise
            (Type_mismatch (sprintf "Expected bool, got %s" (string_of_ty t))))
  | Eq (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "=" Int.( = ) Tyi Tyi Tyb e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected bool for Eq, got %s" (string_of_ty t))))
  | Req (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "=" Float.( = ) Tyr Tyr Tyb e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected bool for Req, got %s" (string_of_ty t))))
  | Noteq (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "<>" Int.( <> ) Tyi Tyi Tyb e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected bool for Noteq, got %s" (string_of_ty t))))
  | Less (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "<" Int.( < ) Tyi Tyi Tyb e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected bool for Less, got %s" (string_of_ty t))))
  | Rless (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "<" Float.( < ) Tyr Tyr Tyb e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected bool for Rless, got %s" (string_of_ty t))))
  | And (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "&&" ( && ) Tyb Tyb Tyb e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected bool for And, got %s" (string_of_ty t))))
  | Or (e1, e2) -> (
      match ty with
      | Tyb -> check_bop tyenv "||" ( || ) Tyb Tyb Tyb e1 e2
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected bool for Or, got %s" (string_of_ty t))))
  | Not e -> (
      match ty with
      | Tyb -> check_uop tyenv "!" not Tyb Tyb e
      | t ->
          raise
            (Type_mismatch
               (sprintf "Expected bool for Not, got %s" (string_of_ty t))))
  | Observe (d, e) -> (
      let (Ex td) = convert tyenv d in
      let (Ex te) = convert tyenv e in
      match (ty, td.ty, te.ty) with
      | Tyi, Tyi, Tyi -> { ty; exp = Observe (td, te) }
      | Tyr, Tyr, Tyr -> { ty; exp = Observe (td, te) }
      | Tyb, Tyb, Tyb -> { ty; exp = Observe (td, te) }
      | _ ->
          raise
            (Type_mismatch (sprintf "Argument to observe has different types")))
  | Seq (e1, e2) ->
      let (Ex te1) = convert tyenv e1 in
      let te2 = check tyenv e2 ty in
      { ty; exp = Let ("_", te1, te2) }
  | Assign (x, e1, e2) ->
      let (Ex ({ ty = ty1; exp = _ } as te1)) = convert tyenv e1 in
      let tyenv = Map.set tyenv ~key:x ~data:(Ex ty1) in
      let te2 = check tyenv e2 ty in
      { ty; exp = Let (x, te1, te2) }
  | If (pred, conseq, alt) ->
      let tpred = check tyenv pred Tyb in
      let tconseq = check tyenv conseq ty in
      let talt = check tyenv alt ty in
      { ty; exp = If (tpred, tconseq, talt) }
  | Call (prim, args) -> (
      let (Ex dist) = Dist.get_dist prim in
      let args = check_args tyenv args dist.params in
      match (dist.ret, ty) with
      | Tyi, Tyi -> { ty; exp = Call (dist, args) }
      | Tyr, Tyr -> { ty; exp = Call (dist, args) }
      | Tyb, Tyb -> { ty; exp = Call (dist, args) }
      | _ ->
          raise
            (Type_mismatch
               (sprintf "Expected %s for Call, got %s" (string_of_ty dist.ret)
                  (string_of_ty ty))))
  | Sample e ->
      let te = check tyenv e ty in
      { ty; exp = Sample te }
  | List _ -> raise (Type_mismatch "List not implemented")
  | Record _ -> raise (Type_mismatch "Record not implemented")

and check_uop :
    type arg ret.
    tyenv ->
    Id.t ->
    (arg -> ret) ->
    arg ty ->
    ret ty ->
    Parse_tree.exp ->
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
    Parse_tree.exp ->
    Parse_tree.exp ->
    (ret, non_det) texp =
 fun tyenv name f t1 t2 ty e1 e2 ->
  let te1 = check tyenv e1 t1 in
  let te2 = check tyenv e2 t2 in
  { ty; exp = Bop ({ name; f }, te1, te2) }

and check_args :
    type a. tyenv -> Parse_tree.exp list -> a params -> (a, non_det) args =
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

and convert (tyenv : tyenv) (e : Parse_tree.exp) : some_ndet =
  match e with
  | Var x -> (
      match Map.find tyenv x with
      | None -> failwith ("Unbound variable " ^ x)
      | Some (Ex t) -> Ex { ty = t; exp = Var x })
  | Int _ | Add _ | Minus _ | Neg _ | Mult _ | Div _ -> Ex (check tyenv e Tyi)
  | Real _ | Radd _ | Rminus _ | Rneg _ | Rmult _ | Rdiv _ ->
      Ex (check tyenv e Tyr)
  | Bool _ | Eq _ | Req _ | Noteq _ | Less _ | Rless _ | And _ | Or _ | Not _ ->
      Ex (check tyenv e Tyb)
  | Observe (d, e) -> (
      let (Ex td) = convert tyenv d in
      let (Ex te) = convert tyenv e in
      match (td.ty, te.ty) with
      | Tyi, Tyi -> Ex { ty = Tyi; exp = Observe (td, te) }
      | Tyr, Tyr -> Ex { ty = Tyr; exp = Observe (td, te) }
      | Tyb, Tyb -> Ex { ty = Tyb; exp = Observe (td, te) }
      | _, _ -> failwith "Argument to observe has different types.")
  | Seq (e1, e2) ->
      let (Ex te1) = convert tyenv e1 in
      let (Ex ({ ty = ty2; exp = _ } as te2)) = convert tyenv e2 in
      Ex { ty = ty2; exp = Let ("_", te1, te2) }
  | Assign (x, e1, e2) ->
      let (Ex ({ ty = ty1; exp = _ } as te1)) = convert tyenv e1 in
      let tyenv = Map.set tyenv ~key:x ~data:(Ex ty1) in
      let (Ex ({ ty = ty2; exp = _ } as te2)) = convert tyenv e2 in
      Ex { ty = ty2; exp = Let (x, te1, te2) }
  | If (pred, conseq, alt) -> (
      let tpred = check tyenv pred Tyb in
      let (Ex tconseq) = convert tyenv conseq in
      let (Ex talt) = convert tyenv alt in
      match (tconseq.ty, talt.ty) with
      | Tyi, Tyi -> Ex { ty = Tyi; exp = If (tpred, tconseq, talt) }
      | Tyr, Tyr -> Ex { ty = Tyr; exp = If (tpred, tconseq, talt) }
      | Tyb, Tyb -> Ex { ty = Tyb; exp = If (tpred, tconseq, talt) }
      | _, _ -> failwith "Branches of an if statement must return the same type"
      )
  | Call (prim, args) ->
      let (Ex dist) = Dist.get_dist prim in
      let args = check_args tyenv args dist.params in
      Ex { ty = dist.ret; exp = Call (dist, args) }
  | Sample e ->
      let (Ex te) = convert tyenv e in
      Ex { ty = te.ty; exp = Sample te }
  | List _ -> failwith "List not implemented"
  | Record _ -> failwith "Record not implemented"

let check_program (program : Parse_tree.program) : some_ndet =
  convert Id.Map.empty (inline program)

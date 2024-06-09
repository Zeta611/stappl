open! Core
open Typed_tree

type tyenv = some_ty Id.Map.t

exception Arity_mismatch of string
exception Unbound_variable of string
exception Type_error of string

let raise_if_type_error (exp : Parse_tree.exp) (t1 : _ ty) (t2 : _ ty) : _ =
  raise
    (Type_error
       (sprintf
          "Branches of an if statement must return the same type: got (%s) and \
           (%s) in %s"
          (string_of_ty t1) (string_of_ty t2)
          ([%sexp (exp : Parse_tree.exp)] |> Sexp.to_string_hum)))

let get_bop :
    type a b c. Parse_tree.exp * (a dty * b dty * c dty) -> (a, b, c) bop =
  function
  | Add _, (Tyi, Tyi, Tyi) -> { name = "+"; op = ( + ) }
  | Radd _, (Tyr, Tyr, Tyr) -> { name = "+."; op = ( +. ) }
  | Minus _, (Tyi, Tyi, Tyi) -> { name = "-"; op = ( - ) }
  | Rminus _, (Tyr, Tyr, Tyr) -> { name = "-."; op = ( -. ) }
  | Mult _, (Tyi, Tyi, Tyi) -> { name = "*"; op = ( * ) }
  | Rmult _, (Tyr, Tyr, Tyr) -> { name = "*."; op = ( *. ) }
  | Div _, (Tyi, Tyi, Tyi) -> { name = "/"; op = ( / ) }
  | Rdiv _, (Tyr, Tyr, Tyr) -> { name = "/."; op = ( /. ) }
  | Eq _, (Tyi, Tyi, Tyb) -> { name = "="; op = ( = ) }
  | Req _, (Tyr, Tyr, Tyb) -> { name = "=."; op = Float.( = ) }
  | Noteq _, (Tyi, Tyi, Tyb) -> { name = "<>"; op = ( <> ) }
  | Less _, (Tyi, Tyi, Tyb) -> { name = "<"; op = ( < ) }
  | Rless _, (Tyr, Tyr, Tyb) -> { name = "<."; op = Float.( < ) }
  | And _, (Tyb, Tyb, Tyb) -> { name = "&&"; op = ( && ) }
  | Or _, (Tyb, Tyb, Tyb) -> { name = "||"; op = ( || ) }
  | _ -> raise (Type_error "Expected binary operation")

let get_uop : type a b. Parse_tree.exp * (a dty * b dty) -> (a, b) uop =
  function
  | Neg _, (Tyi, Tyi) -> { name = "~-"; op = ( ~- ) }
  | Rneg _, (Tyr, Tyr) -> { name = "~-."; op = ( ~-. ) }
  | Not _, (Tyb, Tyb) -> { name = "!"; op = not }
  | e, _ ->
      raise
        (Type_error
           ("Expected unary operation, got "
           ^ ([%sexp (e : Parse_tree.exp)] |> Sexp.to_string_hum)))

let unify_branches :
    type a_con a_alt s_pred s_con s_alt.
    ((bool, s_pred) dat_ty, non_det) texp ->
    ((a_con, s_con) dat_ty, non_det) texp ->
    ((a_alt, s_alt) dat_ty, non_det) texp ->
    (a_con, a_alt) eq ->
    a_con some_dat_non_det_texp =
 fun te_pred te_con te_alt Refl ->
  match te_pred.ty with
  | Dat_ty (Tyb, Val) -> (
      match (te_con.ty, te_alt.ty) with
      | Dat_ty (Tyu, Val), Dat_ty (Tyu, Val) ->
          Ex { ty = Dat_ty (Tyu, Val); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyu, Val), Dat_ty (Tyu, Rv) ->
          Ex { ty = Dat_ty (Tyu, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyu, Rv), Dat_ty (Tyu, Val) ->
          Ex { ty = Dat_ty (Tyu, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyu, Rv), Dat_ty (Tyu, Rv) ->
          Ex { ty = Dat_ty (Tyu, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyb, Val), Dat_ty (Tyb, Val) ->
          Ex { ty = Dat_ty (Tyb, Val); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyb, Val), Dat_ty (Tyb, Rv) ->
          Ex { ty = Dat_ty (Tyb, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyb, Rv), Dat_ty (Tyb, Val) ->
          Ex { ty = Dat_ty (Tyb, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyb, Rv), Dat_ty (Tyb, Rv) ->
          Ex { ty = Dat_ty (Tyb, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyi, Val), Dat_ty (Tyi, Val) ->
          Ex { ty = Dat_ty (Tyi, Val); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyi, Val), Dat_ty (Tyi, Rv) ->
          Ex { ty = Dat_ty (Tyi, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyi, Rv), Dat_ty (Tyi, Val) ->
          Ex { ty = Dat_ty (Tyi, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyi, Rv), Dat_ty (Tyi, Rv) ->
          Ex { ty = Dat_ty (Tyi, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyr, Val), Dat_ty (Tyr, Val) ->
          Ex { ty = Dat_ty (Tyr, Val); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyr, Val), Dat_ty (Tyr, Rv) ->
          Ex { ty = Dat_ty (Tyr, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyr, Rv), Dat_ty (Tyr, Val) ->
          Ex { ty = Dat_ty (Tyr, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyr, Rv), Dat_ty (Tyr, Rv) ->
          Ex { ty = Dat_ty (Tyr, Rv); exp = If (te_pred, te_con, te_alt) })
  | Dat_ty (Tyb, Rv) -> (
      match (te_con.ty, te_alt.ty) with
      | Dat_ty (Tyu, Val), Dat_ty (Tyu, Val) ->
          Ex { ty = Dat_ty (Tyu, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyu, Val), Dat_ty (Tyu, Rv) ->
          Ex { ty = Dat_ty (Tyu, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyu, Rv), Dat_ty (Tyu, Val) ->
          Ex { ty = Dat_ty (Tyu, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyu, Rv), Dat_ty (Tyu, Rv) ->
          Ex { ty = Dat_ty (Tyu, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyb, Val), Dat_ty (Tyb, Val) ->
          Ex { ty = Dat_ty (Tyb, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyb, Val), Dat_ty (Tyb, Rv) ->
          Ex { ty = Dat_ty (Tyb, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyb, Rv), Dat_ty (Tyb, Val) ->
          Ex { ty = Dat_ty (Tyb, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyb, Rv), Dat_ty (Tyb, Rv) ->
          Ex { ty = Dat_ty (Tyb, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyi, Val), Dat_ty (Tyi, Val) ->
          Ex { ty = Dat_ty (Tyi, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyi, Val), Dat_ty (Tyi, Rv) ->
          Ex { ty = Dat_ty (Tyi, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyi, Rv), Dat_ty (Tyi, Val) ->
          Ex { ty = Dat_ty (Tyi, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyi, Rv), Dat_ty (Tyi, Rv) ->
          Ex { ty = Dat_ty (Tyi, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyr, Val), Dat_ty (Tyr, Val) ->
          Ex { ty = Dat_ty (Tyr, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyr, Val), Dat_ty (Tyr, Rv) ->
          Ex { ty = Dat_ty (Tyr, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyr, Rv), Dat_ty (Tyr, Val) ->
          Ex { ty = Dat_ty (Tyr, Rv); exp = If (te_pred, te_con, te_alt) }
      | Dat_ty (Tyr, Rv), Dat_ty (Tyr, Rv) ->
          Ex { ty = Dat_ty (Tyr, Rv); exp = If (te_pred, te_con, te_alt) })

let rec check_dat :
    type a. tyenv -> Parse_tree.exp * a dty -> a some_dat_non_det_texp =
 fun tyenv (exp, dty) ->
  Logs.debug (fun m ->
      m "Checking exp (%a : %a)" Sexp.pp_hum
        [%sexp (exp : Parse_tree.exp)]
        (fun fmt dty -> Format.pp_print_string fmt (string_of_dty dty))
        dty);

  match exp with
  | Var x -> (
      match Map.find tyenv x with
      | None -> raise (Unbound_variable x)
      | Some (Ex ty_x) -> (
          match (ty_x, dty) with
          | Dat_ty (Tyu, _), Tyu -> Ex { ty = ty_x; exp = Var x }
          | Dat_ty (Tyi, _), Tyi -> Ex { ty = ty_x; exp = Var x }
          | Dat_ty (Tyr, _), Tyr -> Ex { ty = ty_x; exp = Var x }
          | Dat_ty (Tyb, _), Tyb -> Ex { ty = ty_x; exp = Var x }
          | ty_x, dty ->
              raise
                (Type_error
                   (sprintf "Variable %s: expected (%s _), got %s" x
                      (string_of_dty dty) (string_of_ty ty_x)))))
  | Int i -> (
      match dty with
      | Tyi -> Ex { ty = Dat_ty (Tyi, Val); exp = Value i }
      | dty ->
          raise
            (Type_error (sprintf "Expected int, got %s" (string_of_dty dty))))
  | Bool b -> (
      match dty with
      | Tyb -> Ex { ty = Dat_ty (Tyb, Val); exp = Value b }
      | dty ->
          raise
            (Type_error (sprintf "Expected bool, got %s" (string_of_dty dty))))
  | Real r -> (
      match dty with
      | Tyr -> Ex { ty = Dat_ty (Tyr, Val); exp = Value r }
      | dty ->
          raise
            (Type_error (sprintf "Expected real, got %s" (string_of_dty dty))))
  | Add (e1, e2) | Minus (e1, e2) | Mult (e1, e2) | Div (e1, e2) -> (
      match dty with
      | Tyi ->
          let bop = get_bop (exp, (Tyi, Tyi, Tyi)) in
          check_bop tyenv bop (e1, Tyi) (e2, Tyi) Tyi
      | dty ->
          raise
            (Type_error (sprintf "Expected int, got %s" (string_of_dty dty))))
  | Radd (e1, e2) | Rminus (e1, e2) | Rmult (e1, e2) | Rdiv (e1, e2) -> (
      match dty with
      | Tyr ->
          let bop = get_bop (exp, (Tyr, Tyr, Tyr)) in
          check_bop tyenv bop (e1, Tyr) (e2, Tyr) Tyr
      | dty ->
          raise
            (Type_error (sprintf "Expected real, got %s" (string_of_dty dty))))
  | Eq (e1, e2) | Noteq (e1, e2) | Less (e1, e2) -> (
      match dty with
      | Tyb ->
          let bop = get_bop (exp, (Tyi, Tyi, Tyb)) in
          check_bop tyenv bop (e1, Tyi) (e2, Tyi) Tyb
      | dty ->
          raise
            (Type_error (sprintf "Expected int, got %s" (string_of_dty dty))))
  | Req (e1, e2) | Rless (e1, e2) -> (
      match dty with
      | Tyb ->
          let bop = get_bop (exp, (Tyr, Tyr, Tyb)) in
          check_bop tyenv bop (e1, Tyr) (e2, Tyr) Tyb
      | dty ->
          raise
            (Type_error (sprintf "Expected real, got %s" (string_of_dty dty))))
  | And (e1, e2) | Or (e1, e2) -> (
      match dty with
      | Tyb ->
          let bop = get_bop (exp, (Tyb, Tyb, Tyb)) in
          check_bop tyenv bop (e1, Tyb) (e2, Tyb) Tyb
      | dty ->
          raise
            (Type_error (sprintf "Expected bool, got %s" (string_of_dty dty))))
  | Neg e -> (
      match dty with
      | Tyi ->
          let uop = get_uop (exp, (Tyi, Tyi)) in
          check_uop tyenv uop (e, Tyi) Tyi
      | dty ->
          raise
            (Type_error (sprintf "Expected int, got %s" (string_of_dty dty))))
  | Rneg e -> (
      match dty with
      | Tyr ->
          let uop = get_uop (exp, (Tyr, Tyr)) in
          check_uop tyenv uop (e, Tyr) Tyr
      | dty ->
          raise
            (Type_error (sprintf "Expected real, got %s" (string_of_dty dty))))
  | Not e -> (
      match dty with
      | Tyb ->
          let uop = get_uop (exp, (Tyb, Tyb)) in
          check_uop tyenv uop (e, Tyb) Tyb
      | dty ->
          raise
            (Type_error (sprintf "Expected bool, got %s" (string_of_dty dty))))
  | Observe (de, ve) -> (
      match dty with
      | Tyu -> (
          let tde = infer tyenv de in
          let tve = infer tyenv ve in
          match (tde, tve) with
          | ( Ex ({ ty = Dist_ty Tyu; _ } as tde),
              Ex ({ ty = Dat_ty (Tyu, Val); _ } as tve) ) ->
              Ex { ty = Dat_ty (Tyu, Val); exp = Observe (tde, tve) }
          | ( Ex ({ ty = Dist_ty Tyb; _ } as tde),
              Ex ({ ty = Dat_ty (Tyb, Val); _ } as tve) ) ->
              Ex { ty = Dat_ty (Tyu, Val); exp = Observe (tde, tve) }
          | ( Ex ({ ty = Dist_ty Tyi; _ } as tde),
              Ex ({ ty = Dat_ty (Tyi, Val); _ } as tve) ) ->
              Ex { ty = Dat_ty (Tyu, Val); exp = Observe (tde, tve) }
          | ( Ex ({ ty = Dist_ty Tyr; _ } as tde),
              Ex ({ ty = Dat_ty (Tyr, Val); _ } as tve) ) ->
              Ex { ty = Dat_ty (Tyu, Val); exp = Observe (tde, tve) }
          | _, _ ->
              (* TODO: more precise error message *)
              raise
                (Type_error
                   (sprintf "Arguments to observe have unexpected types")))
      | dty ->
          raise
            (Type_error (sprintf "Expected unit, got %s" (string_of_dty dty))))
  | Seq (e1, e2) ->
      let (Ex te1) = infer tyenv e1 in
      let (Ex te2) = check_dat tyenv (e2, dty) in
      Ex { te2 with exp = Let ("_", te1, te2) }
  | Assign (x, e1, e2) ->
      let (Ex te1) = infer tyenv e1 in
      let tyenv = Map.set tyenv ~key:x ~data:(Ex te1.ty) in
      let (Ex te2) = check_dat tyenv (e2, dty) in
      Ex { te2 with exp = Let (x, te1, te2) }
  | If (e_pred, e_con, e_alt) ->
      let (Ex te_pred) = check_dat tyenv (e_pred, Tyb) in
      let (Ex te_con) = check_dat tyenv (e_con, dty) in
      let (Ex te_alt) = check_dat tyenv (e_alt, dty) in
      unify_branches te_pred te_con te_alt Refl
  | Sample e -> (
      let te = check_dist tyenv (e, dty) in
      match te.ty with
      | Dist_ty Tyu -> Ex { ty = Dat_ty (Tyu, Rv); exp = Sample te }
      | Dist_ty Tyb -> Ex { ty = Dat_ty (Tyb, Rv); exp = Sample te }
      | Dist_ty Tyi -> Ex { ty = Dat_ty (Tyi, Rv); exp = Sample te }
      | Dist_ty Tyr -> Ex { ty = Dat_ty (Tyr, Rv); exp = Sample te })
  | List _ -> raise (Type_error "List not implemented")
  | Record _ -> raise (Type_error "Record not implemented")
  | Call (f, e) ->
      raise
        (Type_error
           ("Expected data type, got distribution: " ^ f ^ " "
           ^ ([%sexp (e : Parse_tree.exp list)] |> Sexp.to_string_hum)))

and check_uop :
    type a ret.
    tyenv ->
    (a, ret) uop ->
    Parse_tree.exp * a dty ->
    ret dty ->
    ret some_dat_non_det_texp =
 fun tyenv uop (e, t) tret ->
  let (Ex ({ ty = Dat_ty (_, s); _ } as te)) = check_dat tyenv (e, t) in
  match s with
  | Val -> Ex { ty = Dat_ty (tret, Val); exp = Uop (uop, te) }
  | _ -> Ex { ty = Dat_ty (tret, Rv); exp = Uop (uop, te) }

and check_bop :
    type a1 a2 ret.
    tyenv ->
    (a1, a2, ret) bop ->
    Parse_tree.exp * a1 dty ->
    Parse_tree.exp * a2 dty ->
    ret dty ->
    ret some_dat_non_det_texp =
 fun tyenv bop (e1, t1) (e2, t2) tret ->
  let (Ex ({ ty = Dat_ty (_, s1); _ } as te1)) = check_dat tyenv (e1, t1) in
  let (Ex ({ ty = Dat_ty (_, s2); _ } as te2)) = check_dat tyenv (e2, t2) in
  match (s1, s2) with
  | Val, Val -> Ex { ty = Dat_ty (tret, Val); exp = Bop (bop, te1, te2) }
  | _, _ -> Ex { ty = Dat_ty (tret, Rv); exp = Bop (bop, te1, te2) }

and check_args :
    type a. tyenv -> Id.t -> Parse_tree.exp list * a params -> (a, non_det) args
    =
 fun tyenv prim (es, dtys) ->
  match dtys with
  | [] -> []
  | dty :: dtys -> (
      match es with
      | [] -> raise (Arity_mismatch prim)
      | arg :: args ->
          let (Ex arg) = check_dat tyenv (arg, dty) in
          let args = check_args tyenv prim (args, dtys) in
          arg :: args)

and check_dist : type a. tyenv -> Parse_tree.exp * a dty -> a dist_non_det_texp
    =
 fun tyenv (exp, dty) ->
  Logs.debug (fun m ->
      m "Checking exp (%a : %a dist)" Sexp.pp_hum
        [%sexp (exp : Parse_tree.exp)]
        (fun fmt dty -> Format.pp_print_string fmt (string_of_dty dty))
        dty);

  match exp with
  | Var x -> (
      match Map.find tyenv x with
      | None -> raise (Unbound_variable x)
      | Some (Ex ty_x) -> (
          match (ty_x, dty) with
          | Dist_ty Tyu, Tyu -> { ty = ty_x; exp = Var x }
          | Dist_ty Tyb, Tyb -> { ty = ty_x; exp = Var x }
          | Dist_ty Tyi, Tyi -> { ty = ty_x; exp = Var x }
          | Dist_ty Tyr, Tyr -> { ty = ty_x; exp = Var x }
          | ty_x, dty ->
              raise
                (Type_error
                   (sprintf "Variable %s: expected (%s _), got %s" x
                      (string_of_dty dty) (string_of_ty ty_x)))))
  | Seq (e1, e2) ->
      let (Ex te1) = infer tyenv e1 in
      let te2 = check_dist tyenv (e2, dty) in
      { ty = te2.ty; exp = Let ("_", te1, te2) }
  | Assign (x, e1, e2) ->
      let (Ex te1) = infer tyenv e1 in
      let tyenv = Map.set tyenv ~key:x ~data:(Ex te1.ty) in
      let te2 = check_dist tyenv (e2, dty) in
      { ty = te2.ty; exp = Let (x, te1, te2) }
  | If _ ->
      raise (Type_error "You cannot return a distribution from a conditional")
  | Call (prim, args) -> (
      let (Ex dist) = Dist.get_dist prim in
      let args = check_args tyenv dist.name (args, dist.params) in
      match (dist.ret, dty) with
      | Tyu, Tyu -> { ty = Dist_ty Tyu; exp = Call (dist, args) }
      | Tyb, Tyb -> { ty = Dist_ty Tyb; exp = Call (dist, args) }
      | Tyi, Tyi -> { ty = Dist_ty Tyi; exp = Call (dist, args) }
      | Tyr, Tyr -> { ty = Dist_ty Tyr; exp = Call (dist, args) }
      | _ ->
          raise
            (Type_error
               (sprintf "Expected %s for Call, got %s" (string_of_dty dist.ret)
                  (string_of_dty dty))))
  | Bool _ | Int _ | Real _ | Add _ | Radd _ | Minus _ | Rminus _ | Mult _
  | Rmult _ | Div _ | Rdiv _ | Eq _ | Req _ | Noteq _ | Less _ | Rless _ | And _
  | Or _ | Neg _ | Rneg _ | Not _ | Sample _ | Observe _ | List _ | Record _ ->
      raise (Type_error "Expected distribution")

and infer (tyenv : tyenv) (exp : Parse_tree.exp) : some_non_det_texp =
  Logs.debug (fun m ->
      m "Infering exp %a" Sexp.pp_hum [%sexp (exp : Parse_tree.exp)]);
  match exp with
  | Var x -> (
      match Map.find tyenv x with
      | None -> raise (Unbound_variable x)
      | Some (Ex t) -> Ex { ty = t; exp = Var x })
  | (Int _ | Add _ | Minus _ | Neg _ | Mult _ | Div _) as e ->
      let (Ex t) = check_dat tyenv (e, Tyi) in
      Ex t
  | (Real _ | Radd _ | Rminus _ | Rneg _ | Rmult _ | Rdiv _) as e ->
      let (Ex t) = check_dat tyenv (e, Tyr) in
      Ex t
  | (Bool _ | Eq _ | Req _ | Noteq _ | Less _ | Rless _ | And _ | Or _ | Not _)
    as e ->
      let (Ex t) = check_dat tyenv (e, Tyb) in
      Ex t
  | Observe _ as e ->
      let (Ex t) = check_dat tyenv (e, Tyu) in
      Ex t
  | Seq (e1, e2) ->
      let (Ex te1) = infer tyenv e1 in
      let (Ex te2) = infer tyenv e2 in
      Ex { ty = te2.ty; exp = Let ("_", te1, te2) }
  | Assign (x, e1, e2) ->
      let (Ex te1) = infer tyenv e1 in
      let tyenv = Map.set tyenv ~key:x ~data:(Ex te1.ty) in
      let (Ex te2) = infer tyenv e2 in
      Ex { ty = te2.ty; exp = Let (x, te1, te2) }
  | If (e_pred, e_con, e_alt) -> (
      let (Ex te_pred) = check_dat tyenv (e_pred, Tyb) in
      let (Ex te_con) = infer tyenv e_con in
      let (Ex te_alt) = infer tyenv e_alt in
      match
        ( some_dat_ndet_texp_of_ndet_texp te_con,
          some_dat_ndet_texp_of_ndet_texp te_alt )
      with
      | Some (Ex te_con), Some (Ex te_alt) -> (
          match eq_dat_ndet_texps te_con te_alt with
          | Some Refl ->
              let (Ex texp) = unify_branches te_pred te_con te_alt Refl in
              Ex texp
          | None -> raise_if_type_error exp te_con.ty te_alt.ty)
      | _, _ -> raise_if_type_error exp te_con.ty te_alt.ty)
  | Call (prim, args) ->
      let (Ex dist) = Dist.get_dist prim in
      let args = check_args tyenv prim (args, dist.params) in
      Ex { ty = Dist_ty dist.ret; exp = Call (dist, args) }
  | Sample e -> (
      let (Ex te) = infer tyenv e in
      match te with
      | { ty = Dist_ty Tyu; _ } -> Ex { ty = Dat_ty (Tyu, Rv); exp = Sample te }
      | { ty = Dist_ty Tyb; _ } -> Ex { ty = Dat_ty (Tyb, Rv); exp = Sample te }
      | { ty = Dist_ty Tyi; _ } -> Ex { ty = Dat_ty (Tyi, Rv); exp = Sample te }
      | { ty = Dist_ty Tyr; _ } -> Ex { ty = Dat_ty (Tyr, Rv); exp = Sample te }
      | _ -> raise (Type_error "Expected distribution"))
  | List _ -> failwith "List not implemented"
  | Record _ -> failwith "Record not implemented"

let check : Parse_tree.exp -> some_non_det_texp = infer Id.Map.empty

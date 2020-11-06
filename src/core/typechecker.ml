open Utils

type state = {
  variables_ty : Ast.ty_scheme Ast.VariableMap.t;
  variables_expr : Ast.expression Ast.VariableMap.t;
  operations : Ast.ty Ast.OperationMap.t;
  type_definitions : (Ast.ty_param list * Ast.ty_def) Ast.TyNameMap.t;
}

let initial_state =
  {
    variables_ty = Ast.VariableMap.empty;
    variables_expr = Ast.VariableMap.empty;
    operations = Ast.OperationMap.empty;
    type_definitions =
      ( Ast.TyNameMap.empty
      |> Ast.TyNameMap.add Ast.bool_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.BooleanTy))
      |> Ast.TyNameMap.add Ast.int_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.IntegerTy))
      |> Ast.TyNameMap.add Ast.unit_ty_name ([], Ast.TyInline (Ast.TyTuple []))
      |> Ast.TyNameMap.add Ast.string_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.StringTy))
      |> Ast.TyNameMap.add Ast.float_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.FloatTy))
      |> Ast.TyNameMap.add Ast.empty_ty_name ([], Ast.TySum [])
      |>
      let a = Ast.TyParam.fresh "list" in
      Ast.TyNameMap.add Ast.list_ty_name
        ( [ a ],
          Ast.TySum
            [
              (Ast.nil_label, None);
              ( Ast.cons_label,
                Some
                  (Ast.TyTuple
                     [
                       Ast.TyParam a;
                       Ast.TyApply (Ast.list_ty_name, [ Ast.TyParam a ]);
                     ]) );
            ] ) );
  }

let fresh_ty () =
  let a = Ast.TyParam.fresh "ty" in
  Ast.TyParam a

let rec unfold_type_definitions state ty =
  match ty with
  | (Ast.TyConst _ | Ast.TyParam _) as ty -> ty
  | Ast.TyApply (ty_name, tys) -> (
      match Ast.TyNameMap.find ty_name state.type_definitions with
      | params, Ast.TyInline ty_def ->
          let subst =
            List.combine params tys |> List.to_seq |> Ast.TyParamMap.of_seq
          in
          unfold_type_definitions state (Ast.substitute_ty subst ty_def)
      | _, Ast.TySum _ ->
          Ast.TyApply (ty_name, List.map (unfold_type_definitions state) tys) )
  | Ast.TyTuple tys ->
      Ast.TyTuple (List.map (unfold_type_definitions state) tys)
  | Ast.TyArrow (ty1, ty2) ->
      Ast.TyArrow
        (unfold_type_definitions state ty1, unfold_type_definitions state ty2)
  | Ast.TyPromise ty -> Ast.TyPromise (unfold_type_definitions state ty)
  | Ast.TyReference ty -> Ast.TyReference (unfold_type_definitions state ty)

let extend_variables state vars =
  List.fold_left
    (fun state (x, ty) ->
      {
        state with
        variables_ty = Ast.VariableMap.add x ([], ty) state.variables_ty;
      })
    state vars

let refreshing_subst params =
  List.fold_left
    (fun subst param ->
      let ty = fresh_ty () in
      Ast.TyParamMap.add param ty subst)
    Ast.TyParamMap.empty params

let infer_variant state lbl =
  let rec find = function
    | [] -> assert false
    | (_, (_, Ast.TyInline _)) :: ty_defs -> find ty_defs
    | (ty_name, (params, Ast.TySum variants)) :: ty_defs -> (
        match List.assoc_opt lbl variants with
        | None -> find ty_defs
        | Some ty -> (ty_name, params, ty) )
  in
  let ty_name, params, ty =
    find (Ast.TyNameMap.bindings state.type_definitions)
  in
  let subst = refreshing_subst params in
  let args = List.map (fun param -> Ast.TyParamMap.find param subst) params
  and ty' = Option.map (Ast.substitute_ty subst) ty in
  (ty', Ast.TyApply (ty_name, args))

let check_subtype1 state ty1 ty2 =
  unfold_type_definitions state ty1 = unfold_type_definitions state ty2

let check_equaltype1 state ty1 ty2 =
  unfold_type_definitions state ty1 = unfold_type_definitions state ty2

let check_subtype state ty1 ty2 =
  if not (check_subtype1 state ty1 ty2) then
    let print_param = Ast.new_print_param () in
    Error.typing "%t does not match %t"
      (Ast.print_ty print_param ty1)
      (Ast.print_ty print_param ty2)

let calculate_super_type _state _ty1 _ty2 =
  failwith "Super_type is not implemented yet."

let rec izracunaj_vzorec state patter_type = function
  | Ast.PVar x -> [ (x, patter_type) ]
  | Ast.PAs (pat, x) ->
      let vars = izracunaj_vzorec state patter_type pat in
      (x, patter_type) :: vars
  | Ast.PAnnotated (pat, ty) ->
      check_subtype state patter_type ty;
      izracunaj_vzorec state patter_type pat
  | Ast.PConst c ->
      let ty = Ast.TyConst (Const.infer_ty c) in
      check_subtype state patter_type ty;
      []
  | Ast.PNonbinding -> []
  | Ast.PTuple pats -> (
      match patter_type with
      | Ast.TyTuple patter_types
        when List.length pats = List.length patter_types ->
          let fold (pat_ty, pat) vars =
            let vars' = izracunaj_vzorec state pat_ty pat in
            vars' @ vars
          in
          List.fold_right fold (List.combine patter_types pats) []
      | _ -> Error.typing "Expected pattern tuple" )
  | Ast.PVariant (lbl, pat) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, pat) with
      | None, None ->
          check_subtype state patter_type ty_out;
          []
      | Some ty_in, Some pat ->
          check_subtype state patter_type ty_out;
          izracunaj_vzorec state ty_in pat
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

(*Če dobimo principal type vrnemo principal types*)
let rec check_pattern state annotation = function
  | Ast.PVar x -> [ (x, annotation) ]
  | Ast.PAs (pat, x) ->
      let vars = check_pattern state annotation pat in
      (x, annotation) :: vars
  | Ast.PAnnotated (pat, ty) ->
      check_subtype state annotation ty;
      check_pattern state annotation pat
  | Ast.PConst c ->
      let ty = Ast.TyConst (Const.infer_ty c) in
      check_subtype state annotation ty;
      []
  | Ast.PNonbinding -> []
  | Ast.PTuple pats -> (
      match annotation with
      | Ast.TyTuple annotations when List.length pats = List.length annotations
        ->
          let fold (anno, pat) vars =
            let vars' = check_pattern state anno pat in
            vars' @ vars
          in
          List.fold_right fold (List.combine annotations pats) []
      | _ -> Error.typing "Expected pattern tuple" )
  | Ast.PVariant (lbl, pat) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, pat) with
      | None, None ->
          check_subtype state annotation ty_out;
          []
      | Some ty_in, Some pat ->
          check_subtype state annotation ty_out;
          check_pattern state ty_in pat
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

let rec izracunaj_izraz state = function
  | Ast.Var x ->
      let params, ty = Ast.VariableMap.find x state.variables_ty in
      let subst = refreshing_subst params in
      Ast.substitute_ty subst ty
  | Ast.Const c -> Ast.TyConst (Const.infer_ty c)
  | Ast.Annotated (e, ty) ->
      izracunaj_izraz_z_anno state ty e (*Premisli če je res z namigom ali *)
  | Ast.Tuple exprs ->
      let fold e tys =
        let ty' = izracunaj_izraz state e in
        ty' :: tys
      in
      let tys = List.fold_right fold exprs [] in
      Ast.TyTuple tys
  | Ast.Lambda _ | Ast.RecLambda _ -> Error.typing "Function must be annotated"
  | Ast.Fulfill e ->
      let ty = izracunaj_izraz state e in
      Ast.TyPromise ty
  | Ast.Reference e ->
      let ty = izracunaj_izraz state !e in
      Ast.TyReference ty
  | Ast.Variant (lbl, e) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, e) with
      | None, None -> ty_out
      | Some ty_in, Some expr ->
          let ty = izracunaj_izraz state expr in
          check_subtype state ty ty_in;
          ty_out
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

and izracunaj_izraz_z_anno state annotation = function
  | Ast.Var x ->
      let params, ty = Ast.VariableMap.find x state.variables_ty in
      let subst = refreshing_subst params in
      let ty' = Ast.substitute_ty subst ty in
      check_subtype state ty' annotation;
      ty'
  | _ -> failwith "Not implemented yet"

and preveri_izraz_anno state annotation = function
  | Ast.Var x ->
      let params, ty = Ast.VariableMap.find x state.variables_ty in
      let subst = refreshing_subst params in
      let ty' = Ast.substitute_ty subst ty in
      check_subtype state ty' annotation
  | _ -> failwith "Not implemented yet"

let rec izracunaj_racun state = function
  | Ast.Return e ->
      let ty = izracunaj_izraz state e in
      ty
  | Ast.Do (comp, abs) ->
      let ty_comp = izracunaj_racun state comp in
      (* tu moramo v state dodati še comp kot anotiran *)
      let ty_abs = preveri_izracunaj_abstraction state ty_comp abs in
      ty_abs
  | Ast.Apply (e1, e2) ->
      let ty_arg = izracunaj_izraz state e2 in
      let ty_app = preveri_izracunaj_arrow state ty_arg e1 in
      ty_app
  | Ast.Out (op, e, comp) | Ast.In (op, e, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations
      and ty_e = izracunaj_izraz state e
      and ty_comp = izracunaj_racun state comp in
      check_subtype state ty_e ty_op;
      ty_comp
  | Ast.Await (e, abs) -> (
      let ty_promise = izracunaj_izraz state e in
      match ty_promise with
      | Ast.TyPromise ty1 ->
          let ty_comp = preveri_izracunaj_abstraction state ty1 abs in
          ty_comp
      | _ -> Error.typing "Expected Await." )
  | Ast.Match (_, []) ->
      Error.typing "Cannot infer the type of a match with no cases"
  | Ast.Match (e, case :: cases) ->
      (* TODO prva izbira ni nujno prava če imamo podtipe, je pa v smiselnem primeru gotovo njen nadtip.*)
      let ty_e = izracunaj_izraz state e in
      let ty1 = preveri_izracunaj_abstraction state ty_e case in
      let infer_super_type candidate case' =
        let ty_current = preveri_izracunaj_abstraction state ty_e case' in
        if check_subtype1 state ty_current candidate then candidate
        else calculate_super_type state ty_current candidate
      in
      let ty_super = List.fold_left infer_super_type ty1 cases in
      ty_super
  | Ast.Handler (op, abs, p, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations in
      let ty_abs = preveri_izracunaj_abstraction state ty_op abs in
      let state' = extend_variables state [ (p, ty_abs) ] in
      let ty_comp = izracunaj_racun state' comp in
      ty_comp

and preveri_izracunaj_arrow state ty_arg = function
  | Ast.Annotated (e, anno) -> (
      match e with
      | Ast.Var x -> (
          match Ast.VariableMap.find_opt x state.variables_expr with
          | Some expr ->
              preveri_izracunaj_arrow state ty_arg (Ast.Annotated (expr, anno))
          | None -> Error.typing "Unknown variable" )
      | Ast.Lambda abs -> preveri_izracunaj_abstraction state ty_arg abs
      | Ast.RecLambda (_f, _abs) -> failwith "not implemented yet"
      | Ast.Annotated _ as annotated ->
          preveri_izracunaj_arrow state ty_arg annotated
      | _ -> Error.typing "Expected arrow type." )
  | Ast.Var x -> (
      match Ast.VariableMap.find_opt x state.variables_expr with
      | Some e -> preveri_izracunaj_arrow state ty_arg e
      | None -> (
          (* This is here because i dont know how to save expresions of build in functions into state. Its ugly and should be fixed*)
          match Ast.VariableMap.find_opt x state.variables_ty with
          | Some ([], Ast.TyArrow (ty_in, ty_out))
            when check_equaltype1 state ty_arg ty_in ->
              ty_out
          | Some ([], wrong_ty) ->
              let print_param = Ast.new_print_param () in
              Error.typing
                "Cannot apply %t of type %t to an argument of type %t"
                (Ast.print_expression (Ast.Var x))
                (Ast.print_ty print_param wrong_ty)
                (Ast.print_ty print_param ty_arg)
          | Some (_params, wrong_ty) ->
              let print_param = Ast.new_print_param () in
              Error.typing
                "Cannot apply %t of type %t to an argument of type %t, because \
                 it is polymorphic with params but we dont have the body to \
                 instantiate."
                (Ast.print_expression (Ast.Var x))
                (Ast.print_ty print_param wrong_ty)
                (Ast.print_ty print_param ty_arg)
          | None -> Error.typing "Unknown variable" ) )
  | Ast.Lambda _ | Ast.RecLambda _ -> Error.typing "Function must be annotated"
  | _ -> Error.typing "Expected arrow type."

and preveri_izracunaj_abstraction state ty_argument (pat, comp) =
  let vars = check_pattern state ty_argument pat in
  let state' = extend_variables state vars in
  let ty_comp = izracunaj_racun state' comp in
  ty_comp

(* state * expresion -> type  ?    *)
let rec infer_expression state = function
  | Ast.Var x ->
      let params, ty = Ast.VariableMap.find x state.variables_ty in
      let subst = refreshing_subst params in
      (Ast.Var x, Ast.substitute_ty subst ty)
  | Ast.Const c -> (Ast.Const c, Ast.TyConst (Const.infer_ty c))
  | Ast.Annotated (e, ty) ->
      let expr = check_expression state ty e in
      (Ast.Annotated (expr, ty), ty)
  | Ast.Tuple exprs ->
      let fold e (exprs, tys) =
        let expr, ty' = infer_expression state e in
        (expr :: exprs, ty' :: tys)
      in
      let exprs, tys = List.fold_right fold exprs ([], []) in
      (Ast.Tuple exprs, Ast.TyTuple tys)
  | Ast.Lambda _ | Ast.RecLambda _ -> Error.typing "Function must be annotated"
  | Ast.Fulfill e ->
      let expr, ty = infer_expression state e in
      (Ast.Fulfill expr, Ast.TyPromise ty)
  | Ast.Reference expr_ref ->
      let expr, ty = infer_expression state !expr_ref in
      (Ast.Reference (ref expr), Ast.TyReference ty)
  | Ast.Variant (lbl, e) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, e) with
      | None, None -> (Ast.Variant (lbl, e), ty_out)
      | Some ty_in, Some ex ->
          let expr, ty = infer_expression state ex in
          check_subtype state ty ty_in;
          (Ast.Variant (lbl, Some expr), ty_out)
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

(* state * annotation * expresion -> unit *)
and check_expression state annotation = function
  | Ast.Tuple exprs -> (
      match annotation with
      | Ast.TyTuple annotations when List.length exprs = List.length annotations
        ->
          let fold (ty, e) exprs =
            let ex = check_expression state ty e in
            ex :: exprs
          in
          let expr = List.fold_right fold (List.combine annotations exprs) [] in
          Ast.Tuple expr
      | _ -> Error.typing "Expected tuple." )
  | Ast.Lambda abs -> (
      match annotation with
      | Ast.TyArrow (pat_anno, com_anno) ->
          let expr = check_check_abstraction state (pat_anno, com_anno) abs in
          Ast.Lambda expr
      | _ -> Error.typing "Expected Lambda." )
  | Ast.RecLambda (f, abs) -> (
      match annotation with
      | Ast.TyArrow (pat_anno, com_anno) ->
          let state' = extend_variables state [ (f, annotation) ] in
          let expr = check_check_abstraction state' (pat_anno, com_anno) abs in
          Ast.RecLambda (f, expr)
      | _ -> Error.typing "Expected Rec Lambda." )
  | Ast.Fulfill e -> (
      match annotation with
      | Ast.TyPromise anno -> Ast.Fulfill (check_expression state anno e)
      | _ -> Error.typing "Expected Promise." )
  | Ast.Reference expr_ref -> (
      match annotation with
      | Ast.TyReference anno ->
          Ast.Reference (ref (check_expression state anno !expr_ref))
      | _ -> Error.typing "Expected Reference" )
  | Ast.Variant (lbl, expr) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, expr) with
      | None, None ->
          check_subtype state ty_out annotation;
          (* nebi mogl bit to obrnjeno? preveri vse subtype*)
          Ast.Variant (lbl, expr)
      | Some ty_in, Some expr ->
          check_subtype state ty_out annotation;
          check_expression state ty_in expr
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )
  | (Ast.Var _ | Ast.Const _ | Ast.Annotated _) as e ->
      let expr, ty = infer_expression state e in
      check_subtype state ty annotation;
      expr

(* state * computation -> type  ?    *)
and infer_computation state = function
  | Ast.Return e ->
      let expr, ty = infer_expression state e in
      (Ast.Return expr, ty)
  | Ast.Do (comp1, comp2) ->
      let expr1, ty1 = infer_computation state comp1 in

      let expr2, ty2 = check_infer_abstraction state ty1 comp2 in
      (* Povej comp2 da uporabi expr1 ne pa comp1 *)
      (Ast.Do (expr1, expr2), ty2)
  | Ast.Apply (e1, e2) ->
      let expr_argument, ty_argument = infer_expression state e2 in
      let expr_fun, ty = check_infer_expr_of_ty_arrow state ty_argument e1 in
      (Ast.Apply (expr_fun, expr_argument), ty)
  | Ast.Out (op, expr, comp) | Ast.In (op, expr, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations
      and expr_expr, ty_expr = infer_expression state expr
      and expr_comp, ty_comp = infer_computation state comp in
      check_subtype state ty_expr ty_op;
      (Ast.Out (op, expr_expr, expr_comp), ty_comp)
  | Ast.Await (e, abs) ->
      let expr_prom, pty1 = infer_expression state e in
      let expr_abs, ty =
        match pty1 with
        | Ast.TyPromise ty1 -> check_infer_abstraction state ty1 abs
        | _ -> Error.typing "Expected Await."
      in
      (Ast.Await (expr_prom, expr_abs), ty)
  | Ast.Match (_, []) ->
      Error.typing "Cannot infer the type of a match with no cases"
  | Ast.Match (e, case :: cases) ->
      (* TODO prva izbira ni nujno prava če imamo podtipe, je pa v smiselnem primeru gotovo njen nadtip.*)
      let expr_e, ty1 = infer_expression state e in
      let _, ty2 = check_infer_abstraction state ty1 case in
      let check_case (expr, ty') case' =
        let expr_case, ty2' = check_infer_abstraction state ty1 case' in
        if check_subtype1 state ty2' ty' then (expr_case :: expr, ty')
        else if check_subtype1 state ty' ty2' then (expr_case :: expr, ty2')
        else Error.typing "Types do not match."
      in
      let expr_cases, super_ty = List.fold_left check_case ([], ty2) cases in
      (Ast.Match (expr_e, expr_cases), super_ty)
  | Ast.Handler (op, abs, p, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations in
      let expr_abs, ty_abs = check_infer_abstraction state ty_op abs in
      let state' = extend_variables state [ (p, ty_abs) ] in
      let expr_comp, ty = infer_computation state' comp in
      (Ast.Handler (op, expr_abs, p, expr_comp), ty)

(** TODO je treba pri vsem tem pošiljanju expr kot popravit tudi state??? premisli!!! *)

and check_infer_expr_of_ty_arrow state ty_argument = function
  | Ast.Annotated (e, ty) -> (
      match ty with
      | Ast.TyArrow (ty_in, ty_out) ->
          check_subtype state ty_argument ty_in;
          let expr =
            check_check_expr_of_ty_arrow state (ty_argument, ty_out) e
          in
          (Ast.Annotated (expr, ty), ty)
      | _ -> failwith "Canot apply something that is not of type arrow." )
  | Ast.Lambda abs ->
      let expr, ty = check_infer_abstraction state ty_argument abs in
      (Ast.Lambda expr, ty)
  | Ast.RecLambda (_f, _abs) -> failwith "not implemented"
  | Ast.Var x -> (
      match Ast.VariableMap.find_opt x state.variables_expr with
      | Some expr -> check_infer_expr_of_ty_arrow state ty_argument expr
      | None -> (
          (*Build in functions can not be polymorphic yet. preveri če prejš stavek drži. ali se res dodaja samo v toplet.*)
          match Ast.VariableMap.find_opt x state.variables_ty with
          | Some ([], Ast.TyArrow (ty_in, ty_out))
            when check_equaltype1 state ty_in ty_argument ->
              (Ast.Var x, ty_out)
          | Some ([], wrong_ty) ->
              let print_param = Ast.new_print_param () in
              Error.typing
                "Cannot apply %t of type %t to an argument of type %t"
                (Ast.print_expression (Ast.Var x))
                (Ast.print_ty print_param wrong_ty)
                (Ast.print_ty print_param ty_argument)
          | Some (_params, wrong_ty) ->
              let print_param = Ast.new_print_param () in
              Error.typing
                "Cannot apply %t of type %t to an argument of type %t, because \
                 it is polymorphic with params but we dont have the body to \
                 instantiate."
                (Ast.print_expression (Ast.Var x))
                (Ast.print_ty print_param wrong_ty)
                (Ast.print_ty print_param ty_argument)
          | None -> Error.typing "Unknown variable" ) )
  | e ->
      let print_param = Ast.new_print_param () in
      let _, ty = infer_expression state e in
      Error.typing
        "Cannot apply %t of type %t (this one should be of type Ast.TyArrow) \
         to an argument of type %t"
        (Ast.print_expression e)
        (Ast.print_ty print_param ty)
        (Ast.print_ty print_param ty_argument)

and check_computation state annotation = function
  | Ast.Return expr -> Ast.Return (check_expression state annotation expr)
  | Ast.Do (comp1, comp2) ->
      let expr1, ty1 = infer_computation state comp1 in
      let expr2 = check_check_abstraction state (ty1, annotation) comp2 in
      Ast.Do (expr1, expr2)
  | Ast.Apply (e1, e2) ->
      let expr_argument, ty_argument = infer_expression state e2 in
      let expr_fun =
        check_check_expr_of_ty_arrow state (ty_argument, annotation) e1
      in
      Ast.Apply (expr_fun, expr_argument)
  | Ast.Out (op, e, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations in
      let expr1 = check_expression state ty1 e in
      let expr2 = check_computation state annotation comp in
      Ast.Out (op, expr1, expr2)
  | Ast.In (op, e, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations in
      let expr1 = check_expression state ty1 e in
      let expr2 = check_computation state annotation comp in
      Ast.In (op, expr1, expr2)
  | Ast.Await (e, abs) -> (
      let expr_prom, pty1 = infer_expression state e in
      match pty1 with
      | Ast.TyPromise ty1 ->
          Ast.Await
            (expr_prom, check_check_abstraction state (ty1, annotation) abs)
      | _ -> Error.typing "Expected Promise" )
  | Ast.Match (e, cases) ->
      let expr, ty1 = infer_expression state e in
      let exprs =
        List.map (check_check_abstraction state (ty1, annotation)) cases
      in
      Ast.Match (expr, exprs)
  | Ast.Handler (op, abs, p, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations in
      let expr1, ty2 = check_infer_abstraction state ty1 abs in
      let state' = extend_variables state [ (p, ty2) ] in
      let expr2 = check_computation state' annotation comp in
      Ast.Handler (op, expr1, p, expr2)

and check_check_expr_of_ty_arrow state (ty_in, ty_out) = function
  | Ast.Annotated (e, ty) ->
      let expr = check_check_expr_of_ty_arrow state (ty_in, ty_out) e in
      Ast.Annotated (expr, ty)
  | Ast.Lambda abs ->
      let expr = check_check_abstraction state (ty_in, ty_out) abs in
      Ast.Lambda expr
  | Ast.RecLambda (_f, _abs) -> failwith "not implemented"
  | Ast.Var x -> (
      match Ast.VariableMap.find_opt x state.variables_expr with
      | Some expr -> check_check_expr_of_ty_arrow state (ty_in, ty_out) expr
      | None -> (
          (*Build in functions can not be polymorphic yet. preveri če prejš stavek drži. ali se res dodaja samo v toplet.*)
          match Ast.VariableMap.find_opt x state.variables_ty with
          | Some ([], Ast.TyArrow (ty_in', ty_out'))
            when check_equaltype1 state ty_in ty_in'
                 && check_equaltype1 state ty_out ty_out' ->
              Ast.Var x
          | Some ([], wrong_ty) ->
              let print_param = Ast.new_print_param () in
              Error.typing
                "Got %t of type %t but we expected something of type %t->%t"
                (Ast.print_expression (Ast.Var x))
                (Ast.print_ty print_param wrong_ty)
                (Ast.print_ty print_param ty_in)
                (Ast.print_ty print_param ty_out)
          | Some (_params, wrong_ty) ->
              let print_param = Ast.new_print_param () in
              Error.typing
                "Got polymorphic %t of type %t. We dont have the body to \
                 instantiate. Probably problem with build in functions"
                (Ast.print_expression (Ast.Var x))
                (Ast.print_ty print_param wrong_ty)
          | None -> Error.typing "Unknown variable" ) )
  | e ->
      let print_param = Ast.new_print_param () in
      let _, ty = infer_expression state e in
      Error.typing "Got %t of type %t but we expected something of type %t->%t"
        (Ast.print_expression e)
        (Ast.print_ty print_param ty)
        (Ast.print_ty print_param ty_in)
        (Ast.print_ty print_param ty_out)

(**state type abs -> () *)
and check_check_abstraction state (pat_ty, comp_ty) (pat, comp) =
  let vars = check_pattern state pat_ty pat in
  let state' = extend_variables state vars in
  let expr = check_computation state' comp_ty comp in
  (pat, expr)
  (*če damo principa ty_in dobimo principal ty_out. (za int:number bomo seveda dobili number in ne int kar pa je vredu)*)

(**state pat_ty abs -> com_ty *)
and check_infer_abstraction state pat_ty (pat, comp) =
  let vars = check_pattern state pat_ty pat in
  let state' = extend_variables state vars in
  let expr, ty = infer_computation state' comp in
  ((pat, expr), ty)

let is_transparent_type state ty_name =
  match Ast.TyNameMap.find ty_name state.type_definitions with
  | _, Ast.TySum _ -> false
  | _, Ast.TyInline _ -> true

let unfold state ty_name args =
  match Ast.TyNameMap.find ty_name state.type_definitions with
  | _, Ast.TySum _ -> assert false
  | params, Ast.TyInline ty ->
      let subst =
        List.combine params args |> List.to_seq |> Ast.TyParamMap.of_seq
      in
      Ast.substitute_ty subst ty

let check_polymorphic_expression state (_params, ty) expr =
  (* THIS IS WRONG *)
  (* Zakaj? Ko poly funkcijo dodamo je vredu.
     Edini problem (ki ga jaz vidim) lahko nastane v apply. Recimo, ko uporabimo id a->a na 5 in dobimo, da ima id 5 = 5 tip a kar pa ni res.
     Kar je pa (mislim da)enostavno popraviti v apply. *)
  let _expr = check_expression state ty expr in
  ()

let add_external_function x ty_sch state =
  Format.printf "@[val %t : %t@]@." (Ast.Variable.print x)
    (Ast.print_ty_scheme ty_sch);
  { state with variables_ty = Ast.VariableMap.add x ty_sch state.variables_ty }

let add_operation state op ty =
  Format.printf "@[operation %t : %t@]@." (Ast.Operation.print op)
    (Ast.print_ty_scheme ([], ty));
  { state with operations = Ast.OperationMap.add op ty state.operations }

let add_top_definition state x ty_sch expr =
  check_polymorphic_expression state ty_sch expr;
  let state' = add_external_function x ty_sch state in
  {
    state' with
    variables_expr = Ast.VariableMap.add x expr state.variables_expr;
  }

let add_type_definitions state ty_defs =
  List.fold_left
    (fun state (params, ty_name, ty_def) ->
      Format.printf "@[type %t@]@." (Ast.TyName.print ty_name);
      {
        state with
        type_definitions =
          Ast.TyNameMap.add ty_name (params, ty_def) state.type_definitions;
      })
    state ty_defs

let check_payload state op expr =
  let ty1 = Ast.OperationMap.find op state.operations in
  check_expression state ty1 expr

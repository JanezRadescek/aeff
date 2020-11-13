open Utils

type state = {
  variables_ty : Ast.ty_scheme Ast.VariableMap.t;
  operations : Ast.ty Ast.OperationMap.t;
  type_definitions : (Ast.ty_param list * Ast.ty_def) Ast.TyNameMap.t;
}

let initial_state =
  {
    variables_ty = Ast.VariableMap.empty;
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

let rec free_params_in_ty ty =
  let fold sez ty = free_params_in_ty ty @ sez in
  let rec remove_dup = function
    | [] -> []
    | x :: xs ->
        let xs' = remove_dup xs in
        if List.mem x xs' then xs else x :: xs'
  in
  let result =
    match ty with
    | Ast.TyApply (_y_name, tys) ->
        let free_params = List.fold_left fold [] tys in
        free_params
    | Ast.TyParam ty_param -> [ ty_param ]
    | Ast.TyArrow (ty1, ty2) ->
        let free_params1 = free_params_in_ty ty1 in
        let free_params2 = free_params_in_ty ty2 in
        free_params1 @ free_params2
    | Ast.TyTuple tys ->
        let free_params = List.fold_left fold [] tys in
        free_params
    | Ast.TyConst _c -> []
    | Ast.TyReference ty | Ast.TyPromise ty -> free_params_in_ty ty
  in
  remove_dup result

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

(**replace all ty_old with ty_new in ty_poly*)
let rec instantian_poly state ty_new ty_old ty_poly =
  let ty_new' = unfold_type_definitions state ty_new
  and ty_old' = unfold_type_definitions state ty_old
  and ty_poly' = unfold_type_definitions state ty_poly in
  match ty_poly' with
  | Ast.TyConst _ as tyc -> tyc
  | Ast.TyParam _ as typ ->
      if unfold_type_definitions state typ = ty_old' then ty_new' else ty_old'
  | Ast.TyApply (name, tys) ->
      Ast.TyApply (name, List.map (instantian_poly state ty_new ty_old) tys)
  | Ast.TyTuple tys ->
      Ast.TyTuple (List.map (instantian_poly state ty_new ty_old) tys)
  | Ast.TyArrow (ty_in, ty_out) ->
      Ast.TyArrow
        ( instantian_poly state ty_new ty_old ty_in,
          instantian_poly state ty_new ty_old ty_out )
  | Ast.TyPromise ty -> Ast.TyPromise (instantian_poly state ty_new ty_old ty)
  | Ast.TyReference ty ->
      Ast.TyReference (instantian_poly state ty_new ty_old ty)

let rec check_subtype1 state ty1 ty2 =
  let ty11 = unfold_type_definitions state ty1
  and ty22 = unfold_type_definitions state ty2 in
  match (ty11, ty22) with
  | Ast.TyConst c1, Ast.TyConst c2 -> c1 == c2
  | Ast.TyApply (name1, tys1), Ast.TyApply (name2, tys2)
    when name1 = name2 && List.length tys1 = List.length tys2 ->
      let fold' result ty1' ty2' = result && check_subtype1 state ty1' ty2' in
      List.fold_left2 fold' true tys1 tys2
  | _, Ast.TyParam _ -> true
  | Ast.TyArrow (in1, out1), Ast.TyArrow (in2, out2) ->
      check_subtype1 state in1 in2 && check_subtype1 state out1 out2
  | Ast.TyTuple tys1, Ast.TyTuple tys2 when List.length tys1 = List.length tys2
    ->
      let fold' result ty1' ty2' = result && check_subtype1 state ty1' ty2' in
      List.fold_left2 fold' true tys1 tys2
  | Ast.TyPromise t1, Ast.TyPromise t2 | Ast.TyReference t1, Ast.TyReference t2
    ->
      check_subtype1 state t1 t2
  | _ -> false

let rec check_subtype2 state ty1 ty2 =
  let ty11 = unfold_type_definitions state ty1
  and ty22 = unfold_type_definitions state ty2 in
  let fold' result ty1' ty2' =
    match (check_subtype2 state ty1' ty2', result) with
    | Some r, Some rs -> Some (r @ rs)
    | _ -> None
  in
  match (ty11, ty22) with
  | Ast.TyConst c1, Ast.TyConst c2 when c1 = c2 -> Some []
  | Ast.TyApply (name1, tys1), Ast.TyApply (name2, tys2)
    when name1 = name2 && List.length tys1 = List.length tys2 ->
      List.fold_left2 fold' (Some []) tys1 tys2
  | Ast.TyParam _, Ast.TyParam _ -> Some []
  | ty, (Ast.TyParam _ as p) -> Some [ (ty, p) ]
  | Ast.TyArrow (in1, out1), Ast.TyArrow (in2, out2) -> (
      match (check_subtype2 state in1 in2, check_subtype2 state out1 out2) with
      | Some r1, Some r2 -> Some (r1 @ r2)
      | _ -> None )
  | Ast.TyTuple tys1, Ast.TyTuple tys2 when List.length tys1 = List.length tys2
    ->
      List.fold_left2 fold' (Some []) tys1 tys2
  | Ast.TyPromise t1, Ast.TyPromise t2 | Ast.TyReference t1, Ast.TyReference t2
    ->
      check_subtype2 state t1 t2
  | _ -> None

let check_equaltype1 state ty1 ty2 =
  unfold_type_definitions state ty1 = unfold_type_definitions state ty2

let check_subtype state ty1 ty2 =
  if not (check_subtype1 state ty1 ty2) then
    let print_param = Ast.new_print_param () in
    Error.typing "%t does not match %t"
      (Ast.print_ty print_param ty1)
      (Ast.print_ty print_param ty2)

(**takes types ty1 and ty2 and returns the smallest ty3 such that subtype1 state ty1 ty3 && subtype1 state ty2 ty3 == true*)
let calculate_super_type state ty1 ty2 =
  if check_equaltype1 state ty1 ty2 then ty1
  else
    failwith
      "Super_type is not implemented yet, because we dont have subtypes yet."

let rec check_pattern state patter_type = function
  | Ast.PVar x -> [ (x, patter_type) ]
  | Ast.PAs (pat, x) ->
      let vars = check_pattern state patter_type pat in
      (x, patter_type) :: vars
  | Ast.PAnnotated (pat, ty) ->
      check_subtype state patter_type ty;
      check_pattern state patter_type pat
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
            let vars' = check_pattern state pat_ty pat in
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
          check_pattern state ty_in pat
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

let rec infer_expression state = function
  | Ast.Var x ->
      let params, ty = Ast.VariableMap.find x state.variables_ty in
      let subst = refreshing_subst params in
      Ast.substitute_ty subst ty
  | Ast.Const c -> Ast.TyConst (Const.infer_ty c)
  | Ast.Annotated (e, ty) ->
      let _ = check_expression state ty e in
      ty
  | Ast.Tuple exprs ->
      let fold e tys =
        let ty' = infer_expression state e in
        ty' :: tys
      in
      let tys = List.fold_right fold exprs [] in
      Ast.TyTuple tys
  | Ast.Lambda _ | Ast.RecLambda _ ->
      Error.typing "Infer_expression : Function must be annotated"
  | Ast.Fulfill e ->
      let ty = infer_expression state e in
      Ast.TyPromise ty
  | Ast.Reference e ->
      let ty = infer_expression state !e in
      Ast.TyReference ty
  | Ast.Variant (lbl, e) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, e) with
      | None, None -> ty_out
      | Some ty_in', Some expr ->
          let ty_e = infer_expression state expr in
          check_subtype state ty_e ty_in';
          let fold' ty_out' (ty_new, ty_old) =
            instantian_poly state ty_new ty_old ty_out'
          in
          let ty_out'' =
            match check_subtype2 state ty_e ty_in' with
            | Some sez -> List.fold_left fold' ty_out sez
            | None ->
                let print_param = Ast.new_print_param () in
                Error.typing "%t does not match %t"
                  (Ast.print_ty print_param ty_e)
                  (Ast.print_ty print_param ty_in')
          in
          ty_out''
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

and check_expression state annotation = function
  | Ast.Tuple exprs -> (
      match annotation with
      | Ast.TyTuple annos ->
          Ast.TyTuple (List.map2 (check_expression state) annos exprs)
      | _ -> Error.typing "Wrong annotation." )
  | Ast.Lambda abs -> (
      match annotation with
      | Ast.TyArrow (ty_in, ty_out) ->
          Ast.TyArrow (ty_in, check_check_abstraction state (ty_in, ty_out) abs)
      | _ -> Error.typing "Wrong annotation." )
  | Ast.RecLambda (f, abs) -> (
      match annotation with
      | Ast.TyArrow (ty_in, ty_out) ->
          let state' = extend_variables state [ (f, annotation) ] in
          Ast.TyArrow (ty_in, check_check_abstraction state' (ty_in, ty_out) abs)
      | _ -> Error.typing "Wrong annotation." )
  | Ast.Fulfill e -> (
      match annotation with
      | Ast.TyPromise anno -> check_expression state anno e
      | _ -> Error.typing "Wrong annotation." )
  | Ast.Reference e -> (
      match annotation with
      | Ast.TyReference anno -> check_expression state anno !e
      | _ -> Error.typing "Expected Reference" )
  | Ast.Variant (lbl, e) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, e) with
      | None, None ->
          check_subtype state ty_out annotation;
          ty_out
      | Some ty_in', Some expr ->
          let ty_e = check_expression state ty_in' expr in
          let fold' ty_out' (ty_n, ty_o) =
            instantian_poly state ty_n ty_o ty_out'
          in
          let ty_out'' =
            match check_subtype2 state ty_e ty_in' with
            | Some sez -> List.fold_left fold' ty_out sez
            | None -> ty_out
          in
          check_subtype state ty_out'' annotation;
          ty_out''
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )
  | (Ast.Var _ | Ast.Const _ | Ast.Annotated _) as e ->
      let ty = infer_expression state e in
      check_subtype state ty annotation;
      ty

and infer_computation state = function
  | Ast.Return e ->
      let ty = infer_expression state e in
      ty
  | Ast.Do (comp, abs) ->
      let ty_comp = infer_computation state comp in
      (* tu moramo v state dodati še comp kot anotiran *)
      let ty_abs = check_infer_abstraction state ty_comp abs in
      ty_abs
  | Ast.Apply (e1, e2) ->
      let ty_arg = infer_expression state e2 in
      let ty_app = check_infer_arrow state ty_arg e1 in
      ty_app
  | Ast.Out (op, e, comp) | Ast.In (op, e, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations in
      let _ = check_expression state ty_op e
      and ty_comp = infer_computation state comp in
      ty_comp
  | Ast.Await (e, abs) -> (
      let ty_promise = infer_expression state e in
      match ty_promise with
      | Ast.TyPromise ty1 ->
          let ty_comp = check_infer_abstraction state ty1 abs in
          ty_comp
      | _ -> Error.typing "Expected Await." )
  | Ast.Match (_, []) ->
      Error.typing "Cannot infer the type of a match with no cases"
  | Ast.Match (e, case :: cases) ->
      (* TODO prva izbira ni nujno prava če imamo podtipe, je pa v smiselnem primeru gotovo njen nadtip.*)
      let ty_e = infer_expression state e in
      let ty1 = check_infer_abstraction state ty_e case in
      let infer_super_type candidate case' =
        let ty_current = check_infer_abstraction state ty_e case' in
        if check_subtype1 state ty_current candidate then candidate
        else calculate_super_type state ty_current candidate
      in
      let ty_super = List.fold_left infer_super_type ty1 cases in
      ty_super
  | Ast.Handler (op, abs, p, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations in
      let ty_abs = check_infer_abstraction state ty_op abs in
      let state' = extend_variables state [ (p, ty_abs) ] in
      let ty_comp = infer_computation state' comp in
      ty_comp

and check_computation state annotation = function
  | Ast.Return expr -> check_expression state annotation expr
  | Ast.Do (comp1, comp2) ->
      let ty1 = infer_computation state comp1 in
      check_check_abstraction state (ty1, annotation) comp2
  | Ast.Apply (e1, e2) ->
      let ty_argument = infer_expression state e2 in
      let ty = check_check_arrow state (ty_argument, annotation) e1 in
      check_subtype state ty annotation;
      ty
  | Ast.Out (op, e, comp) | Ast.In (op, e, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations in
      let _ = check_expression state ty1 e in
      check_computation state annotation comp
  | Ast.Await (e, abs) -> (
      let ty_promise = infer_expression state e in
      match ty_promise with
      | Ast.TyPromise ty -> check_check_abstraction state (ty, annotation) abs
      | _ -> Error.typing "Expected Promise" )
  | Ast.Match (_e, []) -> Error.typing "Canot check match without cases."
  | Ast.Match (e, case :: cases) ->
      let ty_e = infer_expression state e in
      let ty1 = check_check_abstraction state (ty_e, annotation) case in
      let fold' ty' case' =
        let ty_current =
          check_check_abstraction state (ty_e, annotation) case'
        in
        calculate_super_type state ty' ty_current
      in
      List.fold_left fold' ty1 cases
  | Ast.Handler (op, abs, p, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations in
      let ty2 = check_infer_abstraction state ty1 abs in
      let state' = extend_variables state [ (p, ty2) ] in
      check_computation state' annotation comp

and check_infer_arrow state ty_arg = function
  | Ast.Annotated (e, anno) -> (
      match anno with
      | Ast.TyArrow (ty_in, ty_out) ->
          check_subtype state ty_arg ty_in;
          check_check_arrow state (ty_arg, ty_out) e
      | _ -> Error.typing "Expected arrow type." )
  | Ast.Var x -> greedy_inst_var state ty_arg x
  | (Ast.Lambda _ | Ast.RecLambda _) as e ->
      Error.typing "Arrow : Function %t must be annotated"
        (Ast.print_expression e)
  | _ -> Error.typing "Expected arrow type."

and check_check_arrow state (ty_in, ty_out) = function
  | Ast.Annotated (e, anno) -> (
      match anno with
      | Ast.TyArrow (ty_in', ty_out') ->
          check_subtype state ty_in ty_in';
          check_subtype state ty_out' ty_out;
          check_check_arrow state (ty_in, ty_out) e
      | _ -> Error.typing "Expected arrow type." )
  | Ast.Var x ->
      let ty = greedy_inst_var state ty_in x in
      check_subtype state ty ty_out;
      ty
  | Ast.Lambda abs -> (
      (* We only allow poly function in toplet*)
      let params = free_params_in_ty ty_out in
      match params with
      | [] -> check_check_abstraction state (ty_in, ty_out) abs
      | _ :: _ -> Error.typing "Poly functions must be defined in top let." )
  | Ast.RecLambda (f, abs) -> (
      (* We only allow poly function in toplet*)
      let params = free_params_in_ty ty_out in
      match params with
      | [] ->
          let state' = extend_variables state [ (f, ty_out) ] in
          check_check_abstraction state' (ty_in, ty_out) abs
      | _ :: _ -> Error.typing "Poly rec functions must be defined in top let."
      )
  | _ -> Error.typing "Expected arrow type."

and greedy_inst_var state ty_arg x =
  match Ast.VariableMap.find_opt x state.variables_ty with
  | Some (_, Ast.TyArrow (ty_in, ty_out))
    when check_equaltype1 state ty_arg ty_in ->
      ty_out
  | Some (_, Ast.TyArrow (ty_in, ty_out)) when check_subtype1 state ty_arg ty_in
    ->
      instantian_poly state ty_arg ty_in ty_out
  | Some (_, wrong_ty) ->
      let print_param = Ast.new_print_param () in
      Error.typing "Cannot apply %t of type %t to an argument of type %t"
        (Ast.print_expression (Ast.Var x))
        (Ast.print_ty print_param wrong_ty)
        (Ast.print_ty print_param ty_arg)
  | None -> Error.typing "Unknown variable"

and check_infer_abstraction state ty_argument (pat, comp) =
  let vars = check_pattern state ty_argument pat in
  let state' = extend_variables state vars in
  let ty_comp = infer_computation state' comp in
  ty_comp

and check_check_abstraction state (ty_argument, ty_comp) (pat, comp) =
  let vars = check_pattern state ty_argument pat in
  let state' = extend_variables state vars in
  check_computation state' ty_comp comp

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
  let _ = check_expression state ty expr in
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
  state'

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

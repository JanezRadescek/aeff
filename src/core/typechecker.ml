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

(*let rec check_subtype2 state ty1 ty2 =
  let ty11 = unfold_type_definitions state ty1
  and ty22 = unfold_type_definitions state ty2 in
  match ty22 with
  | Ast.TyConst c2 -> (
      match ty11 with Ast.TyConst c1 -> (c1 = c2, []) | _ -> (false, []) )
  | Ast.TyApply (name2, tys2) -> (
      match ty11 with
      | Ast.TyApply (name1, tys1)
        when name1 = name2 && List.length tys1 = List.length tys2 ->
          let fold' (resultBool, resultArray) ty1' ty2' =
            let resultBool1, resultArray1 = check_subtype2 state ty1' ty2' in
            (resultBool && resultBool1, resultArray1 @ resultArray)
          in
          List.fold_left2 fold' (true, []) tys1 tys2
      | _ -> (false, []) )
  | Ast.TyTuple tys2 -> (
      match ty11 with
      | Ast.TyTuple tys1 when List.length tys1 = List.length tys2 ->
          let fold' (resultBool, resultArray) ty1' ty2' =
            let resultBool1, resultArray1 = check_subtype2 state ty1' ty2' in
            (resultBool && resultBool1, resultArray1 @ resultArray)
          in
          List.fold_left2 fold' (true, []) tys1 tys2
      | _ -> (false, []) )
  | Ast.TyParam _ -> (true, [ (ty22, ty11) ])
  | Ast.TyArrow (in2, out2) -> (
      match ty11 with
      | Ast.TyArrow (in1, out1) ->
          let resultBool1, resultArray1 = check_subtype2 state in1 in2 in
          let resultBool2, resultArray2 = check_subtype2 state out1 out2 in
          (resultBool1 && resultBool2, resultArray1 @ resultArray2)
      | _ -> (false, []) )
  | Ast.TyPromise t2 -> (
      match ty11 with
      | Ast.TyPromise t1 -> check_subtype2 state t1 t2
      | _ -> (false, []) )
  | Ast.TyReference t2 -> (
      match ty11 with
      | Ast.TyReference t1 -> check_subtype2 state t1 t2
      | _ -> (false, []) )

and check_subtype3 state ty1 ty2 =
  match check_subtype2 state ty1 ty2 with
  | false, _ -> false
  | true, eqs -> solve state eqs

and solve state = function
  | [] -> true
  | (ty1, ty2) :: eqs -> (
      match List.assoc_opt ty1 eqs with
      | Some ty2' -> (
          match (ty2, ty2') with
          | Ast.TyParam p1, Ast.TyParam p2 when p1 = p2 -> solve state eqs
          | Ast.TyParam _, _ | _, Ast.TyParam _ -> false
          | _ ->
              if check_subtype3 state ty2 ty2' then solve state eqs
              else if check_subtype3 state ty2' ty2 then
                solve state (eqs @ [ (ty1, ty2) ])
              else false )
      | None -> solve state eqs )*)

let check_equaltype1 state ty1 ty2 =
  unfold_type_definitions state ty1 = unfold_type_definitions state ty2

let check_equaltype state ty1 ty2 =
  if not (check_equaltype1 state ty1 ty2) then
    let print_param = Ast.new_print_param () in
    Error.typing "%t is not equal to %t"
      (Ast.print_ty print_param ty1)
      (Ast.print_ty print_param ty2)

(*let check_subtype state ty1 ty2 =
  if not (check_subtype3 state ty1 ty2) then
    let print_param = Ast.new_print_param () in
    Error.typing "%t is not subtype of %t"
      (Ast.print_ty print_param ty1)
      (Ast.print_ty print_param ty2)*)

(**takes types ty1 and ty2 and returns the smallest ty3 such that subtype1 state ty1 ty3 && subtype1 state ty2 ty3 = true*)

(*let calculate_super_type state ty1 ty2 =
  if check_equaltype1 state ty1 ty2 then ty1
  else
    failwith
      "Super_type is not implemented yet, because we dont have subtypes yet."*)

let rec apply_substitution state subs poly_type =
  let poly_type' = unfold_type_definitions state poly_type in
  let subs' =
    List.map (fun (par, ty) -> (par, unfold_type_definitions state ty)) subs
  in
  (*let subs'' = reduce_substitution state subs' in*)
  let map' ty = apply_substitution state subs' ty in
  match poly_type' with
  | Ast.TyConst _c -> poly_type'
  | Ast.TyApply (name, tys) -> Ast.TyApply (name, List.map map' tys)
  | Ast.TyParam p -> (
      match List.assoc_opt p subs' with Some ty -> ty | None -> poly_type' )
  | Ast.TyArrow (ty_in, ty_out) ->
      Ast.TyArrow
        ( apply_substitution state subs' ty_in,
          apply_substitution state subs' ty_out )
  | Ast.TyTuple tys -> Ast.TyTuple (List.map map' tys)
  | Ast.TyPromise ty -> Ast.TyPromise (apply_substitution state subs' ty)
  | Ast.TyReference ty -> Ast.TyReference (apply_substitution state subs' ty)

(*and reduce_substitution state = function
  | [] -> []
  | sub :: subs ->
      let subs' =
        List.map (fun (a, b) -> (a, apply_substitution state [ sub ] b)) subs
      in
      sub :: subs'*)

let rec check_pattern state patter_type = function
  | Ast.PVar x -> [ (x, patter_type) ]
  | Ast.PAs (pat, x) ->
      let vars = check_pattern state patter_type pat in
      (x, patter_type) :: vars
  | Ast.PAnnotated (pat, ty) ->
      check_equaltype state patter_type ty;
      check_pattern state patter_type pat
  | Ast.PConst c ->
      let ty = Ast.TyConst (Const.infer_ty c) in
      check_equaltype state patter_type ty;
      []
  | Ast.PNonbinding -> []
  | Ast.PTuple pats as p -> (
      match patter_type with
      | Ast.TyTuple patter_types
        when List.length pats = List.length patter_types ->
          let fold (pat_ty, pat) vars =
            let vars' = check_pattern state pat_ty pat in
            vars' @ vars
          in
          List.fold_right fold (List.combine patter_types pats) []
      | _ ->
          let print_param = Ast.new_print_param () in
          Error.typing "Expected tuple. we got %t but per anno expected %t"
            (Ast.print_pattern p)
            (Ast.print_ty print_param patter_type) )
  | Ast.PVariant (lbl, pat) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, pat) with
      | None, None ->
          check_equaltype state patter_type ty_out;
          []
      | Some ty_in, Some pat ->
          check_equaltype state patter_type ty_out;
          check_pattern state ty_in pat
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

let rec infer_expression state = function
  | Ast.Var x ->
      let params, ty = Ast.VariableMap.find x state.variables_ty in
      let subst = refreshing_subst params in
      (Ast.substitute_ty subst ty, [])
  | Ast.Const c -> (Ast.TyConst (Const.infer_ty c), [])
  | Ast.Annotated (e, ty) ->
      let _ty, subs = check_expression state ty e in
      (ty, subs)
  | Ast.Tuple exprs ->
      let fold' (tys, subs) e =
        let ty', subs' = infer_expression state e in
        (ty' :: tys, subs @ subs')
      in
      let tys, subs = List.fold_left fold' ([], []) exprs in
      (Ast.TyTuple tys, subs)
  | Ast.Lambda _ | Ast.RecLambda _ ->
      Error.typing "Infer_expression : Function must be annotated"
  | Ast.Fulfill e ->
      let ty, subs = infer_expression state e in
      (Ast.TyPromise ty, subs)
  | Ast.Reference e ->
      let ty, subs = infer_expression state !e in
      (Ast.TyReference ty, subs)
  | Ast.Variant (lbl, e) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, e) with
      | None, None -> (ty_out, [])
      | Some ty_in', Some expr ->
          let _ty_e, subs = check_expression state ty_in' expr in
          let ty_out' = apply_substitution state subs ty_out in
          (ty_out', subs)
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

and check_expression state annotation = function
  | Ast.Tuple exprs as t -> (
      match annotation with
      | Ast.TyTuple annos ->
          let fold' (tys', subs') anno expr =
            let ty', sub' = check_expression state anno expr in
            (ty' :: tys', sub' @ subs')
          in
          let tys, subs = List.fold_left2 fold' ([], []) annos exprs in
          (Ast.TyTuple tys, subs)
      | Ast.TyParam p ->
          let ty, subs = infer_expression state t in
          (ty, (p, annotation) :: subs)
          (* Kaj če dobimo 'a = 'b list, 'b = 'a * 'c ali kaj drugega izmenično rekurzivnega? *)
      | _ -> Error.typing "Wrong annotation." )
  | Ast.Lambda abs as l -> (
      match annotation with
      | Ast.TyArrow (ty_in, ty_out) ->
          let ty_abs, subs_abs =
            check_check_abstraction state (ty_in, ty_out) abs
          in
          let ty = Ast.TyArrow (ty_in, ty_abs) in
          (ty, subs_abs)
      | Ast.TyParam p ->
          let ty, subs = infer_expression state l in
          (ty, (p, annotation) :: subs)
      | _ -> Error.typing "Wrong annotation." )
  | Ast.RecLambda (f, abs) as r -> (
      match annotation with
      | Ast.TyArrow (ty_in, ty_out) ->
          let state' = extend_variables state [ (f, annotation) ] in
          let ty_abs, subs_abs =
            check_check_abstraction state' (ty_in, ty_out) abs
          in
          let ty = Ast.TyArrow (ty_in, ty_abs) in
          (ty, subs_abs)
      | Ast.TyParam p ->
          let ty, subs = infer_expression state r in
          (ty, (p, annotation) :: subs)
      | _ -> Error.typing "Wrong annotation." )
  | Ast.Fulfill e as f -> (
      match annotation with
      | Ast.TyPromise anno -> check_expression state anno e
      | Ast.TyParam p ->
          let ty, subs = infer_expression state f in
          (ty, (p, annotation) :: subs)
      | _ -> Error.typing "Wrong annotation." )
  | Ast.Reference e as r -> (
      match annotation with
      | Ast.TyReference anno -> check_expression state anno !e
      | Ast.TyParam p ->
          let ty, subs = infer_expression state r in
          (ty, (p, annotation) :: subs)
      | _ -> Error.typing "Expected Reference" )
  | Ast.Variant (lbl, e) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, e) with
      | None, None ->
          check_equaltype state ty_out annotation;
          (ty_out, [])
      | Some ty_in', Some expr ->
          let _ty_e, subs = check_expression state ty_in' expr in
          let ty_out' = apply_substitution state subs ty_out in
          check_equaltype state ty_out' annotation;
          (ty_out', subs)
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )
  | (Ast.Var _ | Ast.Const _ | Ast.Annotated _) as e -> (
      let ty, subs = infer_expression state e in
      check_equaltype state ty annotation;
      match annotation with
      | Ast.TyParam p -> (ty, (p, ty) :: subs)
      | _ -> (ty, subs) )

and infer_computation state = function
  | Ast.Return e -> infer_expression state e
  | Ast.Do (comp, abs) ->
      let ty_c, subs_c = infer_computation state comp in
      (* tu moramo v state dodati še comp kot anotiran *)
      let ty_a, subs_a = check_infer_abstraction state ty_c abs in
      (ty_a, subs_c @ subs_a)
  | Ast.Apply (e1, e2) -> (
      let ty_1, subs_1 = infer_expression state e1 in
      match ty_1 with
      | Ast.TyArrow (ty_in, ty_out) ->
          let _ty_2, subs_2 = check_expression state ty_in e2 in
          (ty_out, subs_2 @ subs_1)
      | _ -> Error.typing "First expresion in apply need to be of type arrow." )
  | Ast.Out (op, e, comp) | Ast.In (op, e, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations in
      let _ = check_expression state ty_op e
      and ty_comp = infer_computation state comp in
      ty_comp
  | Ast.Await (e, abs) -> (
      let ty_promise, subs_e = infer_expression state e in
      match ty_promise with
      | Ast.TyPromise ty1 ->
          let ty_c, subs_c = check_infer_abstraction state ty1 abs in
          (ty_c, subs_e @ subs_c)
      | _ -> Error.typing "Expected Await." )
  | Ast.Match (_, []) ->
      Error.typing "Cannot infer the type of a match with no cases"
  | Ast.Match (e, case :: cases) ->
      (* TODO prva izbira ni nujno prava če imamo podtipe, je pa v smiselnem primeru gotovo njen nadtip.*)
      let ty_e, subs_e = infer_expression state e in
      let ty_1, subs_1 = check_infer_abstraction state ty_e case in
      let fold' subs case' =
        let ty_current, subs_current =
          check_infer_abstraction state ty_e case'
        in
        check_equaltype state ty_current ty_1;
        subs @ subs_current
      in
      let subs = List.fold_left fold' [] cases in
      (ty_1, subs_e @ subs_1 @ subs)
  | Ast.Handler (op, abs, p, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations in
      let ty_a, subs_a = check_infer_abstraction state ty_op abs in
      let state' = extend_variables state [ (p, ty_a) ] in
      let ty_c, subs_c = infer_computation state' comp in
      (ty_c, subs_a @ subs_c)

and check_computation state annotation = function
  | Ast.Return expr -> check_expression state annotation expr
  | Ast.Do (comp1, comp2) ->
      let ty_1, subs_1 = infer_computation state comp1 in
      let ty_2, subs_2 =
        check_check_abstraction state (ty_1, annotation) comp2
      in
      (ty_2, subs_1 @ subs_2)
  | Ast.Apply (e1, e2) -> (
      let ty_1, subs_1 = infer_expression state e1 in
      match ty_1 with
      | Ast.TyArrow (ty_in, ty_out) ->
          let _ty_2, subs_2 = check_expression state ty_in e2 in
          check_equaltype state ty_out annotation;
          (ty_out, subs_2 @ subs_1)
      | _ -> Error.typing "First expresion in apply need to be of type arrow." )
  | Ast.Out (op, e, comp) | Ast.In (op, e, comp) ->
      let ty_o = Ast.OperationMap.find op state.operations in
      let _ty_e, subs_e = check_expression state ty_o e in
      let ty_comp, subs_comp = check_computation state annotation comp in
      (ty_comp, subs_e @ subs_comp)
  | Ast.Await (e, abs) -> (
      let ty_1, subs_1 = infer_expression state e in
      match ty_1 with
      | Ast.TyPromise ty ->
          let ty_2, subs_2 =
            check_check_abstraction state (ty, annotation) abs
          in
          (ty_2, subs_1 @ subs_2)
      | _ -> Error.typing "Expected Promise" )
  | Ast.Match (_e, []) -> Error.typing "Canot check match without cases."
  | Ast.Match (e, case :: cases) ->
      let ty_e, subs_e = infer_expression state e in
      let ty_1, subs_1 =
        check_check_abstraction state (ty_e, annotation) case
      in
      let fold' subs' case' =
        let ty_current, subs_current =
          check_check_abstraction state (ty_e, annotation) case'
        in
        check_equaltype state ty_current ty_1;
        subs' @ subs_current
      in
      let subs = List.fold_left fold' [] cases in
      (ty_1, subs_e @ subs_1 @ subs)
  | Ast.Handler (op, abs, p, comp) ->
      let ty_1 = Ast.OperationMap.find op state.operations in
      let ty_2, subs_2 = check_infer_abstraction state ty_1 abs in
      let state' = extend_variables state [ (p, ty_2) ] in
      let ty_3, subs_3 = check_computation state' annotation comp in
      (ty_3, subs_2 @ subs_3)

and check_infer_abstraction state ty_argument (pat, comp) =
  let vars = check_pattern state ty_argument pat in
  let state' = extend_variables state vars in
  let ty_c, subs_c = infer_computation state' comp in
  (ty_c, subs_c)

and check_check_abstraction state (ty_argument, ty_comp) (pat, comp) =
  let vars = check_pattern state ty_argument pat in
  let state' = extend_variables state vars in
  let ty_c, subs_c = check_computation state' ty_comp comp in
  (ty_c, subs_c)

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

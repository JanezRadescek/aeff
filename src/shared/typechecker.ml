type state = {
  variables : (Ast.ty_param list * Ast.ty) Ast.VariableMap.t;
  operations : Ast.ty Ast.OperationMap.t;
  type_definitions : (Ast.ty_param list * Ast.ty_def) Ast.TyNameMap.t;
}

let initial_state =
  {
    variables = Ast.VariableMap.empty;
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

let extend_variables state vars =
  List.fold_left
    (fun state (x, ty) ->
      { state with variables = Ast.VariableMap.add x ([], ty) state.variables })
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

let uncurry f = function (a,b) -> f a b

let rec infer_pattern state = function
  | Ast.PVar x ->
      let ty = fresh_ty () in
      (ty, [ (x, ty) ], [])
  | Ast.PAs (pat, x) ->
      let ty, vars, eqs = infer_pattern state pat in
      (ty, (x, ty) :: vars, eqs)
  | Ast.PAnnotated (pat, ty) ->
      let ty', vars, eqs = infer_pattern state pat in
      (ty, vars, (ty, ty') :: eqs)
  | Ast.PConst c -> (Ast.TyConst (Const.infer_ty c), [], [])
  | Ast.PNonbinding ->
      let ty = fresh_ty () in
      (ty, [], [])
  | Ast.PTuple pats ->
      let fold pat (tys, vars, eqs) =
        let ty', vars', eqs' = infer_pattern state pat in
        (ty' :: tys, vars' @ vars, eqs' @ eqs)
      in
      let tys, vars, eqs = List.fold_right fold pats ([], [], []) in
      (Ast.TyTuple tys, vars, eqs)
  | Ast.PVariant (lbl, pat) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, pat) with
      | None, None -> (ty_out, [], [])
      | Some ty_in, Some pat ->
          let ty, vars, eqs = infer_pattern state pat in
          (ty_out, vars, (ty_in, ty) :: eqs)
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

let rec check_pattern state annotation = function
  | Ast.PVar x ->
      (annotation, [ (x, annotation) ], [])
  | Ast.PAs (pat, x) ->
      let ty, vars, eqs = check_pattern state annotation pat in
      (annotation, (x, annotation) :: vars, eqs)
  | Ast.PAnnotated (pat, ty) ->
      let ty', vars, eqs = check_pattern state annotation pat in
      match ty with
      | annotation -> (annotation, vars, eqs)
      | _ -> Error.typing "Annotation conflict"
  | Ast.PConst c -> 
      let ty = Ast.TyConst (Const.infer_ty c) in
      match ty with
      | annotation -> (annotation, [], [])
      | _ -> Error.typing "Wrong constant type"
  | Ast.PNonbinding ->
      (annotation, [], [])
  | Ast.PTuple pats ->
      match annotation with
      | Ast.TyTuple annotations -> (
        let fold (anno,pat) (tys, vars, eqs) =
          let ty', vars', eqs' = check_pattern state anno pat in
          (anno :: tys, vars' @ vars, eqs' @ eqs)
        in
        let tys', vars, eqs = List.fold_right fold (List.combine annotations pats) ([], [], []) in
        (annotation, vars, eqs))
      | _ Error.typing "Expected pattern tuple"
  | Ast.PVariant (lbl, pat) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, pat, ty_out) with
      | None, None, annotation -> (ty_out, [], [])
      | Some ty_in, Some pat, annotation ->
          let ty, vars, eqs = check_pattern state ty_in pat in
          (annotation, vars, eqs)
      | None, Some _, _| Some _, None, _ ->
          Error.typing "Variant optional argument mismatch" )

(*let subtype a b = a = b *)

let rec infer_expression state expr = function
  let ty = Ast.TypeMap.Find expr  in (* TODO Ast.TypeMap.Find če še nismp izračunali tip ga poračunajmo sicer le vrnemo*))
  match ty with
  | ?TODO -> infer_expression1 state expr
  | x -> (x, [])

let rec infer_expression1 state = function
  | Ast.Var x ->
      let params, ty = Ast.VariableMap.find x state.variables in
      let subst = refreshing_subst params in
      (Ast.substitute_ty subst ty, [])
  | Ast.Const c -> (Ast.TyConst (Const.infer_ty c), [])
  | Ast.Annotated (expr, ty) ->
      check_expression state ty expr
  | Ast.Tuple exprs ->
      let fold expr (tys, eqs) =
        let ty', eqs' = infer_expression state expr in
        (ty' :: tys, eqs' @ eqs)
      in
      let tys, eqs = List.fold_right fold exprs ([], []) in
      (Ast.TyTuple tys, eqs)
  | Ast.Lambda abs ->
      let ty, ty', eqs = infer_abstraction state abs in
      (Ast.TyArrow (ty, ty'), eqs)
  | Ast.RecLambda (f, abs) ->
      let f_ty = fresh_ty () in
      let state' = extend_variables state [ (f, f_ty) ] in
      let ty, ty', eqs = infer_abstraction state' abs in
      let out_ty = Ast.TyArrow (ty, ty') in
      (out_ty, (f_ty, out_ty) :: eqs)
  | Ast.Fulfill expr ->
      let ty, eqs = infer_expression state expr in
      (Ast.TyPromise ty, eqs)
  | Ast.Reference expr_ref ->
      let ty, eqs = infer_expression state !expr_ref in
      (Ast.TyReference ty, eqs)
  | Ast.Variant (lbl, expr) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, expr) with
      | None, None -> (ty_out, [])
      | Some ty_in, Some expr ->
          let ty, eqs = infer_expression state expr in
          (ty_out, (ty_in, ty) :: eqs)
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

(* state * annotation * expresion -> type * unsolved equations ?      we should save manual results *)
and check_expression state annotation = function
  | Ast.Var x ->
      let params, ty = Ast.VariableMap.find x state.variables in
      let subst = refreshing_subst params in
      (Ast.substitute_ty subst ty, [])
  | Ast.Const c -> (Ast.TyConst (Const.infer_ty c), [])
  | Ast.Annotated (expr, ty) ->
      if ty = annotation then check_expression state ty expr else Error.typing "Annotations do not match."
  | Ast.Tuple expr ->
      match annotation with
      | Ast.PTuple annotations when List.length expr = List.length annotations -> (
        let fold (anno,expr) (tys, eqs) =
          let ty', eqs' = check_expression state anno expr in
          (anno :: tys, eqs' @ eqs)
        in
        let tys, eqs = List.fold_right fold (List.combine annotations expr) ([], []) in
        (annotation, eqs)
      | _ -> Error.typing "Expected tuple." 
        
  | Ast.Lambda (pat, com) ->
      match annotation with ->
      | Ast.TyArrow(pat_anno,com_anno) -> (
          let state' = extend_variables state [ (pat,pat_anno) ] in
          check_expression state' com_anno com )
      | _ -> Error.typing "Expected Lambda." 

  | Ast.RecLambda (f, (pat, com)) ->
      match annotation with ->
      | Ast.TyArrow(pat_anno,com_anno) -> (
          let state' = extend_variables state [ (f, annotation) ] in
          let state'' = extend_variables state' [ (pat,pat_anno) ] in
          check_expression state'' com_anno com )
      | _ -> Error.typing "Expected Rec Lambda." 

  | Ast.Fulfill expr ->
      match annotation with ->
      | Ast.TyPromise anno -> check_expression state anno expr 
      | _ -> Error.typing "Expected Promise."  

  | Ast.Reference expr_ref ->
      match annotation with ->
      | Ast.TyReference anno -> check_expression state anno !expr 
      | _ -> Error.typing "Expected Reference"  

  | Ast.Variant (lbl, expr) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, expr) with
      | None, None -> (ty_out,[])
      | Some ty_in, Some expr ->
          let ty, eqs = check_expression state ty_in expr in
          (ty_out, eqs)
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )    

  | _ -> Error.typing "Type does not exist" 

and infer_computation state = function
  | Ast.Return expr ->
      let ty, eqs = infer_expression state expr in
      (ty, eqs)
  | Ast.Do (comp1, comp2) ->
      let ty1, eqs1 = infer_computation state comp1 in
      let ty1', ty2, eqs2 = infer_abstraction state comp2 in
      (ty2, ((ty1, ty1') :: eqs1) @ eqs2)
  | Ast.Apply (e1, e2) ->
      let t1, eqs1 = infer_expression state e1
      and t2, eqs2 = infer_expression state e2
      and a = fresh_ty () in
      (a, ((t1, Ast.TyArrow (t2, a)) :: eqs1) @ eqs2)
  | Ast.Out (op, expr, comp) | Ast.In (op, expr, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations
      and ty2, eqs1 = infer_expression state expr
      and ty3, eqs2 = infer_computation state comp in
      (ty3, ((ty1, ty2) :: eqs1) @ eqs2)
  | Ast.Await (e, abs) ->
      let pty1, eqs1 = infer_expression state e
      and ty1, ty2, eqs2 = infer_abstraction state abs in
      (ty2, ((pty1, Ast.TyPromise ty1) :: eqs1) @ eqs2)
  | Ast.Match (e, cases) ->
      let ty1, eqs = infer_expression state e and ty2 = fresh_ty () in
      let fold eqs abs =
        let ty1', ty2', eqs' = infer_abstraction state abs in
        ((ty1, ty1') :: (ty2, ty2') :: eqs') @ eqs
      in
      (ty2, List.fold_left fold eqs cases)
  | Ast.Handler (op, abs, p, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations
      and ty1', ty2, eqs1 = infer_abstraction state abs
      and ty2' = Ast.TyPromise (fresh_ty ()) in
      let state' = extend_variables state [ (p, ty2') ] in
      let ty, eqs2 = infer_computation state' comp in
      (ty, ((ty1, ty1') :: (ty2, ty2') :: eqs1) @ eqs2)

and check_computation state annotation = function
  | Ast.Return expr ->
    check_expression state annotation expr

  | Ast.Do (comp1, comp2) ->
      let ty1, eqs1 = infer_computation state comp1 in
      let _, ty2, eqs2 = check_abstraction state (ty1, annotation) comp2 in
      (ty2, eqs1 @ eqs2)

  | Ast.Apply (expr1,expr2) -> (
    let (ty1, eqs1) = infer_expression state expr1 in
    match ty1 with
    | Ast.TyArrow(ty',ty'') -> (
      let (ty2, eqs2) = check_expression state ty' expr2 in 
      if ty'' = annotation then (annotation, eqs1 @ eqs2) else Error.typing "Wrong annotation"
      )
    | _ -> Error.typing "Expected Arrow")

  | Ast.Out (op, expr, comp) | Ast.In (op, expr, comp) ->
    let ty1 = Ast.OperationMap.find op state.operations
    and (ty2, eqs1) = check_expression state ty1 expr
    and (ty3, eqs2) = check_computation state annotation comp in
    (ty3, eqs1 @ eqs2)

  | Ast.Await (e, abs) ->
      let pty1, eqs1 = infer_expression state e in 
      match pty1 with
      | Ast.TyPromise ty1 -> 
          let ty1', ty2, eqs2 = check_abstraction state (pty1, annotation) abs in
          (ty2, eqs1 @ eqs2)
      | _ -> Error.typing "Expected Promise"

  | Ast.Match (e, cases) ->
      let ty1, eqs = infer_expression state e in
      let fold eqs abs =
        let ty1', ty2', eqs' = check_abstraction state (ty1, annotation) abs in
        eqs' @ eqs
      in
      (annotation, List.fold_left fold eqs cases)


  | Ast.Handler (op, abs, p, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations
      and ty1', ty2, eqs1 = check_infer_abstraction state ty1 abs in
      let state' = extend_variables state [ (p, ty2) ] in
      let (ty3, eqs2) = check_computation state' annotation comp in
      (ty3, eqs1 @ eqs2)


and infer_abstraction state (pat, comp) =
  let ty, vars, eqs = infer_pattern state pat in
  let state' = extend_variables state vars in
  let ty', eqs' = infer_computation state' comp in
  (ty, ty', eqs @ eqs')

and check_abstraction state (pat_ty, comp_ty) (pat, comp) = 
  let ty1, vars, eqs = check_pattern state pat_ty pat in
  let state' = extend_variables state vars in
  let (ty2, eqs') = check_computation state' comp_ty comp in
  (pat_ty, comp_ty, eqs @ eqs')

and check_infer_abstraction state pat_ty (pat, comp) = 
  let ty1, vars, eqs = check_pattern state pat_ty pat in
  let state' = extend_variables state vars in
  let (ty2, eqs') = infer_computation state' comp in
  (pat_ty, ty2, eqs @ eqs')

let subst_equations sbst =
  let subst_equation (t1, t2) =
    (Ast.substitute_ty sbst t1, Ast.substitute_ty sbst t2)
  in
  List.map subst_equation

let add_subst a t sbst = Ast.TyParamMap.add a (Ast.substitute_ty sbst t) sbst

let rec occurs a = function
  | Ast.TyParam a' -> a = a'
  | Ast.TyConst _ -> false
  | Ast.TyArrow (ty1, ty2) -> occurs a ty1 || occurs a ty2
  | Ast.TyApply (_, tys) -> List.exists (occurs a) tys
  | Ast.TyTuple tys -> List.exists (occurs a) tys
  | Ast.TyPromise ty -> occurs a ty
  | Ast.TyReference ty -> occurs a ty

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

let rec unify state = function
  | [] -> Ast.TyParamMap.empty
  | (t1, t2) :: eqs when t1 = t2 -> unify state eqs
  | (Ast.TyApply (ty_name1, args1), Ast.TyApply (ty_name2, args2)) :: eqs
    when ty_name1 = ty_name2 ->
      unify state (List.combine args1 args2 @ eqs)
  | (Ast.TyApply (ty_name, args), ty) :: eqs
    when is_transparent_type state ty_name ->
      unify state ((unfold state ty_name args, ty) :: eqs)
  | (ty, Ast.TyApply (ty_name, args)) :: eqs
    when is_transparent_type state ty_name ->
      unify state ((ty, unfold state ty_name args) :: eqs)
  | (Ast.TyTuple tys1, Ast.TyTuple tys2) :: eqs
    when List.length tys1 = List.length tys2 ->
      unify state (List.combine tys1 tys2 @ eqs)
  | (Ast.TyArrow (t1, t1'), Ast.TyArrow (t2, t2')) :: eqs ->
      unify state ((t1, t2) :: (t1', t2') :: eqs)
  | (Ast.TyPromise ty1, Ast.TyPromise ty2) :: eqs ->
      unify state ((ty1, ty2) :: eqs)
  | (Ast.TyReference ty1, Ast.TyReference ty2) :: eqs ->
      unify state ((ty1, ty2) :: eqs)
  | (Ast.TyParam a, t) :: eqs when not (occurs a t) ->
      add_subst a t
        (unify state (subst_equations (Ast.TyParamMap.singleton a t) eqs))
  | (t, Ast.TyParam a) :: eqs when not (occurs a t) ->
      add_subst a t
        (unify state (subst_equations (Ast.TyParamMap.singleton a t) eqs))
  | (t1, t2) :: _ ->
      let print_param = Ast.new_print_param () in
      Error.typing "Cannot unify %t = %t"
        (Ast.print_ty print_param t1)
        (Ast.print_ty print_param t2)

let infer state e =
  let t, eqs = infer_computation state e in
  let sbst = unify state eqs in
  let t' = Ast.substitute_ty sbst t in
  t'

let add_external_function x ty_sch state =
  Format.printf "@[val %t : %t@]@." (Ast.Variable.print x)
    (Ast.print_ty_scheme ty_sch);
  { state with variables = Ast.VariableMap.add x ty_sch state.variables }

let add_operation state op ty =
  Format.printf "@[operation %t : %t@]@." (Ast.Operation.print op)
    (Ast.print_ty_scheme ([], ty));
  { state with operations = Ast.OperationMap.add op ty state.operations }

let add_top_definition state x expr =
  let ty, eqs = infer_expression state expr in
  let subst = unify state eqs in
  let ty' = Ast.substitute_ty subst ty in
  let free_vars = Ast.free_vars ty' |> Ast.TyParamSet.elements in
  let ty_sch = (free_vars, ty') in
  add_external_function x ty_sch state

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
  let ty1 = Ast.OperationMap.find op state.operations
  and ty2, eqs = infer_expression state expr in
  unify state ((ty1, ty2) :: eqs)

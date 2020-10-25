open Utils

type state = {
  variables : Ast.ty_scheme Ast.VariableMap.t;
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

let check_subtype1 state ty1 ty2 =
  unfold_type_definitions state ty1 <> unfold_type_definitions state ty2

let check_subtype state ty1 ty2 =
  if check_subtype1 state ty1 ty2 then
    let print_param = Ast.new_print_param () in
    Error.typing "%t does not match %t"
      (Ast.print_ty print_param ty1)
      (Ast.print_ty print_param ty2)

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

(* state * expresion -> type  ?    *)
let rec infer_expression state = function
  | Ast.Var x ->
      let params, ty = Ast.VariableMap.find x state.variables in
      let subst = refreshing_subst params in
      Ast.substitute_ty subst ty
  | Ast.Const c -> Ast.TyConst (Const.infer_ty c)
  | Ast.Annotated (expr, ty) ->
      let _ = check_expression state ty expr in
      ty
  | Ast.Tuple exprs ->
      let fold expr tys =
        let ty' = infer_expression state expr in
        ty' :: tys
      in
      let tys = List.fold_right fold exprs [] in
      Ast.TyTuple tys
  | Ast.Lambda _ | Ast.RecLambda _ -> Error.typing "Function must be annotated"
  | Ast.Fulfill expr ->
      let ty = infer_expression state expr in
      Ast.TyPromise ty
  | Ast.Reference expr_ref ->
      let ty = infer_expression state !expr_ref in
      Ast.TyReference ty
  | Ast.Variant (lbl, expr) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, expr) with
      | None, None -> ty_out
      | Some ty_in, Some expr ->
          let ty = infer_expression state expr in
          check_subtype state ty ty_in;
          ty_out
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )

(* state * annotation * expresion -> unit *)
and check_expression state annotation = function
  | Ast.Tuple exprs -> (
      match annotation with
      | Ast.TyTuple annotations when List.length exprs = List.length annotations
        ->
          List.iter2 (check_expression state) annotations exprs
      | _ -> Error.typing "Expected tuple." )
  | Ast.Lambda (pat, com) -> (
      match annotation with
      | Ast.TyArrow (pat_anno, com_anno) ->
          let vars = check_pattern state pat_anno pat in
          let state' = extend_variables state vars in
          check_computation state' com_anno com
      | _ -> Error.typing "Expected Lambda." )
  | Ast.RecLambda (f, (pat, com)) -> (
      match annotation with
      | Ast.TyArrow (pat_anno, com_anno) ->
          let vars = check_pattern state pat_anno pat in
          let state' = extend_variables state ((f, annotation) :: vars) in
          check_computation state' com_anno com
      | _ -> Error.typing "Expected Rec Lambda." )
  | Ast.Fulfill expr -> (
      match annotation with
      | Ast.TyPromise anno -> check_expression state anno expr
      | _ -> Error.typing "Expected Promise." )
  | Ast.Reference expr_ref -> (
      match annotation with
      | Ast.TyReference anno -> check_expression state anno !expr_ref
      | _ -> Error.typing "Expected Reference" )
  | Ast.Variant (lbl, expr) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, expr) with
      | None, None -> check_subtype state ty_out annotation
      | Some ty_in, Some expr ->
          check_expression state ty_in expr;
          check_subtype state ty_out annotation
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch" )
  | (Ast.Var _ | Ast.Const _ | Ast.Annotated _) as expr ->
      let ty = infer_expression state expr in
      check_subtype state ty annotation

(* state * computation -> type  ?    *)
and infer_computation state = function
  | Ast.Return expr ->
      let ty = infer_expression state expr in
      ty
  | Ast.Do (comp1, comp2) ->
      let ty1 = infer_computation state comp1 in
      let ty2 = check_infer_abstraction state ty1 comp2 in
      ty2
  | Ast.Apply (e1, e2) -> (
      let ty_argument = infer_expression state e2 in
      match e1 with
      | Ast.Annotated (Ast.Lambda abs, _ty) ->
          check_infer_abstraction state ty_argument abs
      | Ast.Annotated (Ast.RecLambda (_f, _abs), _ty) ->
          failwith "not implemented"
      | _ ->
          Error.typing
            "Apply needs annotated function expression for first argument. Got \
             %t"
            (Ast.print_expression e1) )
  | Ast.Out (op, expr, comp) | Ast.In (op, expr, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations
      and ty_expr = infer_expression state expr
      and ty_comp = infer_computation state comp in
      check_subtype state ty_expr ty_op;
      ty_comp
  | Ast.Await (e, abs) -> (
      let pty1 = infer_expression state e in
      match pty1 with
      | Ast.TyPromise ty1 -> check_infer_abstraction state ty1 abs
      | _ -> Error.typing "Expected Await." )
  | Ast.Match (_, []) ->
      Error.typing "Cannot infer the type of a match with no cases"
  | Ast.Match (e, case :: cases) ->
      (* TODO prva izbira ni nujno prava če imamo podtipe, je pa v smiselnem primeru gotovo njen nadtip.*)
      let ty1 = infer_expression state e in
      let ty2 = check_infer_abstraction state ty1 case in
      let check_case ty' case' =
        let ty2' = check_infer_abstraction state ty1 case' in
        if check_subtype1 state ty2' ty' then ty'
        else if check_subtype1 state ty' ty2' then ty2'
        else Error.typing "Types do not match."
      in
      let super_ty = List.fold_left check_case ty2 cases in
      super_ty
  | Ast.Handler (op, abs, p, comp) ->
      let ty_op = Ast.OperationMap.find op state.operations in
      let ty_abs = check_infer_abstraction state ty_op abs in
      let state' = extend_variables state [ (p, ty_abs) ] in
      let ty = infer_computation state' comp in
      ty

and check_computation state annotation = function
  | Ast.Return expr -> check_expression state annotation expr
  | Ast.Do (comp1, comp2) ->
      let ty1 = infer_computation state comp1 in
      check_abstraction state (ty1, annotation) comp2
  | Ast.Apply _ as expr ->
      let ty = infer_computation state expr in
      check_subtype state ty annotation
  | Ast.Out (op, expr, comp) | Ast.In (op, expr, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations in
      check_expression state ty1 expr;
      check_computation state annotation comp
  | Ast.Await (e, abs) -> (
      let pty1 = infer_expression state e in
      match pty1 with
      | Ast.TyPromise ty1 -> check_abstraction state (ty1, annotation) abs
      | _ -> Error.typing "Expected Promise" )
  | Ast.Match (e, cases) ->
      let ty1 = infer_expression state e in
      let _ = List.map (check_abstraction state (ty1, annotation)) cases in
      ()
  | Ast.Handler (op, abs, p, comp) ->
      let ty1 = Ast.OperationMap.find op state.operations in
      let ty2 = check_infer_abstraction state ty1 abs in
      let state' = extend_variables state [ (p, ty2) ] in
      check_computation state' annotation comp

(**state type abs -> () *)
and check_abstraction state (pat_ty, comp_ty) (pat, comp) =
  let vars = check_pattern state pat_ty pat in
  let state' = extend_variables state vars in
  check_computation state' comp_ty comp
  (*če damo principa ty_in dobimo principal ty_out. (za int:number bomo seveda dobili number in ne int kar pa je vredu)*)

(**state pat_ty abs -> com_ty *)
and check_infer_abstraction state pat_ty (pat, comp) =
  let vars = check_pattern state pat_ty pat in
  let state' = extend_variables state vars in
  infer_computation state' comp

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
  check_expression state ty expr

let add_external_function x ty_sch state =
  Format.printf "@[val %t : %t@]@." (Ast.Variable.print x)
    (Ast.print_ty_scheme ty_sch);
  { state with variables = Ast.VariableMap.add x ty_sch state.variables }

let add_operation state op ty =
  Format.printf "@[operation %t : %t@]@." (Ast.Operation.print op)
    (Ast.print_ty_scheme ([], ty));
  { state with operations = Ast.OperationMap.add op ty state.operations }

let add_top_definition state x ty_sch expr =
  check_polymorphic_expression state ty_sch expr;
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
  let ty1 = Ast.OperationMap.find op state.operations in
  check_expression state ty1 expr

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

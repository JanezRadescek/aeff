(** Desugaring of syntax into the core language. *)

open Utils
module S = Syntax
module StringMap = Map.Make (String)

type state = {
  ty_names : Ast.ty_name StringMap.t;
  ty_params : Ast.ty_param StringMap.t;
  variables : Ast.variable StringMap.t;
  operations : Ast.operation StringMap.t;
  labels : Ast.label StringMap.t;
}

let initial_state =
  {
    ty_names =
      StringMap.empty
      |> StringMap.add Syntax.bool_ty_name Ast.bool_ty_name
      |> StringMap.add Syntax.int_ty_name Ast.int_ty_name
      |> StringMap.add Syntax.unit_ty_name Ast.unit_ty_name
      |> StringMap.add Syntax.string_ty_name Ast.string_ty_name
      |> StringMap.add Syntax.float_ty_name Ast.float_ty_name
      |> StringMap.add Syntax.empty_ty_name Ast.empty_ty_name
      |> StringMap.add Syntax.list_ty_name Ast.list_ty_name;
    ty_params = StringMap.empty;
    variables = StringMap.empty;
    operations = StringMap.empty;
    labels =
      StringMap.empty
      |> StringMap.add Syntax.nil_label Ast.nil_label
      |> StringMap.add Syntax.cons_label Ast.cons_label;
  }

let find_symbol ~loc map name =
  match StringMap.find_opt name map with
  | None -> Error.syntax ~loc "Unknown name --%s--" name
  | Some symbol -> symbol

let lookup_ty_name ~loc state = find_symbol ~loc state.ty_names

let lookup_ty_param ~loc state = find_symbol ~loc state.ty_params

let lookup_variable ~loc state = find_symbol ~loc state.variables

let lookup_operation ~loc state = find_symbol ~loc state.operations

let lookup_label ~loc state = find_symbol ~loc state.labels

let add_fresh_ty_params state vars =
  let aux ty_params (x, x') = StringMap.add x x' ty_params in
  let ty_params' = List.fold_left aux state.ty_params vars in
  { state with ty_params = ty_params' }

let rec free_params_in_ty { it = plain_ty; Location.at = _ } =
  let fold sez ty = free_params_in_ty ty @ sez in
  let rec remove_dup = function
    | [] -> []
    | x :: xs ->
        let xs' = remove_dup xs in
        if List.mem x xs' then xs else x :: xs'
  in
  let result =
    match plain_ty with
    | S.TyApply (_y_name, tys) ->
        let free_params = List.fold_left fold [] tys in
        free_params
    | S.TyParam ty_param -> [ ty_param ]
    | S.TyArrow (ty1, ty2) ->
        let free_params1 = free_params_in_ty ty1 in
        let free_params2 = free_params_in_ty ty2 in
        free_params1 @ free_params2
    | S.TyTuple tys ->
        let free_params = List.fold_left fold [] tys in
        free_params
    | S.TyConst _c -> []
    | S.TyReference ty | S.TyPromise ty -> free_params_in_ty ty
  in
  remove_dup result

let rec desugar_ty state { it = plain_ty; Location.at = loc } =
  desugar_plain_ty ~loc state plain_ty

and desugar_plain_ty ~loc state = function
  | S.TyApply (ty_name, tys) ->
      let ty_name' = lookup_ty_name ~loc state ty_name in
      let tys' = List.map (desugar_ty state) tys in
      Ast.TyApply (ty_name', tys')
  | S.TyParam ty_param ->
      let ty_param' = lookup_ty_param ~loc state ty_param in
      Ast.TyParam ty_param'
  | S.TyArrow (ty1, ty2) ->
      let ty1' = desugar_ty state ty1 in
      let ty2' = desugar_ty state ty2 in
      Ast.TyArrow (ty1', ty2')
  | S.TyTuple tys ->
      let tys' = List.map (desugar_ty state) tys in
      Ast.TyTuple tys'
  | S.TyConst c -> Ast.TyConst c
  | S.TyReference ty -> Ast.TyReference (desugar_ty state ty)
  | S.TyPromise ty -> Ast.TyPromise (desugar_ty state ty)

let desugar_ty_scheme state ty =
  let params = free_params_in_ty ty in
  let params' = List.map Ast.TyParam.fresh params in
  let params'' = List.combine params params' in
  let state' = add_fresh_ty_params state params'' in
  let ty' = desugar_ty state' ty in
  (state', (* Ast.ty_scheme *) (params', ty'))

let rec desugar_pattern state { it = pat; Location.at = loc } =
  let vars, pat' = desugar_plain_pattern ~loc state pat in
  (vars, pat')

and desugar_plain_pattern ~loc state = function
  | S.PVar x ->
      let x' = Ast.Variable.fresh x in
      ([ (x, x') ], Ast.PVar x')
  | S.PAnnotated (pat, ty) ->
      let vars, pat' = desugar_pattern state pat
      and ty' = desugar_ty state ty in
      (vars, Ast.PAnnotated (pat', ty'))
  | S.PAs (pat, x) ->
      let vars, pat' = desugar_pattern state pat in
      let x' = Ast.Variable.fresh x in
      ((x, x') :: vars, Ast.PAs (pat', x'))
  | S.PTuple ps ->
      let aux p (vars, ps') =
        let vars', p' = desugar_pattern state p in
        (vars' @ vars, p' :: ps')
      in
      let vars, ps' = List.fold_right aux ps ([], []) in
      (vars, Ast.PTuple ps')
  | S.PVariant (lbl, None) ->
      let lbl' = lookup_label ~loc state lbl in
      ([], Ast.PVariant (lbl', None))
  | S.PVariant (lbl, Some pat) ->
      let lbl' = lookup_label ~loc state lbl in
      let vars, pat' = desugar_pattern state pat in
      (vars, Ast.PVariant (lbl', Some pat'))
  | S.PConst c -> ([], Ast.PConst c)
  | S.PNonbinding -> ([], Ast.PNonbinding)

let add_fresh_variables state vars =
  let aux variables (x, x') = StringMap.add x x' variables in
  let variables' = List.fold_left aux state.variables vars in
  { state with variables = variables' }

let add_operation state op =
  let op' = Ast.Operation.fresh op in
  (op', { state with operations = StringMap.add op op' state.operations })

let rec desugar_expression state { it = term; Location.at = loc } =
  let binds, expr = desugar_plain_expression ~loc state term in
  (binds, expr)

and desugar_plain_expression ~loc state = function
  | S.Var x ->
      let x' = lookup_variable ~loc state x in
      ([], Ast.Var x')
  | S.Const k -> ([], Ast.Const k)
  | S.Annotated (term, ty) ->
      let binds, expr = desugar_expression state term in
      let ty' = desugar_ty state ty in
      (binds, Ast.Annotated (expr, ty'))
  | S.Lambda a ->
      let a' = desugar_abstraction state a in
      ([], Ast.Lambda a')
  | S.Function cases ->
      let x = Ast.Variable.fresh "arg" in
      let cases' = List.map (desugar_abstraction state) cases in
      ([], Ast.Lambda (Ast.PVar x, Ast.Match (Ast.Var x, cases')))
  | S.Tuple ts ->
      let binds, es = desugar_expressions state ts in
      (binds, Ast.Tuple es)
  | S.Variant (lbl, None) ->
      let lbl' = lookup_label ~loc state lbl in
      ([], Ast.Variant (lbl', None))
  | S.Variant (lbl, Some term) ->
      let lbl' = lookup_label ~loc state lbl in
      let binds, expr = desugar_expression state term in
      (binds, Ast.Variant (lbl', Some expr))
  | S.Fulfill term ->
      let binds, e = desugar_expression state term in
      (binds, Ast.Fulfill e)
  | ( S.Apply _ | S.Match _ | S.Let _ | S.LetRec _ | S.Conditional _
    | S.Handler _ | S.Await _ | S.Send _ ) as term ->
      let x = Ast.Variable.fresh "b" in
      let comp = desugar_computation state (Location.add_loc ~loc term) in
      let hoist = (Ast.PVar x, comp) in
      ([ hoist ], Ast.Var x)

and desugar_computation state { it = term; at = loc } =
  let binds, comp = desugar_plain_computation ~loc state term in
  List.fold_right (fun (p, c1) c2 -> Ast.Do (c1, (p, c2))) binds comp

and desugar_plain_computation ~loc state =
  let if_then_else e c1 c2 =
    let true_p = Ast.PConst Const.of_true in
    let false_p = Ast.PConst Const.of_false in
    Ast.Match (e, [ (true_p, c1); (false_p, c2) ])
  in
  function
  | S.Apply ({ it = S.Var "(&&)"; _ }, { it = S.Tuple [ t1; t2 ]; _ }) ->
      let binds1, e1 = desugar_expression state t1 in
      let c1 = desugar_computation state t2 in
      let c2 = Ast.Return (Ast.Const (Const.Boolean false)) in
      (binds1, if_then_else e1 c1 c2)
  | S.Apply ({ it = S.Var "(||)"; _ }, { it = S.Tuple [ t1; t2 ]; _ }) ->
      let binds1, e1 = desugar_expression state t1 in
      let c1 = Ast.Return (Ast.Const (Const.Boolean true)) in
      let c2 = desugar_computation state t2 in
      (binds1, if_then_else e1 c1 c2)
  | S.Apply (t1, t2) ->
      (*TODO !!! user might be lazy and didnt write down type of e1. As such we should check if he has and i case he didnt we should try to calculate it for him.*)
      let binds1, e1 = desugar_expression state t1 in
      let binds2, e2 = desugar_expression state t2 in
      (binds1 @ binds2, Ast.Apply (e1, e2))
  | S.Match (t, cs) ->
      let binds, e = desugar_expression state t in
      let cs' = List.map (desugar_abstraction state) cs in
      (binds, Ast.Match (e, cs'))
  | S.Conditional (t, t1, t2) ->
      let binds, e = desugar_expression state t in
      let c1 = desugar_computation state t1 in
      let c2 = desugar_computation state t2 in
      (binds, if_then_else e c1 c2)
  | S.Let (pat, term1, term2) ->
      let c1 = desugar_computation state term1 in
      let c2 = desugar_abstraction state (pat, term2) in
      ([], Ast.Do (c1, c2))
  | S.LetRec (x, term1, term2) ->
      let state', f, comp1 = desugar_let_rec_def state (x, term1) in
      let c = desugar_computation state' term2 in
      ([], Ast.Do (Ast.Return comp1, (Ast.PVar f, c)))
  | S.Handler (op, (p, None, c), abs2) ->
      let op' = lookup_operation ~loc state op in
      let abs1' = desugar_abstraction state (p, c) in
      let p, cont = desugar_promise_abstraction ~loc state abs2 in
      ([], Ast.Handler (op', abs1', p, cont))
  | S.Handler (op, (x, Some guard, comp), (p, cont)) ->
      let op = lookup_operation ~loc state op
      and x, guard, comp = desugar_guarded_abstraction state (x, guard, comp)
      and p, cont = desugar_promise_abstraction ~loc state (p, cont) in
      let wait_for_guard = Ast.Variable.fresh "waitForGuard"
      and p' = Ast.Variable.fresh "p'"
      and guard_var = Ast.Variable.fresh "guardVar" in
      let recursive_call = Ast.Apply (Ast.Var wait_for_guard, Ast.Tuple []) in
      ( [],
        Ast.Do
          ( Ast.Return
              (Ast.RecLambda
                 ( wait_for_guard,
                   ( Ast.PTuple [],
                     Ast.Handler
                       ( op,
                         ( x,
                           Ast.Do
                             ( guard,
                               ( Ast.PVar guard_var,
                                 if_then_else (Ast.Var guard_var) comp
                                   recursive_call ) ) ),
                         p',
                         Ast.Return (Ast.Var p') ) ) )),
            ( Ast.PVar wait_for_guard,
              Ast.Do (recursive_call, (Ast.PVar p, cont)) ) ) )
  | S.Await (t, abs) ->
      let binds, e = desugar_expression state t in
      let abs' = desugar_abstraction state abs in
      (binds, Ast.Await (e, abs'))
  | S.Send (op, t) ->
      let op' = lookup_operation ~loc state op in
      let binds, e = desugar_expression state t in
      (binds, Ast.Out (op', e, Ast.Return (Ast.Tuple [])))
  (* The remaining cases are expressions, which we list explicitly to catch any
     future changes. *)
  | ( S.Var _ | S.Const _ | S.Annotated _ | S.Tuple _ | S.Variant _ | S.Lambda _
    | S.Function _ | S.Fulfill _ ) as term ->
      let binds, expr = desugar_expression state { it = term; at = loc } in
      (binds, Ast.Return expr)

and desugar_abstraction state (pat, term) =
  let vars, pat' = desugar_pattern state pat in
  let state' = add_fresh_variables state vars in
  let comp = desugar_computation state' term in
  (pat', comp)

and desugar_guarded_abstraction state (pat, term1, term2) =
  let vars, pat' = desugar_pattern state pat in
  let state' = add_fresh_variables state vars in
  let comp1 = desugar_computation state' term1
  and comp2 = desugar_computation state' term2 in
  (pat', comp1, comp2)

and desugar_promise_abstraction ~loc state abs2 =
  match desugar_abstraction state abs2 with
  | Ast.PVar p, comp' -> (p, comp')
  | Ast.PNonbinding, comp' ->
      let p = Ast.Variable.fresh "_" in
      (p, comp')
  | _ -> Error.syntax ~loc "Variable or underscore expected"

and desugar_let_rec_def state (f, { it = exp; at = loc }) =
  match exp with
  | S.Annotated (exp', ty') ->
      let state_desu, f_desu, exp_desu = desugar_let_rec_def state (f, exp') in
      let ty_desu = desugar_ty state ty' in
      (state_desu, f_desu, Ast.Annotated (exp_desu, ty_desu))
  | _ ->
      let f' = Ast.Variable.fresh f in
      let state' = add_fresh_variables state [ (f, f') ] in
      let abs' =
        match exp with
        | S.Lambda a -> desugar_abstraction state' a
        | S.Function cs ->
            let x = Ast.Variable.fresh "rf" in
            let cs = List.map (desugar_abstraction state') cs in
            let new_match = Ast.Match (Ast.Var x, cs) in
            (Ast.PVar x, new_match)
        | _ ->
            Error.syntax ~loc
              "This kind of expression is not allowed in a recursive definition"
      in
      let expr = Ast.RecLambda (f', abs') in
      (state', f', expr)

and desugar_expressions state = function
  | [] -> ([], [])
  | t :: ts ->
      let binds, e = desugar_expression state t in
      let ws, es = desugar_expressions state ts in
      (binds @ ws, e :: es)

let desugar_pure_expression state term =
  let binds, expr = desugar_expression state term in
  match binds with
  | [] -> expr
  | _ -> Error.syntax ~loc:term.at "Only pure expressions are allowed"

let add_label state label label' =
  let labels' = StringMap.add label label' state.labels in
  { state with labels = labels' }

let add_fresh_ty_names state vars =
  let aux ty_names (x, x') = StringMap.add x x' ty_names in
  let ty_names' = List.fold_left aux state.ty_names vars in
  { state with ty_names = ty_names' }

let desugar_ty_def state = function
  | Syntax.TyInline ty -> (state, Ast.TyInline (desugar_ty state ty))
  | Syntax.TySum variants ->
      let aux state (label, ty) =
        let label' = Ast.Label.fresh label in
        let ty' = Option.map (desugar_ty state) ty in
        let state' = add_label state label label' in
        (state', (label', ty'))
      in
      let state', variants' = List.fold_map aux state variants in
      (state', Ast.TySum variants')

let desugar_command state = function
  | Syntax.TyDef defs ->
      let def_name (_, ty_name, _) =
        let ty_name' = Ast.TyName.fresh ty_name in
        (ty_name, ty_name')
      in
      let new_names = List.map def_name defs in
      let state' = add_fresh_ty_names state new_names in
      let aux (params, _, ty_def) (_, ty_name') (state', defs) =
        let params' = List.map (fun a -> (a, Ast.TyParam.fresh a)) params in
        let state'' = add_fresh_ty_params state' params' in
        let state''', ty_def' = desugar_ty_def state'' ty_def in
        (state''', (List.map snd params', ty_name', ty_def') :: defs)
      in
      let state'', defs' = List.fold_right2 aux defs new_names (state', []) in
      (state'', Ast.TyDef defs')
  | Syntax.TopLet (x, ty, term) ->
      let x' = Ast.Variable.fresh x in
      let state', ty_sch = desugar_ty_scheme state ty in
      let state'' = add_fresh_variables state [ (x, x') ] in
      let expr = desugar_pure_expression state' term in
      (state'', Ast.TopLet (x', ty_sch, expr))
  | Syntax.TopDo term ->
      let comp = desugar_computation state term in
      (state, Ast.TopDo comp)
  | Syntax.TopLetRec (f, ty, term) ->
      let state', ty_sch = desugar_ty_scheme state ty in
      let state'', f', expr = desugar_let_rec_def state' (f, term) in
      (state'', Ast.TopLet (f', ty_sch, expr))
  | Syntax.Operation (op, ty) ->
      let op', state' = add_operation state op in
      let ty' = desugar_ty state ty in
      (state', Ast.Operation (op', ty'))

let add_external_variable x state =
  let x' = Ast.Variable.fresh x in
  (add_fresh_variables state [ (x, x') ], x')

open Utils

module TyName = Symbol.Make ()

type ty_name = TyName.t

module TyNameMap = Map.Make (TyName)

let bool_ty_name = TyName.fresh (Some "bool")

let int_ty_name = TyName.fresh (Some "int")

let unit_ty_name = TyName.fresh (Some "unit")

let string_ty_name = TyName.fresh (Some "string")

let float_ty_name = TyName.fresh (Some "float")

let list_ty_name = TyName.fresh (Some "list")

let empty_ty_name = TyName.fresh (Some "empty")

let reference_ty_name = TyName.fresh (Some "ref")

module TyParam = Symbol.Make ()

type ty_param = TyParam.t

module TyParamMap = Map.Make (TyParam)
module TyParamSet = Set.Make (TyParam)

type ty =
  | TyConst of Const.ty
  | TyApply of ty_name * ty list  (** [(ty1, ty2, ..., tyn) type_name] *)
  | TyParam of ty_param  (** ['a] *)
  | TyArrow of ty * ty  (** [ty1 -> ty2] *)
  | TyTuple of ty list  (** [ty1 * ty2 * ... * tyn] *)
  | TyPromise of ty  (** [<<ty>>] *)
  | TyReference of ty  (** [ty ref] *)
  | TyBoxed of ty  (** [[ty]] *)

type ty_scheme = ty_param list * ty

let rec print_ty ?max_level print_param p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | TyConst c -> print "%t" (Const.print_ty c)
  | TyApply (ty_name, []) -> print "%t" (TyName.print ty_name)
  | TyApply (ty_name, [ ty ]) ->
      print ~at_level:1 "%t %t"
        (print_ty ~max_level:1 print_param ty)
        (TyName.print ty_name)
  | TyApply (ty_name, tys) ->
      print ~at_level:1 "%t %t"
        (Print.print_tuple (print_ty print_param) tys)
        (TyName.print ty_name)
  | TyParam a -> print "%t" (print_param a)
  | TyArrow (ty1, ty2) ->
      print ~at_level:3 "%t → %t"
        (print_ty ~max_level:2 print_param ty1)
        (print_ty ~max_level:3 print_param ty2)
  | TyTuple [] -> print "unit"
  | TyTuple tys ->
      print ~at_level:2 "%t"
        (Print.print_sequence " × " (print_ty ~max_level:1 print_param) tys)
  | TyPromise ty -> print "⟨%t⟩" (print_ty print_param ty)
  | TyReference ty ->
      print ~at_level:1 "%t ref" (print_ty ~max_level:1 print_param ty)
  | TyBoxed ty ->
      print ~at_level:1 "[%t]" (print_ty ~max_level:1 print_param ty)

let true_print_param ?max_level param ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print "%t" (TyParam.print param)

let rec true_print_ty ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | TyConst c -> print "%t" (Const.print_ty c)
  | TyApply (ty_name, []) -> print "%t" (TyName.print ty_name)
  | TyApply (ty_name, [ ty ]) ->
      print ~at_level:1 "%t %t"
        (print_ty ~max_level:1 TyParam.print ty)
        (TyName.print ty_name)
  | TyApply (ty_name, tys) ->
      print ~at_level:1 "%t %t"
        (Print.print_tuple true_print_ty tys)
        (TyName.print ty_name)
  | TyParam a -> print "%t" (TyParam.print a)
  | TyArrow (ty1, ty2) ->
      print ~at_level:3 "%t → %t"
        (true_print_ty ~max_level:2 ty1)
        (true_print_ty ~max_level:3 ty2)
  | TyTuple [] -> print "unit"
  | TyTuple tys ->
      print ~at_level:2 "%t"
        (Print.print_sequence " × " (true_print_ty ~max_level:1) tys)
  | TyPromise ty -> print "⟨%t⟩" (true_print_ty ty)
  | TyReference ty -> print ~at_level:1 "%t ref" (true_print_ty ~max_level:1 ty)
  | TyBoxed ty -> print ~at_level:1 "[%t]" (true_print_ty ~max_level:1 ty)

let new_print_param () =
  let names = ref TyParamMap.empty in
  let counter = ref 0 in
  let print_param (param : ty_param) ppf =
    let symbol =
      match TyParam.split param with
      | _, Some s -> s
      | _ -> (
          match TyParamMap.find_opt param !names with
          | Some symbol -> symbol
          | None ->
              let symbol = Symbol.type_symbol !counter in
              incr counter;
              names := TyParamMap.add param symbol !names;
              symbol )
    in

    Print.print ppf "%s" symbol
  in
  print_param

let print_ty_scheme (_params, ty) ppf =
  let print_param = new_print_param () in
  Print.print ppf "@[%t@]" (print_ty print_param ty)

let pretty_print_ty ty ppf =
  let print_param = new_print_param () in
  Print.print ppf "@[%t@]" (print_ty print_param ty)

let rec substitute_ty subst = function
  | TyConst _ as ty -> ty
  | TyParam a as ty -> (
      match TyParamMap.find_opt a subst with None -> ty | Some ty' -> ty' )
  | TyApply (ty_name, tys) ->
      TyApply (ty_name, List.map (substitute_ty subst) tys)
  | TyTuple tys -> TyTuple (List.map (substitute_ty subst) tys)
  | TyArrow (ty1, ty2) ->
      TyArrow (substitute_ty subst ty1, substitute_ty subst ty2)
  | TyPromise ty -> TyPromise (substitute_ty subst ty)
  | TyReference ty -> TyReference (substitute_ty subst ty)
  | TyBoxed ty -> TyBoxed (substitute_ty subst ty)

let rec free_vars = function
  | TyConst _ -> TyParamSet.empty
  | TyParam a -> TyParamSet.singleton a
  | TyApply (_, tys) ->
      List.fold_left
        (fun vars ty -> TyParamSet.union vars (free_vars ty))
        TyParamSet.empty tys
  | TyTuple tys ->
      List.fold_left
        (fun vars ty -> TyParamSet.union vars (free_vars ty))
        TyParamSet.empty tys
  | TyArrow (ty1, ty2) -> TyParamSet.union (free_vars ty1) (free_vars ty2)
  | TyPromise ty -> free_vars ty
  | TyReference ty -> free_vars ty
  | TyBoxed ty -> free_vars ty

module Variable = Symbol.Make ()

module Label = Symbol.Make ()

module Operation = Symbol.Make ()

type variable = Variable.t

type label = Label.t

type operation = Operation.t

let nil_label = Label.fresh (Some Syntax.nil_label)

let cons_label = Label.fresh (Some Syntax.cons_label)

type pattern =
  | PVar of variable
  | PAnnotated of pattern * ty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

type expression =
  | Var of variable
  | Const of Const.t
  | Annotated of expression * ty
  | Tuple of expression list
  | Variant of label * expression option
  | Lambda of abstraction
  | RecLambda of variable * abstraction
  | Fulfill of expression
  | Reference of expression ref
  | Boxed of expression

and computation =
  | Return of expression
  | Do of computation * abstraction
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Out of operation * expression * computation
  | In of operation * expression * computation
  | Promise of
      variable option * operation * abstraction * variable * computation
  | Await of expression * abstraction
  | Unbox of expression * abstraction

and abstraction = pattern * computation

module VariableMap = Map.Make (Variable)
module OperationMap = Map.Make (Operation)

let rec remove_pattern_bound_variables subst = function
  | PVar x -> VariableMap.remove x subst
  | PAnnotated (pat, _) -> remove_pattern_bound_variables subst pat
  | PAs (pat, x) ->
      let subst = remove_pattern_bound_variables subst pat in
      VariableMap.remove x subst
  | PTuple pats -> List.fold_left remove_pattern_bound_variables subst pats
  | PVariant (_, None) -> subst
  | PVariant (_, Some pat) -> remove_pattern_bound_variables subst pat
  | PConst _ -> subst
  | PNonbinding -> subst

let rec refresh_pattern = function
  | PVar x ->
      let x' = Variable.refresh x in
      (PVar x', [ (x, x') ])
  | PAnnotated (pat, _) -> refresh_pattern pat
  | PAs (pat, x) ->
      let pat', vars = refresh_pattern pat in
      let x' = Variable.refresh x in
      (PAs (pat', x'), (x, x') :: vars)
  | PTuple pats ->
      let fold pat (pats', vars) =
        let pat', vars' = refresh_pattern pat in
        (pat' :: pats', vars' @ vars)
      in
      let pats', vars = List.fold_right fold pats ([], []) in
      (PTuple pats', vars)
  | PVariant (lbl, Some pat) ->
      let pat', vars = refresh_pattern pat in
      (PVariant (lbl, Some pat'), vars)
  | (PVariant (_, None) | PConst _ | PNonbinding) as pat -> (pat, [])

let rec refresh_expression vars = function
  | Var x as expr -> (
      match List.assoc_opt x vars with None -> expr | Some x' -> Var x' )
  | Const _ as expr -> expr
  | Annotated (expr, ty) -> Annotated (refresh_expression vars expr, ty)
  | Tuple exprs -> Tuple (List.map (refresh_expression vars) exprs)
  | Variant (label, expr) ->
      Variant (label, Option.map (refresh_expression vars) expr)
  | Lambda abs -> Lambda (refresh_abstraction vars abs)
  | RecLambda (x, abs) ->
      let x' = Variable.refresh x in
      RecLambda (x', refresh_abstraction ((x, x') :: vars) abs)
  | Fulfill expr -> Fulfill (refresh_expression vars expr)
  | Reference ref -> Reference ref
  | Boxed expr -> Boxed (refresh_expression vars expr)

and refresh_computation vars = function
  | Return expr -> Return (refresh_expression vars expr)
  | Do (comp, abs) ->
      Do (refresh_computation vars comp, refresh_abstraction vars abs)
  | Match (expr, cases) ->
      Match
        (refresh_expression vars expr, List.map (refresh_abstraction vars) cases)
  | Apply (expr1, expr2) ->
      Apply (refresh_expression vars expr1, refresh_expression vars expr2)
  | Out (op, expr, comp) ->
      Out (op, refresh_expression vars expr, refresh_computation vars comp)
  | In (op, expr, comp) ->
      In (op, refresh_expression vars expr, refresh_computation vars comp)
  | Promise (k, op, abs, p, comp) ->
      let p' = Variable.refresh p in
      let k', vars' =
        match k with
        | None -> (None, vars)
        | Some k'' ->
            let k''' = Variable.refresh k'' in
            (Some k''', (k'', k''') :: vars)
      in
      Promise
        ( k',
          op,
          refresh_abstraction vars' abs,
          p',
          refresh_computation ((p, p') :: vars) comp )
  | Await (expr, abs) ->
      Await (refresh_expression vars expr, refresh_abstraction vars abs)
  | Unbox (expr, abs) ->
      Unbox (refresh_expression vars expr, refresh_abstraction vars abs)

and refresh_abstraction vars (pat, comp) =
  let pat', vars' = refresh_pattern pat in
  (pat', refresh_computation (vars @ vars') comp)

let rec substitute_expression subst = function
  | Var x as expr -> (
      match VariableMap.find_opt x subst with None -> expr | Some expr -> expr )
  | Const _ as expr -> expr
  | Annotated (expr, ty) -> Annotated (substitute_expression subst expr, ty)
  | Tuple exprs -> Tuple (List.map (substitute_expression subst) exprs)
  | Variant (label, expr) ->
      Variant (label, Option.map (substitute_expression subst) expr)
  | Lambda abs -> Lambda (substitute_abstraction subst abs)
  | RecLambda (x, abs) -> RecLambda (x, substitute_abstraction subst abs)
  | Fulfill expr -> Fulfill (substitute_expression subst expr)
  | Reference ref -> Reference ref
  | Boxed expr -> Boxed (substitute_expression subst expr)

and substitute_computation subst = function
  | Return expr -> Return (substitute_expression subst expr)
  | Do (comp, abs) ->
      Do (substitute_computation subst comp, substitute_abstraction subst abs)
  | Match (expr, cases) ->
      Match
        ( substitute_expression subst expr,
          List.map (substitute_abstraction subst) cases )
  | Apply (expr1, expr2) ->
      Apply
        (substitute_expression subst expr1, substitute_expression subst expr2)
  | Out (op, expr, comp) ->
      Out
        (op, substitute_expression subst expr, substitute_computation subst comp)
  | In (op, expr, comp) ->
      In
        (op, substitute_expression subst expr, substitute_computation subst comp)
  | Promise (k, op, abs, p, comp) ->
      let subst' = remove_pattern_bound_variables subst (PVar p) in
      Promise
        ( k,
          op,
          substitute_abstraction subst abs,
          p,
          substitute_computation subst' comp )
  | Await (expr, abs) ->
      Await (substitute_expression subst expr, substitute_abstraction subst abs)
  | Unbox (expr, abs) ->
      Unbox (substitute_expression subst expr, substitute_abstraction subst abs)

and substitute_abstraction subst (pat, comp) =
  let subst' = remove_pattern_bound_variables subst pat in
  (pat, substitute_computation subst' comp)

type process =
  | Run of computation
  | InProc of operation * expression * process
  | OutProc of operation * expression * process

type condition = Done | Ready | Waiting

type id = int

type thread = computation * id * condition

type ty_def = TySum of (label * ty option) list | TyInline of ty

type command =
  | TyDef of (ty_param list * ty_name * ty_def) list
  | Operation of operation * ty
  | TopLet of variable * ty_scheme * expression
  | TopDo of computation

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | PVar x -> print "%t" (Variable.print x)
  | PAs (p, x) -> print "%t as %t" (print_pattern p) (Variable.print x)
  | PAnnotated (p, ty) ->
      let print_param = new_print_param () in
      print "%t : %t" (print_pattern ?max_level p) (print_ty print_param ty)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.print_tuple print_pattern lst ppf
  | PVariant (lbl, None) when lbl = nil_label -> print "[]"
  | PVariant (lbl, None) -> print "%t" (Label.print lbl)
  | PVariant (lbl, Some (PTuple [ v1; v2 ])) when lbl = cons_label ->
      print "%t::%t" (print_pattern v1) (print_pattern v2)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "%t @[<hov>%t@]" (Label.print lbl) (print_pattern p)
  | PNonbinding -> print "_"

let rec print_command ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | TyDef _ -> print "TyDef"
  | Operation _ -> print "Operation"
  | TopLet (_, _, e) -> Format.printf "%t" (print_expression e)
  | TopDo c -> Format.printf "%t" (print_computation c)

and print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e with
  | Var x -> print "%t" (Variable.print x)
  | Const c -> print "%t" (Const.print c)
  | Annotated (t, ty) ->
      let print_param = new_print_param () in
      print "%t : %t" (print_expression ?max_level t) (print_ty print_param ty)
  | Tuple lst -> Print.print_tuple print_expression lst ppf
  | Variant (lbl, None) when lbl = nil_label -> print "[]"
  | Variant (lbl, None) -> print "%t" (Label.print lbl)
  | Variant (lbl, Some (Tuple [ v1; v2 ])) when lbl = cons_label ->
      print ~at_level:1 "%t::%t"
        (print_expression ~max_level:0 v1)
        (print_expression ~max_level:1 v2)
  | Variant (lbl, Some e) ->
      print ~at_level:1 "%t @[<hov>%t@]" (Label.print lbl)
        (print_expression ~max_level:0 e)
  | Lambda a -> print ~at_level:2 "fun %t" (print_abstraction a)
  | RecLambda (f, _a) -> print ~at_level:2 "rec %t ..." (Variable.print f)
  | Fulfill expr -> print "⟨%t⟩" (print_expression expr)
  | Reference r -> print "{ contents = %t }" (print_expression !r)
  | Boxed expr -> print "[%t]" (print_expression expr)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | Return e -> print ~at_level:1 "return %t" (print_expression ~max_level:0 e)
  | Do (c1, (PNonbinding, c2)) ->
      print "@[<hov>%t;@ %t@]" (print_computation c1) (print_computation c2)
  | Do (c1, (pat, c2)) ->
      print "@[<hov>let@[<hov>@ %t =@ %t@] in@ %t@]" (print_pattern pat)
        (print_computation c1) (print_computation c2)
  | Match (e, lst) ->
      print "match %t with (@[<hov>%t@])" (print_expression e)
        (Print.print_sequence " | " case lst)
  | Apply (e1, e2) ->
      print ~at_level:1 "@[%t@ %t@]"
        (print_expression ~max_level:1 e1)
        (print_expression ~max_level:0 e2)
  | In (op, e, c) ->
      print "↓%t(@[<hv>%t,@ %t@])" (Operation.print op) (print_expression e)
        (print_computation c)
  | Out (op, e, c) ->
      print "↑%t(@[<hv>%t,@ %t@])" (Operation.print op) (print_expression e)
        (print_computation c)
  | Promise (None, op, (p1, c1), p2, c2) ->
      print "@[<hv>promise (@[<hov>%t %t ↦@ %t@])@ as %t in@ %t@]"
        (Operation.print op) (print_pattern p1) (print_computation c1)
        (Variable.print p2) (print_computation c2)
  | Promise (Some k, op, (p1, c1), p2, c2) ->
      print "@[<hv>promise (@[<hov>%t %t %t ↦@ %t@])@ as %t in@ %t@]"
        (Operation.print op) (print_pattern p1) (Variable.print k)
        (print_computation c1) (Variable.print p2) (print_computation c2)
  | Await (e, (p, c)) ->
      print "@[<hov>await @[<hov>%t until@ ⟨%t⟩@] in@ %t@]"
        (print_expression e) (print_pattern p) (print_computation c)
  | Unbox (e, (p, c)) ->
      print "%t as @[%t@] in %t" (print_expression e) (print_pattern p)
        (print_computation c)

and print_abstraction (p, c) ppf =
  Format.fprintf ppf "%t ↦ %t" (print_pattern p) (print_computation c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and case a ppf = Format.fprintf ppf "%t" (print_abstraction a)

let rec print_process ?max_level proc ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match proc with
  | Run comp -> print ~at_level:1 "run %t" (print_computation ~max_level:0 comp)
  | InProc (op, expr, proc) ->
      print "↓%t(@[<hv>%t,@ %t@])" (Operation.print op)
        (print_expression expr) (print_process proc)
  | OutProc (op, expr, proc) ->
      print "↑%t(@[<hv>%t,@ %t@])" (Operation.print op)
        (print_expression expr) (print_process proc)

(* let rec print_threads : thread list -> unit = function
   | [] -> ()
   | (c, id, _) :: ts ->
      Format.printf "thread id=%i %t@." id (print_computation c);
      print_threads ts *)

let string_of_operation op =
  Operation.print op Format.str_formatter;
  Format.flush_str_formatter ()

let string_of_expression e =
  print_expression e Format.str_formatter;
  Format.flush_str_formatter ()

let string_of_computation c =
  print_computation c Format.str_formatter;
  Format.flush_str_formatter ()

let string_of_process proc =
  print_process proc Format.str_formatter;
  Format.flush_str_formatter ()

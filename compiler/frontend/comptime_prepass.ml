[@@@warning "-45"]

open Ast_helper
open Ast_mapper
open Asttypes
open Longident
open Parsetree

module StringMap = Map.Make (String)

type resolved_type =
  | Type_string
  | Type_int
  | Type_float
  | Type_bool
  | Type_json
  | Type_option of resolved_type
  | Type_array of resolved_type
  | Type_record of string * resolved_field list

and resolved_field = {field_name: string; field_type: resolved_type}

type value =
  | VUnit
  | VInt of int
  | VFloat of float
  | VString of string
  | VBool of bool
  | VArray of value list
  | VTuple of value list
  | VRecord of value StringMap.t
  | VVariant of string * value option
  | VClosure of closure
  | VBuiltin of builtin
  | VCode of expression

and closure = {
  pattern: pattern;
  body: expression;
  env: value StringMap.t;
  closure_newtypes: core_type StringMap.t;
}

and builtin = {arity: int; apply: context -> Location.t -> value list -> value}

and binding = {expression: expression; is_comptime_binding: bool}

and context = {
  type_decls: type_declaration StringMap.t;
  bindings: binding StringMap.t;
  target_type: core_type option;
  newtypes: core_type StringMap.t;
}

let errorf ~loc fmt =
  Format.kasprintf (fun message -> Location.raise_errorf ~loc "%s" message) fmt

let lid txt = Location.mknoloc (Lident txt)

let exp_ident txt = Exp.ident (lid txt)

let exp_string s = Exp.constant (Const.string s)

let exp_int i = Exp.constant (Const.int i)

let exp_float f = Exp.constant (Const.float (string_of_float f))

let exp_bool b = Exp.construct (lid (if b then "true" else "false")) None

let exp_none () = Exp.construct (lid "None") None

let exp_some expr = Exp.construct (lid "Some") (Some expr)

let pat_var txt = Pat.var (Location.mknoloc txt)

let pat_any () = Pat.any ()

let pat_none () = Pat.construct (lid "None") None

let pat_some pat = Pat.construct (lid "Some") (Some pat)

let longident_last = function
  | Lident name -> name
  | Ldot (_, name) -> name
  | Lapply _ -> ""

let rec core_type_mentions_comptime (ct : core_type) =
  match ct.ptyp_desc with
  | Ptyp_any | Ptyp_var _ -> false
  | Ptyp_arrow {arg = {typ = a; _}; ret = b; _} ->
    core_type_mentions_comptime a || core_type_mentions_comptime b
  | Ptyp_tuple tys -> List.exists core_type_mentions_comptime tys
  | Ptyp_constr ({txt; _}, args) ->
    let last = longident_last txt in
    last = "Code" || last = "TypeDesc"
    || List.exists core_type_mentions_comptime args
  | Ptyp_alias (ct, _) | Ptyp_poly (_, ct) -> core_type_mentions_comptime ct
  | Ptyp_package _ | Ptyp_object _ | Ptyp_variant _ | Ptyp_extension _ -> false

let rec expr_mentions_comptime (expr : expression) =
  match expr.pexp_desc with
  | Pexp_ident {txt = Lident "reflect"; _}
  | Pexp_ident {txt = Lident "compileError"; _}
  | Pexp_ident {txt = Ldot (Lident "Code", _); _}
  | Pexp_ident {txt = Ldot (Lident "Comptime", _); _} ->
    true
  | Pexp_extension ({txt; _}, _) ->
    txt = "comptime" || txt = "quote" || txt = "splice"
  | Pexp_constant _ | Pexp_ident _ -> false
  | Pexp_let (_, bindings, body) ->
    List.exists
      (fun vb ->
        pattern_mentions_comptime vb.pvb_pat
        || expr_mentions_comptime vb.pvb_expr)
      bindings
    || expr_mentions_comptime body
  | Pexp_fun {default; lhs = pat; rhs = body; _} ->
    Option.fold ~none:false ~some:expr_mentions_comptime default
    || pattern_mentions_comptime pat
    || expr_mentions_comptime body
  | Pexp_apply {funct = fn; args; _} ->
    expr_mentions_comptime fn
    || List.exists (fun (_, arg) -> expr_mentions_comptime arg) args
  | Pexp_match (expr, cases) | Pexp_try (expr, cases) ->
    expr_mentions_comptime expr
    || List.exists
         (fun case ->
           pattern_mentions_comptime case.pc_lhs
           || Option.fold ~none:false ~some:expr_mentions_comptime case.pc_guard
           || expr_mentions_comptime case.pc_rhs)
         cases
  | Pexp_tuple exprs | Pexp_array exprs ->
    List.exists expr_mentions_comptime exprs
  | Pexp_construct (_, payload) | Pexp_variant (_, payload) ->
    Option.fold ~none:false ~some:expr_mentions_comptime payload
  | Pexp_record (fields, default) ->
    List.exists (fun field -> expr_mentions_comptime field.x) fields
    || Option.fold ~none:false ~some:expr_mentions_comptime default
  | Pexp_ifthenelse (a, b, c) ->
    expr_mentions_comptime a || expr_mentions_comptime b
    || Option.fold ~none:false ~some:expr_mentions_comptime c
  | Pexp_field (expr, _) -> expr_mentions_comptime expr
  | Pexp_setfield (expr, _, value) ->
    expr_mentions_comptime expr || expr_mentions_comptime value
  | Pexp_send (expr, _) -> expr_mentions_comptime expr
  | Pexp_newtype (_, expr)
  | Pexp_sequence (expr, _)
  | Pexp_constraint (expr, _)
  | Pexp_assert expr
  | Pexp_open (_, _, expr) ->
    expr_mentions_comptime expr
  | Pexp_coerce (expr, (), b) ->
    expr_mentions_comptime expr || core_type_mentions_comptime b
  | Pexp_while (a, b) -> expr_mentions_comptime a || expr_mentions_comptime b
  | Pexp_for (_, start, finish, _, body) ->
    expr_mentions_comptime start
    || expr_mentions_comptime finish
    || expr_mentions_comptime body
  | Pexp_pack _ | Pexp_letmodule _ | Pexp_letexception _ | Pexp_await _
  | Pexp_jsx_element _ ->
    false

and pattern_mentions_comptime (pat : pattern) =
  match pat.ppat_desc with
  | Ppat_constraint (pat, ct) ->
    pattern_mentions_comptime pat || core_type_mentions_comptime ct
  | Ppat_tuple pats -> List.exists pattern_mentions_comptime pats
  | Ppat_record (fields, _) ->
    List.exists (fun field -> pattern_mentions_comptime field.x) fields
  | Ppat_construct (_, arg) ->
    Option.fold ~none:false ~some:pattern_mentions_comptime arg
  | Ppat_alias (pat, _) -> pattern_mentions_comptime pat
  | _ -> false

let is_comptime_open = function
  | {pstr_desc = Pstr_open {popen_lid = {txt = Lident "Comptime"; _}; _}; _} ->
    true
  | _ -> false

let expr_payload_single ~loc payload =
  match payload with
  | PStr [{pstr_desc = Pstr_eval (expr, _); _}] -> expr
  | _ -> errorf ~loc "Expected a single expression payload"

let rec binding_name_from_pattern pat =
  match pat.ppat_desc with
  | Ppat_var {txt; _} -> Some txt
  | Ppat_constraint (pat, _) | Ppat_alias (pat, _) ->
    binding_name_from_pattern pat
  | _ -> None

let rec pattern_constraint pat =
  match pat.ppat_desc with
  | Ppat_constraint (_, ct) -> Some ct
  | Ppat_alias (pat, _) -> pattern_constraint pat
  | _ -> None

let collect_type_decls structure =
  List.fold_left
    (fun acc item ->
      match item.pstr_desc with
      | Pstr_type (_, decls) ->
        List.fold_left
          (fun acc decl -> StringMap.add decl.ptype_name.txt decl acc)
          acc decls
      | _ -> acc)
    StringMap.empty structure

let collect_bindings structure =
  List.fold_left
    (fun acc item ->
      match item.pstr_desc with
      | Pstr_value (_, bindings) ->
        List.fold_left
          (fun acc vb ->
            match binding_name_from_pattern vb.pvb_pat with
            | None -> acc
            | Some name ->
              let is_comptime_binding =
                expr_mentions_comptime vb.pvb_expr
                || pattern_mentions_comptime vb.pvb_pat
              in
              StringMap.add name
                {expression = vb.pvb_expr; is_comptime_binding}
                acc)
          acc bindings
      | _ -> acc)
    StringMap.empty structure

let rec substitute_newtypes_in_core_type newtypes ct =
  match ct.ptyp_desc with
  | Ptyp_constr ({txt = Lident name; _}, []) -> (
    match StringMap.find_opt name newtypes with
    | Some replacement -> replacement
    | None -> ct)
  | Ptyp_arrow {arg = {attrs; lbl; typ = a}; ret = b; arity} ->
    {
      ct with
      ptyp_desc =
        Ptyp_arrow
          {
            arg = {attrs; lbl; typ = substitute_newtypes_in_core_type newtypes a};
            ret = substitute_newtypes_in_core_type newtypes b;
            arity;
          };
    }
  | Ptyp_tuple tys ->
    {
      ct with
      ptyp_desc =
        Ptyp_tuple (List.map (substitute_newtypes_in_core_type newtypes) tys);
    }
  | Ptyp_constr (lid, args) ->
    {
      ct with
      ptyp_desc =
        Ptyp_constr
          (lid, List.map (substitute_newtypes_in_core_type newtypes) args);
    }
  | Ptyp_alias (ct, name) ->
    {
      ct with
      ptyp_desc = Ptyp_alias (substitute_newtypes_in_core_type newtypes ct, name);
    }
  | Ptyp_poly (vars, ct) ->
    {
      ct with
      ptyp_desc = Ptyp_poly (vars, substitute_newtypes_in_core_type newtypes ct);
    }
  | _ -> ct

let substitute_newtypes_in_expr newtypes expr =
  let mapper =
    {
      default_mapper with
      typ =
        (fun self ct ->
          default_mapper.typ self (substitute_newtypes_in_core_type newtypes ct));
    }
  in
  mapper.expr mapper expr

let rec resolve_type context visited (ct : core_type) =
  match ct.ptyp_desc with
  | Ptyp_constr ({txt = Lident "string"; _}, []) -> Type_string
  | Ptyp_constr ({txt = Lident "int"; _}, []) -> Type_int
  | Ptyp_constr ({txt = Lident "float"; _}, []) -> Type_float
  | Ptyp_constr ({txt = Lident "bool"; _}, []) -> Type_bool
  | Ptyp_constr ({txt = Ldot (Lident "JSON", "t"); _}, []) -> Type_json
  | Ptyp_constr ({txt = Lident "option"; _}, [inner]) ->
    Type_option (resolve_type context visited inner)
  | Ptyp_constr ({txt = Lident "array"; _}, [inner]) ->
    Type_array (resolve_type context visited inner)
  | Ptyp_constr ({txt = Lident name; _}, []) -> (
    match StringMap.find_opt name context.newtypes with
    | Some resolved -> resolve_type context visited resolved
    | None -> (
      match StringMap.find_opt name context.type_decls with
      | None ->
        errorf ~loc:ct.ptyp_loc "Unsupported type `%s` in comptime reflection"
          name
      | Some decl -> (
        if List.mem name visited then
          errorf ~loc:ct.ptyp_loc
            "Recursive types are not supported in comptime reflection"
        else if decl.ptype_params <> [] then
          errorf ~loc:decl.ptype_loc
            "Generic types are not supported in comptime reflection"
        else
          match decl.ptype_kind with
          | Ptype_record labels ->
            Type_record
              ( decl.ptype_name.txt,
                List.map
                  (fun label ->
                    {
                      field_name = label.pld_name.txt;
                      field_type =
                        resolve_type context (name :: visited) label.pld_type;
                    })
                  labels )
          | Ptype_abstract -> (
            match decl.ptype_manifest with
            | Some manifest -> resolve_type context (name :: visited) manifest
            | None ->
              errorf ~loc:decl.ptype_loc
                "Abstract types are not supported in comptime reflection")
          | Ptype_variant _ ->
            errorf ~loc:decl.ptype_loc
              "Variant types are not supported in comptime reflection"
          | Ptype_open ->
            errorf ~loc:decl.ptype_loc
              "Open types are not supported in comptime reflection")))
  | _ -> errorf ~loc:ct.ptyp_loc "Unsupported type shape in comptime reflection"

let rec type_desc_value_of_resolved_type resolved =
  match resolved with
  | Type_string -> VVariant ("String", None)
  | Type_int -> VVariant ("Int", None)
  | Type_float -> VVariant ("Float", None)
  | Type_bool -> VVariant ("Bool", None)
  | Type_json -> VVariant ("Json", None)
  | Type_option inner ->
    VVariant ("Option", Some (type_desc_value_of_resolved_type inner))
  | Type_array inner ->
    VVariant ("Array", Some (type_desc_value_of_resolved_type inner))
  | Type_record (name, fields) ->
    let fields_value =
      VArray
        (List.map
           (fun field ->
             let map = StringMap.empty in
             let map = StringMap.add "name" (VString field.field_name) map in
             let map =
               StringMap.add "typ"
                 (type_desc_value_of_resolved_type field.field_type)
                 map
             in
             let map = StringMap.add "optional" (VBool false) map in
             let map = StringMap.add "mutable_" (VBool false) map in
             let map =
               StringMap.add "get"
                 (VBuiltin
                    {
                      arity = 1;
                      apply =
                        (fun _context _loc args ->
                          match args with
                          | [VCode expr] ->
                            VCode
                              (Exp.field expr
                                 (Location.mknoloc (Lident field.field_name)))
                          | _ ->
                            errorf ~loc:Location.none
                              "field.get expects a quoted expression");
                    })
                 map
             in
             VRecord map)
           fields)
    in
    VVariant
      ( "Record",
        Some
          (VRecord
             (StringMap.empty
             |> StringMap.add "name" (VString name)
             |> StringMap.add "fields" fields_value)) )

let value_to_expr ~loc = function
  | VUnit -> Exp.construct ~loc (lid "()") None
  | VInt i -> exp_int i
  | VFloat f -> exp_float f
  | VString s -> exp_string s
  | VBool b -> exp_bool b
  | VCode expr -> expr
  | _ ->
    errorf ~loc "Expected a comptime value that can be reified as an expression"

let rec match_pattern ~loc pat value =
  match (pat.ppat_desc, value) with
  | Ppat_any, _ -> Some StringMap.empty
  | Ppat_var {txt; _}, value -> Some (StringMap.singleton txt value)
  | Ppat_constraint (pat, _), value | Ppat_alias (pat, _), value ->
    match_pattern ~loc pat value
  | Ppat_construct ({txt = Lident "()"; _}, None), VUnit -> Some StringMap.empty
  | Ppat_tuple pats, VTuple values when List.length pats = List.length values ->
    match_patterns ~loc pats values
  | Ppat_record (fields, _), VRecord record ->
    List.fold_left
      (fun acc field ->
        match (acc, field.lid.txt) with
        | None, _ -> None
        | _, Ldot _ | _, Lapply _ -> None
        | Some env, Lident label -> (
          match StringMap.find_opt label record with
          | None -> None
          | Some value -> merge_envs env (match_pattern ~loc field.x value)))
      (Some StringMap.empty) fields
  | Ppat_construct ({txt; _}, arg), VVariant (name, payload)
    when longident_last txt = name -> (
    match (arg, payload) with
    | None, None -> Some StringMap.empty
    | Some pat, Some value -> match_pattern ~loc pat value
    | _ -> None)
  | Ppat_constant (Pconst_integer (text, _)), VInt value ->
    if int_of_string text = value then Some StringMap.empty else None
  | Ppat_constant (Pconst_string (text, _)), VString value ->
    if text = value then Some StringMap.empty else None
  | Ppat_constant (Pconst_float (text, _)), VFloat value ->
    if float_of_string text = value then Some StringMap.empty else None
  | _ -> None

and match_patterns ~loc pats values =
  List.fold_left2
    (fun acc pat value ->
      match acc with
      | None -> None
      | Some env -> merge_envs env (match_pattern ~loc pat value))
    (Some StringMap.empty) pats values

and merge_envs left right =
  match right with
  | None -> None
  | Some right ->
    Some (StringMap.union (fun _ _ value -> Some value) left right)

let builtin arity fn = VBuiltin {arity; apply = fn}

let rec eval context env expr =
  match expr.pexp_desc with
  | Pexp_constant (Pconst_integer (text, _)) -> VInt (int_of_string text)
  | Pexp_constant (Pconst_float (text, _)) -> VFloat (float_of_string text)
  | Pexp_constant (Pconst_string (text, _)) -> VString text
  | Pexp_construct ({txt = Lident "()"; _}, None) -> VUnit
  | Pexp_construct ({txt = Lident "true"; _}, None) -> VBool true
  | Pexp_construct ({txt = Lident "false"; _}, None) -> VBool false
  | Pexp_construct ({txt = Lident "Some"; _}, Some value) ->
    VVariant ("Some", Some (eval context env value))
  | Pexp_construct ({txt = Lident "None"; _}, None) -> VVariant ("None", None)
  | Pexp_tuple exprs -> VTuple (List.map (eval context env) exprs)
  | Pexp_array exprs -> VArray (List.map (eval context env) exprs)
  | Pexp_constraint (expr, _) -> eval context env expr
  | Pexp_newtype (name, expr) ->
    let newtypes =
      match context.target_type with
      | Some target -> StringMap.add name.txt target context.newtypes
      | None -> context.newtypes
    in
    eval {context with newtypes} env expr
  | Pexp_ident {txt = Lident "reflect"; _}
  | Pexp_ident {txt = Ldot (Lident "Comptime", "reflect"); _} ->
    builtin 1 (fun context loc args ->
        match args with
        | [VUnit] -> (
          match context.target_type with
          | None ->
            errorf ~loc
              "reflect() requires a call site type annotation that identifies \
               the reflected type"
          | Some target ->
            type_desc_value_of_resolved_type (resolve_type context [] target))
        | _ -> errorf ~loc "reflect() expects unit")
  | Pexp_ident {txt = Lident "compileError"; _}
  | Pexp_ident {txt = Ldot (Lident "Comptime", "compileError"); _} ->
    builtin 1 (fun _context loc args ->
        match args with
        | [VString message] -> errorf ~loc "%s" message
        | _ -> errorf ~loc "compileError expects a string")
  | Pexp_ident {txt = Lident "+"; _} ->
    builtin 2 (fun _context loc args ->
        match args with
        | [VInt left; VInt right] -> VInt (left + right)
        | _ -> errorf ~loc "`+` expects two ints during comptime evaluation")
  | Pexp_ident {txt = Lident "++"; _} ->
    builtin 2 (fun _context loc args ->
        match args with
        | [VString left; VString right] -> VString (left ^ right)
        | _ -> errorf ~loc "`++` expects two strings during comptime evaluation")
  | Pexp_ident {txt = Ldot (Lident "Code", "dict"); _} ->
    builtin 1 (fun _context loc args ->
        match args with
        | [VArray rows] ->
          let entries =
            List.map
              (function
                | VTuple [VString key; VCode value] ->
                  Exp.tuple [exp_string key; value]
                | _ ->
                  errorf ~loc
                    "Code.dict expects an array of (string, quotedExpression) \
                     pairs")
              rows
          in
          VCode
            (Exp.apply
               (Exp.ident
                  (Location.mknoloc (Ldot (Lident "Primitive_dict", "make"))))
               [(Nolabel, Exp.array entries)])
        | _ -> errorf ~loc "Code.dict expects a single array argument")
  | Pexp_ident {txt = Ldot (Lident "Code", "recordOption"); _} ->
    builtin 2 (fun _context loc args ->
        match args with
        | [VString _name; VArray rows] ->
          let names_and_codes =
            List.mapi
              (fun index row ->
                match row with
                | VTuple [VString field_name; VCode code] ->
                  (field_name, code, "field_" ^ string_of_int index)
                | _ ->
                  errorf ~loc
                    "Code.recordOption expects an array of (string, \
                     quotedExpression) pairs")
              rows
          in
          let tuple_expr =
            Exp.tuple (List.map (fun (_, code, _) -> code) names_and_codes)
          in
          let success_pattern =
            Pat.tuple
              (List.map
                 (fun (_, _, var_name) -> pat_some (pat_var var_name))
                 names_and_codes)
          in
          let success_record =
            Exp.record
              (List.map
                 (fun (field_name, _, var_name) ->
                   {
                     lid = Location.mknoloc (Lident field_name);
                     x = exp_ident var_name;
                     opt = false;
                   })
                 names_and_codes)
              None
          in
          let success_case =
            Exp.case success_pattern (exp_some success_record)
          in
          let fallback_case = Exp.case (pat_any ()) (exp_none ()) in
          VCode (Exp.match_ tuple_expr [success_case; fallback_case])
        | _ -> errorf ~loc "Code.recordOption expects two arguments")
  | Pexp_ident {txt = Ldot (Lident "Array", "map"); _} ->
    builtin 2 (fun context loc args ->
        match args with
        | [VArray values; fn] ->
          VArray (List.map (fun value -> apply context ~loc fn [value]) values)
        | _ -> errorf ~loc "Array.map expects an array and a function")
  | Pexp_ident {txt = Ldot (Lident "Int", "toFloat"); _} ->
    builtin 1 (fun _context loc args ->
        match args with
        | [VInt value] -> VFloat (float_of_int value)
        | _ -> errorf ~loc "Int.toFloat expects an int")
  | Pexp_ident {txt = Ldot (Lident "Float", "toInt"); _} ->
    builtin 1 (fun _context loc args ->
        match args with
        | [VFloat value] -> VInt (int_of_float value)
        | _ -> errorf ~loc "Float.toInt expects a float")
  | Pexp_ident {txt = Lident name; _} -> (
    match StringMap.find_opt name env with
    | Some value -> value
    | None -> eval_identifier context name expr.pexp_loc)
  | Pexp_fun {default; lhs = pattern; rhs = body; _} ->
    Option.iter
      (fun _ ->
        errorf ~loc:expr.pexp_loc
          "Optional arguments are not supported in comptime evaluation")
      default;
    VClosure {pattern; body; env; closure_newtypes = context.newtypes}
  | Pexp_apply {funct = fn; args; _} ->
    let fn = eval context env fn in
    let args = List.map (fun (_, arg) -> eval context env arg) args in
    apply context ~loc:expr.pexp_loc fn args
  | Pexp_let (Nonrecursive, bindings, body) ->
    let env =
      List.fold_left
        (fun env binding ->
          let value = eval context env binding.pvb_expr in
          match
            match_pattern ~loc:binding.pvb_pat.ppat_loc binding.pvb_pat value
          with
          | None ->
            errorf ~loc:binding.pvb_pat.ppat_loc
              "Failed to bind a comptime let-pattern"
          | Some bindings ->
            StringMap.union (fun _ value _ -> Some value) bindings env)
        env bindings
    in
    eval context env body
  | Pexp_match (scrutinee, cases) ->
    let scrutinee = eval context env scrutinee in
    eval_case_list context env expr.pexp_loc scrutinee cases
  | Pexp_ifthenelse (condition, when_true, when_false) -> (
    match eval context env condition with
    | VBool true -> eval context env when_true
    | VBool false -> (
      match when_false with
      | Some when_false -> eval context env when_false
      | None -> VUnit)
    | _ ->
      errorf ~loc:condition.pexp_loc
        "if conditions in comptime evaluation must be booleans")
  | Pexp_field (record_expr, {txt; loc}) -> (
    match (eval context env record_expr, txt) with
    | VRecord record, Lident label -> (
      match StringMap.find_opt label record with
      | Some value -> value
      | None -> errorf ~loc "Unknown comptime field `%s`" label)
    | _ ->
      errorf ~loc
        "Field access in comptime evaluation expects a reflected record value")
  | Pexp_extension ({txt = "quote"; loc; _}, payload) ->
    let quoted = expr_payload_single ~loc payload in
    VCode (quote_expression context env quoted)
  | _ ->
    errorf ~loc:expr.pexp_loc "Unsupported expression in comptime evaluation"

and eval_identifier context name loc =
  match StringMap.find_opt name context.bindings with
  | Some binding -> eval context StringMap.empty binding.expression
  | None ->
    errorf ~loc "Unknown identifier `%s` during comptime evaluation" name

and apply context ~loc fn args =
  match fn with
  | VBuiltin builtin ->
    if List.length args <> builtin.arity then
      errorf ~loc "Unexpected comptime builtin arity"
    else builtin.apply context loc args
  | VClosure closure -> (
    match args with
    | [] -> fn
    | [arg] -> (
      match match_pattern ~loc closure.pattern arg with
      | None -> errorf ~loc "Failed to apply comptime function"
      | Some bindings ->
        let env =
          StringMap.union (fun _ value _ -> Some value) bindings closure.env
        in
        eval {context with newtypes = closure.closure_newtypes} env closure.body
      )
    | arg :: rest ->
      let partially_applied = apply context ~loc fn [arg] in
      apply context ~loc partially_applied rest)
  | _ -> errorf ~loc "Expected a function during comptime evaluation"

and eval_case_list context env loc scrutinee cases =
  match cases with
  | [] -> errorf ~loc "Non-exhaustive comptime switch"
  | case :: rest -> (
    match match_pattern ~loc:case.pc_lhs.ppat_loc case.pc_lhs scrutinee with
    | None -> eval_case_list context env loc scrutinee rest
    | Some bindings ->
      let env = StringMap.union (fun _ value _ -> Some value) bindings env in
      let guard_ok =
        match case.pc_guard with
        | None -> true
        | Some guard -> (
          match eval context env guard with
          | VBool result -> result
          | _ ->
            errorf ~loc:guard.pexp_loc
              "Comptime guard expressions must evaluate to bool")
      in
      if guard_ok then eval context env case.pc_rhs
      else eval_case_list context env loc scrutinee rest)

and quote_expression context env expr =
  let inline_constant expr =
    match expr.pexp_desc with
    | Pexp_ident {txt = Lident name; _} -> (
      match StringMap.find_opt name env with
      | Some (VString value) -> Some (exp_string value)
      | Some (VInt value) -> Some (exp_int value)
      | Some (VFloat value) -> Some (exp_float value)
      | Some (VBool value) -> Some (exp_bool value)
      | _ -> None)
    | Pexp_field
        ( {pexp_desc = Pexp_ident {txt = Lident name; _}; _},
          {txt = Lident label; _} ) -> (
      match StringMap.find_opt name env with
      | Some (VRecord record) -> (
        match StringMap.find_opt label record with
        | Some (VString value) -> Some (exp_string value)
        | Some (VInt value) -> Some (exp_int value)
        | Some (VFloat value) -> Some (exp_float value)
        | Some (VBool value) -> Some (exp_bool value)
        | _ -> None)
      | _ -> None)
    | _ -> None
  in
  let mapper =
    {
      default_mapper with
      expr =
        (fun self expr ->
          match expr.pexp_desc with
          | Pexp_extension ({txt = "splice"; loc; _}, payload) ->
            let expr = expr_payload_single ~loc payload in
            let value = eval context env expr in
            let quoted =
              match value with
              | VCode expr -> expr
              | _ -> errorf ~loc "%%splice expects a quoted code value"
            in
            substitute_newtypes_in_expr context.newtypes quoted
          | _ -> (
            match inline_constant expr with
            | Some constant -> constant
            | None -> default_mapper.expr self expr));
      typ =
        (fun self ct ->
          default_mapper.typ self
            (substitute_newtypes_in_core_type context.newtypes ct));
    }
  in
  mapper.expr mapper expr

let extract_target_type_from_expected ~loc:_ expected =
  match expected.ptyp_desc with
  | Ptyp_arrow {arg = {typ = domain; _}; ret = codomain; _} -> (
    match codomain.ptyp_desc with
    | Ptyp_constr ({txt = Ldot (Lident "JSON", "t"); _}, []) -> Some domain
    | Ptyp_constr ({txt = Lident "option"; _}, [inner]) -> (
      match domain.ptyp_desc with
      | Ptyp_constr ({txt = Ldot (Lident "JSON", "t"); _}, []) -> Some inner
      | _ -> None)
    | _ -> None)
  | _ -> None

let rewrite_comptime_binding context vb =
  match vb.pvb_expr.pexp_desc with
  | Pexp_extension ({txt = "comptime"; loc; _}, payload) ->
    let comptime_expr = expr_payload_single ~loc payload in
    let expected_type = pattern_constraint vb.pvb_pat in
    let target_type =
      match expected_type with
      | None -> None
      | Some expected -> extract_target_type_from_expected ~loc expected
    in
    let value =
      eval
        {context with target_type; newtypes = StringMap.empty}
        StringMap.empty comptime_expr
    in
    let expression =
      match value with
      | VCode expression -> expression
      | value -> value_to_expr ~loc value
    in
    {vb with pvb_expr = expression}
  | _ -> vb

let expression_has_extension names expr =
  let found = ref false in
  let iterator =
    {
      Ast_iterator.default_iterator with
      expr =
        (fun self expr ->
          (match expr.pexp_desc with
          | Pexp_extension ({txt; _}, _) when List.mem txt names ->
            found := true
          | _ -> ());
          Ast_iterator.default_iterator.expr self expr);
    }
  in
  iterator.expr iterator expr;
  !found

let assert_no_remaining_extensions structure =
  List.iter
    (fun item ->
      match item.pstr_desc with
      | Pstr_value (_, bindings) ->
        List.iter
          (fun vb ->
            if
              expression_has_extension
                ["comptime"; "quote"; "splice"]
                vb.pvb_expr
            then
              errorf ~loc:vb.pvb_expr.pexp_loc
                "Unexpected comptime extension after comptime rewriting")
          bindings
      | _ -> ())
    structure

let rewrite (ast : structure) : structure =
  let type_decls = collect_type_decls ast in
  let bindings = collect_bindings ast in
  let context =
    {type_decls; bindings; target_type = None; newtypes = StringMap.empty}
  in
  let ast =
    List.filter_map
      (fun item ->
        if is_comptime_open item then None
        else
          match item.pstr_desc with
          | Pstr_value (rec_flag, bindings) ->
            let rewritten =
              List.map
                (fun vb ->
                  let is_call_site =
                    match vb.pvb_expr.pexp_desc with
                    | Pexp_extension ({txt = "comptime"; _}, _) -> true
                    | _ -> false
                  in
                  (rewrite_comptime_binding context vb, is_call_site))
                bindings
            in
            let keep =
              List.filter
                (fun (vb, is_call_site) ->
                  match binding_name_from_pattern vb.pvb_pat with
                  | None -> true
                  | Some name -> (
                    match StringMap.find_opt name context.bindings with
                    | Some binding ->
                      is_call_site || not binding.is_comptime_binding
                    | None -> true))
                rewritten
            in
            let keep = List.map fst keep in
            if keep = [] then None
            else Some {item with pstr_desc = Pstr_value (rec_flag, keep)}
          | _ -> Some item)
      ast
  in
  assert_no_remaining_extensions ast;
  ast

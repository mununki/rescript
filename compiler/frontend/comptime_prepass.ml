[@@@warning "-45"]

open Ast_helper
open Ast_mapper
open Asttypes
open Longident
open Parsetree

module StringMap = Map.Make (String)

let comptime_splice_field_label = "__rescript_comptime_splice_field__"
let comptime_splice_rows_label = "__rescript_comptime_splice_rows__"
let gensym_counter = ref 0

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
  | VBuilder of (string * expression) list ref
  | VRecordFields of expression record_element list
  | VCode of expression

and closure = {
  pattern: pattern;
  body: expression;
  env: value StringMap.t ref;
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

let substitute_newtypes_in_pattern newtypes pat =
  let mapper =
    {
      default_mapper with
      typ =
        (fun self ct ->
          default_mapper.typ self (substitute_newtypes_in_core_type newtypes ct));
    }
  in
  mapper.pat mapper pat

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

let field_constructor_name_of_resolved_type = function
  | Type_string -> "StringField"
  | Type_int -> "IntField"
  | Type_float -> "FloatField"
  | Type_bool -> "BoolField"
  | Type_json -> "JsonField"
  | Type_option _ -> "OptionField"
  | Type_array _ -> "ArrayField"
  | Type_record _ -> "RecordField"

let field_get_builtin field_name =
  VBuiltin
    {
      arity = 1;
      apply =
        (fun _context loc args ->
          match args with
          | [VCode expr] ->
            VCode (Exp.field expr (Location.mknoloc (Lident field_name)))
          | _ ->
            errorf ~loc
              "Reflected field getter expects a runtime record expression");
    }

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
             let payload =
               VRecord
                 (StringMap.empty
                 |> StringMap.add "name" (VString field.field_name)
                 |> StringMap.add "get" (field_get_builtin field.field_name))
             in
             VVariant
               ( field_constructor_name_of_resolved_type field.field_type,
                 Some payload ))
           fields)
    in
    VVariant
      ( "Record",
        Some
          (VRecord
             (StringMap.empty
             |> StringMap.add "name" (VString name)
             |> StringMap.add "fields" fields_value)) )

let builder_entries_set builder field_name value_expr =
  let rec loop acc = function
    | [] -> List.rev ((field_name, value_expr) :: acc)
    | (name, _) :: rest when name = field_name ->
      List.rev_append acc ((field_name, value_expr) :: rest)
    | entry :: rest -> loop (entry :: acc) rest
  in
  builder := loop [] !builder

let resolve_builder_field_name ~loc = function
  | VString field_name -> field_name
  | VRecord field -> (
    match StringMap.find_opt "name" field with
    | Some (VString field_name) -> field_name
    | _ ->
      errorf ~loc
        "Dict.set on a comptime builder expects a compile-time string or \
         reflected field descriptor")
  | VVariant (_, Some (VRecord field)) -> (
    match StringMap.find_opt "name" field with
    | Some (VString field_name) -> field_name
    | _ ->
      errorf ~loc
        "Dict.set on a comptime builder expects a compile-time string or \
         reflected field descriptor")
  | _ ->
    errorf ~loc
      "Dict.set on a comptime builder expects a compile-time string or \
       reflected field descriptor"

let expected_type_of_some_payload = function
  | {ptyp_desc = Ptyp_constr ({txt = Lident "option"; _}, [inner]); _} ->
    Some inner
  | _ -> None

let rec expr_of_value ~loc ?expected_type context = function
  | VUnit -> Exp.construct ~loc (lid "()") None
  | VInt i -> exp_int i
  | VFloat f -> exp_float f
  | VString s -> exp_string s
  | VBool b -> exp_bool b
  | VVariant ("None", None) -> exp_none ()
  | VVariant ("Some", Some value) ->
    let payload_expected =
      match expected_type with
      | Some expected -> expected_type_of_some_payload expected
      | None -> None
    in
    exp_some (expr_of_value ~loc ?expected_type:payload_expected context value)
  | VCode expr -> expr
  | VBuilder builder -> (
    let entries = !builder in
    match expected_type with
    | Some expected -> (
      match resolve_type context [] expected with
      | Type_record (_name, fields) ->
        let find_entry field_name =
          List.find_opt (fun (name, _) -> name = field_name) entries
        in
        let rows =
          List.map
            (fun field ->
              match find_entry field.field_name with
              | Some (_, expr) ->
                {
                  lid = Location.mknoloc (Lident field.field_name);
                  x = expr;
                  opt = false;
                }
              | None ->
                errorf ~loc "Missing field `%s` in comptime record construction"
                  field.field_name)
            fields
        in
        Exp.record rows None
      | _ ->
        let tuple_entries =
          List.map
            (fun (name, expr) -> Exp.tuple [exp_string name; expr])
            entries
        in
        Exp.apply
          (Exp.ident (Location.mknoloc (Ldot (Lident "Dict", "fromArray"))))
          [(Nolabel, Exp.array tuple_entries)])
    | None ->
      let tuple_entries =
        List.map (fun (name, expr) -> Exp.tuple [exp_string name; expr]) entries
      in
      Exp.apply
        (Exp.ident (Location.mknoloc (Ldot (Lident "Dict", "fromArray"))))
        [(Nolabel, Exp.array tuple_entries)])
  | _ ->
    errorf ~loc "Expected a comptime value that can be reified as an expression"

let value_to_expr ~loc context value = expr_of_value ~loc context value

let value_to_expr_with_expected ~loc context expected_type value =
  expr_of_value ~loc ~expected_type context value

let expected_function_codomain = function
  | Some {ptyp_desc = Ptyp_arrow {ret; _}; _} -> Some ret
  | _ -> None

let value_to_statement_expr ~loc context = function
  | VUnit | VBuilder _ -> None
  | value -> Some (expr_of_value ~loc context value)

let rec value_is_runtime = function
  | VCode _ -> true
  | VArray values | VTuple values -> List.exists value_is_runtime values
  | VVariant (_, Some value) -> value_is_runtime value
  | _ -> false

let runtime_expr_of_value ~loc context = function
  | VCode expr -> expr
  | value -> expr_of_value ~loc context value

let value_to_pattern_runtime_name ~loc = function
  | VString name -> Pat.var (Location.mknoloc name)
  | _ ->
    errorf ~loc
      "Comptime-generated runtime pattern binders must be compile-time strings"

let runtime_ident_or_binding_name expr =
  match expr.pexp_desc with
  | Pexp_ident {txt = Lident name; _} -> Some name
  | _ -> None

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

let fresh_runtime_name base =
  incr gensym_counter;
  base ^ "$comptime" ^ string_of_int !gensym_counter

let rec rename_runtime_pattern_bindings pat =
  match pat.ppat_desc with
  | Ppat_var {txt; loc} ->
    let fresh = fresh_runtime_name txt in
    ( StringMap.singleton txt (VCode (exp_ident fresh)),
      {pat with ppat_desc = Ppat_var {txt = fresh; loc}} )
  | Ppat_constraint (inner, ct) ->
    let env, inner = rename_runtime_pattern_bindings inner in
    (env, {pat with ppat_desc = Ppat_constraint (inner, ct)})
  | Ppat_alias (inner, alias) ->
    let env, inner = rename_runtime_pattern_bindings inner in
    let fresh = fresh_runtime_name alias.txt in
    let env = StringMap.add alias.txt (VCode (exp_ident fresh)) env in
    (env, {pat with ppat_desc = Ppat_alias (inner, {alias with txt = fresh})})
  | Ppat_tuple pats ->
    let env, pats =
      List.fold_right
        (fun pat (env, pats) ->
          let env_pat, pat = rename_runtime_pattern_bindings pat in
          ( StringMap.union (fun _ value _ -> Some value) env_pat env,
            pat :: pats ))
        pats (StringMap.empty, [])
    in
    (env, {pat with ppat_desc = Ppat_tuple pats})
  | Ppat_record (fields, closed) ->
    let env, fields =
      List.fold_right
        (fun field (env, fields) ->
          let env_field, pat = rename_runtime_pattern_bindings field.x in
          ( StringMap.union (fun _ value _ -> Some value) env_field env,
            {field with x = pat} :: fields ))
        fields (StringMap.empty, [])
    in
    (env, {pat with ppat_desc = Ppat_record (fields, closed)})
  | Ppat_construct (lid, arg) ->
    let env, arg =
      match arg with
      | None -> (StringMap.empty, None)
      | Some pat ->
        let env, pat = rename_runtime_pattern_bindings pat in
        (env, Some pat)
    in
    (env, {pat with ppat_desc = Ppat_construct (lid, arg)})
  | _ -> (StringMap.empty, pat)

let builtin arity fn = VBuiltin {arity; apply = fn}

let build_recursive_env context env bindings =
  let rec_env = ref env in
  let recursive_bindings =
    List.fold_left
      (fun acc binding ->
        match
          (binding_name_from_pattern binding.pvb_pat, binding.pvb_expr.pexp_desc)
        with
        | Some name, Pexp_fun {default; lhs = pattern; rhs = body; _} ->
          Option.iter
            (fun _ ->
              errorf ~loc:binding.pvb_expr.pexp_loc
                "Optional arguments are not supported in recursive comptime \
                 bindings")
            default;
          StringMap.add name
            (VClosure
               {
                 pattern;
                 body;
                 env = rec_env;
                 closure_newtypes = context.newtypes;
               })
            acc
        | Some _, _ ->
          errorf ~loc:binding.pvb_expr.pexp_loc
            "Recursive comptime bindings must be functions"
        | None, _ ->
          errorf ~loc:binding.pvb_pat.ppat_loc
            "Recursive comptime bindings must use simple variable patterns")
      StringMap.empty bindings
  in
  rec_env :=
    StringMap.union (fun _ value _ -> Some value) recursive_bindings env;
  !rec_env

let resolve_spliced_record_field_name ~loc value =
  match value with
  | VString field_name -> field_name
  | VRecord field -> (
    match StringMap.find_opt "name" field with
    | Some (VString field_name) -> field_name
    | _ ->
      errorf ~loc
        "%%splice(field) in a record label expects a reflected field descriptor"
    )
  | _ ->
    errorf ~loc
      "%%splice(field) in a record label expects a reflected field descriptor \
       or compile-time string"

let resolve_spliced_identifier_name ~loc value =
  match value with
  | VString name -> name
  | _ -> errorf ~loc "%%splice(name) in an identifier position expects a string"

let rec quote_value context env expr =
  match expr.pexp_desc with
  | Pexp_record (rows, spread_expr) ->
    let rows, spread_expr, has_fragment_syntax =
      quote_record_rows
        ~map_expr:(quote_expression context env)
        context env rows spread_expr
    in
    if spread_expr = None && (has_fragment_syntax || rows = []) then
      VRecordFields rows
    else VCode (Exp.record rows spread_expr)
  | _ -> VCode (quote_expression context env expr)

and eval context env expr =
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
    builtin 1 (fun _context loc _args ->
        errorf ~loc
          "`compileError` has been removed from the public comptime surface; \
           use `failwith` or an assertion failure instead")
  | Pexp_ident {txt = Lident "failwith"; _} ->
    builtin 1 (fun _context loc args ->
        match args with
        | [VString message] -> errorf ~loc "%s" message
        | _ -> errorf ~loc "failwith expects a string")
  | Pexp_ident {txt = Ldot (Lident "Comptime", "__fieldName"); _} ->
    builtin 1 (fun _context loc args ->
        match args with
        | [VVariant (_, Some (VRecord field))] -> (
          match StringMap.find_opt "name" field with
          | Some (VString name) -> VString name
          | _ ->
            errorf ~loc
              "__fieldName expects a reflected field descriptor payload")
        | _ -> errorf ~loc "__fieldName expects a reflected field descriptor")
  | Pexp_ident {txt = Ldot (Lident "Comptime", "__fieldGet"); _} ->
    builtin 2 (fun _context loc args ->
        match args with
        | [VVariant (_, Some (VRecord field)); VCode expr] -> (
          match StringMap.find_opt "name" field with
          | Some (VString name) ->
            VCode (Exp.field expr (Location.mknoloc (Lident name)))
          | _ ->
            errorf ~loc
              "__fieldGet expects a reflected field descriptor payload")
        | _ ->
          errorf ~loc
            "__fieldGet expects a reflected field descriptor and runtime value")
  | Pexp_ident {txt = Ldot (Lident "Comptime", "__erase"); _} ->
    builtin 1 (fun _context loc args ->
        match args with
        | [value] -> value
        | _ -> errorf ~loc "__erase expects a single argument")
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
  | Pexp_ident {txt = Ldot (Lident "Array", "map"); _} ->
    builtin 2 (fun context loc args ->
        match args with
        | [VArray values; fn] ->
          VArray (List.map (fun value -> apply context ~loc fn [value]) values)
        | _ -> errorf ~loc "Array.map expects an array and a function")
  | Pexp_ident {txt = Ldot (Lident "Array", "get"); _} ->
    builtin 2 (fun _context loc args ->
        match args with
        | [VArray values; VInt index] ->
          if index < 0 || index >= List.length values then
            VVariant ("None", None)
          else VVariant ("Some", Some (List.nth values index))
        | _ -> errorf ~loc "Array.get expects an array and an int")
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
    VClosure {pattern; body; env = ref env; closure_newtypes = context.newtypes}
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
  | Pexp_let (Recursive, bindings, body) ->
    let env = build_recursive_env context env bindings in
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
  | Pexp_assert asserted -> (
    match eval context env asserted with
    | VBool true -> VUnit
    | VBool false ->
      errorf ~loc:asserted.pexp_loc
        "Assertion failed during comptime evaluation"
    | _ ->
      errorf ~loc:asserted.pexp_loc
        "assert expects a boolean during comptime evaluation")
  | Pexp_field (record_expr, {txt; loc}) -> (
    match (eval context env record_expr, txt) with
    | VRecord record, Lident label -> (
      match StringMap.find_opt label record with
      | Some value -> value
      | None -> errorf ~loc "Unknown comptime field `%s`" label)
    | _ ->
      errorf ~loc
        "Field access in comptime evaluation expects a reflected record value")
  | Pexp_extension ({txt = "quote"; loc; _}, _) ->
    errorf ~loc "`%%quote` has been removed from the public comptime surface"
  | Pexp_extension ({txt = "splice"; loc; _}, _) ->
    errorf ~loc "`%%splice` has been removed from the public comptime surface"
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
          StringMap.union (fun _ value _ -> Some value) bindings !(closure.env)
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

and stage_expression context env ?expected_type expr =
  match expr.pexp_desc with
  | Pexp_constant _ -> eval context env expr
  | Pexp_construct ({txt = Lident "()"; _}, None) -> VUnit
  | Pexp_construct ({txt = Lident "true"; _}, None) -> VBool true
  | Pexp_construct ({txt = Lident "false"; _}, None) -> VBool false
  | Pexp_construct ({txt = Lident "None"; _}, None) -> VVariant ("None", None)
  | Pexp_construct (({txt = Lident "Some"; _} as ctor), Some payload) ->
    let payload_expected =
      Option.bind expected_type expected_type_of_some_payload
    in
    let payload_value =
      stage_expression context env ?expected_type:payload_expected payload
    in
    if value_is_runtime payload_value then
      VCode
        (Exp.construct ctor
           (Some
              (expr_of_value ~loc:payload.pexp_loc
                 ?expected_type:payload_expected context payload_value)))
    else VVariant ("Some", Some payload_value)
  | Pexp_construct (ctor, Some payload) ->
    let payload_value = stage_expression context env payload in
    if
      value_is_runtime payload_value
      ||
      match payload_value with
      | VBuilder _ -> true
      | _ -> false
    then
      VCode
        (Exp.construct ctor
           (Some
              (runtime_expr_of_value ~loc:payload.pexp_loc context payload_value)))
    else eval context env expr
  | Pexp_construct (_, None) -> eval context env expr
  | Pexp_tuple exprs ->
    let values =
      List.map (fun expr -> stage_expression context env expr) exprs
    in
    if List.exists value_is_runtime values then
      VCode
        (Exp.tuple
           (List.map (runtime_expr_of_value ~loc:expr.pexp_loc context) values))
    else VTuple values
  | Pexp_array exprs ->
    let values =
      List.map (fun expr -> stage_expression context env expr) exprs
    in
    if List.exists value_is_runtime values then
      VCode
        (Exp.array
           (List.map (runtime_expr_of_value ~loc:expr.pexp_loc context) values))
    else VArray values
  | Pexp_constraint (inner, _) ->
    stage_expression context env ?expected_type inner
  | Pexp_newtype (name, inner) ->
    let newtypes =
      match context.target_type with
      | Some target -> StringMap.add name.txt target context.newtypes
      | None -> context.newtypes
    in
    stage_expression {context with newtypes} env ?expected_type inner
  | Pexp_ident {txt = Lident name; _} -> (
    match StringMap.find_opt name env with
    | Some value -> value
    | None -> (
      match StringMap.find_opt name context.bindings with
      | Some binding -> eval context StringMap.empty binding.expression
      | None -> VCode expr))
  | Pexp_field (record_expr, ({txt; loc} as field_lid)) -> (
    match stage_expression context env record_expr with
    | VRecord record -> (
      match txt with
      | Lident label -> (
        match StringMap.find_opt label record with
        | Some value -> value
        | None -> errorf ~loc "Unknown comptime field `%s`" label)
      | _ ->
        errorf ~loc
          "Field access in comptime evaluation expects an identifier field")
    | VCode record_expr -> VCode (Exp.field record_expr field_lid)
    | _ ->
      errorf ~loc
        "Field access in comptime staging expects a reflected record or \
         runtime expression")
  | Pexp_fun {default; lhs = pattern; rhs = body; _} ->
    Option.iter
      (fun _ ->
        errorf ~loc:expr.pexp_loc
          "Optional arguments are not supported in comptime evaluation")
      default;
    VClosure {pattern; body; env = ref env; closure_newtypes = context.newtypes}
  | Pexp_let (Nonrecursive, bindings, body) ->
    stage_let context env ?expected_type expr.pexp_loc bindings body
  | Pexp_let (Recursive, bindings, body) ->
    let env = build_recursive_env context env bindings in
    stage_expression context env ?expected_type body
  | Pexp_sequence (left, right) ->
    let left_value = stage_expression context env left in
    let right_value = stage_expression context env ?expected_type right in
    stage_sequence context expr.pexp_loc left_value right_value
  | Pexp_ifthenelse (condition, when_true, when_false) ->
    let condition_value = stage_expression context env condition in
    stage_ifthenelse context env ?expected_type expr.pexp_loc condition_value
      when_true when_false
  | Pexp_match (scrutinee, cases) ->
    let scrutinee_value = stage_expression context env scrutinee in
    stage_match context env ?expected_type expr.pexp_loc scrutinee_value cases
  | Pexp_assert asserted -> (
    match stage_expression context env asserted with
    | VBool true -> VUnit
    | VBool false ->
      errorf ~loc:asserted.pexp_loc
        "Assertion failed during comptime evaluation"
    | VCode asserted_code -> VCode (Exp.assert_ asserted_code)
    | _ ->
      errorf ~loc:asserted.pexp_loc
        "assert expects a boolean during comptime evaluation")
  | Pexp_apply {funct = fn; args; _} ->
    stage_apply context env ?expected_type expr.pexp_loc fn args
  | Pexp_extension ({txt = "quote"; loc; _}, _) ->
    errorf ~loc "`%%quote` has been removed from the public comptime surface"
  | Pexp_extension ({txt = "splice"; loc; _}, _) ->
    errorf ~loc "`%%splice` has been removed from the public comptime surface"
  | _ -> VCode (quote_expression context env expr)

and stage_let context env ?expected_type _loc bindings body =
  let env, runtime_bindings =
    List.fold_left
      (fun (env, runtime_bindings) binding ->
        let value = stage_expression context env binding.pvb_expr in
        match
          (binding_name_from_pattern binding.pvb_pat, value_is_runtime value)
        with
        | Some name, false ->
          let env = StringMap.add name value env in
          (env, runtime_bindings)
        | Some name, true ->
          let runtime_expr =
            runtime_expr_of_value ~loc:binding.pvb_expr.pexp_loc context value
          in
          let env = StringMap.add name (VCode (exp_ident name)) env in
          (env, runtime_bindings @ [{binding with pvb_expr = runtime_expr}])
        | None, false -> (env, runtime_bindings)
        | None, true ->
          errorf ~loc:binding.pvb_pat.ppat_loc
            "Comptime staging only supports runtime let bindings for simple \
             variable patterns")
      (env, []) bindings
  in
  let body_value = stage_expression context env ?expected_type body in
  match runtime_bindings with
  | [] -> body_value
  | _ ->
    VCode
      (Exp.let_ Nonrecursive runtime_bindings
         (expr_of_value ~loc:body.pexp_loc ?expected_type context body_value))

and stage_sequence context loc left_value right_value =
  match value_to_statement_expr ~loc context left_value with
  | None -> right_value
  | Some left_expr ->
    let right_expr = runtime_expr_of_value ~loc context right_value in
    VCode (Exp.sequence left_expr right_expr)

and stage_ifthenelse context env ?expected_type loc condition_value when_true
    when_false =
  match condition_value with
  | VBool true -> stage_expression context env ?expected_type when_true
  | VBool false -> (
    match when_false with
    | Some when_false -> stage_expression context env ?expected_type when_false
    | None -> VUnit)
  | _ ->
    let condition_expr = runtime_expr_of_value ~loc context condition_value in
    let true_value = stage_expression context env ?expected_type when_true in
    let false_expr =
      match when_false with
      | Some when_false ->
        expr_of_value ~loc:when_false.pexp_loc ?expected_type context
          (stage_expression context env ?expected_type when_false)
      | None -> expr_of_value ~loc context VUnit
    in
    VCode
      (Exp.ifthenelse condition_expr
         (expr_of_value ~loc:when_true.pexp_loc ?expected_type context
            true_value)
         (Some false_expr))

and stage_match context env ?expected_type loc scrutinee_value cases =
  if not (value_is_runtime scrutinee_value) then
    let rec select_case = function
      | [] -> errorf ~loc "Non-exhaustive comptime switch"
      | case :: rest -> (
        match
          match_pattern ~loc:case.pc_lhs.ppat_loc case.pc_lhs scrutinee_value
        with
        | None -> select_case rest
        | Some bindings ->
          let env =
            StringMap.union (fun _ value _ -> Some value) bindings env
          in
          let guard_ok =
            match case.pc_guard with
            | None -> true
            | Some guard -> (
              match stage_expression context env guard with
              | VBool result -> result
              | _ ->
                errorf ~loc:guard.pexp_loc
                  "Comptime guard expressions must evaluate to bool")
          in
          if guard_ok then
            stage_expression context env ?expected_type case.pc_rhs
          else select_case rest)
    in
    select_case cases
  else
    let scrutinee_expr = runtime_expr_of_value ~loc context scrutinee_value in
    let cases =
      List.map
        (fun case ->
          let runtime_bindings, runtime_pattern =
            rename_runtime_pattern_bindings case.pc_lhs
          in
          let case_env =
            StringMap.union (fun _ value _ -> Some value) runtime_bindings env
          in
          let guard =
            match case.pc_guard with
            | None -> None
            | Some guard -> (
              match stage_expression context case_env guard with
              | VBool true -> None
              | VBool false -> Some (Exp.construct (lid "false") None)
              | value ->
                Some (runtime_expr_of_value ~loc:guard.pexp_loc context value))
          in
          {
            case with
            pc_lhs = runtime_pattern;
            pc_guard = guard;
            pc_rhs =
              expr_of_value ~loc:case.pc_rhs.pexp_loc ?expected_type context
                (stage_expression context case_env ?expected_type case.pc_rhs);
          })
        cases
    in
    VCode (Exp.match_ scrutinee_expr cases)

and stage_apply context env ?expected_type loc fn args =
  let stage_arg (_, arg) = stage_expression context env arg in
  match fn.pexp_desc with
  | Pexp_ident {txt = Lident "reflect"; _}
  | Pexp_ident {txt = Ldot (Lident "Comptime", "reflect"); _} ->
    apply context ~loc (eval context env fn) (List.map stage_arg args)
  | Pexp_ident {txt = Lident "failwith"; _} ->
    apply context ~loc (eval context env fn) (List.map stage_arg args)
  | Pexp_ident {txt = Ldot (Lident "Comptime", "__erase"); _} ->
    apply context ~loc (eval context env fn) (List.map stage_arg args)
  | Pexp_ident {txt = Ldot (Lident "Comptime", "__fieldName"); _}
  | Pexp_ident {txt = Ldot (Lident "Comptime", "__fieldGet"); _} ->
    apply context ~loc (eval context env fn) (List.map stage_arg args)
  | Pexp_ident {txt = Lident "+"; _}
  | Pexp_ident {txt = Lident "++"; _}
  | Pexp_ident {txt = Ldot (Lident "Array", "get"); _}
  | Pexp_ident {txt = Ldot (Lident "Array", "forEach"); _}
  | Pexp_ident {txt = Ldot (Lident "Array", "reduce"); _}
  | Pexp_ident {txt = Ldot (Lident "Array", "reduceRight"); _}
  | Pexp_ident {txt = Ldot (Lident "Int", "toFloat"); _}
  | Pexp_ident {txt = Ldot (Lident "Float", "toInt"); _} ->
    stage_builtin_application context env ?expected_type loc fn args
  | Pexp_ident {txt = Ldot (Lident "Dict", "make"); _} -> VBuilder (ref [])
  | Pexp_ident {txt = Ldot (Lident "Dict", "copy"); _} -> (
    match List.map stage_arg args with
    | [VBuilder builder] -> VBuilder (ref !builder)
    | [value] ->
      VCode
        (Exp.apply fn
           (List.map
              (fun (label, arg) ->
                (label, runtime_expr_of_value ~loc:arg.pexp_loc context value))
              args))
    | _ -> errorf ~loc "Dict.copy expects one argument")
  | Pexp_ident {txt = Ldot (Lident "Dict", "set"); _} -> (
    match List.map stage_arg args with
    | [VBuilder builder; key; value] ->
      let field_name = resolve_builder_field_name ~loc key in
      let value_expr = runtime_expr_of_value ~loc context value in
      builder_entries_set builder field_name value_expr;
      VUnit
    | values ->
      let arg_exprs =
        List.map2
          (fun (label, arg) value ->
            (label, runtime_expr_of_value ~loc:arg.pexp_loc context value))
          args values
      in
      VCode (Exp.apply fn arg_exprs))
  | _ ->
    let fn_value = stage_expression context env fn in
    let arg_values = List.map stage_arg args in
    apply_stage context ~loc ?expected_type fn args fn_value arg_values

and stage_builtin_application context env ?expected_type:_ loc fn args =
  let values =
    List.map (fun (_, arg) -> stage_expression context env arg) args
  in
  let fallback_runtime () =
    VCode
      (Exp.apply fn
         (List.map2
            (fun (label, arg) value ->
              (label, runtime_expr_of_value ~loc:arg.pexp_loc context value))
            args values))
  in
  match fn.pexp_desc with
  | Pexp_ident {txt = Lident "+"; _} -> (
    match values with
    | [VInt left; VInt right] -> VInt (left + right)
    | _ -> fallback_runtime ())
  | Pexp_ident {txt = Lident "++"; _} -> (
    match values with
    | [VString left; VString right] -> VString (left ^ right)
    | _ -> fallback_runtime ())
  | Pexp_ident {txt = Ldot (Lident "Array", "get"); _} -> (
    match values with
    | [VArray values; VInt index] ->
      if index < 0 || index >= List.length values then VVariant ("None", None)
      else VVariant ("Some", Some (List.nth values index))
    | _ -> fallback_runtime ())
  | Pexp_ident {txt = Ldot (Lident "Array", "forEach"); _} -> (
    match values with
    | [VArray values; ((VClosure _ | VBuiltin _) as fn_value)] ->
      List.iter
        (fun value ->
          ignore
            (apply_stage context ~loc
               (exp_ident "__comptime_array_forEach")
               [(Nolabel, exp_ident "__comptime_forEach_arg")]
               fn_value [value]))
        values;
      VUnit
    | _ -> fallback_runtime ())
  | Pexp_ident {txt = Ldot (Lident "Array", "reduce"); _} -> (
    match values with
    | [VArray values; init; ((VClosure _ | VBuiltin _) as fn_value)] ->
      List.fold_left
        (fun acc value ->
          apply_stage context ~loc
            (exp_ident "__comptime_array_reduce")
            [
              (Nolabel, exp_ident "__comptime_reduce_acc");
              (Nolabel, exp_ident "__comptime_reduce_value");
            ]
            fn_value [acc; value])
        init values
    | _ -> fallback_runtime ())
  | Pexp_ident {txt = Ldot (Lident "Array", "reduceRight"); _} -> (
    match values with
    | [VArray values; init; ((VClosure _ | VBuiltin _) as fn_value)] ->
      List.fold_right
        (fun value acc ->
          apply_stage context ~loc
            (exp_ident "__comptime_array_reduceRight")
            [
              (Nolabel, exp_ident "__comptime_reduceRight_acc");
              (Nolabel, exp_ident "__comptime_reduceRight_value");
            ]
            fn_value [acc; value])
        values init
    | _ -> fallback_runtime ())
  | Pexp_ident {txt = Ldot (Lident "Int", "toFloat"); _} -> (
    match values with
    | [VInt value] -> VFloat (float_of_int value)
    | _ -> fallback_runtime ())
  | Pexp_ident {txt = Ldot (Lident "Float", "toInt"); _} -> (
    match values with
    | [VFloat value] -> VInt (int_of_float value)
    | _ -> fallback_runtime ())
  | Pexp_ident {txt = Lident "reflect"; _}
  | Pexp_ident {txt = Ldot (Lident "Comptime", "reflect"); _} ->
    apply context ~loc (eval context env fn) values
  | Pexp_ident {txt = Lident "failwith"; _} ->
    apply context ~loc (eval context env fn) values
  | _ -> fallback_runtime ()

and apply_stage context ~loc ?expected_type fn_expr args_exprs fn args =
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
          StringMap.union (fun _ value _ -> Some value) bindings !(closure.env)
        in
        stage_expression
          {context with newtypes = closure.closure_newtypes}
          env ?expected_type closure.body)
    | arg :: rest ->
      let partially_applied =
        apply_stage context ~loc fn_expr args_exprs fn [arg]
      in
      apply_stage context ~loc ?expected_type fn_expr args_exprs
        partially_applied rest)
  | VCode fn_code ->
    let arg_exprs =
      List.map2
        (fun (label, arg_expr) value ->
          (label, runtime_expr_of_value ~loc:arg_expr.pexp_loc context value))
        args_exprs args
    in
    VCode (Exp.apply fn_code arg_exprs)
  | _ ->
    let fn_expr = runtime_expr_of_value ~loc context fn in
    let arg_exprs =
      List.map2
        (fun (label, arg_expr) value ->
          (label, runtime_expr_of_value ~loc:arg_expr.pexp_loc context value))
        args_exprs args
    in
    VCode (Exp.apply fn_expr arg_exprs)

and stage_closure_expression context expected_type closure =
  match expected_type.ptyp_desc with
  | Ptyp_arrow {ret; _} ->
    let pattern =
      substitute_newtypes_in_pattern closure.closure_newtypes closure.pattern
    in
    let body_value =
      stage_expression
        {context with newtypes = closure.closure_newtypes}
        !(closure.env) ~expected_type:ret closure.body
    in
    Exp.fun_ ~arity:None Nolabel None pattern
      (expr_of_value ~loc:closure.body.pexp_loc ~expected_type:ret context
         body_value)
  | _ ->
    errorf ~loc:expected_type.ptyp_loc
      "Expected a function type for a comptime-generated function"

and quote_record_rows ~map_expr context env rows spread_expr =
  let has_fragment_syntax = ref false in
  let append_row acc row = acc @ [row] in
  let rows =
    List.fold_left
      (fun acc row ->
        match row.lid.txt with
        | Lident field_name when field_name = comptime_splice_rows_label -> (
          has_fragment_syntax := true;
          match row.x.pexp_desc with
          | Pexp_extension ({txt = "splice"; loc; _}, payload) -> (
            let splice_expr = expr_payload_single ~loc payload in
            match eval context env splice_expr with
            | VRecordFields rows -> acc @ rows
            | _ ->
              errorf ~loc
                "%%splice(fields) in a record literal expects record field \
                 fragments")
          | _ ->
            errorf ~loc:row.x.pexp_loc
              "Record field splices must use %%splice(...)")
        | Lident field_name when field_name = comptime_splice_field_label -> (
          has_fragment_syntax := true;
          match row.x.pexp_desc with
          | Pexp_tuple [label_expr; value_expr] ->
            let field_name =
              match label_expr.pexp_desc with
              | Pexp_extension ({txt = "splice"; loc; _}, payload) ->
                let splice_expr = expr_payload_single ~loc payload in
                let value = eval context env splice_expr in
                resolve_spliced_record_field_name ~loc value
              | _ ->
                errorf ~loc:label_expr.pexp_loc
                  "Record field label splices must use %%splice(...)"
            in
            append_row acc
              {
                row with
                lid = Location.mkloc (Lident field_name) row.lid.loc;
                x = map_expr value_expr;
              }
          | _ ->
            errorf ~loc:row.x.pexp_loc "Malformed comptime record field splice")
        | _ -> append_row acc {row with x = map_expr row.x})
      [] rows
  in
  let spread_expr =
    match spread_expr with
    | None -> None
    | Some spread_expr -> (
      match spread_expr.pexp_desc with
      | Pexp_extension ({txt = "splice"; loc; _}, payload) -> (
        let splice_expr = expr_payload_single ~loc payload in
        match eval context env splice_expr with
        | VCode expr -> Some (substitute_newtypes_in_expr context.newtypes expr)
        | _ -> errorf ~loc "Record spread splices expect quoted expressions")
      | _ -> Some (map_expr spread_expr))
  in
  (rows, spread_expr, !has_fragment_syntax)

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
          | Pexp_record (rows, spread_expr) ->
            let rows, spread_expr, _ =
              quote_record_rows ~map_expr:(self.expr self) context env rows
                spread_expr
            in
            {expr with pexp_desc = Pexp_record (rows, spread_expr)}
          | Pexp_extension ({txt = "splice"; loc; _}, payload) ->
            let expr = expr_payload_single ~loc payload in
            let value = eval context env expr in
            let quoted =
              match value with
              | VCode expr -> substitute_newtypes_in_expr context.newtypes expr
              | VString name -> Exp.ident (lid name)
              | VRecordFields _ ->
                errorf ~loc
                  "Record field fragments can only be spliced inside record \
                   literals"
              | _ ->
                errorf ~loc
                  "%%splice expects a quoted code value or identifier name"
            in
            quoted
          | _ -> (
            match inline_constant expr with
            | Some constant -> constant
            | None -> default_mapper.expr self expr));
      pat =
        (fun self pat ->
          match pat.ppat_desc with
          | Ppat_extension ({txt = "splice"; loc; _}, payload) ->
            let expr = expr_payload_single ~loc payload in
            let value = eval context env expr in
            let name = resolve_spliced_identifier_name ~loc value in
            Pat.var (Location.mknoloc name)
          | _ -> default_mapper.pat self pat);
      typ =
        (fun self ct ->
          default_mapper.typ self
            (substitute_newtypes_in_core_type context.newtypes ct));
    }
  in
  match expr.pexp_desc with
  | Pexp_record (rows, spread_expr) ->
    let rows, spread_expr, _ =
      quote_record_rows ~map_expr:(mapper.expr mapper) context env rows
        spread_expr
    in
    {expr with pexp_desc = Pexp_record (rows, spread_expr)}
  | Pexp_extension ({txt = "splice"; loc; _}, payload) -> (
    let expr = expr_payload_single ~loc payload in
    let value = eval context env expr in
    match value with
    | VCode expr -> substitute_newtypes_in_expr context.newtypes expr
    | VString name -> Exp.ident (lid name)
    | VRecordFields _ ->
      errorf ~loc
        "Record field fragments can only be spliced inside record literals"
    | _ -> errorf ~loc "%%splice expects a quoted code value or identifier name"
    )
  | _ -> mapper.expr mapper expr

let extract_target_type_from_expected ~loc:_ expected =
  match expected.ptyp_desc with
  | Ptyp_arrow {arg = {typ = domain; _}; ret = codomain; _} -> (
    match (domain.ptyp_desc, codomain.ptyp_desc) with
    | ( Ptyp_constr ({txt = Ldot (Lident "JSON", "t"); _}, []),
        Ptyp_constr ({txt = Lident "option"; _}, [inner]) ) ->
      Some inner
    | _ -> Some domain)
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
      | VClosure closure -> (
        match expected_type with
        | Some expected -> stage_closure_expression context expected closure
        | None ->
          errorf ~loc
            "Comptime-generated functions require a binding type annotation")
      | value -> (
        match expected_type with
        | Some expected ->
          value_to_expr_with_expected ~loc context expected value
        | None -> value_to_expr ~loc context value)
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

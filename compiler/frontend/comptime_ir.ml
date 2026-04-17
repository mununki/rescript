[@@@warning "-45"]

open Asttypes
open Typedtree

module IdentSet = Set.Make (Ident)

type builtin =
  | BReflect
  | BFailwith
  | BFieldType
  | BFieldName
  | BFieldGet
  | BItemType
  | BItemIndex
  | BItemGet
  | BConstructorPayload
  | BConstructorName
  | BConstructorUnpack
  | BConstructorMake
  | BErase
  | BAdd
  | BConcat
  | BArrayGet
  | BArrayMap
  | BArrayForEach
  | BArrayReduce
  | BArrayReduceRight
  | BStringCapitalize
  | BIntToFloat
  | BFloatToInt
  | BDictMake
  | BDictCopy
  | BDictSet
  | BDictGet
  | BTypeString
  | BTypeInt
  | BTypeFloat
  | BTypeBool
  | BTypeJson
  | BTypeOption
  | BTypeArray
  | BTypeList
  | BTypeTuple
  | BTypeField
  | BTypeRecord
  | BTypeNoPayload
  | BTypeSinglePayload
  | BTypeTuplePayload
  | BTypeConstructor
  | BTypeVariant
  | BTypeOfDesc
  | BDeclValue
  | BDeclType
  | BDeclModule

type ident =
  | ILocal of Ident.t * string
  | ITop of Ident.t * string
  | IGlobal of Longident.t loc
  | IBuiltin of builtin * Longident.t loc option

type pattern =
  | PAny
  | PVar of Ident.t * string
  | PAlias of pattern * Ident.t * string
  | PConstant of Parsetree.constant
  | PTuple of pattern list
  | PRecord of (string * pattern) list
  | PConstruct of string * pattern list

type expr = {desc: expr_desc; loc: Location.t; typ: Types.type_expr; env: Env.t}

and expr_desc =
  | EIdent of ident
  | EConstant of Parsetree.constant
  | EWitness of Types.type_expr
  | ELet of rec_flag * binding list * expr
  | EFun of pattern * expr
  | EApply of expr * expr list
  | EMatch of expr * case list
  | ETuple of expr list
  | EConstruct of Longident.t loc * string * expr list
  | ERecord of (string * expr) list * expr option
  | EField of expr * string
  | EArray of expr list
  | EIfThenElse of expr * expr * expr option
  | ESequence of expr * expr
  | EAssert of expr

and binding = {pattern: pattern; expr: expr; loc: Location.t}

and case = {lhs: pattern; guard: expr option; rhs: expr; loc: Location.t}

type top_binding = {id: Ident.t; name: string; expr: expr; loc: Location.t}

let longident_last = function
  | Longident.Lident name -> name
  | Ldot (_, name) -> name
  | Lapply _ -> ""

let longident_to_string lid =
  let rec loop = function
    | Longident.Lident name -> name
    | Ldot (prev, name) -> loop prev ^ "." ^ name
    | Lapply (a, b) -> loop a ^ "(" ^ loop b ^ ")"
  in
  loop lid

let path_name_ends_with path suffix =
  let name = Path.name path in
  String.length name >= String.length suffix
  && String.sub name
       (String.length name - String.length suffix)
       (String.length suffix)
     = suffix

let builtin_of_path path lid prims =
  match prims with
  | "comptime_dict_make" :: _ -> Some (IBuiltin (BDictMake, Some lid))
  | "comptime_dict_copy" :: _ -> Some (IBuiltin (BDictCopy, Some lid))
  | "comptime_dict_set" :: _ -> Some (IBuiltin (BDictSet, Some lid))
  | "comptime_dict_get" :: _ -> Some (IBuiltin (BDictGet, Some lid))
  | "comptime_field_type" :: _ -> Some (IBuiltin (BFieldType, Some lid))
  | "comptime_field_name" :: _ -> Some (IBuiltin (BFieldName, Some lid))
  | "comptime_field_get" :: _ -> Some (IBuiltin (BFieldGet, Some lid))
  | "comptime_item_type" :: _ -> Some (IBuiltin (BItemType, Some lid))
  | "comptime_item_index" :: _ -> Some (IBuiltin (BItemIndex, Some lid))
  | "comptime_item_get" :: _ -> Some (IBuiltin (BItemGet, Some lid))
  | "comptime_constructor_payload" :: _ ->
    Some (IBuiltin (BConstructorPayload, Some lid))
  | "comptime_constructor_name" :: _ ->
    Some (IBuiltin (BConstructorName, Some lid))
  | "comptime_constructor_unpack" :: _ ->
    Some (IBuiltin (BConstructorUnpack, Some lid))
  | "comptime_constructor_make" :: _ ->
    Some (IBuiltin (BConstructorMake, Some lid))
  | "comptime_erase" :: _ -> Some (IBuiltin (BErase, Some lid))
  | "comptime_type_string" :: _ -> Some (IBuiltin (BTypeString, Some lid))
  | "comptime_type_int" :: _ -> Some (IBuiltin (BTypeInt, Some lid))
  | "comptime_type_float" :: _ -> Some (IBuiltin (BTypeFloat, Some lid))
  | "comptime_type_bool" :: _ -> Some (IBuiltin (BTypeBool, Some lid))
  | "comptime_type_json" :: _ -> Some (IBuiltin (BTypeJson, Some lid))
  | "comptime_type_option" :: _ -> Some (IBuiltin (BTypeOption, Some lid))
  | "comptime_type_array" :: _ -> Some (IBuiltin (BTypeArray, Some lid))
  | "comptime_type_list" :: _ -> Some (IBuiltin (BTypeList, Some lid))
  | "comptime_type_tuple" :: _ -> Some (IBuiltin (BTypeTuple, Some lid))
  | "comptime_type_field" :: _ -> Some (IBuiltin (BTypeField, Some lid))
  | "comptime_type_record" :: _ -> Some (IBuiltin (BTypeRecord, Some lid))
  | "comptime_type_no_payload" :: _ ->
    Some (IBuiltin (BTypeNoPayload, Some lid))
  | "comptime_type_single_payload" :: _ ->
    Some (IBuiltin (BTypeSinglePayload, Some lid))
  | "comptime_type_tuple_payload" :: _ ->
    Some (IBuiltin (BTypeTuplePayload, Some lid))
  | "comptime_type_constructor" :: _ ->
    Some (IBuiltin (BTypeConstructor, Some lid))
  | "comptime_type_variant" :: _ -> Some (IBuiltin (BTypeVariant, Some lid))
  | "comptime_type_of_desc" :: _ -> Some (IBuiltin (BTypeOfDesc, Some lid))
  | "comptime_decl_value" :: _ -> Some (IBuiltin (BDeclValue, Some lid))
  | "comptime_decl_type" :: _ -> Some (IBuiltin (BDeclType, Some lid))
  | "comptime_decl_module" :: _ -> Some (IBuiltin (BDeclModule, Some lid))
  | _ -> (
    match longident_last lid.txt with
    | "reflect" when path_name_ends_with path "Comptime.reflect" ->
      Some (IBuiltin (BReflect, Some lid))
    | "failwith" -> Some (IBuiltin (BFailwith, Some lid))
    | "+" -> Some (IBuiltin (BAdd, Some lid))
    | "++" -> Some (IBuiltin (BConcat, Some lid))
    | "get"
      when path_name_ends_with path "Array.get"
           || path_name_ends_with path "Stdlib_Array.get" ->
      Some (IBuiltin (BArrayGet, Some lid))
    | "map"
      when path_name_ends_with path "Array.map"
           || path_name_ends_with path "Stdlib_Array.map" ->
      Some (IBuiltin (BArrayMap, Some lid))
    | "forEach"
      when path_name_ends_with path "Array.forEach"
           || path_name_ends_with path "Stdlib_Array.forEach" ->
      Some (IBuiltin (BArrayForEach, Some lid))
    | "reduce"
      when path_name_ends_with path "Array.reduce"
           || path_name_ends_with path "Stdlib_Array.reduce" ->
      Some (IBuiltin (BArrayReduce, Some lid))
    | "reduceRight"
      when path_name_ends_with path "Array.reduceRight"
           || path_name_ends_with path "Stdlib_Array.reduceRight" ->
      Some (IBuiltin (BArrayReduceRight, Some lid))
    | "make"
      when path_name_ends_with path "Dict.make"
           || path_name_ends_with path "Stdlib!.Dict.make"
           || path_name_ends_with path "Stdlib_Dict.make" ->
      Some (IBuiltin (BDictMake, Some lid))
    | "copy"
      when path_name_ends_with path "Dict.copy"
           || path_name_ends_with path "Stdlib!.Dict.copy"
           || path_name_ends_with path "Stdlib_Dict.copy" ->
      Some (IBuiltin (BDictCopy, Some lid))
    | "set"
      when path_name_ends_with path "Dict.set"
           || path_name_ends_with path "Stdlib!.Dict.set"
           || path_name_ends_with path "Stdlib_Dict.set" ->
      Some (IBuiltin (BDictSet, Some lid))
    | "get"
      when path_name_ends_with path "Dict.get"
           || path_name_ends_with path "Stdlib!.Dict.get"
           || path_name_ends_with path "Stdlib_Dict.get" ->
      Some (IBuiltin (BDictGet, Some lid))
    | "capitalize"
      when path_name_ends_with path "String.capitalize"
           || path_name_ends_with path "Stdlib_String.capitalize" ->
      Some (IBuiltin (BStringCapitalize, Some lid))
    | "toFloat"
      when path_name_ends_with path "Int.toFloat"
           || path_name_ends_with path "Stdlib_Int.toFloat" ->
      Some (IBuiltin (BIntToFloat, Some lid))
    | "toInt"
      when path_name_ends_with path "Float.toInt"
           || path_name_ends_with path "Stdlib_Float.toInt" ->
      Some (IBuiltin (BFloatToInt, Some lid))
    | _ -> None)

let rec lower_pattern pat =
  match pat.pat_desc with
  | Tpat_any -> PAny
  | Tpat_var (id, {txt; _}) -> PVar (id, txt)
  | Tpat_alias (pat, id, {txt; _}) -> PAlias (lower_pattern pat, id, txt)
  | Tpat_constant c -> PConstant (Untypeast.constant c)
  | Tpat_tuple pats -> PTuple (List.map lower_pattern pats)
  | Tpat_record (fields, _) ->
    PRecord
      (List.map
         (fun (lid, _label, pat, _optional) ->
           (longident_last lid.txt, lower_pattern pat))
         fields)
  | Tpat_construct (_lid, cstr, pats) ->
    PConstruct (cstr.cstr_name, List.map lower_pattern pats)
  | _ ->
    Location.raise_errorf ~loc:pat.pat_loc
      "Unsupported pattern in typed comptime lowering"

let witness_type_of_package ~loc ty =
  match (Ctype.repr ty).desc with
  | Types.Tpackage (_path, names, tys) -> (
    match
      List.combine names tys
      |> List.find_opt (fun (name, _ty) -> name = Longident.Lident "t")
    with
    | Some (_name, ty) -> ty
    | None ->
      Location.raise_errorf ~loc
        "Comptime module witnesses must provide `type t`")
  | _ ->
    Location.raise_errorf ~loc
      "Expected a first-class module witness with `type t`"

let rec lower_expr top_ids expr =
  let make desc =
    {desc; loc = expr.exp_loc; typ = expr.exp_type; env = expr.exp_env}
  in
  match expr.exp_desc with
  | Texp_ident (path, lid, vd) -> (
    let prims =
      match vd.val_kind with
      | Types.Val_prim prim ->
        if prim.prim_native_name <> "" then
          [prim.prim_name; prim.prim_native_name]
        else [prim.prim_name]
      | Types.Val_reg -> []
    in
    match builtin_of_path path lid prims with
    | Some ident -> make (EIdent ident)
    | None -> (
      match path with
      | Path.Pident id when IdentSet.mem id top_ids ->
        make (EIdent (ITop (id, Ident.name id)))
      | Path.Pident id -> make (EIdent (ILocal (id, Ident.name id)))
      | _ -> make (EIdent (IGlobal lid))))
  | Texp_constant c -> make (EConstant (Untypeast.constant c))
  | Texp_pack _module_expr ->
    make (EWitness (witness_type_of_package ~loc:expr.exp_loc expr.exp_type))
  | Texp_let (rec_flag, bindings, body) ->
    let bindings =
      List.map
        (fun vb ->
          {
            pattern = lower_pattern vb.vb_pat;
            expr = lower_expr top_ids vb.vb_expr;
            loc = vb.vb_loc;
          })
        bindings
    in
    make (ELet (rec_flag, bindings, lower_expr top_ids body))
  | Texp_function {case; _} ->
    make (EFun (lower_pattern case.c_lhs, lower_expr top_ids case.c_rhs))
  | Texp_apply {funct; args; _} ->
    let args =
      List.filter_map
        (fun (_label, arg) -> Option.map (lower_expr top_ids) arg)
        args
    in
    make (EApply (lower_expr top_ids funct, args))
  | Texp_match (scrutinee, cases, exception_cases, _partial) ->
    if exception_cases <> [] then
      Location.raise_errorf ~loc:expr.exp_loc
        "Exception cases are not supported in typed comptime lowering";
    let cases =
      List.map
        (fun case ->
          {
            lhs = lower_pattern case.c_lhs;
            guard = Option.map (lower_expr top_ids) case.c_guard;
            rhs = lower_expr top_ids case.c_rhs;
            loc = case.c_rhs.exp_loc;
          })
        cases
    in
    make (EMatch (lower_expr top_ids scrutinee, cases))
  | Texp_tuple exprs -> make (ETuple (List.map (lower_expr top_ids) exprs))
  | Texp_construct (lid, cstr, exprs) ->
    make (EConstruct (lid, cstr.cstr_name, List.map (lower_expr top_ids) exprs))
  | Texp_record {fields; extended_expression; _} ->
    let rows =
      Array.fold_right
        (fun (label, def, _optional) rows ->
          match def with
          | Kept _ -> rows
          | Overridden (_lid, expr) ->
            (label.Types.lbl_name, lower_expr top_ids expr) :: rows)
        fields []
    in
    make (ERecord (rows, Option.map (lower_expr top_ids) extended_expression))
  | Texp_field (record_expr, _lid, label) ->
    make (EField (lower_expr top_ids record_expr, label.lbl_name))
  | Texp_array exprs -> make (EArray (List.map (lower_expr top_ids) exprs))
  | Texp_ifthenelse (a, b, c) ->
    make
      (EIfThenElse
         ( lower_expr top_ids a,
           lower_expr top_ids b,
           Option.map (lower_expr top_ids) c ))
  | Texp_sequence (a, b) ->
    make (ESequence (lower_expr top_ids a, lower_expr top_ids b))
  | Texp_assert expr -> make (EAssert (lower_expr top_ids expr))
  | _ ->
    Location.raise_errorf ~loc:expr.exp_loc
      "Unsupported expression in typed comptime lowering"

let top_level_ids structure =
  List.fold_left
    (fun top_ids item ->
      match item.str_desc with
      | Tstr_value (_, bindings) ->
        List.fold_left
          (fun top_ids binding ->
            match Typecore.id_of_pattern binding.vb_pat with
            | Some id -> IdentSet.add id top_ids
            | None -> top_ids)
          top_ids bindings
      | _ -> top_ids)
    IdentSet.empty structure.str_items

let top_level_bindings structure =
  let top_ids = top_level_ids structure in
  List.fold_left
    (fun bindings item ->
      match item.str_desc with
      | Tstr_value (_, value_bindings) ->
        List.fold_left
          (fun bindings vb ->
            match Typecore.id_of_pattern vb.vb_pat with
            | Some id ->
              {
                id;
                name = Ident.name id;
                expr = lower_expr top_ids vb.vb_expr;
                loc = vb.vb_loc;
              }
              :: bindings
            | None -> bindings)
          bindings value_bindings
      | _ -> bindings)
    [] structure.str_items
  |> List.rev

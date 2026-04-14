[@@@warning "-45"]

open Ast_helper
open Asttypes
open Parsetree

module Ir = Comptime_ir
module StringMap = Map.Make (String)
module IdentSet = Set.Make (Ident)

type resolved_type =
  | Type_string
  | Type_int
  | Type_float
  | Type_bool
  | Type_json
  | Type_option of resolved_type
  | Type_array of resolved_type
  | Type_list of resolved_type
  | Type_record of string * resolved_field list
  | Type_tuple of resolved_item list
  | Type_variant of string * resolved_constructor list

and resolved_field = {field_name: string; field_type: resolved_type}

and resolved_item = {item_index: int; item_arity: int; item_type: resolved_type}

and resolved_constructor_payload =
  | Payload_none
  | Payload_single of resolved_type
  | Payload_tuple of resolved_item list

and resolved_constructor = {
  constructor_name: string;
  constructor_payload: resolved_constructor_payload;
}

type builder_kind = Builder_unknown | Builder_tuple

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
  | VBuilder of builder_kind ref * (string * expression) list ref
  | VCode of expression

and closure = {pattern: Ir.pattern; body: Ir.expr; env: value Ident.tbl ref}

and builtin = {arity: int; apply: context -> Location.t -> value list -> value}

and top_source = {
  source_name: string;
  source_expr: Typedtree.expression;
  source_loc: Location.t;
}

and context = {
  top_bindings: top_source Ident.tbl;
  top_ids: IdentSet.t;
  mutable cache: value Ident.tbl;
  mutable used_top: IdentSet.t;
  target_type: Types.type_expr option;
  type_env: Env.t;
}

let gensym_counter = ref 0

let stage_expression_ref : (context -> value Ident.tbl -> Ir.expr -> value) ref
    =
  ref (fun _context _env _expr -> assert false)

let stage_expression context env expr = !stage_expression_ref context env expr

let errorf ~loc fmt =
  Format.kasprintf (fun message -> Location.raise_errorf ~loc "%s" message) fmt

let lid txt = Location.mknoloc (Longident.Lident txt)

let exp_ident txt = Exp.ident (lid txt)
let exp_string s = Exp.constant (Const.string s)
let exp_int i = Exp.constant (Const.int i)
let exp_float f = Exp.constant (Const.float (string_of_float f))
let exp_bool b = Exp.construct (lid (if b then "true" else "false")) None
let exp_none () = Exp.construct (lid "None") None
let exp_some expr = Exp.construct (lid "Some") (Some expr)

let longident_is_unqualified = function
  | Longident.Lident _ -> true
  | Longident.Ldot _ | Longident.Lapply _ -> false

let is_comptime_constructor ctor_lid name =
  longident_is_unqualified ctor_lid.txt
  &&
  match name with
  | "()" | "true" | "false" | "None" | "Some" | "String" | "Int" | "Float"
  | "Bool" | "Json" | "Option" | "Array" | "List" | "Record" | "Tuple"
  | "Variant" | "NoPayload" | "Single" | "StringField" | "IntField"
  | "FloatField" | "BoolField" | "JsonField" | "OptionField" | "ArrayField"
  | "ListField" | "RecordField" | "TupleField" | "VariantField" | "StringItem"
  | "IntItem" | "FloatItem" | "BoolItem" | "JsonItem" | "OptionItem"
  | "ArrayItem" | "ListItem" | "RecordItem" | "TupleItem" | "VariantItem"
  | "NoPayloadConstructor" | "SingleConstructor" | "TupleConstructor" ->
    true
  | _ -> false

let rec path_string = function
  | Longident.Lident name -> name
  | Longident.Ldot (prev, name) -> path_string prev ^ "." ^ name
  | Longident.Lapply (a, b) -> path_string a ^ "(" ^ path_string b ^ ")"

let is_json_path path =
  let name = Path.name path in
  String.ends_with ~suffix:"JSON.t" name
  || String.ends_with ~suffix:"Stdlib_JSON.t" name

let resolve_type env ty =
  let rec loop visited ty =
    let ty = Ctype.repr ty in
    match ty.desc with
    | Types.Ttuple tys ->
      Type_tuple
        (List.mapi
           (fun item_index item_type ->
             {
               item_index;
               item_arity = List.length tys;
               item_type = loop visited item_type;
             })
           tys)
    | Types.Tconstr (path, [inner], _) when Path.name path = "option" ->
      Type_option (loop visited inner)
    | Types.Tconstr (path, [inner], _) when Path.name path = "array" ->
      Type_array (loop visited inner)
    | Types.Tconstr (path, [inner], _) when Path.name path = "list" ->
      Type_list (loop visited inner)
    | Types.Tconstr (path, [ok_ty; err_ty], _) when Path.name path = "result" ->
      Type_variant
        ( "result",
          [
            {
              constructor_name = "Ok";
              constructor_payload = Payload_single (loop visited ok_ty);
            };
            {
              constructor_name = "Error";
              constructor_payload = Payload_single (loop visited err_ty);
            };
          ] )
    | Types.Tconstr (path, [], _) -> (
      match Path.name path with
      | "string" -> Type_string
      | "int" -> Type_int
      | "float" -> Type_float
      | "bool" -> Type_bool
      | _ when is_json_path path -> Type_json
      | type_name -> (
        if List.mem type_name visited then
          errorf ~loc:Location.none
            "Recursive types are not supported in comptime reflection";
        let decl = Env.find_type path env in
        if decl.type_params <> [] then
          errorf ~loc:Location.none
            "Generic types are not supported in comptime reflection";
        match decl.type_kind with
        | Types.Type_record (labels, _) ->
          Type_record
            ( Path.last path,
              List.map
                (fun label ->
                  {
                    field_name = Ident.name label.Types.ld_id;
                    field_type = loop (type_name :: visited) label.Types.ld_type;
                  })
                labels )
        | Types.Type_variant constructors ->
          Type_variant
            ( Path.last path,
              List.map
                (fun constructor ->
                  let constructor_payload =
                    match constructor.Types.cd_args with
                    | Types.Cstr_tuple [] -> Payload_none
                    | Types.Cstr_tuple [inner] ->
                      Payload_single (loop (type_name :: visited) inner)
                    | Types.Cstr_tuple inners ->
                      Payload_tuple
                        (List.mapi
                           (fun item_index item_type ->
                             {
                               item_index;
                               item_arity = List.length inners;
                               item_type = loop (type_name :: visited) item_type;
                             })
                           inners)
                    | Types.Cstr_record _ ->
                      errorf ~loc:constructor.Types.cd_loc
                        "Inline-record variant constructors are not supported \
                         in comptime reflection"
                  in
                  if constructor.Types.cd_res <> None then
                    errorf ~loc:constructor.Types.cd_loc
                      "GADT constructors are not supported in comptime \
                       reflection";
                  {
                    constructor_name = Ident.name constructor.Types.cd_id;
                    constructor_payload;
                  })
                constructors )
        | Types.Type_abstract -> (
          match decl.type_manifest with
          | Some manifest -> loop (type_name :: visited) manifest
          | None ->
            errorf ~loc:Location.none
              "Abstract types are not supported in comptime reflection")
        | Types.Type_open ->
          errorf ~loc:Location.none
            "Open types are not supported in comptime reflection"))
    | _ ->
      errorf ~loc:Location.none "Unsupported type shape in comptime reflection"
  in
  loop [] ty

let field_get_builtin field_name =
  VBuiltin
    {
      arity = 1;
      apply =
        (fun _context loc args ->
          match args with
          | [VCode expr] ->
            VCode
              (Exp.field expr (Location.mknoloc (Longident.Lident field_name)))
          | _ ->
            errorf ~loc
              "Reflected field getter expects a runtime record expression");
    }

let tuple_item_get_builtin item_index item_count =
  VBuiltin
    {
      arity = 1;
      apply =
        (fun _context loc args ->
          let tuple_projection expr =
            let names =
              List.init item_count (fun index ->
                  "tuple$" ^ string_of_int item_index ^ "$"
                  ^ string_of_int index)
            in
            let tuple_pattern =
              Pat.tuple
                (List.map (fun name -> Pat.var (Location.mknoloc name)) names)
            in
            let selected =
              Exp.ident
                (Location.mknoloc
                   (Longident.Lident (List.nth names item_index)))
            in
            Exp.match_ expr [Exp.case tuple_pattern selected]
          in
          match args with
          | [VCode expr] -> VCode (tuple_projection expr)
          | _ ->
            errorf ~loc
              "Reflected tuple item getter expects a runtime tuple expression");
    }

let constructor_unpack_builtin constructor_name payload =
  VBuiltin
    {
      arity = 1;
      apply =
        (fun _context loc args ->
          let match_cases () =
            match payload with
            | Payload_none ->
              [
                Exp.case
                  (Pat.construct (lid constructor_name) None)
                  (exp_some (Exp.construct (lid "()") None));
                Exp.case (Pat.any ()) (exp_none ());
              ]
            | Payload_single _ ->
              let payload_name = "payload$comptime" in
              [
                Exp.case
                  (Pat.construct (lid constructor_name)
                     (Some (Pat.var (Location.mknoloc payload_name))))
                  (exp_some
                     (Exp.ident
                        (Location.mknoloc (Longident.Lident payload_name))));
                Exp.case (Pat.any ()) (exp_none ());
              ]
            | Payload_tuple items ->
              let names =
                List.map
                  (fun item ->
                    "payload$comptime" ^ string_of_int item.item_index)
                  items
              in
              [
                Exp.case
                  (Pat.construct (lid constructor_name)
                     (Some
                        (Pat.tuple
                           (List.map
                              (fun name -> Pat.var (Location.mknoloc name))
                              names))))
                  (exp_some
                     (Exp.tuple
                        (List.map
                           (fun name ->
                             Exp.ident
                               (Location.mknoloc (Longident.Lident name)))
                           names)));
                Exp.case (Pat.any ()) (exp_none ());
              ]
          in
          match args with
          | [VCode expr] -> VCode (Exp.match_ expr (match_cases ()))
          | _ ->
            errorf ~loc
              "Reflected constructor unpack expects a runtime variant \
               expression");
    }

let constructor_make_builtin constructor_name payload =
  VBuiltin
    {
      arity = 1;
      apply =
        (fun _context loc args ->
          let constructor_application_expr names =
            let source =
              "let __comptime_ctor = " ^ constructor_name ^ "("
              ^ String.concat ", " names ^ ")"
            in
            match
              Res_driver.parse_implementation_from_source ~for_printer:false
                ~display_filename:"__comptime_constructor__.res" ~source
            with
            | {
             parsetree = [{pstr_desc = Pstr_value (_, [{pvb_expr; _}]); _}];
             _;
            } ->
              pvb_expr
            | _ ->
              errorf ~loc
                "Failed to lower reflected constructor application for `%s`"
                constructor_name
          in
          let rec payload_expr resolved value =
            match (resolved, value) with
            | _, VCode expr -> expr
            | _, VUnit -> Exp.construct (lid "()") None
            | _, VInt i -> exp_int i
            | _, VFloat f -> exp_float f
            | _, VString s -> exp_string s
            | _, VBool b -> exp_bool b
            | Some (Type_option _), VVariant ("None", None) -> exp_none ()
            | Some (Type_option inner), VVariant ("Some", Some value) ->
              exp_some (payload_expr (Some inner) value)
            | Some (Type_array inner), VArray values ->
              Exp.array (List.map (payload_expr (Some inner)) values)
            | Some (Type_list inner), VArray values ->
              Exp.apply
                (Exp.ident
                   (Location.mknoloc
                      (Longident.Ldot (Longident.Lident "List", "fromArray"))))
                [
                  ( Nolabel,
                    Exp.array (List.map (payload_expr (Some inner)) values) );
                ]
            | Some (Type_tuple items), VTuple values ->
              Exp.tuple
                (List.map2
                   (fun item value -> payload_expr (Some item.item_type) value)
                   items values)
            | Some (Type_tuple items), VBuilder (_, builder) ->
              let find_entry index =
                List.find_opt
                  (fun (name, _) -> name = string_of_int index)
                  !builder
              in
              Exp.tuple
                (List.map
                   (fun item ->
                     match find_entry item.item_index with
                     | Some (_, expr) -> expr
                     | None ->
                       errorf ~loc
                         "Missing tuple item %d in reflected constructor \
                          payload"
                         item.item_index)
                   items)
            | Some (Type_record (_name, fields)), VBuilder (_, builder) ->
              let find_entry field_name =
                List.find_opt (fun (name, _) -> name = field_name) !builder
              in
              Exp.record
                (List.map
                   (fun field ->
                     match find_entry field.field_name with
                     | Some (_, expr) ->
                       {
                         lid =
                           Location.mknoloc (Longident.Lident field.field_name);
                         x = expr;
                         opt = false;
                       }
                     | None ->
                       errorf ~loc
                         "Missing field `%s` in reflected constructor payload"
                         field.field_name)
                   fields)
                None
            | _, VTuple values ->
              Exp.tuple (List.map (payload_expr None) values)
            | _, VArray values ->
              Exp.array (List.map (payload_expr None) values)
            | _ ->
              errorf ~loc
                "Reflected constructor make expects a runtime expression or \
                 reifiable payload"
          in
          let resolved_payload =
            match payload with
            | Payload_none -> None
            | Payload_single inner -> Some inner
            | Payload_tuple items -> Some (Type_tuple items)
          in
          let tuple_payload_exprs items value =
            match value with
            | VTuple values ->
              List.map2
                (fun item value -> payload_expr (Some item.item_type) value)
                items values
            | VBuilder (_, builder) ->
              let find_entry index =
                List.find_opt
                  (fun (name, _) -> name = string_of_int index)
                  !builder
              in
              List.map
                (fun item ->
                  match find_entry item.item_index with
                  | Some (_, expr) -> expr
                  | None ->
                    errorf ~loc
                      "Missing tuple item %d in reflected constructor payload"
                      item.item_index)
                items
            | _ ->
              errorf ~loc
                "Reflected tuple constructor make expects a tuple payload"
          in
          match (payload, args) with
          | Payload_none, [VUnit] ->
            VCode (Exp.construct (lid constructor_name) None)
          | Payload_none, [value] ->
            let payload = payload_expr None value in
            VCode
              (Exp.match_ payload
                 [
                   Exp.case
                     (Pat.construct (lid "()") None)
                     (Exp.construct (lid constructor_name) None);
                 ])
          | Payload_single _, [value] ->
            VCode
              (Exp.construct (lid constructor_name)
                 (Some (payload_expr resolved_payload value)))
          | Payload_tuple items, [VCode tuple_expr] ->
            let names =
              List.map
                (fun item -> "payloadComptime" ^ string_of_int item.item_index)
                items
            in
            let applied = constructor_application_expr names in
            VCode
              (Exp.match_ tuple_expr
                 [
                   Exp.case
                     (Pat.tuple
                        (List.map
                           (fun name -> Pat.var (Location.mknoloc name))
                           names))
                     applied;
                 ])
          | Payload_tuple items, [value] ->
            let names =
              List.map
                (fun item -> "payloadComptime" ^ string_of_int item.item_index)
                items
            in
            let bindings =
              List.map2
                (fun name expr -> Vb.mk (Pat.var (Location.mknoloc name)) expr)
                names
                (tuple_payload_exprs items value)
            in
            VCode
              (Exp.let_ Nonrecursive bindings
                 (constructor_application_expr names))
          | _ -> errorf ~loc "Reflected constructor make expects one payload");
    }

let rec field_record_payload field_name field_type =
  let payload =
    StringMap.empty
    |> StringMap.add "fieldName" (VString field_name)
    |> StringMap.add "fieldGet" (field_get_builtin field_name)
    |> StringMap.add "__type" (type_desc_value_of_resolved_type field_type)
  in
  match field_type with
  | Type_string -> VVariant ("StringField", Some (VRecord payload))
  | Type_int -> VVariant ("IntField", Some (VRecord payload))
  | Type_float -> VVariant ("FloatField", Some (VRecord payload))
  | Type_bool -> VVariant ("BoolField", Some (VRecord payload))
  | Type_json -> VVariant ("JsonField", Some (VRecord payload))
  | Type_option inner ->
    VVariant
      ( "OptionField",
        Some
          (VRecord
             (StringMap.add "fieldInner"
                (type_desc_value_of_resolved_type inner)
                payload)) )
  | Type_array inner ->
    VVariant
      ( "ArrayField",
        Some
          (VRecord
             (StringMap.add "fieldInner"
                (type_desc_value_of_resolved_type inner)
                payload)) )
  | Type_list inner ->
    VVariant
      ( "ListField",
        Some
          (VRecord
             (StringMap.add "fieldInner"
                (type_desc_value_of_resolved_type inner)
                payload)) )
  | Type_record (_name, fields) ->
    VVariant
      ( "RecordField",
        Some
          (VRecord
             (StringMap.add "fieldFields"
                (VArray (List.map field_value_of_resolved_field fields))
                payload)) )
  | Type_tuple items ->
    VVariant
      ( "TupleField",
        Some
          (VRecord
             (StringMap.add "fieldItems"
                (VArray (List.map item_value_of_resolved_item items))
                payload)) )
  | Type_variant (_name, constructors) ->
    VVariant
      ( "VariantField",
        Some
          (VRecord
             (StringMap.add "fieldConstructors"
                (VArray
                   (List.map constructor_value_of_resolved_constructor
                      constructors))
                payload)) )

and item_value_of_resolved_item item =
  let payload =
    StringMap.empty
    |> StringMap.add "itemIndex" (VInt item.item_index)
    |> StringMap.add "itemGet"
         (tuple_item_get_builtin item.item_index item.item_arity)
    |> StringMap.add "__type" (type_desc_value_of_resolved_type item.item_type)
  in
  match item.item_type with
  | Type_string -> VVariant ("StringItem", Some (VRecord payload))
  | Type_int -> VVariant ("IntItem", Some (VRecord payload))
  | Type_float -> VVariant ("FloatItem", Some (VRecord payload))
  | Type_bool -> VVariant ("BoolItem", Some (VRecord payload))
  | Type_json -> VVariant ("JsonItem", Some (VRecord payload))
  | Type_option inner ->
    VVariant
      ( "OptionItem",
        Some
          (VRecord
             (StringMap.add "itemInner"
                (type_desc_value_of_resolved_type inner)
                payload)) )
  | Type_array inner ->
    VVariant
      ( "ArrayItem",
        Some
          (VRecord
             (StringMap.add "itemInner"
                (type_desc_value_of_resolved_type inner)
                payload)) )
  | Type_list inner ->
    VVariant
      ( "ListItem",
        Some
          (VRecord
             (StringMap.add "itemInner"
                (type_desc_value_of_resolved_type inner)
                payload)) )
  | Type_record (_name, fields) ->
    VVariant
      ( "RecordItem",
        Some
          (VRecord
             (StringMap.add "itemFields"
                (VArray (List.map field_value_of_resolved_field fields))
                payload)) )
  | Type_tuple items ->
    VVariant
      ( "TupleItem",
        Some
          (VRecord
             (StringMap.add "itemItems"
                (VArray (List.map item_value_of_resolved_item items))
                payload)) )
  | Type_variant (_name, constructors) ->
    VVariant
      ( "VariantItem",
        Some
          (VRecord
             (StringMap.add "itemConstructors"
                (VArray
                   (List.map constructor_value_of_resolved_constructor
                      constructors))
                payload)) )

and constructor_value_of_resolved_constructor constructor =
  let payload =
    StringMap.empty
    |> StringMap.add "constructorName" (VString constructor.constructor_name)
    |> StringMap.add "__payload"
         (match constructor.constructor_payload with
         | Payload_none -> VVariant ("NoPayload", None)
         | Payload_single inner ->
           VVariant ("Single", Some (type_desc_value_of_resolved_type inner))
         | Payload_tuple items ->
           VVariant
             ( "Tuple",
               Some
                 (VRecord
                    (StringMap.empty
                    |> StringMap.add "items"
                         (VArray (List.map item_value_of_resolved_item items))))
             ))
    |> StringMap.add "constructorUnpack"
         (constructor_unpack_builtin constructor.constructor_name
            constructor.constructor_payload)
    |> StringMap.add "constructorMake"
         (constructor_make_builtin constructor.constructor_name
            constructor.constructor_payload)
  in
  match constructor.constructor_payload with
  | Payload_none -> VVariant ("NoPayloadConstructor", Some (VRecord payload))
  | Payload_single inner ->
    VVariant
      ( "SingleConstructor",
        Some
          (VRecord
             (StringMap.add "constructorInner"
                (type_desc_value_of_resolved_type inner)
                payload)) )
  | Payload_tuple items ->
    VVariant
      ( "TupleConstructor",
        Some
          (VRecord
             (StringMap.add "constructorItems"
                (VArray (List.map item_value_of_resolved_item items))
                payload)) )

and field_value_of_resolved_field field =
  field_record_payload field.field_name field.field_type

and type_desc_value_of_resolved_type = function
  | Type_string -> VVariant ("String", None)
  | Type_int -> VVariant ("Int", None)
  | Type_float -> VVariant ("Float", None)
  | Type_bool -> VVariant ("Bool", None)
  | Type_json -> VVariant ("Json", None)
  | Type_option inner ->
    VVariant ("Option", Some (type_desc_value_of_resolved_type inner))
  | Type_array inner ->
    VVariant ("Array", Some (type_desc_value_of_resolved_type inner))
  | Type_list inner ->
    VVariant ("List", Some (type_desc_value_of_resolved_type inner))
  | Type_record (name, fields) ->
    let fields_value = VArray (List.map field_value_of_resolved_field fields) in
    VVariant
      ( "Record",
        Some
          (VRecord
             (StringMap.empty
             |> StringMap.add "recordName" (VString name)
             |> StringMap.add "fields" fields_value)) )
  | Type_tuple items ->
    VVariant
      ( "Tuple",
        Some
          (VRecord
             (StringMap.empty
             |> StringMap.add "items"
                  (VArray (List.map item_value_of_resolved_item items)))) )
  | Type_variant (name, constructors) ->
    VVariant
      ( "Variant",
        Some
          (VRecord
             (StringMap.empty
             |> StringMap.add "variantName" (VString name)
             |> StringMap.add "constructors"
                  (VArray
                     (List.map constructor_value_of_resolved_constructor
                        constructors)))) )

let expected_type_of_some_payload ty =
  let ty = Ctype.repr ty in
  match ty.desc with
  | Types.Tconstr (path, [inner], _) when Path.name path = "option" ->
    Some inner
  | _ -> None

let expected_function_codomain ty =
  let ty = Ctype.repr ty in
  match ty.desc with
  | Types.Tarrow (_arg, ret, _, _) -> Some ret
  | _ -> None

let builder_entries_set builder field_name value_expr =
  let rec loop acc = function
    | [] -> List.rev ((field_name, value_expr) :: acc)
    | (name, _) :: rest when name = field_name ->
      List.rev_append acc ((field_name, value_expr) :: rest)
    | entry :: rest -> loop (entry :: acc) rest
  in
  builder := loop [] !builder

let builder_kind_of_key = function
  | VInt _ -> Some Builder_tuple
  | VRecord field -> (
    match StringMap.find_opt "itemIndex" field with
    | Some (VInt _) -> Some Builder_tuple
    | _ -> (
      match StringMap.find_opt "index" field with
      | Some (VInt _) -> Some Builder_tuple
      | _ -> None))
  | VVariant (_, Some (VRecord field)) -> (
    match StringMap.find_opt "itemIndex" field with
    | Some (VInt _) -> Some Builder_tuple
    | _ -> (
      match StringMap.find_opt "index" field with
      | Some (VInt _) -> Some Builder_tuple
      | _ -> None))
  | _ -> None

let reflected_member_key field =
  match StringMap.find_opt "itemIndex" field with
  | Some (VInt index) -> Some (string_of_int index)
  | _ -> (
    match StringMap.find_opt "fieldName" field with
    | Some (VString name) -> Some name
    | _ -> (
      match StringMap.find_opt "index" field with
      | Some (VInt index) -> Some (string_of_int index)
      | _ -> (
        match StringMap.find_opt "name" field with
        | Some (VString name) -> Some name
        | _ -> None)))

let resolve_builder_key ~loc = function
  | VString field_name -> field_name
  | VInt index -> string_of_int index
  | VRecord field -> (
    match reflected_member_key field with
    | Some key -> key
    | None ->
      errorf ~loc
        "Dict.set on a comptime builder expects a compile-time string, int, or \
         reflected member descriptor")
  | VVariant (_, Some (VRecord field)) -> (
    match reflected_member_key field with
    | Some key -> key
    | None ->
      errorf ~loc
        "Dict.set on a comptime builder expects a compile-time string, int, or \
         reflected member descriptor")
  | _ ->
    errorf ~loc
      "Dict.set on a comptime builder expects a compile-time string, int, or \
       reflected member descriptor"

let resolve_builder_expected_type context expected =
  try Some (resolve_type context.type_env expected) with
  | Location.Error _ -> (
    match context.target_type with
    | Some target -> Some (resolve_type context.type_env target)
    | None -> None)
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
  | VArray values -> Exp.array (List.map (expr_of_value ~loc context) values)
  | VTuple values -> Exp.tuple (List.map (expr_of_value ~loc context) values)
  | VCode expr -> expr
  | VBuilder (kind, builder) -> (
    let entries = !builder in
    let tuple_expr () =
      let parse_index name =
        try int_of_string name
        with Failure _ -> errorf ~loc "Invalid tuple builder key `%s`" name
      in
      let entries =
        List.sort
          (fun (left, _) (right, _) ->
            compare (parse_index left) (parse_index right))
          entries
      in
      Exp.tuple (List.map snd entries)
    in
    match expected_type with
    | Some expected -> (
      match resolve_builder_expected_type context expected with
      | Some (Type_record (_name, fields)) ->
        let find_entry field_name =
          List.find_opt (fun (name, _) -> name = field_name) entries
        in
        let rows =
          List.map
            (fun field ->
              match find_entry field.field_name with
              | Some (_, expr) ->
                {
                  lid = Location.mknoloc (Longident.Lident field.field_name);
                  x = expr;
                  opt = false;
                }
              | None ->
                errorf ~loc "Missing field `%s` in comptime record construction"
                  field.field_name)
            fields
        in
        Exp.record rows None
      | Some (Type_tuple items) ->
        let find_entry index =
          List.find_opt (fun (name, _) -> name = string_of_int index) entries
        in
        Exp.tuple
          (List.map
             (fun item ->
               match find_entry item.item_index with
               | Some (_, expr) -> expr
               | None ->
                 errorf ~loc "Missing tuple item %d in comptime construction"
                   item.item_index)
             items)
      | Some _ | None -> (
        match !kind with
        | Builder_tuple -> tuple_expr ()
        | Builder_unknown ->
          let tuple_entries =
            List.map
              (fun (name, expr) -> Exp.tuple [exp_string name; expr])
              entries
          in
          Exp.apply
            (Exp.ident
               (Location.mknoloc
                  (Longident.Ldot (Longident.Lident "Dict", "fromArray"))))
            [(Nolabel, Exp.array tuple_entries)]))
    | None -> (
      match !kind with
      | Builder_tuple -> tuple_expr ()
      | Builder_unknown ->
        let tuple_entries =
          List.map
            (fun (name, expr) -> Exp.tuple [exp_string name; expr])
            entries
        in
        Exp.apply
          (Exp.ident
             (Location.mknoloc
                (Longident.Ldot (Longident.Lident "Dict", "fromArray"))))
          [(Nolabel, Exp.array tuple_entries)]))
  | VClosure closure -> expr_of_closure ~loc ?expected_type context closure
  | _ -> errorf ~loc "Unsupported comptime value reification"

and expr_of_closure ~loc:_ ?expected_type context closure =
  let ret_type =
    match expected_type with
    | Some expected -> expected_function_codomain expected
    | None -> None
  in
  let runtime_env, pattern = runtime_pattern_bindings closure.pattern in
  let env =
    Ident.fold_name
      (fun id value env -> Ident.add id value env)
      runtime_env !(closure.env)
  in
  let body_value = stage_expression context env closure.body in
  let body =
    expr_of_value ~loc:closure.body.Ir.loc ?expected_type:ret_type context
      body_value
  in
  Exp.fun_ ~arity:None Nolabel None pattern body

and runtime_pattern_bindings pattern =
  let fresh name =
    incr gensym_counter;
    name ^ "$comptime" ^ string_of_int !gensym_counter
  in
  match pattern with
  | Ir.PVar (id, name) ->
    let fresh_name = fresh name in
    ( Ident.add id (VCode (exp_ident fresh_name)) Ident.empty,
      Pat.var (Location.mknoloc fresh_name) )
  | Ir.PAny -> (Ident.empty, Pat.any ())
  | Ir.PConstant c -> (Ident.empty, Pat.constant c)
  | Ir.PTuple patterns ->
    let env, patterns =
      List.fold_right
        (fun pattern (env, patterns) ->
          let env_pattern, pattern = runtime_pattern_bindings pattern in
          ( Ident.fold_name
              (fun id value env -> Ident.add id value env)
              env_pattern env,
            pattern :: patterns ))
        patterns (Ident.empty, [])
    in
    (env, Pat.tuple patterns)
  | Ir.PConstruct (name, patterns) ->
    let env, patterns =
      List.fold_right
        (fun pattern (env, patterns) ->
          let env_pattern, pattern = runtime_pattern_bindings pattern in
          ( Ident.fold_name
              (fun id value env -> Ident.add id value env)
              env_pattern env,
            pattern :: patterns ))
        patterns (Ident.empty, [])
    in
    let payload =
      match patterns with
      | [] -> None
      | [pattern] -> Some pattern
      | patterns -> Some (Pat.tuple patterns)
    in
    (env, Pat.construct (lid name) payload)
  | Ir.PRecord fields ->
    let env, fields =
      List.fold_right
        (fun (name, pattern) (env, fields) ->
          let env_pattern, pattern = runtime_pattern_bindings pattern in
          ( Ident.fold_name
              (fun id value env -> Ident.add id value env)
              env_pattern env,
            {lid = lid name; x = pattern; opt = false} :: fields ))
        fields (Ident.empty, [])
    in
    (env, Pat.record fields Closed)
  | Ir.PAlias (pattern, id, name) ->
    let env, pattern = runtime_pattern_bindings pattern in
    let fresh_name = fresh name in
    ( Ident.add id (VCode (exp_ident fresh_name)) env,
      Pat.alias pattern (Location.mknoloc fresh_name) )

let rec value_is_runtime = function
  | VCode _ -> true
  | VArray values | VTuple values -> List.exists value_is_runtime values
  | VVariant (_, Some value) -> value_is_runtime value
  | _ -> false

let runtime_expr_of_value ~loc context = function
  | VCode expr -> expr
  | value -> expr_of_value ~loc context value

let runtime_expr_of_value_with_expected ~loc context expected_type = function
  | VCode expr -> expr
  | value -> expr_of_value ~loc ~expected_type context value

let rec match_pattern ~loc pattern value =
  match (pattern, value) with
  | Ir.PAny, _ -> Some Ident.empty
  | Ir.PVar (id, _), value -> Some (Ident.add id value Ident.empty)
  | Ir.PAlias (pattern, id, _), value -> (
    match match_pattern ~loc pattern value with
    | None -> None
    | Some env -> Some (Ident.add id value env))
  | Ir.PConstant (Pconst_integer (text, _)), VInt value ->
    if int_of_string text = value then Some Ident.empty else None
  | Ir.PConstant (Pconst_string (text, _)), VString value ->
    if text = value then Some Ident.empty else None
  | Ir.PConstant (Pconst_float (text, _)), VFloat value ->
    if float_of_string text = value then Some Ident.empty else None
  | Ir.PConstruct ("()", []), VUnit -> Some Ident.empty
  | Ir.PTuple patterns, VTuple values
    when List.length patterns = List.length values ->
    List.fold_left2
      (fun acc pattern value ->
        match (acc, match_pattern ~loc pattern value) with
        | Some env, Some env_pattern ->
          Some
            (Ident.fold_name
               (fun id value env -> Ident.add id value env)
               env_pattern env)
        | _ -> None)
      (Some Ident.empty) patterns values
  | Ir.PRecord fields, VRecord record ->
    List.fold_left
      (fun acc (label, pattern) ->
        match (acc, StringMap.find_opt label record) with
        | Some env, Some value -> (
          match match_pattern ~loc pattern value with
          | Some env_pattern ->
            Some
              (Ident.fold_name
                 (fun id value env -> Ident.add id value env)
                 env_pattern env)
          | None -> None)
        | _ -> None)
      (Some Ident.empty) fields
  | Ir.PConstruct (name, patterns), VVariant (ctor, payload) when name = ctor
    -> (
    match (patterns, payload) with
    | [], None -> Some Ident.empty
    | [pattern], Some value -> match_pattern ~loc pattern value
    | patterns, Some (VTuple values)
      when List.length patterns = List.length values ->
      List.fold_left2
        (fun acc pattern value ->
          match (acc, match_pattern ~loc pattern value) with
          | Some env, Some env_pattern ->
            Some
              (Ident.fold_name
                 (fun id value env -> Ident.add id value env)
                 env_pattern env)
          | _ -> None)
        (Some Ident.empty) patterns values
    | _ -> None)
  | _ -> None

let build_recursive_env _context env bindings =
  let env_ref = ref env in
  let env_with_bindings =
    List.fold_left
      (fun env (binding : Ir.binding) ->
        match binding.Ir.pattern with
        | Ir.PVar (id, _) ->
          let value =
            match binding.Ir.expr.desc with
            | Ir.EFun (pattern, body) -> VClosure {pattern; body; env = env_ref}
            | _ ->
              errorf ~loc:binding.Ir.loc
                "Recursive comptime bindings must be functions"
          in
          Ident.add id value env
        | _ ->
          errorf ~loc:binding.Ir.loc
            "Recursive comptime bindings must use simple variable patterns")
      env bindings
  in
  env_ref := env_with_bindings;
  env_with_bindings

let binding_name_from_pattern = function
  | Ir.PVar (id, _) -> Some id
  | Ir.PAlias (_, id, _) -> Some id
  | _ -> None

let rec eval_case_list context env loc scrutinee = function
  | [] -> errorf ~loc "No matching case during comptime evaluation"
  | (case : Ir.case) :: rest -> (
    match match_pattern ~loc:case.Ir.loc case.Ir.lhs scrutinee with
    | None -> eval_case_list context env loc scrutinee rest
    | Some bindings -> (
      let case_env =
        Ident.fold_name
          (fun id value env -> Ident.add id value env)
          bindings env
      in
      match case.Ir.guard with
      | None -> eval context case_env case.Ir.rhs
      | Some guard -> (
        match eval context case_env guard with
        | VBool true -> eval context case_env case.Ir.rhs
        | VBool false -> eval_case_list context env loc scrutinee rest
        | _ ->
          errorf ~loc:guard.loc
            "Comptime guard expressions must evaluate to bool")))

and eval_ident context loc = function
  | Ir.ILocal (id, name) -> (
    fun env ->
      try Ident.find_same id env
      with Not_found ->
        errorf ~loc "Unknown local identifier `%s` during comptime evaluation"
          name)
  | Ir.ITop (id, name) -> (
    fun env ->
      try Ident.find_same id env
      with Not_found -> (
        context.used_top <- IdentSet.add id context.used_top;
        try Ident.find_same id context.cache
        with Not_found ->
          let binding =
            try Ident.find_same id context.top_bindings
            with Not_found ->
              errorf ~loc
                "Unknown top-level identifier `%s` during comptime evaluation"
                name
          in
          let lowered = Ir.lower_expr context.top_ids binding.source_expr in
          let value = stage_expression context env lowered in
          context.cache <- Ident.add id value context.cache;
          value))
  | Ir.IGlobal lid -> fun _env -> VCode (Exp.ident lid)
  | Ir.IBuiltin (builtin, runtime_ident) ->
    let runtime_expr =
      match runtime_ident with
      | Some lid -> Exp.ident lid
      | None -> Exp.ident (lid "__unknown_builtin")
    in
    let unary f = VBuiltin {arity = 1; apply = f} in
    let binary f = VBuiltin {arity = 2; apply = f} in
    let ternary f = VBuiltin {arity = 3; apply = f} in
    let runtime_callback_expr context loc fn arity =
      let names =
        List.init arity (fun index -> "arg$comptime" ^ string_of_int index)
      in
      let args = List.map (fun name -> VCode (exp_ident name)) names in
      let body =
        runtime_expr_of_value ~loc context (apply context ~loc fn args)
      in
      let body =
        List.fold_right
          (fun name body ->
            Ast_compatible.fun_ ~loc ~arity:None
              (Pat.var (Location.mknoloc name))
              body)
          names body
      in
      match body.pexp_desc with
      | Pexp_fun f ->
        {body with pexp_desc = Pexp_fun {f with arity = Some arity}}
      | _ -> body
    in
    let value =
      match builtin with
      | Ir.BReflect ->
        unary (fun context loc args ->
            match args with
            | [VUnit] -> (
              match context.target_type with
              | Some target ->
                type_desc_value_of_resolved_type
                  (resolve_type context.type_env target)
              | None ->
                errorf ~loc
                  "reflect() requires a call site type annotation that \
                   identifies the reflected type")
            | _ -> errorf ~loc "reflect() expects unit")
      | Ir.BFailwith ->
        unary (fun _context loc args ->
            match args with
            | [VString message] -> errorf ~loc "%s" message
            | _ -> errorf ~loc "failwith expects a string")
      | Ir.BFieldType ->
        unary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord field))] -> (
              match StringMap.find_opt "__type" field with
              | Some value -> value
              | None ->
                errorf ~loc "__fieldType expects a reflected field descriptor")
            | _ ->
              errorf ~loc "__fieldType expects a reflected field descriptor")
      | Ir.BFieldName ->
        unary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord field))] -> (
              match StringMap.find_opt "fieldName" field with
              | Some (VString name) -> VString name
              | _ ->
                errorf ~loc "__fieldName expects a reflected field descriptor")
            | _ ->
              errorf ~loc "__fieldName expects a reflected field descriptor")
      | Ir.BFieldGet ->
        binary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord field)); VCode expr] -> (
              match StringMap.find_opt "fieldName" field with
              | Some (VString name) ->
                VCode
                  (Exp.field expr (Location.mknoloc (Longident.Lident name)))
              | _ ->
                errorf ~loc "__fieldGet expects a reflected field descriptor")
            | [VRecord field; VCode expr] -> (
              match StringMap.find_opt "fieldName" field with
              | Some (VString name) ->
                VCode
                  (Exp.field expr (Location.mknoloc (Longident.Lident name)))
              | _ ->
                errorf ~loc "__fieldGet expects a reflected field descriptor")
            | _ ->
              errorf ~loc
                "__fieldGet expects a reflected field descriptor and runtime \
                 value")
      | Ir.BItemType ->
        unary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord item))] -> (
              match StringMap.find_opt "__type" item with
              | Some value -> value
              | None ->
                errorf ~loc
                  "__itemType expects a reflected tuple item descriptor")
            | _ ->
              errorf ~loc "__itemType expects a reflected tuple item descriptor")
      | Ir.BItemIndex ->
        unary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord item))] -> (
              match StringMap.find_opt "itemIndex" item with
              | Some (VInt index) -> VInt index
              | _ ->
                errorf ~loc
                  "__itemIndex expects a reflected tuple item descriptor")
            | _ ->
              errorf ~loc
                "__itemIndex expects a reflected tuple item descriptor")
      | Ir.BItemGet ->
        binary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord item)); VCode expr] -> (
              match StringMap.find_opt "itemGet" item with
              | Some getter -> apply context ~loc getter [VCode expr]
              | None ->
                errorf ~loc
                  "__itemGet expects a reflected tuple item descriptor")
            | _ ->
              errorf ~loc
                "__itemGet expects a reflected tuple item descriptor and \
                 runtime value")
      | Ir.BConstructorPayload ->
        unary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord constructor))] -> (
              match StringMap.find_opt "__payload" constructor with
              | Some value -> value
              | None ->
                errorf ~loc
                  "__constructorPayload expects a reflected constructor \
                   descriptor")
            | _ ->
              errorf ~loc
                "__constructorPayload expects a reflected constructor \
                 descriptor")
      | Ir.BConstructorName ->
        unary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord constructor))] -> (
              match StringMap.find_opt "constructorName" constructor with
              | Some (VString name) -> VString name
              | _ ->
                errorf ~loc
                  "__constructorName expects a reflected constructor descriptor"
              )
            | _ ->
              errorf ~loc
                "__constructorName expects a reflected constructor descriptor")
      | Ir.BConstructorUnpack ->
        binary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord constructor)); value] -> (
              match StringMap.find_opt "constructorUnpack" constructor with
              | Some unpack -> apply context ~loc unpack [value]
              | None ->
                errorf ~loc
                  "__constructorUnpack expects a reflected constructor \
                   descriptor")
            | _ ->
              errorf ~loc
                "__constructorUnpack expects a reflected constructor \
                 descriptor and runtime value")
      | Ir.BConstructorMake ->
        binary (fun _context loc args ->
            match args with
            | [VVariant (_, Some (VRecord constructor)); value] -> (
              match StringMap.find_opt "constructorMake" constructor with
              | Some make -> apply context ~loc make [value]
              | None ->
                errorf ~loc
                  "__constructorMake expects a reflected constructor descriptor"
              )
            | _ ->
              errorf ~loc
                "__constructorMake expects a reflected constructor descriptor \
                 and payload")
      | Ir.BErase ->
        unary (fun _context _loc args ->
            match args with
            | [value] -> value
            | _ -> assert false)
      | Ir.BAdd ->
        binary (fun _context loc args ->
            match args with
            | [VInt left; VInt right] -> VInt (left + right)
            | _ ->
              VCode
                (Exp.apply runtime_expr
                   [
                     ( Nolabel,
                       runtime_expr_of_value ~loc context (List.nth args 0) );
                     ( Nolabel,
                       runtime_expr_of_value ~loc context (List.nth args 1) );
                   ]))
      | Ir.BConcat ->
        binary (fun _context loc args ->
            match args with
            | [VString left; VString right] -> VString (left ^ right)
            | _ ->
              VCode
                (Exp.apply runtime_expr
                   [
                     ( Nolabel,
                       runtime_expr_of_value ~loc context (List.nth args 0) );
                     ( Nolabel,
                       runtime_expr_of_value ~loc context (List.nth args 1) );
                   ]))
      | Ir.BArrayGet ->
        binary (fun _context loc args ->
            match args with
            | [VArray values; VInt index] ->
              if index < 0 || index >= List.length values then
                VVariant ("None", None)
              else VVariant ("Some", Some (List.nth values index))
            | _ ->
              VCode
                (Exp.apply runtime_expr
                   [
                     ( Nolabel,
                       runtime_expr_of_value ~loc context (List.nth args 0) );
                     ( Nolabel,
                       runtime_expr_of_value ~loc context (List.nth args 1) );
                   ]))
      | Ir.BArrayMap ->
        binary (fun context loc args ->
            match args with
            | [VArray values; fn] ->
              VArray
                (List.map (fun value -> apply context ~loc fn [value]) values)
            | [array_value; fn]
              when value_is_runtime array_value || value_is_runtime fn ->
              let callback = runtime_callback_expr context loc fn 1 in
              VCode
                (Exp.apply runtime_expr
                   [
                     (Nolabel, runtime_expr_of_value ~loc context array_value);
                     (Nolabel, callback);
                   ])
            | _ -> errorf ~loc "Array.map expects an array and a function")
      | Ir.BArrayForEach ->
        binary (fun context loc args ->
            match args with
            | [VArray values; fn] ->
              List.iter
                (fun value -> ignore (apply context ~loc fn [value]))
                values;
              VUnit
            | [array_value; fn]
              when value_is_runtime array_value || value_is_runtime fn ->
              let callback = runtime_callback_expr context loc fn 1 in
              VCode
                (Exp.apply runtime_expr
                   [
                     (Nolabel, runtime_expr_of_value ~loc context array_value);
                     (Nolabel, callback);
                   ])
            | _ -> errorf ~loc "Array.forEach expects an array and a function")
      | Ir.BArrayReduce ->
        ternary (fun context loc args ->
            match args with
            | [VArray values; init; fn] ->
              List.fold_left
                (fun acc value -> apply context ~loc fn [acc; value])
                init values
            | [array_value; init; fn]
              when value_is_runtime array_value
                   || value_is_runtime init || value_is_runtime fn ->
              let callback = runtime_callback_expr context loc fn 2 in
              VCode
                (Exp.apply runtime_expr
                   [
                     (Nolabel, runtime_expr_of_value ~loc context array_value);
                     (Nolabel, runtime_expr_of_value ~loc context init);
                     (Nolabel, callback);
                   ])
            | _ -> errorf ~loc "Array.reduce expects array, init, function")
      | Ir.BArrayReduceRight ->
        ternary (fun context loc args ->
            match args with
            | [VArray values; init; fn] ->
              List.fold_right
                (fun value acc -> apply context ~loc fn [acc; value])
                values init
            | [array_value; init; fn]
              when value_is_runtime array_value
                   || value_is_runtime init || value_is_runtime fn ->
              let callback = runtime_callback_expr context loc fn 2 in
              VCode
                (Exp.apply runtime_expr
                   [
                     (Nolabel, runtime_expr_of_value ~loc context array_value);
                     (Nolabel, runtime_expr_of_value ~loc context init);
                     (Nolabel, callback);
                   ])
            | _ -> errorf ~loc "Array.reduceRight expects array, init, function")
      | Ir.BIntToFloat ->
        unary (fun _context loc args ->
            match args with
            | [VInt value] -> VFloat (float_of_int value)
            | [value] ->
              VCode
                (Exp.apply runtime_expr
                   [(Nolabel, runtime_expr_of_value ~loc context value)])
            | _ -> errorf ~loc "Int.toFloat expects one argument")
      | Ir.BFloatToInt ->
        unary (fun _context loc args ->
            match args with
            | [VFloat value] -> VInt (int_of_float value)
            | [value] ->
              VCode
                (Exp.apply runtime_expr
                   [(Nolabel, runtime_expr_of_value ~loc context value)])
            | _ -> errorf ~loc "Float.toInt expects one argument")
      | Ir.BDictMake ->
        unary (fun _context _loc _args ->
            VBuilder (ref Builder_unknown, ref []))
      | Ir.BDictCopy ->
        unary (fun _context loc args ->
            match args with
            | [VBuilder (kind, builder)] -> VBuilder (ref !kind, ref !builder)
            | [value] ->
              VCode
                (Exp.apply runtime_expr
                   [(Nolabel, runtime_expr_of_value ~loc context value)])
            | _ -> errorf ~loc "Dict.copy expects one argument")
      | Ir.BDictSet ->
        ternary (fun _context loc args ->
            match args with
            | [VBuilder (kind, builder); key; value] ->
              (match builder_kind_of_key key with
              | Some Builder_tuple -> kind := Builder_tuple
              | Some Builder_unknown | None -> ());
              let field_name = resolve_builder_key ~loc key in
              builder_entries_set builder field_name
                (runtime_expr_of_value ~loc context value);
              VUnit
            | [builder; key; value] ->
              VCode
                (Exp.apply runtime_expr
                   [
                     (Nolabel, runtime_expr_of_value ~loc context builder);
                     (Nolabel, runtime_expr_of_value ~loc context key);
                     (Nolabel, runtime_expr_of_value ~loc context value);
                   ])
            | _ -> errorf ~loc "Dict.set expects three arguments")
      | Ir.BDictGet ->
        binary (fun _context loc args ->
            match args with
            | [obj; key] ->
              VCode
                (Exp.apply runtime_expr
                   [
                     (Nolabel, runtime_expr_of_value ~loc context obj);
                     (Nolabel, runtime_expr_of_value ~loc context key);
                   ])
            | _ -> errorf ~loc "Dict.get expects two arguments")
    in
    fun _env -> value

and eval context env expr =
  match expr.Ir.desc with
  | Ir.EConstant (Pconst_integer (text, None)) -> VInt (int_of_string text)
  | Ir.EConstant (Pconst_float (text, _)) -> VFloat (float_of_string text)
  | Ir.EConstant (Pconst_string (text, _)) -> VString text
  | Ir.EConstant _ ->
    errorf ~loc:expr.Ir.loc "Unsupported constant in comptime evaluation"
  | Ir.EIdent ident -> eval_ident context expr.Ir.loc ident env
  | Ir.EConstruct (_, "()", []) -> VUnit
  | Ir.EConstruct (_, "true", []) -> VBool true
  | Ir.EConstruct (_, "false", []) -> VBool false
  | Ir.EConstruct (_, "None", []) -> VVariant ("None", None)
  | Ir.EConstruct (_, "Some", [payload]) ->
    let payload = eval context env payload in
    VVariant ("Some", Some payload)
  | Ir.EConstruct (ctor_lid, name, payloads)
    when not (is_comptime_constructor ctor_lid name) ->
    let payloads = List.map (eval context env) payloads in
    let payload =
      match payloads with
      | [] -> None
      | [payload] ->
        Some (runtime_expr_of_value ~loc:expr.Ir.loc context payload)
      | payloads ->
        Some
          (Exp.tuple
             (List.map
                (runtime_expr_of_value ~loc:expr.Ir.loc context)
                payloads))
    in
    VCode (Exp.construct ctor_lid payload)
  | Ir.ELet (Nonrecursive, bindings, body) ->
    let env =
      List.fold_left
        (fun env (binding : Ir.binding) ->
          let value = eval context env binding.Ir.expr in
          match match_pattern ~loc:binding.Ir.loc binding.Ir.pattern value with
          | Some bindings ->
            Ident.fold_name
              (fun id value env -> Ident.add id value env)
              bindings env
          | None ->
            errorf ~loc:binding.Ir.loc "Failed to bind a comptime let-pattern")
        env bindings
    in
    eval context env body
  | Ir.ELet (Recursive, bindings, body) ->
    let env = build_recursive_env context env bindings in
    eval context env body
  | Ir.EFun (pattern, body) -> VClosure {pattern; body; env = ref env}
  | Ir.EApply (fn, args) ->
    let fn = eval context env fn in
    let args = List.map (eval context env) args in
    apply context ~loc:expr.Ir.loc fn args
  | Ir.EMatch (scrutinee, cases) ->
    let scrutinee = eval context env scrutinee in
    eval_case_list context env expr.Ir.loc scrutinee cases
  | Ir.EIfThenElse (condition, when_true, when_false) -> (
    match eval context env condition with
    | VBool true -> eval context env when_true
    | VBool false -> (
      match when_false with
      | Some when_false -> eval context env when_false
      | None -> VUnit)
    | _ ->
      errorf ~loc:condition.Ir.loc
        "if conditions in comptime evaluation must be booleans")
  | Ir.EAssert asserted -> (
    match eval context env asserted with
    | VBool true -> VUnit
    | VBool false ->
      errorf ~loc:asserted.Ir.loc "Assertion failed during comptime evaluation"
    | _ ->
      errorf ~loc:asserted.Ir.loc
        "assert expects a boolean during comptime evaluation")
  | Ir.EField (record_expr, label) -> (
    match eval context env record_expr with
    | VRecord record -> (
      match StringMap.find_opt label record with
      | Some value -> value
      | None ->
        errorf ~loc:record_expr.Ir.loc "Unknown comptime field `%s`" label)
    | _ ->
      errorf ~loc:record_expr.Ir.loc
        "Field access in comptime evaluation expects a reflected record value")
  | _ -> stage_expression context env expr

and apply context ~loc fn args =
  match fn with
  | VBuiltin builtin ->
    if List.length args <> builtin.arity then
      errorf ~loc "Builtin expected %d arguments" builtin.arity
    else builtin.apply context loc args
  | VClosure closure -> (
    match args with
    | [] -> fn
    | arg :: rest -> (
      match match_pattern ~loc closure.pattern arg with
      | Some bindings ->
        let env =
          Ident.fold_name
            (fun id value env -> Ident.add id value env)
            bindings !(closure.env)
        in
        let result = stage_expression context env closure.body in
        if rest = [] then result else apply context ~loc result rest
      | None -> errorf ~loc "Failed to apply comptime function"))
  | VCode fn_expr ->
    let arg_exprs = List.map (runtime_expr_of_value ~loc context) args in
    VCode (Exp.apply fn_expr (List.map (fun expr -> (Nolabel, expr)) arg_exprs))
  | _ ->
    errorf ~loc "Attempted to apply a non-function during comptime evaluation"

and stage_expression_impl context env expr =
  match expr.Ir.desc with
  | Ir.EConstant (Pconst_integer (text, None)) -> VInt (int_of_string text)
  | Ir.EConstant (Pconst_float (text, _)) -> VFloat (float_of_string text)
  | Ir.EConstant (Pconst_string (text, _)) -> VString text
  | Ir.EConstant _ ->
    errorf ~loc:expr.Ir.loc "Unsupported constant in comptime staging"
  | Ir.EIdent ident -> eval_ident context expr.Ir.loc ident env
  | Ir.EArray exprs ->
    let values = List.map (stage_expression context env) exprs in
    if List.exists value_is_runtime values then
      VCode
        (Exp.array
           (List.map (runtime_expr_of_value ~loc:expr.Ir.loc context) values))
    else VArray values
  | Ir.ETuple exprs ->
    let values = List.map (stage_expression context env) exprs in
    if List.exists value_is_runtime values then
      VCode
        (Exp.tuple
           (List.map (runtime_expr_of_value ~loc:expr.Ir.loc context) values))
    else VTuple values
  | Ir.EConstruct (_, "()", []) -> VUnit
  | Ir.EConstruct (_, "true", []) -> VBool true
  | Ir.EConstruct (_, "false", []) -> VBool false
  | Ir.EConstruct (_, "None", []) -> VVariant ("None", None)
  | Ir.EConstruct (_, "Some", [payload]) ->
    let payload_value = stage_expression context env payload in
    if value_is_runtime payload_value then
      VCode
        (exp_some
           (runtime_expr_of_value ~loc:payload.Ir.loc context payload_value))
    else VVariant ("Some", Some payload_value)
  | Ir.EConstruct (ctor_lid, name, payloads)
    when not (is_comptime_constructor ctor_lid name) ->
    let payloads = List.map (stage_expression context env) payloads in
    let payload =
      match payloads with
      | [] -> None
      | [payload] ->
        Some (runtime_expr_of_value ~loc:expr.Ir.loc context payload)
      | payloads ->
        Some
          (Exp.tuple
             (List.map
                (runtime_expr_of_value ~loc:expr.Ir.loc context)
                payloads))
    in
    VCode (Exp.construct ctor_lid payload)
  | Ir.EConstruct (_, name, payloads) ->
    let payloads = List.map (stage_expression context env) payloads in
    let payload =
      match payloads with
      | [] -> None
      | [payload] -> Some payload
      | payloads -> Some (VTuple payloads)
    in
    VVariant (name, payload)
  | Ir.EField (record_expr, label) -> (
    match stage_expression context env record_expr with
    | VRecord record -> (
      match StringMap.find_opt label record with
      | Some value -> value
      | None ->
        errorf ~loc:record_expr.Ir.loc "Unknown comptime field `%s`" label)
    | VCode record_expr ->
      VCode (Exp.field record_expr (Location.mknoloc (Longident.Lident label)))
    | _ ->
      errorf ~loc:record_expr.Ir.loc
        "Field access in comptime staging expects a reflected record or \
         runtime expression")
  | Ir.EFun (pattern, body) -> VClosure {pattern; body; env = ref env}
  | Ir.ELet (Nonrecursive, bindings, body) ->
    stage_let context env bindings body
  | Ir.ELet (Recursive, bindings, body) ->
    let env = build_recursive_env context env bindings in
    stage_expression context env body
  | Ir.ESequence (left, right) ->
    let left_value = stage_expression context env left in
    let right_value = stage_expression context env right in
    stage_sequence context expr.Ir.loc left_value right_value
  | Ir.EIfThenElse (condition, when_true, when_false) ->
    let condition_value = stage_expression context env condition in
    stage_ifthenelse context env expr.Ir.loc condition_value when_true
      when_false
  | Ir.EMatch (scrutinee, cases) ->
    let scrutinee_value = stage_expression context env scrutinee in
    stage_match context env expr.Ir.loc scrutinee_value cases
  | Ir.EAssert asserted -> (
    match stage_expression context env asserted with
    | VBool true -> VUnit
    | VBool false ->
      errorf ~loc:asserted.Ir.loc "Assertion failed during comptime evaluation"
    | VCode asserted_code -> VCode (Exp.assert_ asserted_code)
    | _ ->
      errorf ~loc:asserted.Ir.loc
        "assert expects a boolean during comptime evaluation")
  | Ir.EApply (fn, args) ->
    let fn = stage_expression context env fn in
    let args = List.map (stage_expression context env) args in
    apply context ~loc:expr.Ir.loc fn args
  | Ir.ERecord (rows, spread) ->
    let rows =
      List.map
        (fun (name, expr) -> (name, stage_expression context env expr))
        rows
    in
    if
      List.exists (fun (_, value) -> value_is_runtime value) rows
      || Option.is_some spread
    then
      let rows =
        List.map
          (fun (name, value) ->
            {
              lid = lid name;
              x = runtime_expr_of_value ~loc:expr.Ir.loc context value;
              opt = false;
            })
          rows
      in
      let spread =
        match spread with
        | Some spread ->
          Some
            (runtime_expr_of_value ~loc:expr.Ir.loc context
               (stage_expression context env spread))
        | None -> None
      in
      VCode (Exp.record rows spread)
    else
      VRecord
        (List.fold_left
           (fun record (name, value) -> StringMap.add name value record)
           StringMap.empty rows)

and stage_let context env bindings body =
  let env, runtime_bindings =
    List.fold_left
      (fun (env, runtime_bindings) (binding : Ir.binding) ->
        let value = stage_expression context env binding.Ir.expr in
        match
          (binding_name_from_pattern binding.Ir.pattern, value_is_runtime value)
        with
        | Some id, false -> (Ident.add id value env, runtime_bindings)
        | Some id, true ->
          let runtime_expr =
            runtime_expr_of_value ~loc:binding.Ir.loc context value
          in
          let name = Ident.name id in
          let env = Ident.add id (VCode (exp_ident name)) env in
          let binding = Vb.mk (Pat.var (Location.mknoloc name)) runtime_expr in
          (env, runtime_bindings @ [binding])
        | None, false -> (env, runtime_bindings)
        | None, true ->
          errorf ~loc:binding.Ir.loc
            "Comptime staging only supports runtime let bindings for simple \
             variable patterns")
      (env, []) bindings
  in
  let body_value = stage_expression context env body in
  match runtime_bindings with
  | [] -> body_value
  | _ ->
    VCode
      (Exp.let_ Nonrecursive runtime_bindings
         (expr_of_value ~loc:body.Ir.loc context body_value))

and stage_sequence context loc left_value right_value =
  match left_value with
  | VUnit -> right_value
  | _ ->
    let left_expr = runtime_expr_of_value ~loc context left_value in
    let right_expr = runtime_expr_of_value ~loc context right_value in
    VCode (Exp.sequence left_expr right_expr)

and stage_ifthenelse context env loc condition_value when_true when_false =
  match condition_value with
  | VBool true -> stage_expression context env when_true
  | VBool false -> (
    match when_false with
    | Some when_false -> stage_expression context env when_false
    | None -> VUnit)
  | _ ->
    let condition_expr = runtime_expr_of_value ~loc context condition_value in
    let when_true_expr =
      runtime_expr_of_value_with_expected ~loc:when_true.Ir.loc context
        when_true.Ir.typ
        (stage_expression context env when_true)
    in
    let when_false_expr =
      match when_false with
      | Some when_false ->
        Some
          (runtime_expr_of_value_with_expected ~loc:when_false.Ir.loc context
             when_false.Ir.typ
             (stage_expression context env when_false))
      | None -> None
    in
    VCode (Exp.ifthenelse condition_expr when_true_expr when_false_expr)

and stage_match context env loc scrutinee_value cases =
  if not (value_is_runtime scrutinee_value) then
    let rec select_case = function
      | [] -> errorf ~loc "Non-exhaustive comptime switch"
      | (case : Ir.case) :: rest -> (
        match match_pattern ~loc:case.Ir.loc case.Ir.lhs scrutinee_value with
        | None -> select_case rest
        | Some bindings ->
          let env =
            Ident.fold_name
              (fun id value env -> Ident.add id value env)
              bindings env
          in
          let guard_ok =
            match case.Ir.guard with
            | None -> true
            | Some guard -> (
              match stage_expression context env guard with
              | VBool result -> result
              | _ ->
                errorf ~loc:guard.Ir.loc
                  "Comptime guard expressions must evaluate to bool")
          in
          if guard_ok then stage_expression context env case.Ir.rhs
          else select_case rest)
    in
    select_case cases
  else
    let scrutinee_expr = runtime_expr_of_value ~loc context scrutinee_value in
    let cases =
      List.map
        (fun (case : Ir.case) ->
          let pattern_env, lhs = runtime_pattern_bindings case.Ir.lhs in
          let env =
            Ident.fold_name
              (fun id value env -> Ident.add id value env)
              pattern_env env
          in
          let guard =
            match case.Ir.guard with
            | None -> None
            | Some guard ->
              Some
                (runtime_expr_of_value ~loc:guard.Ir.loc context
                   (stage_expression context env guard))
          in
          let rhs =
            runtime_expr_of_value_with_expected ~loc:case.Ir.rhs.loc context
              case.Ir.rhs.typ
              (stage_expression context env case.Ir.rhs)
          in
          Exp.case lhs ?guard rhs)
        cases
    in
    VCode (Exp.match_ scrutinee_expr cases)

let extract_target_type_from_expected ty =
  let ty = Ctype.repr ty in
  match ty.desc with
  | Types.Tarrow (arg, ret, _, _) ->
    let arg = Ctype.repr arg.typ in
    if
      match arg.desc with
      | Types.Tconstr (path, [], _) -> is_json_path path
      | _ -> false
    then
      let ret = Ctype.repr ret in
      match ret.desc with
      | Types.Tconstr (path, [inner], _) when Path.name path = "option" ->
        Some inner
      | _ -> None
    else Some arg
  | _ -> None

let is_surface_module = function
  | {
      pstr_desc =
        Pstr_module
          {
            pmb_name = {txt = "Comptime"; _};
            pmb_expr = {pmod_desc = Pmod_structure items; _};
            _;
          };
      _;
    } ->
    List.exists
      (function
        | {pstr_desc = Pstr_primitive {pval_name = {txt = "__marker"; _}; _}; _}
          ->
          true
        | _ -> false)
      items
  | _ -> false

let is_surface_dict_module = function
  | {
      pstr_desc =
        Pstr_module
          {
            pmb_name = {txt = "Dict"; _};
            pmb_expr = {pmod_desc = Pmod_structure items; _};
            _;
          };
      _;
    } ->
    List.exists
      (function
        | {
            pstr_desc =
              Pstr_primitive
                {
                  pval_name = {txt = "make"; _};
                  pval_prim = "comptime_dict_make" :: _;
                  _;
                };
            _;
          } ->
          true
        | _ -> false)
      items
  | _ -> false

let is_comptime_open = function
  | {
      pstr_desc =
        Pstr_open {popen_lid = {txt = Longident.Lident "Comptime"; _}; _};
      _;
    } ->
    true
  | _ -> false

let is_marker_expr expr =
  match expr.pexp_desc with
  | Pexp_apply
      {
        funct =
          {
            pexp_desc =
              Pexp_ident
                {
                  txt = Longident.Ldot (Longident.Lident "Comptime", "__marker");
                  _;
                };
            _;
          };
        args = [(Nolabel, _payload)];
        _;
      } ->
    true
  | _ -> false

let marker_payload expr =
  match expr.pexp_desc with
  | Pexp_apply {args = [(Nolabel, payload)]; _} -> payload
  | _ -> assert false

let rec parsetree_binding_name_from_pattern pat =
  match pat.ppat_desc with
  | Ppat_var {txt; _} -> Some txt
  | Ppat_constraint (pat, _) | Ppat_alias (pat, _) ->
    parsetree_binding_name_from_pattern pat
  | _ -> None

let rewrite ~typedtree ast =
  let () = stage_expression_ref := stage_expression_impl in
  let top_ids = Ir.top_level_ids typedtree in
  let top_bindings =
    List.fold_left
      (fun tbl (item : Typedtree.structure_item) ->
        match item.str_desc with
        | Tstr_value (_, bindings) ->
          List.fold_left
            (fun tbl (binding : Typedtree.value_binding) ->
              match Typecore.id_of_pattern binding.vb_pat with
              | Some id ->
                Ident.add id
                  {
                    source_name = Ident.name id;
                    source_expr = binding.vb_expr;
                    source_loc = binding.vb_loc;
                  }
                  tbl
              | None -> tbl)
            tbl bindings
        | _ -> tbl)
      Ident.empty typedtree.str_items
  in
  let context target_type =
    {
      top_bindings;
      top_ids;
      cache = Ident.empty;
      used_top = IdentSet.empty;
      target_type;
      type_env = typedtree.str_final_env;
    }
  in
  let replacements = Hashtbl.create 8 in
  List.iter
    (fun (item : Typedtree.structure_item) ->
      match item.str_desc with
      | Tstr_value (_, bindings) ->
        List.iter
          (fun (binding : Typedtree.value_binding) ->
            match Typecore.id_of_pattern binding.vb_pat with
            | Some id -> (
              match binding.vb_expr.exp_desc with
              | Texp_apply
                  {
                    funct =
                      {
                        exp_desc =
                          Texp_ident
                            ( _,
                              {
                                txt =
                                  Longident.Ldot
                                    (Longident.Lident "Comptime", "__marker");
                                _;
                              },
                              _ );
                        _;
                      };
                    args = [(_, Some payload)];
                    _;
                  } ->
                let target_type =
                  extract_target_type_from_expected binding.vb_expr.exp_type
                in
                let ctx = context target_type in
                let value =
                  stage_expression ctx Ident.empty
                    (Ir.lower_expr top_ids payload)
                in
                let expr =
                  expr_of_value ~loc:binding.vb_expr.exp_loc
                    ?expected_type:(Some binding.vb_expr.exp_type) ctx value
                in
                Hashtbl.replace replacements (Ident.name id) (expr, ctx.used_top)
              | _ -> ())
            | None -> ())
          bindings
      | _ -> ())
    typedtree.str_items;
  if Hashtbl.length replacements = 0 then None
  else
    let used_top =
      Hashtbl.fold
        (fun _ (_expr, used) acc -> IdentSet.union used acc)
        replacements IdentSet.empty
    in
    let ast =
      List.filter_map
        (fun item ->
          if
            is_surface_module item
            || is_surface_dict_module item
            || is_comptime_open item
          then None
          else
            match item.pstr_desc with
            | Pstr_value (rec_flag, bindings) ->
              let bindings =
                List.filter_map
                  (fun vb ->
                    match parsetree_binding_name_from_pattern vb.pvb_pat with
                    | Some txt ->
                      if Hashtbl.mem replacements txt then
                        let expr, _used = Hashtbl.find replacements txt in
                        Some {vb with pvb_expr = expr}
                      else if
                        IdentSet.exists (fun id -> Ident.name id = txt) used_top
                      then None
                      else Some vb
                    | None -> Some vb)
                  bindings
              in
              if bindings = [] then None
              else Some {item with pstr_desc = Pstr_value (rec_flag, bindings)}
            | _ -> Some item)
        ast
    in
    Some ast

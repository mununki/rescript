[@@@warning "-45"]

open Ast_helper
open Ast_mapper
open Asttypes
open Longident
open Parsetree

let errorf ~loc fmt =
  Format.kasprintf (fun message -> Location.raise_errorf ~loc "%s" message) fmt

let lid txt = Location.mknoloc (Lident txt)

let expr_payload_single ~loc payload =
  match payload with
  | PStr [{pstr_desc = Pstr_eval (expr, _); _}] -> expr
  | _ -> errorf ~loc "Expected a single expression payload"

let comptime_marker_expr expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__marker"))))
    [(Nolabel, expr)]

type typ_subject = FieldSubject of string | ItemSubject of string

let erase_expr expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__erase"))))
    [(Nolabel, expr)]

let field_type_expr field_expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__fieldType"))))
    [(Nolabel, field_expr)]

let field_name_expr field_expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__fieldName"))))
    [(Nolabel, field_expr)]

let field_get_expr field_expr arg_expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__fieldGet"))))
    [(Nolabel, field_expr); (Nolabel, arg_expr)]

let item_type_expr item_expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__itemType"))))
    [(Nolabel, item_expr)]

let item_index_expr item_expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__itemIndex"))))
    [(Nolabel, item_expr)]

let item_get_expr item_expr arg_expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__itemGet"))))
    [(Nolabel, item_expr); (Nolabel, arg_expr)]

let constructor_payload_expr ctor_expr =
  Exp.apply
    (Exp.ident
       (Location.mknoloc (Ldot (Lident "Comptime", "__constructorPayload"))))
    [(Nolabel, ctor_expr)]

let constructor_name_expr ctor_expr =
  Exp.apply
    (Exp.ident
       (Location.mknoloc (Ldot (Lident "Comptime", "__constructorName"))))
    [(Nolabel, ctor_expr)]

let constructor_unpack_expr ctor_expr arg_expr =
  Exp.apply
    (Exp.ident
       (Location.mknoloc (Ldot (Lident "Comptime", "__constructorUnpack"))))
    [(Nolabel, ctor_expr); (Nolabel, arg_expr)]

let constructor_make_expr ctor_expr arg_expr =
  Exp.apply
    (Exp.ident
       (Location.mknoloc (Ldot (Lident "Comptime", "__constructorMake"))))
    [(Nolabel, ctor_expr); (Nolabel, arg_expr)]

let classify_typ_scrutinee expr =
  match expr.pexp_desc with
  | Pexp_field
      ( {pexp_desc = Pexp_ident {txt = Lident "field"; _}; _},
        {txt = Lident "typ"; _} ) ->
    Some (FieldSubject "field")
  | Pexp_field
      ( {pexp_desc = Pexp_ident {txt = Lident "item"; _}; _},
        {txt = Lident "typ"; _} ) ->
    Some (ItemSubject "item")
  | _ -> None

let classify_payload_scrutinee expr =
  match expr.pexp_desc with
  | Pexp_field
      ( {pexp_desc = Pexp_ident {txt = Lident ctor_name; _}; _},
        {txt = Lident "payload"; _} )
    when ctor_name = "constructor" ->
    Some ctor_name
  | _ -> None

let name_get_payload_pattern extra_fields =
  Pat.record
    ([
       {lid = lid "name"; x = Pat.var (Location.mknoloc "name"); opt = false};
       {lid = lid "get"; x = Pat.var (Location.mknoloc "get"); opt = false};
     ]
    @ extra_fields)
    Closed

let index_get_payload_pattern extra_fields =
  Pat.record
    ([
       {lid = lid "index"; x = Pat.var (Location.mknoloc "index"); opt = false};
       {lid = lid "get"; x = Pat.var (Location.mknoloc "get"); opt = false};
     ]
    @ extra_fields)
    Closed

let constructor_payload_pattern extra_fields =
  Pat.record
    ([
       {
         lid = lid "constructorName";
         x = Pat.var (Location.mknoloc "name");
         opt = false;
       };
       {
         lid = lid "constructorUnpack";
         x = Pat.var (Location.mknoloc "unpack");
         opt = false;
       };
       {
         lid = lid "constructorMake";
         x = Pat.var (Location.mknoloc "make");
         opt = false;
       };
     ]
    @ extra_fields)
    Closed

let lower_record_payload_field ~internal pattern =
  {lid = lid internal; x = pattern; opt = false}

let extract_public_record_field_pattern ~label pat =
  match pat.ppat_desc with
  | Ppat_record (fields, _) -> (
    match
      List.find_opt
        (fun field ->
          match field.lid.txt with
          | Lident name -> name = label
          | _ -> false)
        fields
    with
    | Some field -> field.x
    | None ->
      errorf ~loc:pat.ppat_loc
        "Expected `%s` in comptime surface payload pattern" label)
  | _ ->
    errorf ~loc:pat.ppat_loc
      "Expected a record payload pattern in comptime surface"

type type_desc_payload_kind = RecordPayload | TuplePayload | VariantPayload

let lower_type_desc_payload_pattern kind pat =
  match pat.ppat_desc with
  | Ppat_record (fields, closed) ->
    let lowered_fields =
      List.map
        (fun field ->
          let internal =
            match (kind, field.lid.txt) with
            | RecordPayload, Lident "name" -> "recordName"
            | VariantPayload, Lident "name" -> "variantName"
            | TuplePayload, Lident "name" ->
              errorf ~loc:field.lid.loc
                "Tuple descriptors do not expose a `name` field"
            | _, Lident "fields" -> "fields"
            | _, Lident "items" -> "items"
            | _, Lident "constructors" -> "constructors"
            | _, Lident label ->
              errorf ~loc:field.lid.loc
                "Unsupported descriptor field `%s` in comptime surface" label
            | _, _ ->
              errorf ~loc:field.lid.loc
                "Unsupported descriptor field in comptime surface"
          in
          lower_record_payload_field ~internal field.x)
        fields
    in
    Pat.record lowered_fields closed
  | Ppat_any | Ppat_var _ | Ppat_alias _ -> pat
  | _ ->
    errorf ~loc:pat.ppat_loc
      "Expected a record payload pattern in comptime surface"

let rec lower_type_desc_pattern pat =
  match pat.ppat_desc with
  | Ppat_construct ({txt = Lident "String"; _}, None) ->
    Pat.construct (lid "String") None
  | Ppat_construct ({txt = Lident "Int"; _}, None) ->
    Pat.construct (lid "Int") None
  | Ppat_construct ({txt = Lident "Float"; _}, None) ->
    Pat.construct (lid "Float") None
  | Ppat_construct ({txt = Lident "Bool"; _}, None) ->
    Pat.construct (lid "Bool") None
  | Ppat_construct ({txt = Lident "Json"; _}, None) ->
    Pat.construct (lid "Json") None
  | Ppat_construct ({txt = Lident "Option"; _}, Some inner) ->
    Pat.construct (lid "Option") (Some (lower_type_desc_pattern inner))
  | Ppat_construct ({txt = Lident "Array"; _}, Some inner) ->
    Pat.construct (lid "Array") (Some (lower_type_desc_pattern inner))
  | Ppat_construct ({txt = Lident "List"; _}, Some inner) ->
    Pat.construct (lid "List") (Some (lower_type_desc_pattern inner))
  | Ppat_construct ({txt = Lident "Record"; _}, Some payload) ->
    Pat.construct (lid "Record")
      (Some (lower_type_desc_payload_pattern RecordPayload payload))
  | Ppat_construct ({txt = Lident "Tuple"; _}, Some payload) ->
    Pat.construct (lid "Tuple")
      (Some (lower_type_desc_payload_pattern TuplePayload payload))
  | Ppat_construct ({txt = Lident "Variant"; _}, Some payload) ->
    Pat.construct (lid "Variant")
      (Some (lower_type_desc_payload_pattern VariantPayload payload))
  | Ppat_any -> Pat.any ()
  | Ppat_var _ | Ppat_alias _ | Ppat_record _ -> pat
  | _ ->
    errorf ~loc:pat.ppat_loc
      "Unsupported type descriptor pattern in comptime surface"

let lower_member_typ_pattern subject pat =
  let member_ctor extra_fields ctor_name =
    let payload =
      match subject with
      | FieldSubject _ -> name_get_payload_pattern extra_fields
      | ItemSubject _ -> index_get_payload_pattern extra_fields
    in
    Pat.construct (lid ctor_name) (Some payload)
  in
  match pat.ppat_desc with
  | Ppat_construct ({txt = Lident "String"; _}, None) ->
    member_ctor []
      (match subject with
      | FieldSubject _ -> "StringField"
      | ItemSubject _ -> "StringItem")
  | Ppat_construct ({txt = Lident "Int"; _}, None) ->
    member_ctor []
      (match subject with
      | FieldSubject _ -> "IntField"
      | ItemSubject _ -> "IntItem")
  | Ppat_construct ({txt = Lident "Float"; _}, None) ->
    member_ctor []
      (match subject with
      | FieldSubject _ -> "FloatField"
      | ItemSubject _ -> "FloatItem")
  | Ppat_construct ({txt = Lident "Bool"; _}, None) ->
    member_ctor []
      (match subject with
      | FieldSubject _ -> "BoolField"
      | ItemSubject _ -> "BoolItem")
  | Ppat_construct ({txt = Lident "Json"; _}, None) ->
    member_ctor []
      (match subject with
      | FieldSubject _ -> "JsonField"
      | ItemSubject _ -> "JsonItem")
  | Ppat_construct ({txt = Lident "Option"; _}, Some inner) ->
    member_ctor
      [
        {
          lid =
            lid
              (match subject with
              | FieldSubject _ -> "fieldInner"
              | ItemSubject _ -> "itemInner");
          x = lower_type_desc_pattern inner;
          opt = false;
        };
      ]
      (match subject with
      | FieldSubject _ -> "OptionField"
      | ItemSubject _ -> "OptionItem")
  | Ppat_construct ({txt = Lident "Array"; _}, Some inner) ->
    member_ctor
      [
        {
          lid =
            lid
              (match subject with
              | FieldSubject _ -> "fieldInner"
              | ItemSubject _ -> "itemInner");
          x = lower_type_desc_pattern inner;
          opt = false;
        };
      ]
      (match subject with
      | FieldSubject _ -> "ArrayField"
      | ItemSubject _ -> "ArrayItem")
  | Ppat_construct ({txt = Lident "List"; _}, Some inner) ->
    member_ctor
      [
        {
          lid =
            lid
              (match subject with
              | FieldSubject _ -> "fieldInner"
              | ItemSubject _ -> "itemInner");
          x = lower_type_desc_pattern inner;
          opt = false;
        };
      ]
      (match subject with
      | FieldSubject _ -> "ListField"
      | ItemSubject _ -> "ListItem")
  | Ppat_construct ({txt = Lident "Record"; _}, Some payload) ->
    member_ctor
      [
        {
          lid =
            lid
              (match subject with
              | FieldSubject _ -> "fieldFields"
              | ItemSubject _ -> "itemFields");
          x = extract_public_record_field_pattern ~label:"fields" payload;
          opt = false;
        };
      ]
      (match subject with
      | FieldSubject _ -> "RecordField"
      | ItemSubject _ -> "RecordItem")
  | Ppat_construct ({txt = Lident "Tuple"; _}, Some payload) ->
    member_ctor
      [
        {
          lid =
            lid
              (match subject with
              | FieldSubject _ -> "fieldItems"
              | ItemSubject _ -> "itemItems");
          x = extract_public_record_field_pattern ~label:"items" payload;
          opt = false;
        };
      ]
      (match subject with
      | FieldSubject _ -> "TupleField"
      | ItemSubject _ -> "TupleItem")
  | Ppat_construct ({txt = Lident "Variant"; _}, Some payload) ->
    member_ctor
      [
        {
          lid =
            lid
              (match subject with
              | FieldSubject _ -> "fieldConstructors"
              | ItemSubject _ -> "itemConstructors");
          x = extract_public_record_field_pattern ~label:"constructors" payload;
          opt = false;
        };
      ]
      (match subject with
      | FieldSubject _ -> "VariantField"
      | ItemSubject _ -> "VariantItem")
  | Ppat_any -> Pat.any ()
  | _ ->
    errorf ~loc:pat.ppat_loc "Unsupported `.typ` pattern in comptime surface"

let lower_constructor_payload_pattern pat =
  match pat.ppat_desc with
  | Ppat_construct ({txt = Lident "NoPayload"; _}, None) ->
    Pat.construct
      (lid "NoPayloadConstructor")
      (Some (constructor_payload_pattern []))
  | Ppat_construct ({txt = Lident "Single"; _}, Some inner) ->
    Pat.construct (lid "SingleConstructor")
      (Some
         (constructor_payload_pattern
            [
              {
                lid = lid "constructorInner";
                x = lower_type_desc_pattern inner;
                opt = false;
              };
            ]))
  | Ppat_construct ({txt = Lident "Tuple"; _}, Some payload) ->
    Pat.construct (lid "TupleConstructor")
      (Some
         (constructor_payload_pattern
            [
              {
                lid = lid "constructorItems";
                x = extract_public_record_field_pattern ~label:"items" payload;
                opt = false;
              };
            ]))
  | Ppat_any -> Pat.any ()
  | _ ->
    errorf ~loc:pat.ppat_loc
      "Unsupported `constructor.payload` pattern in comptime surface"

let rewrite_subject_case_rhs ~subject_kind ~subject_name expr =
  let mapper =
    {
      default_mapper with
      expr =
        (fun self expr ->
          match expr.pexp_desc with
          | Pexp_field
              ( {pexp_desc = Pexp_ident {txt = Lident name; _}; _},
                {txt = Lident "name"; _} )
            when name = subject_name && subject_kind <> `Item ->
            Exp.ident (lid "name")
          | Pexp_field
              ( {pexp_desc = Pexp_ident {txt = Lident name; _}; _},
                {txt = Lident "index"; _} )
            when name = subject_name && subject_kind = `Item ->
            Exp.ident (lid "index")
          | Pexp_apply
              {
                funct =
                  {
                    pexp_desc =
                      Pexp_field
                        ( {pexp_desc = Pexp_ident {txt = Lident name; _}; _},
                          {txt = Lident "get"; _} );
                    _;
                  };
                args = [(Nolabel, arg)];
                _;
              }
            when name = subject_name && subject_kind <> `Constructor ->
            Exp.apply (Exp.ident (lid "get")) [(Nolabel, self.expr self arg)]
          | Pexp_apply
              {
                funct =
                  {
                    pexp_desc =
                      Pexp_field
                        ( {pexp_desc = Pexp_ident {txt = Lident name; _}; _},
                          {txt = Lident "unpack"; _} );
                    _;
                  };
                args = [(Nolabel, arg)];
                _;
              }
            when name = subject_name && subject_kind = `Constructor ->
            Exp.apply (Exp.ident (lid "unpack")) [(Nolabel, self.expr self arg)]
          | Pexp_apply
              {
                funct =
                  {
                    pexp_desc =
                      Pexp_field
                        ( {pexp_desc = Pexp_ident {txt = Lident name; _}; _},
                          {txt = Lident "make"; _} );
                    _;
                  };
                args = [(Nolabel, arg)];
                _;
              }
            when name = subject_name && subject_kind = `Constructor ->
            Exp.apply (Exp.ident (lid "make")) [(Nolabel, self.expr self arg)]
          | Pexp_construct ({txt = Lident "Some"; _}, Some payload) ->
            Exp.construct (lid "Some")
              (Some (erase_expr (self.expr self payload)))
          | _ -> default_mapper.expr self expr);
    }
  in
  mapper.expr mapper expr

let rec core_type_mentions_removed_surface ct =
  match ct.ptyp_desc with
  | Ptyp_any | Ptyp_var _ -> false
  | Ptyp_arrow {arg = {typ = a; _}; ret = b; _} ->
    core_type_mentions_removed_surface a || core_type_mentions_removed_surface b
  | Ptyp_tuple tys -> List.exists core_type_mentions_removed_surface tys
  | Ptyp_constr ({txt; _}, args) ->
    let last = function
      | Lident name -> name
      | Ldot (_, name) -> name
      | Lapply _ -> ""
    in
    last txt = "Code" || List.exists core_type_mentions_removed_surface args
  | Ptyp_alias (ct, _) | Ptyp_poly (_, ct) ->
    core_type_mentions_removed_surface ct
  | Ptyp_package _ | Ptyp_object _ | Ptyp_variant _ | Ptyp_extension _ -> false

let needs_comptime_surface structure =
  let found = ref false in
  let iterator =
    {
      Ast_iterator.default_iterator with
      structure_item =
        (fun self item ->
          (match item.pstr_desc with
          | Pstr_open {popen_lid = {txt = Lident "Comptime"; _}; _} ->
            found := true
          | _ -> ());
          Ast_iterator.default_iterator.structure_item self item);
      expr =
        (fun self expr ->
          (match expr.pexp_desc with
          | Pexp_extension ({txt = "comptime"; _}, _)
          | Pexp_ident {txt = Lident "reflect"; _}
          | Pexp_ident {txt = Ldot (Lident "Comptime", "reflect"); _} ->
            found := true
          | _ -> ());
          Ast_iterator.default_iterator.expr self expr);
    }
  in
  iterator.structure iterator structure;
  !found

let comptime_surface_source =
  {|
/* [@@@warning "-30"] */

module Dict = {
  external make: unit => 'a = "comptime_dict_make"
  external copy: 'a => 'a = "comptime_dict_copy"
  external set: ('a, 'key, 'b) => unit = "comptime_dict_set"
  external get: ('a, string) => option<'b> = "comptime_dict_get"
}

module Comptime = {
  type rec field<'r> =
    | StringField({fieldName: string, fieldGet: 'r => string}): field<'r>
    | IntField({fieldName: string, fieldGet: 'r => int}): field<'r>
    | FloatField({fieldName: string, fieldGet: 'r => float}): field<'r>
    | BoolField({fieldName: string, fieldGet: 'r => bool}): field<'r>
    | JsonField({fieldName: string, fieldGet: 'r => JSON.t}): field<'r>
    | OptionField({fieldName: string, fieldGet: 'r => option<'a>, fieldInner: typeDesc<'a>}): field<'r>
    | ArrayField({fieldName: string, fieldGet: 'r => array<'a>, fieldInner: typeDesc<'a>}): field<'r>
    | ListField({fieldName: string, fieldGet: 'r => list<'a>, fieldInner: typeDesc<'a>}): field<'r>
    | RecordField({fieldName: string, fieldGet: 'r => 'a, fieldFields: array<field<'a>>}): field<'r>
    | TupleField({fieldName: string, fieldGet: 'r => 'a, fieldItems: array<item<'a>>}): field<'r>
    | VariantField({fieldName: string, fieldGet: 'r => 'a, fieldConstructors: array<constructor<'a>>}): field<'r>

  and item<'r> =
    | StringItem({itemIndex: int, itemGet: 'r => string}): item<'r>
    | IntItem({itemIndex: int, itemGet: 'r => int}): item<'r>
    | FloatItem({itemIndex: int, itemGet: 'r => float}): item<'r>
    | BoolItem({itemIndex: int, itemGet: 'r => bool}): item<'r>
    | JsonItem({itemIndex: int, itemGet: 'r => JSON.t}): item<'r>
    | OptionItem({itemIndex: int, itemGet: 'r => option<'a>, itemInner: typeDesc<'a>}): item<'r>
    | ArrayItem({itemIndex: int, itemGet: 'r => array<'a>, itemInner: typeDesc<'a>}): item<'r>
    | ListItem({itemIndex: int, itemGet: 'r => list<'a>, itemInner: typeDesc<'a>}): item<'r>
    | RecordItem({itemIndex: int, itemGet: 'r => 'a, itemFields: array<field<'a>>}): item<'r>
    | TupleItem({itemIndex: int, itemGet: 'r => 'a, itemItems: array<item<'a>>}): item<'r>
    | VariantItem({itemIndex: int, itemGet: 'r => 'a, itemConstructors: array<constructor<'a>>}): item<'r>

  and constructor<'v> =
    | NoPayloadConstructor({
        constructorName: string,
        constructorUnpack: 'v => option<unit>,
        constructorMake: unit => 'v,
      }): constructor<'v>
    | SingleConstructor({
        constructorName: string,
        constructorUnpack: 'v => option<'a>,
        constructorMake: 'a => 'v,
        constructorInner: typeDesc<'a>,
      }): constructor<'v>
    | TupleConstructor({
        constructorName: string,
        constructorUnpack: 'v => option<'a>,
        constructorMake: 'a => 'v,
        constructorItems: array<item<'a>>,
      }): constructor<'v>

  and recordDesc<'a> = {recordName: string, fields: array<field<'a>>}

  and tupleDesc<'a> = {
    items: array<item<'a>>,
  }

  and variantDesc<'a> = {
    variantName: string,
    constructors: array<constructor<'a>>,
  }

  and typeDesc<'a> =
    | String: typeDesc<string>
    | Int: typeDesc<int>
    | Float: typeDesc<float>
    | Bool: typeDesc<bool>
    | Json: typeDesc<JSON.t>
    | Option(typeDesc<'a>): typeDesc<option<'a>>
    | Array(typeDesc<'a>): typeDesc<array<'a>>
    | List(typeDesc<'a>): typeDesc<list<'a>>
    | Record(recordDesc<'a>): typeDesc<'a>
    | Tuple(tupleDesc<'a>): typeDesc<'a>
    | Variant(variantDesc<'a>): typeDesc<'a>

  external reflect: unit => typeDesc<'a> = "%identity"
  external __marker: 'a => 'a = "%identity"
  external __fieldType: field<'r> => typeDesc<'a> = "comptime_field_type"
  external __fieldName: field<'r> => string = "comptime_field_name"
  external __fieldGet: (field<'r>, 'r) => 'a = "comptime_field_get"
  external __itemType: item<'r> => typeDesc<'a> = "comptime_item_type"
  external __itemIndex: item<'r> => int = "comptime_item_index"
  external __itemGet: (item<'r>, 'r) => 'a = "comptime_item_get"
  external __constructorPayload: constructor<'v> => 'a = "comptime_constructor_payload"
  external __constructorName: constructor<'v> => string = "comptime_constructor_name"
  external __constructorUnpack: (constructor<'v>, 'v) => option<'a> = "comptime_constructor_unpack"
  external __constructorMake: (constructor<'v>, 'a) => 'v = "comptime_constructor_make"
  external __erase: 'a => 'b = "comptime_erase"
}
|}

let comptime_surface_items () =
  let parsed =
    Res_driver.parse_implementation_from_source ~for_printer:false
      ~display_filename:"__rescript_comptime_surface__.res"
      ~source:comptime_surface_source
  in
  parsed.parsetree

let rewrite (ast : structure) : structure =
  let mapper =
    {
      default_mapper with
      expr =
        (fun self expr ->
          match expr.pexp_desc with
          | Pexp_extension ({txt = "comptime"; loc; _}, payload) ->
            let payload = expr_payload_single ~loc payload |> self.expr self in
            comptime_marker_expr payload
          | Pexp_extension ({txt = "quote"; loc; _}, _) ->
            errorf ~loc
              "`%%quote` has been removed from the public comptime surface"
          | Pexp_extension ({txt = "splice"; loc; _}, _) ->
            errorf ~loc
              "`%%splice` has been removed from the public comptime surface"
          | Pexp_ident {txt = Lident "compileError"; loc}
          | Pexp_ident {txt = Ldot (Lident "Comptime", "compileError"); loc} ->
            errorf ~loc
              "`compileError` has been removed from the public comptime \
               surface; use `failwith` or an assertion failure instead"
          | Pexp_match (scrutinee, cases) -> (
            match classify_typ_scrutinee scrutinee with
            | Some subject ->
              let subject_name =
                match subject with
                | FieldSubject name | ItemSubject name -> name
              in
              let subject_kind =
                match subject with
                | FieldSubject _ -> `Field
                | ItemSubject _ -> `Item
              in
              let scrutinee = Exp.ident (lid subject_name) in
              let cases =
                List.map
                  (fun case ->
                    {
                      case with
                      pc_lhs = lower_member_typ_pattern subject case.pc_lhs;
                      pc_rhs =
                        rewrite_subject_case_rhs ~subject_kind ~subject_name
                          case.pc_rhs;
                    })
                  cases
              in
              {expr with pexp_desc = Pexp_match (scrutinee, cases)}
            | None -> (
              match classify_payload_scrutinee scrutinee with
              | Some subject_name ->
                let scrutinee = Exp.ident (lid subject_name) in
                let cases =
                  List.map
                    (fun case ->
                      {
                        case with
                        pc_lhs = lower_constructor_payload_pattern case.pc_lhs;
                        pc_rhs =
                          rewrite_subject_case_rhs ~subject_kind:`Constructor
                            ~subject_name case.pc_rhs;
                      })
                    cases
                in
                {expr with pexp_desc = Pexp_match (scrutinee, cases)}
              | None -> default_mapper.expr self expr))
          | Pexp_field
              ( ({pexp_desc = Pexp_ident {txt = Lident "field"; _}; _} as
                 field_expr),
                {txt = Lident "typ"; _} ) ->
            field_type_expr (self.expr self field_expr)
          | Pexp_field
              ( ({pexp_desc = Pexp_ident {txt = Lident "field"; _}; _} as
                 field_expr),
                {txt = Lident "name"; _} ) ->
            field_name_expr (self.expr self field_expr)
          | Pexp_apply
              {
                funct =
                  {
                    pexp_desc =
                      Pexp_field
                        ( ({pexp_desc = Pexp_ident {txt = Lident "field"; _}; _}
                           as field_expr),
                          {txt = Lident "get"; _} );
                    _;
                  };
                args = [(Nolabel, arg)];
                _;
              } ->
            field_get_expr (self.expr self field_expr) (self.expr self arg)
          | Pexp_field
              ( ({pexp_desc = Pexp_ident {txt = Lident "item"; _}; _} as
                 item_expr),
                {txt = Lident "typ"; _} ) ->
            item_type_expr (self.expr self item_expr)
          | Pexp_field
              ( ({pexp_desc = Pexp_ident {txt = Lident "item"; _}; _} as
                 item_expr),
                {txt = Lident "index"; _} ) ->
            item_index_expr (self.expr self item_expr)
          | Pexp_apply
              {
                funct =
                  {
                    pexp_desc =
                      Pexp_field
                        ( ({pexp_desc = Pexp_ident {txt = Lident "item"; _}; _}
                           as item_expr),
                          {txt = Lident "get"; _} );
                    _;
                  };
                args = [(Nolabel, arg)];
                _;
              } ->
            item_get_expr (self.expr self item_expr) (self.expr self arg)
          | Pexp_field
              ( ({pexp_desc = Pexp_ident {txt = Lident "constructor"; _}; _} as
                 ctor_expr),
                {txt = Lident "payload"; _} ) ->
            constructor_payload_expr (self.expr self ctor_expr)
          | Pexp_field
              ( ({pexp_desc = Pexp_ident {txt = Lident "constructor"; _}; _} as
                 ctor_expr),
                {txt = Lident "name"; _} ) ->
            constructor_name_expr (self.expr self ctor_expr)
          | Pexp_apply
              {
                funct =
                  {
                    pexp_desc =
                      Pexp_field
                        ( ({
                             pexp_desc =
                               Pexp_ident {txt = Lident "constructor"; _};
                             _;
                           } as ctor_expr),
                          {txt = Lident "unpack"; _} );
                    _;
                  };
                args = [(Nolabel, arg)];
                _;
              } ->
            constructor_unpack_expr (self.expr self ctor_expr)
              (self.expr self arg)
          | Pexp_apply
              {
                funct =
                  {
                    pexp_desc =
                      Pexp_field
                        ( ({
                             pexp_desc =
                               Pexp_ident {txt = Lident "constructor"; _};
                             _;
                           } as ctor_expr),
                          {txt = Lident "make"; _} );
                    _;
                  };
                args = [(Nolabel, arg)];
                _;
              } ->
            constructor_make_expr (self.expr self ctor_expr)
              (self.expr self arg)
          | _ -> default_mapper.expr self expr);
      typ =
        (fun self ct ->
          if core_type_mentions_removed_surface ct then
            errorf ~loc:ct.ptyp_loc
              "`Comptime.Code.t` has been removed from the public comptime \
               surface"
          else default_mapper.typ self ct);
    }
  in
  let ast = mapper.structure mapper ast in
  if needs_comptime_surface ast then comptime_surface_items () @ ast else ast

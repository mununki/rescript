[@@@warning "-45"]

open Ast_helper
open Ast_mapper
open Asttypes
open Longident
open Parsetree

module GeneratedEnv = Map.Make (String)

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

let witness_manifest_of_module_expr mod_expr =
  match mod_expr.pmod_desc with
  | Pmod_structure
      [
        {
          pstr_desc =
            Pstr_type
              ( Nonrecursive,
                [
                  {
                    ptype_name = {txt = "t"; _};
                    ptype_params = [];
                    ptype_kind = Ptype_abstract;
                    ptype_manifest = Some manifest;
                    _;
                  };
                ] );
          _;
        };
      ] ->
    Some manifest
  | _ -> None

let add_witness_constraint expr manifest =
  Exp.constraint_ expr
    (Typ.package
       (Location.mknoloc (Lident "Witness"))
       [(Location.mknoloc (Lident "t"), manifest)])

let generated_ident name =
  Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", name)))

let generated_apply name args = Exp.apply (generated_ident name) args

let generated_constant name = generated_ident name

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
      typ =
        (fun self ct ->
          (match ct.ptyp_desc with
          | Ptyp_extension ({txt = "comptime"; _}, _) -> found := true
          | _ -> ());
          Ast_iterator.default_iterator.typ self ct);
    }
  in
  iterator.structure iterator structure;
  !found

let comptime_surface_source =
  {|
/* [@@@warning "-30"] */

module Comptime = {
  module type Witness = {
    type t
  }

  module Dict = {
    external make: unit => 'a = "comptime_dict_make"
    external copy: 'a => 'a = "comptime_dict_copy"
    external set: ('a, 'key, 'b) => unit = "comptime_dict_set"
    external get: ('a, string) => option<'b> = "comptime_dict_get"
  }

  type generatedType
  type generatedField
  type generatedConstructor
  type generatedPayload

  external generatedTuple: array<'a> => generatedType = "comptime_type_tuple"
  external generatedRecord: array<'a> => generatedType = "comptime_type_record"
  external generatedVariant: array<'a> => generatedType = "comptime_type_variant"
  external generatedField: (string, 'a) => generatedField = "comptime_type_field"
  external generatedConstructor: (string, 'a) => generatedConstructor = "comptime_type_constructor"
  external generatedNoPayload: generatedPayload = "comptime_type_no_payload"
  external generatedSingle: 'a => generatedPayload = "comptime_type_single_payload"
  external generatedTuplePayload: array<'a> => generatedPayload = "comptime_type_tuple_payload"

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
  type __generatedType
  type __generatedPayload
  external __generatedString: __generatedType = "comptime_type_string"
  external __generatedInt: __generatedType = "comptime_type_int"
  external __generatedFloat: __generatedType = "comptime_type_float"
  external __generatedBool: __generatedType = "comptime_type_bool"
  external __generatedJson: __generatedType = "comptime_type_json"
  external __generatedOption: __generatedType => __generatedType = "comptime_type_option"
  external __generatedOptional: __generatedType => __generatedType = "comptime_type_optional"
  external __generatedArray: __generatedType => __generatedType = "comptime_type_array"
  external __generatedList: __generatedType => __generatedType = "comptime_type_list"
  external __generatedTuple: array<'a> => __generatedType = "comptime_type_tuple"
  external __generatedRecord: array<'a> => __generatedType = "comptime_type_record"
  external __generatedVariant: array<'a> => __generatedType = "comptime_type_variant"
  external __generatedNoPayload: __generatedPayload = "comptime_type_no_payload"
  external __generatedSinglePayload: __generatedType => __generatedPayload = "comptime_type_single_payload"
  external __generatedTuplePayload: array<'a> => __generatedPayload = "comptime_type_tuple_payload"
  external __generatedOfDesc: typeDesc<'a> => __generatedType = "comptime_type_of_desc"
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

module BuilderEnv = Set.Make (String)

type builder_env = {
  builders: BuilderEnv.t;
  dynamic_fields: BuilderEnv.t;
  updaters: BuilderEnv.t;
}

let empty_builder_env =
  {
    builders = BuilderEnv.empty;
    dynamic_fields = BuilderEnv.empty;
    updaters = BuilderEnv.empty;
  }

let builder_env_add_builder name env =
  {env with builders = BuilderEnv.add name env.builders}

let builder_env_add_updater name env =
  {env with updaters = BuilderEnv.add name env.updaters}

let builder_env_add_dynamic_field name env =
  if name = "field" then
    {env with dynamic_fields = BuilderEnv.add name env.dynamic_fields}
  else env

let builder_env_has_builder name env = BuilderEnv.mem name env.builders

let builder_env_has_dynamic_field name env =
  BuilderEnv.mem name env.dynamic_fields

let builder_env_has_updater name env = BuilderEnv.mem name env.updaters

let rec builder_binding_name_from_pattern pat =
  match pat.ppat_desc with
  | Ppat_var {txt; _} -> Some txt
  | Ppat_constraint (pat, _) -> builder_binding_name_from_pattern pat
  | Ppat_alias (pat, {txt; _}) -> (
    match builder_binding_name_from_pattern pat with
    | Some name -> Some name
    | None -> Some txt)
  | _ -> None

let rec builder_pattern_bound_names pat =
  match pat.ppat_desc with
  | Ppat_var {txt; _} -> [txt]
  | Ppat_alias (pat, {txt; _}) -> txt :: builder_pattern_bound_names pat
  | Ppat_constraint (pat, _) -> builder_pattern_bound_names pat
  | Ppat_tuple pats | Ppat_array pats ->
    List.concat_map builder_pattern_bound_names pats
  | Ppat_record (fields, _) ->
    List.concat_map (fun field -> builder_pattern_bound_names field.x) fields
  | Ppat_construct (_, Some pat) | Ppat_variant (_, Some pat) ->
    builder_pattern_bound_names pat
  | Ppat_or (a, b) ->
    builder_pattern_bound_names a @ builder_pattern_bound_names b
  | _ -> []

let builder_env_with_pattern pat env =
  List.fold_left
    (fun env name -> builder_env_add_dynamic_field name env)
    env
    (builder_pattern_bound_names pat)

let pattern_binds_name pat name =
  List.mem name (builder_pattern_bound_names pat)

let rec builder_strip_constraint expr =
  match expr.pexp_desc with
  | Pexp_constraint (expr, _) -> builder_strip_constraint expr
  | _ -> expr

let is_unit_expr expr =
  match (builder_strip_constraint expr).pexp_desc with
  | Pexp_construct ({txt = Lident "()"; _}, None) -> true
  | _ -> false

let expr_is_record_seed expr =
  match (builder_strip_constraint expr).pexp_desc with
  | Pexp_apply
      {
        funct =
          {
            pexp_desc =
              Pexp_ident
                {txt = Lident "record" | Ldot (Lident "Comptime", "record"); _};
            _;
          };
        args = [(Nolabel, arg)];
        _;
      } ->
    is_unit_expr arg
  | _ -> false

let expr_is_empty_record_literal expr =
  match (builder_strip_constraint expr).pexp_desc with
  | Pexp_record ([], None) -> true
  | _ -> false

let expr_is_ident name expr =
  match (builder_strip_constraint expr).pexp_desc with
  | Pexp_ident {txt = Lident txt; _} -> txt = name
  | _ -> false

let fresh_builder_name =
  let counter = ref 0 in
  fun () ->
    incr counter;
    Printf.sprintf "__comptime_record_builder_%d" !counter

let comptime_dict_ident name =
  Exp.ident (Location.mknoloc (Ldot (Ldot (Lident "Comptime", "Dict"), name)))

let dict_copy_expr expr =
  Exp.apply (comptime_dict_ident "copy") [(Nolabel, expr)]

let dict_make_expr () =
  Exp.apply
    (comptime_dict_ident "make")
    [(Nolabel, Exp.construct (lid "()") None)]

let dict_set_expr builder key value =
  Exp.apply
    (comptime_dict_ident "set")
    [(Nolabel, builder); (Nolabel, key); (Nolabel, value)]

let builder_record_key_expr env field =
  match field.lid.txt with
  | Lident name when builder_env_has_dynamic_field name env ->
    Exp.ident (lid name)
  | Lident name -> Exp.constant (Const.string name)
  | _ ->
    errorf ~loc:field.lid.loc
      "Comptime record builders only support unqualified field labels"

let lower_builder_record ~loc env spread fields =
  let builder_name = fresh_builder_name () in
  let builder_pat = Pat.var (Location.mknoloc builder_name) in
  let builder_expr = Exp.ident (lid builder_name) in
  let body =
    List.fold_right
      (fun field acc ->
        Exp.sequence
          (dict_set_expr builder_expr
             (builder_record_key_expr env field)
             field.x)
          acc)
      fields builder_expr
  in
  Exp.let_ ~loc Nonrecursive [Vb.mk builder_pat (dict_copy_expr spread)] body

let rec builder_update_env_after_bindings env rec_flag bindings =
  match rec_flag with
  | Recursive ->
    List.fold_left
      (fun env binding ->
        let bound_env = builder_env_with_pattern binding.pvb_pat env in
        match
          ( builder_binding_name_from_pattern binding.pvb_pat,
            expr_has_builder_update bound_env binding.pvb_expr )
        with
        | Some name, true -> builder_env_add_updater name env
        | _ -> env)
      env bindings
  | Nonrecursive ->
    List.fold_left
      (fun env binding ->
        let bound_env = builder_env_with_pattern binding.pvb_pat env in
        match
          ( builder_binding_name_from_pattern binding.pvb_pat,
            expr_has_builder_update bound_env binding.pvb_expr )
        with
        | Some name, true -> builder_env_add_updater name bound_env
        | _ -> bound_env)
      env bindings

and expr_has_builder_update env expr =
  match (builder_strip_constraint expr).pexp_desc with
  | Pexp_ident {txt = Lident name; _} -> builder_env_has_updater name env
  | Pexp_constraint (expr, _) -> expr_has_builder_update env expr
  | Pexp_let (rec_flag, bindings, body) ->
    let bindings_have_update =
      List.exists
        (fun binding ->
          let bound_env = builder_env_with_pattern binding.pvb_pat env in
          expr_has_builder_update bound_env binding.pvb_expr)
        bindings
    in
    bindings_have_update
    || expr_has_builder_update
         (builder_update_env_after_bindings env rec_flag bindings)
         body
  | Pexp_fun f ->
    expr_has_builder_update (builder_env_with_pattern f.lhs env) f.rhs
  | Pexp_apply apply ->
    expr_has_builder_update env apply.funct
    || List.exists (fun (_, arg) -> expr_has_builder_update env arg) apply.args
  | Pexp_match (scrutinee, cases) | Pexp_try (scrutinee, cases) ->
    expr_has_builder_update env scrutinee
    || List.exists
         (fun case ->
           let case_env = builder_env_with_pattern case.pc_lhs env in
           Option.fold ~none:false
             ~some:(expr_has_builder_update case_env)
             case.pc_guard
           || expr_has_builder_update case_env case.pc_rhs)
         cases
  | Pexp_ifthenelse (a, b, c) ->
    expr_has_builder_update env a
    || expr_has_builder_update env b
    || Option.fold ~none:false ~some:(expr_has_builder_update env) c
  | Pexp_sequence (a, b) ->
    expr_has_builder_update env a || expr_has_builder_update env b
  | Pexp_assert asserted -> expr_has_builder_update env asserted
  | Pexp_newtype (_, body) | Pexp_open (_, _, body) | Pexp_letmodule (_, _, body)
    ->
    expr_has_builder_update env body
  | Pexp_construct (_, payload) | Pexp_variant (_, payload) ->
    Option.fold ~none:false ~some:(expr_has_builder_update env) payload
  | Pexp_tuple exprs | Pexp_array exprs ->
    List.exists (expr_has_builder_update env) exprs
  | Pexp_record (fields, Some spread) ->
    let has_dynamic_fields =
      List.exists
        (fun field ->
          match field.lid.txt with
          | Lident name -> builder_env_has_dynamic_field name env
          | _ -> false)
        fields
    in
    has_dynamic_fields
    || expr_has_builder_update env spread
    || List.exists (fun field -> expr_has_builder_update env field.x) fields
  | Pexp_record (fields, None) ->
    List.exists (fun field -> expr_has_builder_update env field.x) fields
  | _ -> false

and bindings_use_name_as_builder_seed env target bindings body =
  match bindings with
  | [] -> expr_uses_name_as_builder_seed env target body
  | binding :: rest ->
    let uses_in_expr =
      expr_uses_name_as_builder_seed env target binding.pvb_expr
    in
    let bound_env = builder_env_with_pattern binding.pvb_pat env in
    let env =
      match
        ( builder_binding_name_from_pattern binding.pvb_pat,
          expr_has_builder_update bound_env binding.pvb_expr )
      with
      | Some name, true -> builder_env_add_updater name bound_env
      | _ -> bound_env
    in
    if uses_in_expr then true
    else if pattern_binds_name binding.pvb_pat target then false
    else bindings_use_name_as_builder_seed env target rest body

and expr_uses_name_as_builder_seed env target expr =
  match (builder_strip_constraint expr).pexp_desc with
  | Pexp_constraint (expr, _) -> expr_uses_name_as_builder_seed env target expr
  | Pexp_ident _ | Pexp_constant _ -> false
  | Pexp_let (rec_flag, bindings, body) ->
    let uses_in_bindings =
      match rec_flag with
      | Recursive ->
        List.exists
          (fun binding ->
            (not (pattern_binds_name binding.pvb_pat target))
            && expr_uses_name_as_builder_seed env target binding.pvb_expr)
          bindings
      | Nonrecursive ->
        bindings_use_name_as_builder_seed env target bindings body
    in
    if rec_flag = Recursive then
      uses_in_bindings
      ||
      if
        List.exists
          (fun binding -> pattern_binds_name binding.pvb_pat target)
          bindings
      then false
      else
        expr_uses_name_as_builder_seed
          (builder_update_env_after_bindings env rec_flag bindings)
          target body
    else uses_in_bindings
  | Pexp_fun f ->
    if pattern_binds_name f.lhs target then false
    else
      expr_uses_name_as_builder_seed
        (builder_env_with_pattern f.lhs env)
        target f.rhs
  | Pexp_apply apply ->
    expr_has_builder_update env apply.funct
    && List.exists (fun (_, arg) -> expr_is_ident target arg) apply.args
    || expr_uses_name_as_builder_seed env target apply.funct
    || List.exists
         (fun (_, arg) -> expr_uses_name_as_builder_seed env target arg)
         apply.args
  | Pexp_match (scrutinee, cases) | Pexp_try (scrutinee, cases) ->
    expr_uses_name_as_builder_seed env target scrutinee
    || List.exists
         (fun case ->
           if pattern_binds_name case.pc_lhs target then false
           else
             let case_env = builder_env_with_pattern case.pc_lhs env in
             Option.fold ~none:false
               ~some:(expr_uses_name_as_builder_seed case_env target)
               case.pc_guard
             || expr_uses_name_as_builder_seed case_env target case.pc_rhs)
         cases
  | Pexp_ifthenelse (a, b, c) ->
    expr_uses_name_as_builder_seed env target a
    || expr_uses_name_as_builder_seed env target b
    || Option.fold ~none:false
         ~some:(expr_uses_name_as_builder_seed env target)
         c
  | Pexp_sequence (a, b) ->
    expr_uses_name_as_builder_seed env target a
    || expr_uses_name_as_builder_seed env target b
  | Pexp_assert asserted -> expr_uses_name_as_builder_seed env target asserted
  | Pexp_newtype (_, body) | Pexp_open (_, _, body) | Pexp_letmodule (_, _, body)
    ->
    expr_uses_name_as_builder_seed env target body
  | Pexp_construct (_, payload) | Pexp_variant (_, payload) ->
    Option.fold ~none:false
      ~some:(expr_uses_name_as_builder_seed env target)
      payload
  | Pexp_tuple exprs | Pexp_array exprs ->
    List.exists (expr_uses_name_as_builder_seed env target) exprs
  | Pexp_record (fields, Some spread) ->
    let has_dynamic_fields =
      List.exists
        (fun field ->
          match field.lid.txt with
          | Lident name -> builder_env_has_dynamic_field name env
          | _ -> false)
        fields
    in
    (has_dynamic_fields && expr_is_ident target spread)
    || expr_uses_name_as_builder_seed env target spread
    || List.exists
         (fun field -> expr_uses_name_as_builder_seed env target field.x)
         fields
  | Pexp_record (fields, None) ->
    List.exists
      (fun field -> expr_uses_name_as_builder_seed env target field.x)
      fields
  | _ -> false

let builder_seed_names_for_nonrecursive_let env bindings body =
  let rec collect_seed_names env bindings =
    match bindings with
    | [] -> BuilderEnv.empty
    | binding :: rest -> (
      let bound_env = builder_env_with_pattern binding.pvb_pat env in
      let env_after_updates =
        match
          ( builder_binding_name_from_pattern binding.pvb_pat,
            expr_has_builder_update bound_env binding.pvb_expr )
        with
        | Some name, true -> builder_env_add_updater name bound_env
        | _ -> bound_env
      in
      let rest_seed_names = collect_seed_names env_after_updates rest in
      match builder_binding_name_from_pattern binding.pvb_pat with
      | Some name
        when expr_is_empty_record_literal binding.pvb_expr
             && bindings_use_name_as_builder_seed env_after_updates name rest
                  body ->
        BuilderEnv.add name rest_seed_names
      | _ -> rest_seed_names)
  in
  collect_seed_names env bindings

let rec rewrite_builder_bindings env rec_flag bindings =
  match rec_flag with
  | Recursive ->
    let bindings =
      List.map
        (fun binding ->
          let bound_env = builder_env_with_pattern binding.pvb_pat env in
          let expr, is_builder =
            rewrite_builder_expr bound_env binding.pvb_expr
          in
          let has_update = expr_has_builder_update bound_env binding.pvb_expr in
          ({binding with pvb_expr = expr}, is_builder, has_update))
        bindings
    in
    let env =
      List.fold_left
        (fun env (binding, is_builder, has_update) ->
          match
            ( builder_binding_name_from_pattern binding.pvb_pat,
              is_builder,
              has_update )
          with
          | Some name, true, _ -> builder_env_add_builder name env
          | Some name, false, true -> builder_env_add_updater name env
          | _ -> env)
        env bindings
    in
    (env, List.map (fun (binding, _, _) -> binding) bindings)
  | Nonrecursive ->
    List.fold_left
      (fun (env, acc) binding ->
        let bound_env = builder_env_with_pattern binding.pvb_pat env in
        let expr, is_builder =
          rewrite_builder_expr bound_env binding.pvb_expr
        in
        let has_update = expr_has_builder_update bound_env binding.pvb_expr in
        let binding = {binding with pvb_expr = expr} in
        let env =
          match
            ( builder_binding_name_from_pattern binding.pvb_pat,
              is_builder,
              has_update )
          with
          | Some name, true, _ -> builder_env_add_builder name bound_env
          | Some name, false, true -> builder_env_add_updater name bound_env
          | _ -> bound_env
        in
        (env, acc @ [binding]))
      (env, []) bindings

and rewrite_builder_case env case =
  let case_env = builder_env_with_pattern case.pc_lhs env in
  let guard =
    Option.map
      (fun guard -> fst (rewrite_builder_expr case_env guard))
      case.pc_guard
  in
  let rhs, is_builder = rewrite_builder_expr case_env case.pc_rhs in
  ({case with pc_guard = guard; pc_rhs = rhs}, is_builder)

and rewrite_builder_expr env expr =
  if expr_is_record_seed expr then (expr, true)
  else
    match expr.pexp_desc with
    | Pexp_ident {txt = Lident name; _} when builder_env_has_builder name env ->
      (expr, true)
    | Pexp_constraint (inner, typ) ->
      let inner, is_builder = rewrite_builder_expr env inner in
      ({expr with pexp_desc = Pexp_constraint (inner, typ)}, is_builder)
    | Pexp_let (Nonrecursive, bindings, body) ->
      let seed_names =
        builder_seed_names_for_nonrecursive_let env bindings body
      in
      let env, bindings =
        List.fold_left
          (fun (env, acc) binding ->
            let bound_env = builder_env_with_pattern binding.pvb_pat env in
            let name = builder_binding_name_from_pattern binding.pvb_pat in
            let has_update =
              expr_has_builder_update bound_env binding.pvb_expr
            in
            let expr, is_builder =
              match name with
              | Some name when BuilderEnv.mem name seed_names ->
                (dict_make_expr (), true)
              | _ -> rewrite_builder_expr bound_env binding.pvb_expr
            in
            let binding = {binding with pvb_expr = expr} in
            let env =
              match (name, is_builder) with
              | Some name, true -> builder_env_add_builder name bound_env
              | _ -> bound_env
            in
            let env =
              match (name, has_update) with
              | Some name, true -> builder_env_add_updater name env
              | _ -> env
            in
            (env, acc @ [binding]))
          (env, []) bindings
      in
      let body, is_builder = rewrite_builder_expr env body in
      ( {expr with pexp_desc = Pexp_let (Nonrecursive, bindings, body)},
        is_builder )
    | Pexp_let (rec_flag, bindings, body) ->
      let env, bindings = rewrite_builder_bindings env rec_flag bindings in
      let body, is_builder = rewrite_builder_expr env body in
      ({expr with pexp_desc = Pexp_let (rec_flag, bindings, body)}, is_builder)
    | Pexp_fun f ->
      let env = builder_env_with_pattern f.lhs env in
      let rhs, _ = rewrite_builder_expr env f.rhs in
      ({expr with pexp_desc = Pexp_fun {f with rhs}}, false)
    | Pexp_apply apply ->
      let fn, _ = rewrite_builder_expr env apply.funct in
      let args =
        List.map
          (fun (label, arg) ->
            let arg, _ = rewrite_builder_expr env arg in
            (label, arg))
          apply.args
      in
      ({expr with pexp_desc = Pexp_apply {apply with funct = fn; args}}, false)
    | Pexp_match (scrutinee, cases) ->
      let scrutinee, _ = rewrite_builder_expr env scrutinee in
      let cases = List.map (rewrite_builder_case env) cases in
      let is_builder = cases <> [] && List.for_all snd cases in
      ( {expr with pexp_desc = Pexp_match (scrutinee, List.map fst cases)},
        is_builder )
    | Pexp_try (scrutinee, cases) ->
      let scrutinee, _ = rewrite_builder_expr env scrutinee in
      let cases = List.map (rewrite_builder_case env) cases in
      ({expr with pexp_desc = Pexp_try (scrutinee, List.map fst cases)}, false)
    | Pexp_ifthenelse (a, b, c) ->
      let a, _ = rewrite_builder_expr env a in
      let b, b_builder = rewrite_builder_expr env b in
      let c, c_builder =
        match c with
        | Some expr ->
          let expr, is_builder = rewrite_builder_expr env expr in
          (Some expr, is_builder)
        | None -> (None, false)
      in
      ({expr with pexp_desc = Pexp_ifthenelse (a, b, c)}, b_builder && c_builder)
    | Pexp_sequence (a, b) ->
      let a, _ = rewrite_builder_expr env a in
      let b, is_builder = rewrite_builder_expr env b in
      ({expr with pexp_desc = Pexp_sequence (a, b)}, is_builder)
    | Pexp_assert asserted ->
      let asserted, _ = rewrite_builder_expr env asserted in
      ({expr with pexp_desc = Pexp_assert asserted}, false)
    | Pexp_newtype (name, body) ->
      let body, is_builder = rewrite_builder_expr env body in
      ({expr with pexp_desc = Pexp_newtype (name, body)}, is_builder)
    | Pexp_open (override, lid, body) ->
      let body, is_builder = rewrite_builder_expr env body in
      ({expr with pexp_desc = Pexp_open (override, lid, body)}, is_builder)
    | Pexp_letmodule (name, mod_expr, body) ->
      let body, is_builder = rewrite_builder_expr env body in
      ({expr with pexp_desc = Pexp_letmodule (name, mod_expr, body)}, is_builder)
    | Pexp_construct (lid, payload) ->
      let payload =
        Option.map
          (fun payload -> fst (rewrite_builder_expr env payload))
          payload
      in
      ({expr with pexp_desc = Pexp_construct (lid, payload)}, false)
    | Pexp_tuple exprs ->
      let exprs =
        List.map (fun expr -> fst (rewrite_builder_expr env expr)) exprs
      in
      ({expr with pexp_desc = Pexp_tuple exprs}, false)
    | Pexp_array exprs ->
      let exprs =
        List.map (fun expr -> fst (rewrite_builder_expr env expr)) exprs
      in
      ({expr with pexp_desc = Pexp_array exprs}, false)
    | Pexp_record (fields, Some spread) ->
      let fields =
        List.map
          (fun field ->
            let value, _ = rewrite_builder_expr env field.x in
            {field with x = value})
          fields
      in
      let spread, spread_is_builder = rewrite_builder_expr env spread in
      let has_dynamic_fields =
        List.exists
          (fun field ->
            match field.lid.txt with
            | Lident name -> builder_env_has_dynamic_field name env
            | _ -> false)
          fields
      in
      if has_dynamic_fields || spread_is_builder then
        (lower_builder_record ~loc:expr.pexp_loc env spread fields, true)
      else ({expr with pexp_desc = Pexp_record (fields, Some spread)}, false)
    | Pexp_record (fields, None) ->
      let fields =
        List.map
          (fun field ->
            let value, _ = rewrite_builder_expr env field.x in
            {field with x = value})
          fields
      in
      ({expr with pexp_desc = Pexp_record (fields, None)}, false)
    | _ -> (expr, false)

let rewrite_builder_marker_expr expr =
  fst (rewrite_builder_expr empty_builder_env expr)

let rec rewrite_builder_module_expr mod_expr =
  match mod_expr.pmod_desc with
  | Pmod_structure structure ->
    {
      mod_expr with
      pmod_desc = Pmod_structure (rewrite_builder_structure structure);
    }
  | Pmod_functor (param, mty, body) ->
    {
      mod_expr with
      pmod_desc = Pmod_functor (param, mty, rewrite_builder_module_expr body);
    }
  | _ -> mod_expr

and rewrite_builder_structure_item item =
  match item.pstr_desc with
  | Pstr_value (rec_flag, bindings) ->
    let _, bindings =
      rewrite_builder_bindings empty_builder_env rec_flag bindings
    in
    {item with pstr_desc = Pstr_value (rec_flag, bindings)}
  | Pstr_eval (expr, attrs) ->
    {item with pstr_desc = Pstr_eval (rewrite_builder_marker_expr expr, attrs)}
  | Pstr_module module_binding ->
    {
      item with
      pstr_desc =
        Pstr_module
          {
            module_binding with
            pmb_expr = rewrite_builder_module_expr module_binding.pmb_expr;
          };
    }
  | Pstr_recmodule bindings ->
    {
      item with
      pstr_desc =
        Pstr_recmodule
          (List.map
             (fun binding ->
               {
                 binding with
                 pmb_expr = rewrite_builder_module_expr binding.pmb_expr;
               })
             bindings);
    }
  | Pstr_include include_decl ->
    {
      item with
      pstr_desc =
        Pstr_include
          {
            include_decl with
            pincl_mod = rewrite_builder_module_expr include_decl.pincl_mod;
          };
    }
  | _ -> item

and rewrite_builder_structure structure =
  List.map rewrite_builder_structure_item structure

let rewrite (ast : structure) : structure =
  let mapper =
    {
      default_mapper with
      structure_item =
        (fun self item ->
          let item = default_mapper.structure_item self item in
          match item.pstr_desc with
          | Pstr_open
              ({
                 popen_lid = {txt = Lident "Comptime"; _};
                 popen_override = Fresh;
                 _;
               } as open_decl) ->
            {
              item with
              pstr_desc = Pstr_open {open_decl with popen_override = Override};
            }
          | _ -> item);
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
          | Pexp_pack _ -> (
            let expr = default_mapper.expr self expr in
            match expr.pexp_desc with
            | Pexp_pack mod_expr -> (
              match witness_manifest_of_module_expr mod_expr with
              | Some manifest -> add_witness_constraint expr manifest
              | None -> expr)
            | _ -> expr)
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
  let ast = rewrite_builder_structure ast in
  if needs_comptime_surface ast then comptime_surface_items () @ ast else ast

type generated_kind =
  | Gk_type
  | Gk_type_array
  | Gk_payload
  | Gk_field_array
  | Gk_constructor_array

let rec surface_binding_name_from_pattern pat =
  match pat.ppat_desc with
  | Ppat_var {txt; _} -> Some txt
  | Ppat_constraint (pat, _) | Ppat_alias (pat, _) ->
    surface_binding_name_from_pattern pat
  | _ -> None

let rec strip_constraint expr =
  match expr.pexp_desc with
  | Pexp_constraint (expr, _) -> strip_constraint expr
  | _ -> expr

let expr_is_ident name expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_ident {txt = Lident txt; _} -> txt = name
  | Pexp_ident {txt = Ldot (Lident "Comptime", txt); _} -> txt = name
  | _ -> false

let expr_is_array_map expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_apply
      {
        funct =
          {pexp_desc = Pexp_ident {txt = Ldot (Lident "Array", "map"); _}; _};
        args = [(Nolabel, source); (Nolabel, callback)];
        _;
      } ->
    Some (source, callback)
  | _ -> None

let find_record_field_expr ~label expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_record (fields, None) -> (
    match
      List.find_opt
        (fun field ->
          match field.lid.txt with
          | Lident name -> name = label
          | _ -> false)
        fields
    with
    | Some field -> Some field.x
    | None -> None)
  | _ -> None

let rebuild_record_field ~label ~value fields =
  List.map
    (fun field ->
      match field.lid.txt with
      | Lident name when name = label -> {field with x = value}
      | _ -> field)
    fields

let is_hidden_generated_type_expr expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_ident {txt = Ldot (Lident "Comptime", name); _} ->
    List.mem name
      [
        "__generatedString";
        "__generatedInt";
        "__generatedFloat";
        "__generatedBool";
        "__generatedJson";
      ]
  | Pexp_apply
      {
        funct =
          {pexp_desc = Pexp_ident {txt = Ldot (Lident "Comptime", name); _}; _};
        _;
      } ->
    List.mem name
      [
        "__generatedOption";
        "__generatedOptional";
        "__generatedArray";
        "__generatedList";
        "__generatedTuple";
        "__generatedRecord";
        "__generatedVariant";
        "__generatedOfDesc";
      ]
  | _ -> false

let is_hidden_generated_payload_expr expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_ident {txt = Ldot (Lident "Comptime", "__generatedNoPayload"); _} ->
    true
  | Pexp_apply
      {
        funct =
          {
            pexp_desc =
              Pexp_ident
                {txt = Ldot (Lident "Comptime", "__generatedSinglePayload"); _};
            _;
          };
        _;
      } ->
    true
  | Pexp_apply
      {
        funct =
          {
            pexp_desc =
              Pexp_ident
                {txt = Ldot (Lident "Comptime", "__generatedTuplePayload"); _};
            _;
          };
        _;
      } ->
    true
  | _ -> false

let consistent_generated_kind kinds =
  match kinds with
  | [] -> None
  | first :: rest ->
    if List.for_all (fun kind -> kind = first) rest then Some first else None

let consistent_generated_kind_options kinds =
  if List.for_all Option.is_some kinds then
    consistent_generated_kind (List.filter_map (fun kind -> kind) kinds)
  else None

let expr_is_failwith expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_apply
      {
        funct =
          {
            pexp_desc =
              Pexp_ident
                ( {txt = Lident "failwith"; _}
                | {txt = Ldot (Lident "Comptime", "failwith"); _} );
            _;
          };
        _;
      } ->
    true
  | _ -> false

let infer_type_constructor_kind expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_construct ({txt = Lident name; _}, _)
    when List.mem name
           [
             "String";
             "Int";
             "Float";
             "Bool";
             "Json";
             "Option";
             "Optional";
             "Array";
             "List";
             "Tuple";
             "Record";
             "Variant";
           ] ->
    Some Gk_type
  | _ -> None

let rec is_generated_field_expr expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_construct ({txt = Lident "Field"; _}, Some payload) ->
    is_generated_field_expr payload
  | Pexp_record (fields, None) ->
    List.length fields = 2
    && List.exists
         (fun field ->
           match field.lid.txt with
           | Lident "name" -> true
           | _ -> false)
         fields
    && List.exists
         (fun field ->
           match field.lid.txt with
           | Lident "typ" -> true
           | _ -> false)
         fields
  | _ -> false

let rec is_generated_constructor_expr expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_construct ({txt = Lident "Constructor"; _}, Some payload) ->
    is_generated_constructor_expr payload
  | Pexp_record (fields, None) ->
    List.length fields = 2
    && List.exists
         (fun field ->
           match field.lid.txt with
           | Lident "name" -> true
           | _ -> false)
         fields
    && List.exists
         (fun field ->
           match field.lid.txt with
           | Lident "payload" -> true
           | _ -> false)
         fields
  | _ -> false

let rec infer_generated_kind env expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_ident {txt = Lident name; _} -> GeneratedEnv.find_opt name env
  | Pexp_fun {rhs; _} -> infer_generated_kind env rhs
  | Pexp_let (_rec_flag, bindings, body) ->
    let env =
      List.fold_left
        (fun env binding ->
          match surface_binding_name_from_pattern binding.pvb_pat with
          | Some name -> (
            match infer_generated_kind env binding.pvb_expr with
            | Some kind -> GeneratedEnv.add name kind env
            | None -> env)
          | None -> env)
        env bindings
    in
    infer_generated_kind env body
  | Pexp_ifthenelse (_condition, when_true, Some when_false) ->
    consistent_generated_kind_branches env [when_true; when_false]
  | Pexp_match (_scrutinee, cases) ->
    consistent_generated_kind_branches env
      (List.map (fun case -> case.pc_rhs) cases)
  | Pexp_sequence (_first, second) -> infer_generated_kind env second
  | Pexp_array [] -> None
  | Pexp_array (first :: rest) -> (
    match infer_generated_kind env first with
    | Some kind
      when List.for_all
             (fun expr -> infer_generated_kind env expr = Some kind)
             rest ->
      Some
        (match kind with
        | Gk_type -> Gk_type_array
        | _ -> kind)
    | None
      when is_generated_field_expr first
           && List.for_all is_generated_field_expr rest ->
      Some Gk_field_array
    | None
      when is_generated_constructor_expr first
           && List.for_all is_generated_constructor_expr rest ->
      Some Gk_constructor_array
    | _ -> None)
  | Pexp_apply _ -> (
    match expr_is_array_map expr with
    | Some (_source, callback) -> (
      match (strip_constraint callback).pexp_desc with
      | Pexp_fun {rhs; _} -> (
        match infer_generated_kind env rhs with
        | Some Gk_type -> Some Gk_type_array
        | Some kind -> Some kind
        | None when is_generated_field_expr rhs -> Some Gk_field_array
        | None when is_generated_constructor_expr rhs ->
          Some Gk_constructor_array
        | _ -> None)
      | _ -> None)
    | None -> (
      match (strip_constraint expr).pexp_desc with
      | Pexp_apply
          {funct = {pexp_desc = Pexp_ident {txt = Lident name; _}; _}; _} ->
        GeneratedEnv.find_opt name env
      | Pexp_apply
          {
            funct =
              {
                pexp_desc = Pexp_ident {txt = Ldot (Lident "Comptime", name); _};
                _;
              };
            _;
          }
        when List.mem name
               [
                 "__generatedOption";
                 "__generatedOptional";
                 "__generatedArray";
                 "__generatedList";
                 "__generatedTuple";
                 "__generatedRecord";
                 "__generatedVariant";
                 "__generatedOfDesc";
               ] ->
        Some Gk_type
      | Pexp_apply
          {
            funct =
              {
                pexp_desc =
                  Pexp_ident
                    {
                      txt = Ldot (Lident "Comptime", "__generatedSinglePayload");
                      _;
                    };
                _;
              };
            _;
          } ->
        Some Gk_payload
      | Pexp_apply
          {
            funct =
              {
                pexp_desc =
                  Pexp_ident
                    {
                      txt = Ldot (Lident "Comptime", "__generatedTuplePayload");
                      _;
                    };
                _;
              };
            _;
          } ->
        Some Gk_payload
      | _ -> None))
  | Pexp_ident {txt = Ldot (Lident "Comptime", "__generatedNoPayload"); _} ->
    Some Gk_payload
  | Pexp_construct ({txt = Lident "NoPayload"; _}, _)
  | Pexp_construct ({txt = Lident "Single"; _}, _) ->
    Some Gk_payload
  | Pexp_construct ({txt = Lident "Tuple"; _}, Some payload)
    when Option.is_some (find_record_field_expr ~label:"items" payload) ->
    Some Gk_type
  | _ -> infer_type_constructor_kind expr

and consistent_generated_kind_branches env branches =
  let rec loop inferred = function
    | [] -> consistent_generated_kind (List.rev inferred)
    | branch :: rest -> (
      match infer_generated_kind env branch with
      | Some kind -> loop (kind :: inferred) rest
      | None when expr_is_failwith branch -> loop inferred rest
      | None -> None)
  in
  loop [] branches

let rewrite_callback_body rewrite env callback =
  match callback.pexp_desc with
  | Pexp_fun f ->
    {callback with pexp_desc = Pexp_fun {f with rhs = rewrite env f.rhs}}
  | _ -> callback

let rec rewrite_generated_binding env expr =
  match infer_generated_kind env expr with
  | Some Gk_type -> rewrite_generated_type_expr env expr
  | Some Gk_type_array -> rewrite_generated_type_array_expr env expr
  | Some Gk_payload -> rewrite_generated_payload_expr env expr
  | Some Gk_field_array -> rewrite_generated_field_array_expr env expr
  | Some Gk_constructor_array ->
    rewrite_generated_constructor_array_expr env expr
  | None -> expr

and rewrite_generated_bindings env bindings =
  List.fold_left
    (fun (env, acc) binding ->
      let rewritten = rewrite_generated_binding env binding.pvb_expr in
      let env =
        match surface_binding_name_from_pattern binding.pvb_pat with
        | Some name -> (
          match infer_generated_kind env binding.pvb_expr with
          | Some kind -> GeneratedEnv.add name kind env
          | None -> env)
        | None -> env
      in
      (env, acc @ [{binding with pvb_expr = rewritten}]))
    (env, []) bindings

and rewrite_generated_type_expr env expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_fun f ->
    {
      expr with
      pexp_desc = Pexp_fun {f with rhs = rewrite_generated_type_expr env f.rhs};
    }
  | Pexp_let (rec_flag, bindings, body) ->
    let env, bindings = rewrite_generated_bindings env bindings in
    Exp.let_ rec_flag bindings (rewrite_generated_type_expr env body)
  | Pexp_ifthenelse (a, b, c) ->
    Exp.ifthenelse a
      (rewrite_generated_type_expr env b)
      (Option.map (rewrite_generated_type_expr env) c)
  | Pexp_match (scrutinee, cases) ->
    Exp.match_ scrutinee
      (List.map
         (fun case ->
           {case with pc_rhs = rewrite_generated_type_expr env case.pc_rhs})
         cases)
  | Pexp_construct ({txt = Lident "String"; _}, None) ->
    generated_constant "__generatedString"
  | Pexp_construct ({txt = Lident "Int"; _}, None) ->
    generated_constant "__generatedInt"
  | Pexp_construct ({txt = Lident "Float"; _}, None) ->
    generated_constant "__generatedFloat"
  | Pexp_construct ({txt = Lident "Bool"; _}, None) ->
    generated_constant "__generatedBool"
  | Pexp_construct ({txt = Lident "Json"; _}, None) ->
    generated_constant "__generatedJson"
  | Pexp_construct ({txt = Lident "Option"; _}, Some inner) ->
    generated_apply "__generatedOption"
      [(Nolabel, rewrite_generated_type_expr env inner)]
  | Pexp_construct ({txt = Lident "Optional"; _}, Some inner) ->
    generated_apply "__generatedOptional"
      [(Nolabel, rewrite_generated_type_expr env inner)]
  | Pexp_construct ({txt = Lident "Array"; _}, Some inner) ->
    generated_apply "__generatedArray"
      [(Nolabel, rewrite_generated_type_expr env inner)]
  | Pexp_construct ({txt = Lident "List"; _}, Some inner) ->
    generated_apply "__generatedList"
      [(Nolabel, rewrite_generated_type_expr env inner)]
  | Pexp_construct ({txt = Lident "Tuple"; _}, Some payload) -> (
    match find_record_field_expr ~label:"items" payload with
    | Some items ->
      generated_apply "__generatedTuple"
        [(Nolabel, rewrite_generated_type_array_expr env items)]
    | None ->
      errorf ~loc:expr.pexp_loc
        "Generated `Tuple` expressions must provide an `items` field")
  | Pexp_construct ({txt = Lident "Record"; _}, Some payload) -> (
    match find_record_field_expr ~label:"fields" payload with
    | Some fields ->
      generated_apply "__generatedRecord"
        [(Nolabel, rewrite_generated_field_array_expr env fields)]
    | None ->
      errorf ~loc:expr.pexp_loc
        "Generated `Record` expressions must provide a `fields` field")
  | Pexp_construct ({txt = Lident "Variant"; _}, Some payload) -> (
    match find_record_field_expr ~label:"constructors" payload with
    | Some constructors ->
      generated_apply "__generatedVariant"
        [(Nolabel, rewrite_generated_constructor_array_expr env constructors)]
    | None ->
      errorf ~loc:expr.pexp_loc
        "Generated `Variant` expressions must provide a `constructors` field")
  | Pexp_apply
      {
        funct = {pexp_desc = Pexp_ident {txt = Lident name; _}; _} as funct;
        args;
        _;
      }
    when GeneratedEnv.find_opt name env = Some Gk_type ->
    Exp.apply funct args
  | Pexp_ident {txt = Lident name; _}
    when GeneratedEnv.find_opt name env = Some Gk_type ->
    expr
  | _ when is_hidden_generated_type_expr expr -> expr
  | _ -> generated_apply "__generatedOfDesc" [(Nolabel, expr)]

and rewrite_generated_type_array_expr env expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_let (rec_flag, bindings, body) ->
    let env, bindings = rewrite_generated_bindings env bindings in
    Exp.let_ rec_flag bindings (rewrite_generated_type_array_expr env body)
  | Pexp_ifthenelse (a, b, c) ->
    Exp.ifthenelse a
      (rewrite_generated_type_array_expr env b)
      (Option.map (rewrite_generated_type_array_expr env) c)
  | Pexp_match (scrutinee, cases) ->
    Exp.match_ scrutinee
      (List.map
         (fun case ->
           {
             case with
             pc_rhs = rewrite_generated_type_array_expr env case.pc_rhs;
           })
         cases)
  | Pexp_array exprs ->
    Exp.array (List.map (rewrite_generated_type_expr env) exprs)
  | Pexp_ident {txt = Lident name; _}
    when GeneratedEnv.find_opt name env = Some Gk_type_array ->
    expr
  | Pexp_apply _ -> (
    match expr_is_array_map expr with
    | Some (source, callback) ->
      Exp.apply
        (match (strip_constraint expr).pexp_desc with
        | Pexp_apply {funct; _} -> funct
        | _ -> assert false)
        [
          (Nolabel, source);
          ( Nolabel,
            rewrite_callback_body rewrite_generated_type_expr env callback );
        ]
    | None -> expr)
  | _ -> expr

and rewrite_generated_field_expr env expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_construct ({txt = Lident "Field"; _}, Some payload) ->
    rewrite_generated_field_expr env payload
  | Pexp_record (_, None) when is_generated_field_expr expr -> (
    match
      ( find_record_field_expr ~label:"name" expr,
        find_record_field_expr ~label:"typ" expr )
    with
    | Some name, Some typ ->
      generated_apply "generatedField"
        [(Nolabel, name); (Nolabel, rewrite_generated_type_expr env typ)]
    | _ -> expr)
  | _ -> expr

and rewrite_generated_field_array_expr env expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_let (rec_flag, bindings, body) ->
    let env, bindings = rewrite_generated_bindings env bindings in
    Exp.let_ rec_flag bindings (rewrite_generated_field_array_expr env body)
  | Pexp_ifthenelse (a, b, c) ->
    Exp.ifthenelse a
      (rewrite_generated_field_array_expr env b)
      (Option.map (rewrite_generated_field_array_expr env) c)
  | Pexp_match (scrutinee, cases) ->
    Exp.match_ scrutinee
      (List.map
         (fun case ->
           {
             case with
             pc_rhs = rewrite_generated_field_array_expr env case.pc_rhs;
           })
         cases)
  | Pexp_array exprs ->
    Exp.array (List.map (rewrite_generated_field_expr env) exprs)
  | Pexp_ident {txt = Lident name; _}
    when GeneratedEnv.find_opt name env = Some Gk_field_array ->
    expr
  | Pexp_apply _ -> (
    match expr_is_array_map expr with
    | Some (source, callback) ->
      Exp.apply
        (match (strip_constraint expr).pexp_desc with
        | Pexp_apply {funct; _} -> funct
        | _ -> assert false)
        [
          (Nolabel, source);
          ( Nolabel,
            rewrite_callback_body rewrite_generated_field_expr env callback );
        ]
    | None -> expr)
  | _ -> expr

and rewrite_generated_payload_expr env expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_let (rec_flag, bindings, body) ->
    let env, bindings = rewrite_generated_bindings env bindings in
    Exp.let_ rec_flag bindings (rewrite_generated_payload_expr env body)
  | Pexp_ifthenelse (a, b, c) ->
    Exp.ifthenelse a
      (rewrite_generated_payload_expr env b)
      (Option.map (rewrite_generated_payload_expr env) c)
  | Pexp_match (scrutinee, cases) ->
    Exp.match_ scrutinee
      (List.map
         (fun case ->
           {case with pc_rhs = rewrite_generated_payload_expr env case.pc_rhs})
         cases)
  | Pexp_construct ({txt = Lident "NoPayload"; _}, None) ->
    generated_constant "__generatedNoPayload"
  | Pexp_construct ({txt = Lident "Single"; _}, Some inner) ->
    generated_apply "__generatedSinglePayload"
      [(Nolabel, rewrite_generated_type_expr env inner)]
  | Pexp_construct ({txt = Lident "Tuple"; _}, Some payload) -> (
    match find_record_field_expr ~label:"items" payload with
    | Some items ->
      generated_apply "__generatedTuplePayload"
        [(Nolabel, rewrite_generated_type_array_expr env items)]
    | None ->
      errorf ~loc:expr.pexp_loc
        "Generated tuple payloads must provide an `items` field")
  | Pexp_ident {txt = Lident name; _}
    when GeneratedEnv.find_opt name env = Some Gk_payload ->
    expr
  | _ when is_hidden_generated_payload_expr expr -> expr
  | _ -> expr

and rewrite_generated_constructor_expr env expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_construct ({txt = Lident "Constructor"; _}, Some payload) ->
    rewrite_generated_constructor_expr env payload
  | Pexp_record (_, None) when is_generated_constructor_expr expr -> (
    match
      ( find_record_field_expr ~label:"name" expr,
        find_record_field_expr ~label:"payload" expr )
    with
    | Some name, Some payload ->
      generated_apply "generatedConstructor"
        [(Nolabel, name); (Nolabel, rewrite_generated_payload_expr env payload)]
    | _ -> expr)
  | _ -> expr

and rewrite_generated_constructor_array_expr env expr =
  match (strip_constraint expr).pexp_desc with
  | Pexp_let (rec_flag, bindings, body) ->
    let env, bindings = rewrite_generated_bindings env bindings in
    Exp.let_ rec_flag bindings
      (rewrite_generated_constructor_array_expr env body)
  | Pexp_ifthenelse (a, b, c) ->
    Exp.ifthenelse a
      (rewrite_generated_constructor_array_expr env b)
      (Option.map (rewrite_generated_constructor_array_expr env) c)
  | Pexp_match (scrutinee, cases) ->
    Exp.match_ scrutinee
      (List.map
         (fun case ->
           {
             case with
             pc_rhs = rewrite_generated_constructor_array_expr env case.pc_rhs;
           })
         cases)
  | Pexp_array exprs ->
    Exp.array (List.map (rewrite_generated_constructor_expr env) exprs)
  | Pexp_ident {txt = Lident name; _}
    when GeneratedEnv.find_opt name env = Some Gk_constructor_array ->
    expr
  | Pexp_apply _ -> (
    match expr_is_array_map expr with
    | Some (source, callback) ->
      Exp.apply
        (match (strip_constraint expr).pexp_desc with
        | Pexp_apply {funct; _} -> funct
        | _ -> assert false)
        [
          (Nolabel, source);
          ( Nolabel,
            rewrite_callback_body rewrite_generated_constructor_expr env
              callback );
        ]
    | None -> expr)
  | _ -> expr

let rewrite_expr_in_surface expr =
  let marker = "__comptime_type_expr" in
  let ast =
    rewrite
      [Str.value Nonrecursive [Vb.mk (Pat.var (Location.mknoloc marker)) expr]]
  in
  List.find_map
    (function
      | {
          pstr_desc =
            Pstr_value
              (_, [{pvb_pat = {ppat_desc = Ppat_var {txt; _}; _}; pvb_expr; _}]);
          _;
        }
        when txt = marker ->
        Some (rewrite_generated_type_expr GeneratedEnv.empty pvb_expr)
      | _ -> None)
    ast
  |> Option.get

let rewrite_type_generator_expr expr = rewrite_expr_in_surface expr

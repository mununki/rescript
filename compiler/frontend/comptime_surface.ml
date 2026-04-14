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

let is_field_typ_expr expr =
  match expr.pexp_desc with
  | Pexp_field (_, {txt = Lident "typ"; _}) -> true
  | _ -> false

let field_payload_pattern () =
  Pat.record
    [
      {lid = lid "name"; x = Pat.var (Location.mknoloc "name"); opt = false};
      {lid = lid "get"; x = Pat.var (Location.mknoloc "get"); opt = false};
    ]
    Closed

let lower_field_typ_case_pattern = function
  | {ppat_desc = Ppat_construct ({txt = Lident "String"; _}, None); _} ->
    Pat.construct (lid "StringField") (Some (field_payload_pattern ()))
  | {ppat_desc = Ppat_construct ({txt = Lident "Int"; _}, None); _} ->
    Pat.construct (lid "IntField") (Some (field_payload_pattern ()))
  | {ppat_desc = Ppat_construct ({txt = Lident "Float"; _}, None); _} ->
    Pat.construct (lid "FloatField") (Some (field_payload_pattern ()))
  | {ppat_desc = Ppat_construct ({txt = Lident "Bool"; _}, None); _} ->
    Pat.construct (lid "BoolField") (Some (field_payload_pattern ()))
  | {ppat_desc = Ppat_construct ({txt = Lident "Json"; _}, None); _} ->
    Pat.construct (lid "JsonField") (Some (field_payload_pattern ()))
  | {ppat_desc = Ppat_construct ({txt = Lident "Option"; _}, None); _} ->
    Pat.construct (lid "OptionField") (Some (field_payload_pattern ()))
  | {ppat_desc = Ppat_construct ({txt = Lident "Array"; _}, None); _} ->
    Pat.construct (lid "ArrayField") (Some (field_payload_pattern ()))
  | {ppat_desc = Ppat_construct ({txt = Lident "Record"; _}, None); _} ->
    Pat.construct (lid "RecordField") (Some (field_payload_pattern ()))
  | {ppat_desc = Ppat_any; _} as pat -> pat
  | pat ->
    errorf ~loc:pat.ppat_loc
      "Unsupported `field.typ` pattern in comptime surface"

let field_name_expr field_expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__fieldName"))))
    [(Nolabel, field_expr)]

let field_get_expr field_expr arg_expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__fieldGet"))))
    [(Nolabel, field_expr); (Nolabel, arg_expr)]

let erase_expr expr =
  Exp.apply
    (Exp.ident (Location.mknoloc (Ldot (Lident "Comptime", "__erase"))))
    [(Nolabel, expr)]

let rewrite_field_case_rhs ~field_name expr =
  let mapper =
    {
      default_mapper with
      expr =
        (fun self expr ->
          match expr.pexp_desc with
          | Pexp_field
              ( {pexp_desc = Pexp_ident {txt = Lident name; _}; _},
                {txt = Lident "name"; _} )
            when name = field_name ->
            Exp.ident (lid "name")
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
            when name = field_name ->
            Exp.apply (Exp.ident (lid "get")) [(Nolabel, self.expr self arg)]
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
module Dict = {
  external make: unit => 'a = "comptime_dict_make"
  external copy: 'a => 'a = "comptime_dict_copy"
  external set: ('a, string, 'b) => unit = "comptime_dict_set"
  external get: ('a, string) => option<'b> = "comptime_dict_get"
}

module Comptime = {
  type rec field<'r> =
    | StringField({name: string, get: 'r => string}): field<'r>
    | IntField({name: string, get: 'r => int}): field<'r>
    | FloatField({name: string, get: 'r => float}): field<'r>
    | BoolField({name: string, get: 'r => bool}): field<'r>
    | JsonField({name: string, get: 'r => JSON.t}): field<'r>
    | OptionField({name: string, get: 'a. 'r => 'a}): field<'r>
    | ArrayField({name: string, get: 'a. 'r => 'a}): field<'r>
    | RecordField({name: string, get: 'a. 'r => 'a}): field<'r>

  and typeDesc<'a> =
    | String: typeDesc<string>
    | Int: typeDesc<int>
    | Float: typeDesc<float>
    | Bool: typeDesc<bool>
    | Json: typeDesc<JSON.t>
    | Option(typeDesc<'a>): typeDesc<option<'a>>
    | Array(typeDesc<'a>): typeDesc<array<'a>>
    | Record({name: string, fields: array<field<'a>>}): typeDesc<'a>

  external reflect: unit => typeDesc<'a> = "%identity"
  external __marker: 'a => 'a = "%identity"
  external __fieldName: field<'r> => string = "comptime_field_name"
  external __fieldGet: (field<'r>, 'r) => 'a = "comptime_field_get"
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
          | Pexp_match (scrutinee, cases) when is_field_typ_expr scrutinee ->
            let scrutinee =
              match scrutinee.pexp_desc with
              | Pexp_field
                  ({pexp_desc = Pexp_ident {txt = Lident field_name; _}; _}, _)
                ->
                Exp.ident (lid field_name)
              | _ ->
                errorf ~loc:scrutinee.pexp_loc
                  "`field.typ` matches in comptime surface currently require a \
                   simple field identifier"
            in
            let cases =
              List.map
                (fun case ->
                  let field_name =
                    match scrutinee.pexp_desc with
                    | Pexp_ident {txt = Lident field_name; _} -> field_name
                    | _ -> assert false
                  in
                  {
                    case with
                    pc_lhs = lower_field_typ_case_pattern case.pc_lhs;
                    pc_rhs = rewrite_field_case_rhs ~field_name case.pc_rhs;
                  })
                cases
            in
            {expr with pexp_desc = Pexp_match (scrutinee, cases)}
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

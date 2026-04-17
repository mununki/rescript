[@@@warning "-45"]

open Ast_helper
open Asttypes
open Parsetree

let errorf ~loc fmt =
  Format.kasprintf (fun message -> Location.raise_errorf ~loc "%s" message) fmt

let expr_payload_single ~loc payload =
  match payload with
  | PStr [{pstr_desc = Pstr_eval (expr, _); _}] -> expr
  | _ -> errorf ~loc "Expected a single expression payload"

let comptime_marker_expr expr =
  Exp.apply
    (Exp.ident
       (Location.mknoloc
          (Longident.Ldot (Longident.Lident "Comptime", "__marker"))))
    [(Nolabel, expr)]

let marker_binding marker_name expr =
  Str.value Nonrecursive
    [Vb.mk (Pat.var (Location.mknoloc marker_name)) (comptime_marker_expr expr)]

let fresh_marker =
  let counter = ref 0 in
  fun type_name ->
    incr counter;
    "__comptime_type_" ^ type_name ^ "_" ^ string_of_int !counter

let comptime_manifest_expr tdcl =
  match tdcl.ptype_manifest with
  | Some {ptyp_desc = Ptyp_extension ({txt = "comptime"; loc; _}, payload); _}
    ->
    Some (loc, expr_payload_single ~loc payload)
  | _ -> None

let rewritten_type_item ~initial_env prefix item =
  match item.pstr_desc with
  | Pstr_type (rec_flag, [tdcl]) -> (
    if rec_flag <> Nonrecursive then
      errorf ~loc:item.pstr_loc
        "type-level `%%comptime(...)` only supports non-recursive type aliases";
    if tdcl.ptype_params <> [] then
      errorf ~loc:tdcl.ptype_loc
        "type-level `%%comptime(...)` does not support generic type aliases";
    if tdcl.ptype_kind <> Ptype_abstract then
      errorf ~loc:tdcl.ptype_loc
        "type-level `%%comptime(...)` only supports type aliases";
    match comptime_manifest_expr tdcl with
    | None -> item
    | Some (_loc, payload_expr) ->
      let marker_name = fresh_marker tdcl.ptype_name.txt in
      let payload_expr =
        Comptime_surface.rewrite_type_generator_expr payload_expr
      in
      let synthetic = marker_binding marker_name payload_expr in
      let typedtree, _, _ =
        Warnings.without_warnings (fun () ->
            Typemod.type_structure initial_env (prefix @ [synthetic])
              item.pstr_loc)
      in
      let generated_type =
        Comptime_eval.eval_generated_type ~typedtree ~marker_name
      in
      let rewritten_tdcl =
        Comptime_eval.type_declaration_of_generated_type ~loc:tdcl.ptype_loc
          tdcl.ptype_name.txt generated_type
      in
      let tdcl =
        {
          rewritten_tdcl with
          ptype_attributes = tdcl.ptype_attributes;
          ptype_private = tdcl.ptype_private;
          ptype_loc = tdcl.ptype_loc;
        }
      in
      {item with pstr_desc = Pstr_type (rec_flag, [tdcl])})
  | _ -> assert false

let expand ~initial_env ast =
  let rec loop prefix = function
    | [] -> prefix
    | ({pstr_desc = Pstr_type (_, [tdcl]); _} as item) :: rest
      when Option.is_some (comptime_manifest_expr tdcl) ->
      let item = rewritten_type_item ~initial_env prefix item in
      loop (prefix @ [item]) rest
    | {pstr_desc = Pstr_type (_, tdcls); pstr_loc; _} :: _
      when List.exists
             (fun tdcl -> Option.is_some (comptime_manifest_expr tdcl))
             tdcls ->
      errorf ~loc:pstr_loc
        "type-level `%%comptime(...)` currently only supports one type \
         declaration per `type` item"
    | item :: rest -> loop (prefix @ [item]) rest
  in
  loop [] ast

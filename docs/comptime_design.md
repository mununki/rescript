# ReScript Comptime

This document describes the current `comptime` proof of concept for ReScript.

The public surface is:

- `%comptime(expr)` on top-level value bindings
- `type t = %comptime(expr)` on non-generic top-level type aliases
- `reflect()`
- reflected member accessors
  - `field.name`
  - `field.typ`
  - `field.get(value)`
  - `item.index`
  - `item.typ`
  - `item.get(value)`
  - `constructor.name`
  - `constructor.payload`
  - `constructor.unpack(value)`
  - `constructor.make(payload)`

## Design Goals

- Keep the surface close to ordinary ReScript syntax
- Make staging boundaries explicit
- Let users write generators as ordinary functions
- Reuse existing reflected descriptors for both inspection and type generation
- Keep compiler-owned special forms hidden behind the public surface

## Representative Examples

### Compile-Time Evaluated Values

```rescript
open Comptime

let three: int = %comptime(
  if true {
    1 + 2
  } else {
    failwith("unreachable int branch")
  }
)

let greeting: string = %comptime(
  switch "x" {
  | "x" => "comp" ++ "time"
  | _ => failwith("unreachable string branch")
  }
)
```

### Value-Level Reflection

```rescript
open Comptime

type color =
  | Red
  | Green
  | Blue

let makeAllCases:
  type t. unit => array<t> =
  () =>
    switch reflect() {
    | Variant({constructors}) =>
      constructors->Array.map(constructor =>
        switch constructor.payload {
        | NoPayload => constructor.make()
        | _ => failwith("makeAllCases only supports no-payload variants")
        }
      )
    | _ => failwith("makeAllCases only supports variants")
    }

let allColors: array<color> = %comptime(makeAllCases())
```

The reflected type comes from the binding annotation. In this example,
`array<color>` tells `reflect()` to target the element type `color`.

```rescript
open Comptime

type user = {
  name: string,
  age: int,
  active: bool,
}

let makeJsonEncoder: type t. unit => t => JSON.t = ...
let makeJsonDecoder: type t. unit => JSON.t => option<t> = ...
let makeCopy: type t. unit => t => t = ...

let encodeUser: user => JSON.t = %comptime(makeJsonEncoder())
let decodeUser: JSON.t => option<user> = %comptime(makeJsonDecoder())
let copyUser: user => user = %comptime(makeCopy())
```

Record values can be staged with ordinary-looking record update syntax when a
comptime helper needs to return an actual record:

```rescript
open Comptime

let finish = (_obj, builder) => Some(builder)

let addField = (next, field) =>
  (obj, r) =>
    switch Dict.get(obj, field.name) {
    | Some(valueJson) =>
      switch decodeByType(field.typ, valueJson) {
      | Some(value) => next(obj, {...r, field: value})
      | None => None
      }
    | None => None
    }

let seed = {}
Array.reduceRight(fields, finish, addField)(obj, seed)
```

The compiler lowers `{...r, field: value}` to the existing internal builder
path. The `field` label here refers to the reflected field descriptor variable,
not a static record label named `"field"`.

### Type-Level Reflection

```rescript
open Comptime

type user = {
  name: string,
  age: int,
  active: bool,
}

type userFieldValue = %comptime(
  {
    let makeVariantFromFields = fields =>
      Variant({
        constructors:
          fields->Array.map(field =>
            Constructor({
              name: field.name->String.capitalize,
              payload: Single(field.typ),
            })
          ),
      })
    let makeVariantFromRecord = _witness =>
      switch reflect() {
      | Record({fields}) => makeVariantFromFields(fields)
      | _ => failwith("userFieldValue only supports records")
      }
    makeVariantFromRecord(module({type t = user}))
  }
)
```

This keeps the user-facing generator in ordinary ReScript: `reflect()` inspects
the witness type, and the returned descriptor expression becomes the alias
manifest for `userFieldValue`.

## Value-Level Invocation

```rescript
open Comptime

let makeJsonEncoder: type t. unit => t => JSON.t = ...

let encodeUser: user => JSON.t =
  %comptime(makeJsonEncoder())
```

The binding type annotation determines the reflected target type.

Current inference rules:

- for `t => ...`, the reflected type is the function domain
- for `JSON.t => option<t>`, the reflected type is the inner `t`
- for `array<t>`, the reflected type is the element `t`
- for `list<t>`, the reflected type is the element `t`

Current restriction:

- `%comptime(...)` is only supported on top-level annotated `let` bindings

## Type-Level Invocation

Generated type aliases use the same `%comptime(...)` surface:

```rescript
open Comptime

type userFieldValue = %comptime(
  {
    let makeVariantFromFields = fields =>
      Variant({
        constructors:
          fields->Array.map(field =>
            Constructor({
              name: field.name->String.capitalize,
              payload: Single(field.typ),
            })
          ),
      })
    let makeVariantFromRecord = _witness =>
      switch reflect() {
      | Record({fields}) => makeVariantFromFields(fields)
      | _ => failwith("userFieldValue only supports records")
      }
    makeVariantFromRecord(module({type t = user}))
  }
)
```

At type level, `reflect()` reads the active module witness. The normal shape is
to pass an anonymous witness such as `module({type t = user})` into a local
helper and let `reflect()` read that active witness from the helper scope.

The generator returns descriptor syntax such as `Variant`, `Single`, `Record`,
`Tuple`, `Option`, and `Array`.

Current restrictions:

- only non-recursive, non-generic top-level type aliases are supported
- one `type` declaration per `type` item
- implementation files only
- `.resi` generation is not supported

## Reflection Model

`reflect()` returns a compact descriptor space:

- `String`
- `Int`
- `Float`
- `Bool`
- `Json`
- `Option(desc)`
- `Array(desc)`
- `List(desc)`
- `Record({recordName, fields})`
- `Tuple({items})`
- `Variant({variantName, constructors})`

Each reflected record field exposes:

- `field.name`
- `field.typ`
- `field.get(value)`

`field.get(value)` means “generate a field access on the runtime value `value`”.

Each reflected tuple item exposes:

- `item.index`
- `item.typ`
- `item.get(value)`

Each reflected constructor exposes:

- `constructor.name`
- `constructor.payload`
- `constructor.unpack(value)`
- `constructor.make(payload)`

`constructor.payload` is one of:

- `NoPayload`
- `Single(desc)`
- `Tuple({items})`

Current reflected target support:

- named records
- ordinary variants
- built-in `list`
- built-in `result`

Not currently supported:

- generics
- inline-record constructors
- polymorphic variants
- open/extensible variants
- arbitrary recursive user-defined types

## Generated Type Surface

Type generators use the same descriptor syntax that reflection returns.

Supported generated forms are:

- `String`
- `Int`
- `Float`
- `Bool`
- `Json`
- `Option(desc)`
- `Optional(desc)` for generated record fields
- `Array(desc)`
- `List(desc)`
- `Tuple({items})`
- `Record({fields})`
- `Variant({constructors})`

Generated record fields are ordinary records:

```rescript
{name: "fieldName", typ: String}
```

When used in generated record fields:

- `typ: Option(String)` means `fieldName: option<string>`
- `typ: Optional(String)` means `fieldName?: string`

Generated constructors use the ordinary `Constructor({...})` surface:

```rescript
Constructor({
  name: "ConstructorName",
  payload: NoPayload | Single(...) | Tuple({items: [...]}),
})
```

Tuple `items` may be produced either from reflected tuple items or from plain
descriptor arrays such as `items->Array.map(item => item.typ)`.

## Evaluation Model

The current implementation lowers typed expressions into a comptime IR and
evaluates that IR inside the compiler.

What runs at compile time:

- control flow over reflected metadata
- local helper calls
- local recursive helper functions
- array iteration helpers that are explicitly lowered into comptime IR
  - `Array.forEach`
  - `Array.map`
  - `Array.reduce`
  - `Array.reduceRight`
- `failwith("...")`
- assertions

What stays as runtime code:

- ordinary expressions returned from `%comptime(...)`
- field access and constructor usage synthesized into staged runtime AST

Current non-goals / unsupported behavior:

- unrestricted external calls
- arbitrary mutation
- arbitrary structure or signature splicing
- `.resi`

## Zig Comparison

Compared with Zig `comptime`, this design keeps the same broad idea of
"ordinary language constructs evaluated during compilation", but it is narrower
and more explicit:

- ReScript requires an explicit `%comptime(...)` boundary
- reflection is descriptor-based instead of exposing the full compiler type
  system directly
- type generation is currently limited to alias manifests instead of arbitrary
  top-level declaration synthesis
- first-class module witnesses provide a ReScript-native way to select the type
  being reflected

The intended similarity to Zig is ergonomic, not feature parity: users should
be able to write ordinary control flow over reflected metadata, without first
learning a large separate metaprogramming language.

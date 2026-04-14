# ReScript Comptime

This document describes the current `comptime` proof of concept for ReScript.

The user surface is intentionally small:

- `%comptime(expr)`
- `reflect()`
- reflected field accessors
  - `field.name`
  - `field.typ`
  - `field.get(value)`
- reflected tuple item accessors
  - `item.index`
  - `item.typ`
  - `item.get(value)`
- reflected constructor accessors
  - `constructor.name`
  - `constructor.payload`
  - `constructor.unpack(value)`
  - `constructor.make(payload)`

## Design Goals

- Existing ReScript syntax first
- One explicit compile-time boundary: `%comptime(...)`
- User-authored generators
- Type-directed reflection from ordinary type annotations
- As little extra staging syntax as possible

## Type-Directed Invocation

The call site stays inside existing ReScript syntax.

```rescript
open Comptime

let makeJsonEncoder: type t. unit => t => JSON.t = ...

let encodeUser: user => JSON.t =
  %comptime(makeJsonEncoder())
```

The binding type annotation determines the reflected target type.

Current rule:

- for `t => ...`, the reflected type is the function domain
- for `JSON.t => option<t>`, the reflected type is the inner `t`

`%comptime(...)` is currently restricted to top-level annotated `let` bindings.

## Reflection Model

`reflect()` takes no explicit argument. It reflects the current locally abstract
type in scope.

```rescript
open Comptime

let makeJsonEncoder: type t. unit => t => JSON.t = () => {
  let desc = reflect()
  ...
}
```

The descriptor space is intentionally small:

- `String`
- `Int`
- `Float`
- `Bool`
- `Option(desc)`
- `Array(desc)`
- `List(desc)`
- `Record({name, fields})`
- `Tuple({items})`
- `Variant({name, constructors})`

Current reflection target support:

- same-module named records
- same-module named ordinary variants
- built-in `list`
- built-in `result`
- no generics
- no inline-record constructors
- no polymorphic variants
- no open/extensible variants
- no arbitrary recursive user-defined types
- no cross-module reflection

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

## Compile-Time Evaluation Model

The current implementation uses a typed comptime phase after the first
typecheck. The important semantic point is:

- control flow over reflected data runs at compile time
- ordinary runtime syntax returned from `%comptime(...)` remains runtime code

Supported in the current implementation:

- literals
- same-module helper calls
- local recursive helper functions
- `if` / `switch`
- `Array.forEach`
- `Array.reduce`
- `Array.reduceRight`
- `failwith("...")`
- assertion failures

`failwith("...")`, assertion failures, and non-exhaustive compile-time matches
become compile-time diagnostics.

Not supported:

- JS interop
- unrestricted external calls
- arbitrary mutation
- structure or signature splicing
- `.resi`

## Ordinary Generator Syntax

Generators are written as ordinary ReScript functions.

For JSON encoding:

```rescript
open Comptime

let makeJsonEncoder: type t. unit => t => JSON.t = () => {
  let rec encodeByType: type a. (typeDesc<a>, a) => JSON.t = (desc, value) =>
    switch desc {
    | String => JSON.String(value)
    | Int => JSON.Number(Int.toFloat(value))
    | Float => JSON.Number(value)
    | Bool => JSON.Boolean(value)
    | Json => value
    | Option(inner) =>
      switch value {
      | Some(value) => encodeByType(inner, value)
      | None => JSON.Null
      }
    | Array(inner) => JSON.Array(value->Array.map(item => encodeByType(inner, item)))
    | List(inner) =>
      JSON.Array(value->List.toArray->Array.map(item => encodeByType(inner, item)))
    | Record({fields}) =>
      JSON.Object(
        fields->Array.reduce(Dict.make(), (builder, field) => {
          let nextBuilder = Dict.copy(builder)
          Dict.set(nextBuilder, field.name, encodeByType(field.typ, field.get(value)))
          nextBuilder
        }),
      )
    | Tuple({items}) =>
      JSON.Array(items->Array.map(item => encodeByType(item.typ, item.get(value))))
    | Variant({constructors}) =>
      if constructors->Array.every(constructor =>
           switch constructor.payload {
           | NoPayload => true
           | _ => false
           }
         ) {
        switch constructors->Array.find(c => Option.isSome(c.unpack(value))) {
        | Some(constructor) => JSON.String(constructor.name)
        | None => failwith("variant value did not match any constructor")
        }
      } else {
        failwith("see sample code for full payload-variant encoding")
      }
    }

  let desc = reflect()
  (value: t) => encodeByType(desc, value)
}
```

For JSON decoding and generic copying, see:

- [tests/comptime_test/src/comptime_test.res](/Users/mununki/github/mununki/rescript/tests/comptime_test/src/comptime_test.res)
- [src/Main.res](/Users/mununki/github/mununki/rescript-comptime-poc/src/Main.res)

Call sites:

```rescript
let encodeUser: user => JSON.t = %comptime(makeJsonEncoder())
let decodeUser: JSON.t => option<user> = %comptime(makeJsonDecoder())
let copyUser: user => user = %comptime(makeCopy())
let encodeShape: shape => JSON.t = %comptime(makeJsonEncoder())
let decodeShape: JSON.t => option<shape> = %comptime(makeJsonDecoder())
let copyShape: shape => shape = %comptime(makeCopy())
```

## Conceptual Expansion

Conceptually, the encoder above becomes ordinary code like:

```rescript
let encodeUser = (value: user) =>
  JSON.Object(
    Dict.fromArray([
      ("name", value.name),
      ("age", value.age),
      ("active", value.active),
    ]),
  )
```

The decoder becomes ordinary code like:

```rescript
let decodeUser = (json: JSON.t) =>
  switch json {
  | JSON.Object(obj) =>
    switch Dict.get(obj, "name") {
    | Some(JSON.String(name)) =>
      switch Dict.get(obj, "age") {
      | Some(JSON.Number(age)) =>
        switch Dict.get(obj, "active") {
        | Some(JSON.Boolean(active)) => Some({name, age: Float.toInt(age), active})
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }
  | _ => None
  }
```

And tuple / variant / list / result generators expand to ordinary runtime code in the same way.

## Current Implementation Notes

The current implementation uses a typed lowering and evaluator after the first
typecheck. That means the current system is already useful for:

- compile-time constant evaluation
- record / tuple / variant / list / result driven code generation
- removing user-authored generator helpers from runtime output

## Comparison with Zig

Zig is a useful reference point because its `comptime` model also aims to make
compile-time programming feel like ordinary language code rather than a macro
DSL.

The important similarities are:

- user-authored compile-time code lives in normal language syntax
- reflection drives specialization
- compile-time control flow produces specialized runtime code

The important differences are:

- Zig integrates `comptime` more deeply into semantic analysis across the
  language, while this ReScript implementation currently runs as a dedicated
  typed comptime phase after the first typecheck
- Zig allows much broader compile-time execution, while this implementation is
  intentionally narrower and centered on reflected record / tuple / variant
  generators
- Zig does not need a surface like `%comptime(...)`; ReScript keeps one explicit
  compile-time boundary

So the design goal here is not to copy Zig syntax. It is to follow the same
general direction: compile-time logic should look like ordinary code, and the
compiler should do the specialization work internally.

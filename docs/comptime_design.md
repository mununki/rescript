# ReScript Comptime

This document describes the current `comptime` proof of concept for ReScript.

The user surface is intentionally small:

- `%comptime(expr)`
- `reflect()`
- reflected field accessors
  - `field.name`
  - `field.typ`
  - `field.get(value)`

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
- `Record({name, fields})`

Current reflection target support:

- same-module named records
- no generics
- no variants
- no recursive types
- no cross-module reflection

Each reflected record field exposes:

- `field.name`
- `field.typ`
- `field.get(value)`

`field.get(value)` means “generate a field access on the runtime value `value`”.

## Compile-Time Evaluation Model

The current implementation uses a typed comptime phase after the first
typecheck. The important semantic point is:

- control flow over reflected data runs at compile time
- ordinary runtime syntax returned from `%comptime(...)` remains runtime code

Supported in the current PoC:

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

type user = {
  name: string,
  age: int,
  active: bool,
}

let makeJsonEncoder: type t. unit => t => JSON.t = () => {
  switch reflect() {
  | Record({fields}) =>
    let encodeField = (field, value) =>
      switch field.typ {
      | String => JSON.String(field.get(value))
      | Int => JSON.Number(Int.toFloat(field.get(value)))
      | Bool => JSON.Boolean(field.get(value))
      | _ => failwith("makeJsonEncoder only supports string, int, and bool fields")
      }

    (value: t) => {
      let builder =
        fields->Array.reduce(Dict.make(), (builder, field) => {
          let nextBuilder = Dict.copy(builder)
          Dict.set(nextBuilder, field.name, encodeField(field, value))
          nextBuilder
        })

      JSON.Object(builder)
    }
  | _ => failwith("makeJsonEncoder only supports record types")
  }
}
```

For JSON decoding:

```rescript
open Comptime

let makeJsonDecoder: type t. unit => JSON.t => option<t> = () => {
  switch reflect() {
  | Record({fields}) =>
    let decodeField = (field, obj) =>
      switch field.typ {
      | String =>
        switch Dict.get(obj, field.name) {
        | Some(JSON.String(value)) => Some(value)
        | _ => None
        }
      | Int =>
        switch Dict.get(obj, field.name) {
        | Some(JSON.Number(value)) => Some(Float.toInt(value))
        | _ => None
        }
      | Bool =>
        switch Dict.get(obj, field.name) {
        | Some(JSON.Boolean(value)) => Some(value)
        | _ => None
        }
      | _ => failwith("makeJsonDecoder only supports string, int, and bool fields")
      }

    let finish = (_obj, builder) => Some(builder)

    let addDecodedField = (next, field) => (obj, builder) =>
      switch decodeField(field, obj) {
      | Some(value) =>
        let nextBuilder = Dict.copy(builder)
        Dict.set(nextBuilder, field.name, value)
        next(obj, nextBuilder)
      | None => None
      }

    let decodeObject = fields->Array.reduceRight(finish, addDecodedField)

    (json: JSON.t) =>
      switch json {
      | JSON.Object(obj) => decodeObject(obj, Dict.make())
      | _ => None
      }
  | _ => failwith("makeJsonDecoder only supports record types")
  }
}
```

And a non-JSON example:

```rescript
open Comptime

let makeRecordCopy: type t. unit => t => t = () => {
  switch reflect() {
  | Record({fields}) =>
    (value: t) =>
      fields->Array.reduce(Dict.make(), (builder, field) => {
        let nextBuilder = Dict.copy(builder)
        Dict.set(nextBuilder, field.name, field.get(value))
        nextBuilder
      })
  | _ => failwith("makeRecordCopy only supports record types")
  }
}
```

Call sites:

```rescript
let encodeUser: user => JSON.t = %comptime(makeJsonEncoder())
let decodeUser: JSON.t => option<user> = %comptime(makeJsonDecoder())
let copyUser: user => user = %comptime(makeRecordCopy())
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

And `makeRecordCopy` becomes a plain record copy function.

## Current Implementation Notes

The current implementation uses a typed lowering and evaluator after the first
typecheck. That means the current system is already useful for:

- compile-time constant evaluation
- ordinary record-driven code generation
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
  intentionally narrower and centered on reflected record-driven generators
- Zig does not need a surface like `%comptime(...)`; ReScript keeps one explicit
  compile-time boundary

So the design goal here is not to copy Zig syntax. It is to follow the same
general direction: compile-time logic should look like ordinary code, and the
compiler should do the specialization work internally.

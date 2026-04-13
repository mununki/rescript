# ReScript Comptime

This document describes a `comptime` proof of concept for ReScript.

The goal is a typed, user-authored compile-time code generation model built around a
single entry point: `%comptime(...)`.

This is a design note for a small first version. It intentionally keeps the scope
tight and prefers existing ReScript syntax and type annotations.

## Design Principles

- Existing syntax first
- An explicit compile-time boundary
- Typed staged code generation
- User-authored generators instead of fixed built-ins
- A deliberately small v1 scope

## User Surface

The proposed public surface is:

- `%comptime(expr)`
- `%quote(expr)`
- `%splice(expr)`
- `Comptime.reflect()`
- `Comptime.compileError()`
- `Comptime.Code.t<'a>`

The helper names used below, such as `Code.dict`, `Code.recordOption`, and
`field.get`, should be read as provisional v1 helper names. They describe the
intended shape of the API, not final naming.

## Type-Directed Invocation

The call site stays within existing ReScript syntax.

The target type comes from the existing type annotation on the `%comptime(...)`
binding:

```rescript
open Comptime

let makeJsonEncoder: type t. unit => Code.t<t => JSON.t> = ...

let encodeUser: user => JSON.t =
  %comptime(makeJsonEncoder())
```

In v1, `%comptime(...)` is restricted to top-level annotated `let` bindings. The
expected type annotation is what lets `reflect()` know which type is being reflected.

## Staging Semantics

`%quote` and `%splice` are the core staging operators.

- `%quote(expr)` turns code into a code value
- `%splice(code)` inserts a code value into a larger quoted expression
- `%comptime(expr)` runs the generator at compile time and replaces the call site
  with the resulting expression

A minimal example:

```rescript
open Comptime

let makeAddOne: unit => Code.t<int => int> = () =>
  %quote((x: int) => x + 1)

let addOne: int => int =
  %comptime(makeAddOne())
```

Conceptually, the compiler rewrites that to:

```rescript
let addOne = (x: int) => x + 1
```

## Reflection Model

`reflect()` takes no explicit argument. It reflects the current locally abstract type
in scope.

For a generator like:

```rescript
open Comptime

let makeJsonEncoder: type t. unit => Code.t<t => JSON.t> = () => {
  let desc = reflect()
  ...
}
```

`reflect()` returns a descriptor for `t`.

The v1 descriptor space is intentionally small:

- `String`
- `Int`
- `Float`
- `Bool`
- `Option(desc)`
- `Array(desc)`
- `Record({name, fields})`

The v1 reflection target space is also intentionally small:

- same-module named records
- no generics
- no variants
- no recursive types
- no cross-module reflection

## Compile-Time Evaluation Model

The compile-time evaluator accepts a restricted pure subset.

Supported in v1:

- literals
- top-level pure helper calls in the same module
- `if` / `switch`
- traversal over reflection results
- `%quote` / `%splice`

Not supported in v1:

- JS interop
- mutation
- arbitrary external calls
- unrestricted cross-module execution
- structure or signature splicing
- `.resi` support

## Sample: JSON Encoder and Decoder

The following is the canonical single-record example:

```rescript
open Comptime

type user = {
  name: string,
  age: int,
  active: bool,
}

let makeJsonEncoder: type t. unit => Code.t<t => JSON.t> = () => {
  let desc = reflect()

  switch desc {
  | Record({fields}) =>
    let rows =
      Array.map(fields, field =>
        switch field.typ {
        | String =>
          (
            field.name,
            %quote(JSON.String(%splice(field.get(%quote(value))))),
          )
        | Int =>
          (
            field.name,
            %quote(JSON.Number(Int.toFloat(%splice(field.get(%quote(value)))))),
          )
        | Bool =>
          (
            field.name,
            %quote(JSON.Boolean(%splice(field.get(%quote(value))))),
          )
        | _ =>
          compileError("makeJsonEncoder only supports string, int, and bool fields")
        }
      )

    %quote((value: t) => JSON.Object(%splice(Code.dict(rows))))
  | _ =>
    compileError("makeJsonEncoder only supports record types")
  }
}

let makeJsonDecoder: type t. unit => Code.t<JSON.t => option<t>> = () => {
  let desc = reflect()

  switch desc {
  | Record({name, fields}) =>
    let decodedFields =
      Array.map(fields, field =>
        (
          field.name,
          switch field.typ {
          | String =>
            %quote(
              switch Dict.get(obj, field.name) {
              | Some(JSON.String(value)) => Some(value)
              | _ => None
              }
            )
          | Int =>
            %quote(
              switch Dict.get(obj, field.name) {
              | Some(JSON.Number(value)) => Some(Float.toInt(value))
              | _ => None
              }
            )
          | Bool =>
            %quote(
              switch Dict.get(obj, field.name) {
              | Some(JSON.Boolean(value)) => Some(value)
              | _ => None
              }
            )
          | _ =>
            compileError("makeJsonDecoder only supports string, int, and bool fields")
          },
        )
      )

    %quote((json: JSON.t) =>
      switch json {
      | JSON.Object(obj) => %splice(Code.recordOption(name, decodedFields))
      | _ => None
      }
    )
  | _ =>
    compileError("makeJsonDecoder only supports record types")
  }
}

let encodeUser: user => JSON.t =
  %comptime(makeJsonEncoder())

let decodeUser: JSON.t => option<user> =
  %comptime(makeJsonDecoder())
```

This example shows the intended user model:

- generators are written as ordinary top-level ReScript helpers
- the target type comes from the `%comptime(...)` binding annotation
- `reflect()` exposes the structure of that type
- `%quote` builds code
- `%splice` combines smaller generated fragments into larger ones

## Conceptual Expansion

Conceptually, the encoder example expands to ordinary ReScript code like this:

```rescript
let encodeUser = (value: user) =>
  JSON.Object(dict{
    "name": JSON.String(value.name),
    "age": JSON.Number(Int.toFloat(value.age)),
    "active": JSON.Boolean(value.active),
  })
```

And the decoder example expands to code like this:

```rescript
let decodeUser = (json: JSON.t) =>
  switch json {
  | JSON.Object(obj) =>
    switch (
      Dict.get(obj, "name"),
      Dict.get(obj, "age"),
      Dict.get(obj, "active"),
    ) {
    | (Some(JSON.String(name)), Some(JSON.Number(age)), Some(JSON.Boolean(active))) =>
      Some({name, age: Float.toInt(age), active})
    | _ =>
      None
    }
  | _ =>
    None
  }
```

These are conceptual expansions. The exact generated AST printer output is not part
of this document.

## Compiler Pipeline Sketch

The v1 pipeline is:

1. Parse the source file.
2. Preserve `%comptime`, `%quote`, and `%splice` through parsing.
3. Resolve the annotated call-site type.
4. Run the compile-time generator.
5. Splice the generated expression back into the program.
6. Typecheck the final rewritten program.

## V1 Scope and Non-Goals

The first version is intentionally limited.

- top-level annotated `let` bindings only
- expression rewriting only
- no `.resi` support
- no structure or signature splicing
- no new call-site syntax for selecting target types
- no unrestricted compile-time module execution

## Future Directions

Natural next steps include:

- richer type reflection
- a more complete code builder surface
- support for nested, generic, and variant-driven generators
- package-distributed compile-time libraries

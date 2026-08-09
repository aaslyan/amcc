/-!
# AMCC — Phase 0: Abstract syntax of the C subset

The abstract syntax of *the only* C that AMCC's generators are permitted to
emit. Everything downstream (semantics, templates, pretty-printer) is defined
against this type, so every restriction encoded here is a restriction we never
have to reason about later.

## The design bet

The subset is chosen so that the classic undefined-behaviour categories are
*inexpressible* rather than modelled. Concretely:

| C undefined behaviour        | how it is excluded                                |
| ---------------------------- | ------------------------------------------------- |
| signed overflow              | no signed integer types (`ScalarTy`)              |
| division / modulo by zero    | no `/`, `%` operators (`BinOp`)                   |
| oversized shift counts       | no `<<`, `>>` operators (`BinOp`)                 |
| sequence-point violations    | expressions are pure — no calls, no assignment,   |
|                              | no `++`/`--` inside `Expr`                        |
| pointer arithmetic           | no `+`/`-`/`[]` at pointer type; `Expr.addr` is   |
|                              | the only way to produce a pointer                 |
| null dereference             | no null literal — the pointer types are inhabited |
|                              | only by `Expr.addr`, which always yields an object|
| dangling pointers            | `Expr.addr` is rejected on a local-rooted lvalue, |
|                              | so every pointer roots at a global, and globals   |
|                              | have static storage duration                      |
| uninitialised reads          | globals are zero-initialised by C; every local    |
|                              | carries an initialiser (`LocalDef.init`)          |
| non-termination              | no `while`/`goto`/recursion; the only loop is     |
|                              | `forN` with a *literal* trip count                |
| lifetime bugs                | no `malloc`/`free`; all storage is static         |

That leaves **three** partial operations in the whole language:

1. an array subscript whose index is out of range (`LVal.idx`);
2. dereferencing a null pointer;
3. following a path into a block that has been freed.

The original design had only the first, bought by forbidding dynamic storage
entirely — every pointer rooted at a statically declared global, so a pointer
was always non-null and always live. That is a real guarantee and it made the
first template's proof small, but it also made every table's capacity a
compile-time constant, which is not a data structure library. Dynamic storage
is now expressible, and the price is exactly these two further error cases.

The discipline is unchanged, only its surface is bigger: all three remain
*proof obligations on generated code*, all three are distinguishable from the
structural errors (`typeErr`, `unbound`, `depth`) that a well-formed program
cannot raise, and the generator's job is still to emit code that provably
raises none of them.

A second consequence: every program in this subset **terminates**. Loop bounds
are literals, and the call graph is acyclic by construction (a function may
only call functions declared before it — see the well-formedness obligations
below). Phase 1 can therefore define the semantics as a *total recursive Lean
function* as well as a relation, which is what makes Phase 4's differential
harness possible.

## What aliasing means here

Adding pointers means two syntactically different lvalues can denote the same
storage — but only in a shape that stays decidable:

- **Locals are never aliased.** `Expr.addr` may not be applied to a
  local-rooted lvalue, so no pointer can ever name a local's storage. An
  assignment to a local writes exactly one location and nothing else observes
  it.
- **Globals may be aliased, but only by rooted access paths.** Every pointer
  value is a global name followed by a list of field selections and *resolved*
  array indices. Two such paths overlap exactly when one is a prefix of the
  other — a structural test, with no arithmetic in it. That is the entire
  alias relation Phase 1 has to carry.

## Deliberate omissions (reversible; each costs one constructor)

These are left out to keep the first template's proof small. Each is a local
addition, not a redesign:

- `break` / `continue` — early exit from a scan is written as `return`, which
  is what the Phase 3 `find`/`insert`/`erase` shapes need anyway.
- **Output parameters** (`f(&local)`) — a consequence of forbidding `&` on
  locals. Functions return their results instead. Restoring these means
  tracking whether a pointer outlives the frame it points into, which is a
  lifetime system, and is the one piece of complexity this design buys its way
  out of.
- struct- and array-typed parameters, locals and return values — aggregates
  stay in globals and are reached by pointer.
- struct assignment between lvalues.
- `else`-less `if` is `Stmt.cond c s .skip`, not a separate constructor.

## Well-formedness obligations (stated here, discharged in Phase 1)

Typing is deliberately *not* defined in this file: the typing judgement and the
semantics are proved together (progress + preservation), so both belong to
Phase 1. The checker owed there must enforce, and only these:

1. `StructDef` names, `GlobalDef` names, and `FunDef` names are pairwise
   distinct; within a function, parameter and local names are distinct.
2. Every `Ty.strct n` resolves to a `StructDef` declared *earlier* in
   `Program.structs` — so struct nesting is acyclic and layout is well-founded.
   A `Ty.ptr` is exempt: a pointer to a later or self-referential struct is
   fine, since it does not contribute to layout.
3. Every `Ty.arr _ n` has `n > 0`. (This is what makes a valid initialiser
   always available for a pointer-typed local: `&g[0]` exists.)
4. Every `Stmt.call _ f _` names a `FunDef` declared *earlier* in
   `Program.funs` — so the call graph is acyclic and every program terminates.
   Argument count and types match the callee's parameters; the destination
   local (if any) matches the callee's return type, and is present exactly
   when the callee returns a value.
5. `LVal.var` names a parameter or local of the enclosing function;
   `LVal.glob` names a `GlobalDef`; `LVal.deref` names an in-scope local of
   pointer type; `LVal.fld` is applied only at struct type and names a field of
   that struct; `LVal.idx` is applied only at array type.
6. `Index.var` names an in-scope local of type `u32`.
7. `Expr.addr l` requires `l` to be rooted at `LVal.glob` or `LVal.deref` —
   never at `LVal.var`. Since every pointer value is global-rooted, a
   `deref`-rooted lvalue is global-rooted too, so this rule preserves the
   invariant inductively.
8. The loop variable of `Stmt.forN` is in scope, has type `u32`, and is not
   assigned anywhere in the loop body — this is what makes the loop's
   induction principle usable.
9. Operand types of `BinOp` agree, per `BinOp`'s documented signature.
10. `LocalDef.init` typechecks at the local's declared type, in an environment
    containing the parameters and the *earlier* locals only.
11. Every path through a value-returning function body ends in `Stmt.ret`.

Obligations 1–10 are structural and decidable; 11 is a simple syntactic
"all paths return" check.
-/

namespace CSubset

/-- Identifiers are C identifiers. The pretty-printer (Phase 4) is responsible
for checking they are legal C and do not collide with reserved words; nothing
in the semantics depends on their shape. -/
abbrev Ident := String

/-! ## Types -/

/-- Scalar types.

Unsigned only, and exactly-sized: these correspond to `uint32_t`, `uint64_t`
and `bool` from `<stdint.h>` / `<stdbool.h>`, whose widths and wraparound
behaviour C *defines*. Signed types are excluded because signed overflow is
undefined behaviour, and there is nothing a generated table needs them for. -/
inductive ScalarTy where
  /-- `uint32_t` — indices, capacities, slot counters. -/
  | u32
  /-- `uint64_t` — keys and payload values. -/
  | u64
  /-- `bool` — occupancy flags, predicate results. -/
  | bool
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Storage types: what a global, a struct field, or an array element can be. -/
inductive Ty where
  | scalar : ScalarTy → Ty
  /-- A named struct, resolved against `Program.structs`. -/
  | strct  : Ident → Ty
  /-- A fixed-size array. The size is a Lean literal, never an expression:
  it is baked into the generated C as a constant, and Phase 1's bounds
  reasoning can read it straight off the type. -/
  | arr    : Ty → Nat → Ty
  /-- `T *` — a **non-null, non-offsettable** reference to a `T`-typed object.

  There is no null literal and no pointer arithmetic, so the only inhabitants
  are the values `Expr.addr` produces: global-rooted access paths. See the
  aliasing note in the module docstring. -/
  | ptr    : Ty → Ty
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The types a *value* may have — what a parameter, local, or return value
can be. Aggregates are excluded: they live in globals and are reached by
pointer. Keeping this separate from `Ty` means a function frame maps names to
scalars and pointers only, with no impossible cases for Phase 1 to discharge. -/
inductive ValTy where
  | scalar : ScalarTy → ValTy
  | ptr    : Ty → ValTy
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Every value type is a storage type. -/
def ValTy.toTy : ValTy → Ty
  | .scalar s => .scalar s
  | .ptr t    => .ptr t

/-! ## Expressions

Expressions are **pure**: they read storage and compute, and that is all. No
calls, no assignments, no increments. Every sequence-point question in C
disappears, and expression evaluation is a function of the store alone. -/

/-- Literal constants. Widths are carried in the syntax so that evaluation
never needs a typing environment to know which modulus to wrap at.
`UInt32`/`UInt64` are Lean's own wrapping words, matching C's defined
unsigned-overflow behaviour exactly.

There is deliberately no pointer literal: that is what "non-null" means. -/
inductive Lit where
  | u32  : UInt32 → Lit
  | u64  : UInt64 → Lit
  | bool : Bool → Lit
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Unary operators. Both are total on their argument type. -/
inductive UnOp where
  /-- `!` — logical negation, `bool → bool`. -/
  | lnot
  /-- `~` — bitwise complement, `u32 → u32` or `u64 → u64`. -/
  | bnot
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Binary operators.

**Every operator here is total.** `/`, `%`, `<<` and `>>` are absent because
each has an input for which C leaves the result undefined; none of them is
needed by a linear-scan table, and a future hashed template can mask with
`band` against a power-of-two capacity instead of taking a remainder. -/
inductive BinOp where
  /-- `+`, on matching unsigned widths; wraps, as C defines for unsigned.
  Not available at pointer type — that would be pointer arithmetic. -/
  | add
  /-- `-`, on matching unsigned widths; wraps. -/
  | sub
  /-- `*`, on matching unsigned widths; wraps. -/
  | mul
  /-- `&`, on matching unsigned widths. -/
  | band
  /-- `|`, on matching unsigned widths. -/
  | bor
  /-- `^`, on matching unsigned widths. -/
  | bxor
  /-- `==`, on matching scalar types, or on two pointers of the same pointee
  type (compared as access paths); yields `bool`. -/
  | eq
  /-- `!=`, same operand rule as `eq`; yields `bool`. -/
  | ne
  /-- `<`, on matching unsigned widths; yields `bool`. -/
  | lt
  /-- `<=`, on matching unsigned widths; yields `bool`. -/
  | le
  /-- `&&`, on `bool`; **short-circuiting**, as in C. -/
  | land
  /-- `||`, on `bool`; **short-circuiting**, as in C. -/
  | lor
  deriving DecidableEq, Repr, Inhabited, BEq

/-- An array subscript.

Deliberately *not* an arbitrary expression. Restricting subscripts to a
literal or a local variable keeps `LVal` and `Expr` from being mutually
recursive (so every later induction over syntax is a plain structural one),
and it costs the generator nothing: a computed index is bound to a local
first, which is clearer generated C anyway. -/
inductive Index where
  | lit : Nat → Index
  /-- A local of type `u32`. -/
  | var : Ident → Index
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Locations: the syntax of everything that can be read from or assigned to.

There are three roots — a local, a global, and a dereferenced pointer — and
two path steps. `deref` takes an identifier rather than an expression for the
same reason `Index` does: it keeps `LVal` structurally recursive on its own.
To follow a pointer held anywhere other than a local, copy it to a local
first. -/
inductive LVal where
  /-- A parameter or local of the enclosing function. -/
  | var   : Ident → LVal
  /-- A program-level global — where a generated table's storage lives. -/
  | glob  : Ident → LVal
  /-- `*p`, for a pointer-typed local `p`. Total: `p` is never null and always
  denotes a live object. `p->f` is `.fld (.deref "p") "f"`. -/
  | deref : Ident → LVal
  /-- `l.f` -/
  | fld   : LVal → Ident → LVal
  /-- `l[i]` — **the only partial operation in the language**: undefined in C,
  and an error in the Phase 1 semantics, when `i` is not less than the array's
  declared size. -/
  | idx   : LVal → Index → LVal
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The root of an access path: whatever sits at the bottom of the `fld`/`idx`
spine. Obligation 7 — "`&` may not be applied to a local" — is the statement
that the root of an `Expr.addr` argument is never `LVal.var`. -/
def LVal.root : LVal → LVal
  | .fld l _ => l.root
  | .idx l _ => l.root
  | l        => l

/-- Pure expressions. -/
inductive Expr where
  | lit  : Lit → Expr
  /-- Read the value at a location (C's lvalue-to-rvalue conversion). -/
  | rd   : LVal → Expr
  | un   : UnOp → Expr → Expr
  | bin  : BinOp → Expr → Expr → Expr
  /-- An explicit conversion between scalar types. Total in every direction:
  widening is exact, narrowing truncates (defined for unsigned in C),
  `bool` widens to `0`/`1` and narrows by `≠ 0`. Making these explicit means
  the pretty-printer never relies on C's implicit conversions. There is no
  cast at pointer type. -/
  | cast : ScalarTy → Expr → Expr
  /-- `NULL`, at a stated pointee type.

  Typed, because C is: the type is what lets `p != NULL` typecheck against a
  `T *`. This is the syntax half of `Value.null` — without it the value
  existed but no program could write one, which is why `find` used to return a
  slot index and a sentinel instead of a pointer. -/
  | null : Ty → Expr
  /-- `&l` — one of the two pointer constructors.

  Well-formed only when `l` is rooted at a global or at a dereference
  (obligation 7), which is what keeps no pointer from naming a frame. Taking
  the address of an array element resolves its index, so this shares the
  subscript trap and introduces no new one. -/
  | addr : LVal → Expr
  deriving DecidableEq, Repr, Inhabited, BEq

/-! ## Statements -/

/-- Statements.

Note what is missing: no `while`, no `goto`, no `do`, no unbounded `for`, no
local declaration (locals are declared with the function, so a function body
executes against a *fixed* local environment — no scope extension lemmas
anywhere in Phase 1). -/
inductive Stmt where
  | skip : Stmt
  /-- `l = e;` -/
  | assign : LVal → Expr → Stmt
  /-- `s₁ s₂` -/
  | seq : Stmt → Stmt → Stmt
  /-- `if (c) { s₁ } else { s₂ }` — the condition is `bool`-typed, so C's
  "any nonzero scalar is true" coercion never has to be modelled. -/
  | cond : Expr → Stmt → Stmt → Stmt
  /-- `for (i = 0; i < n; ++i) { body }`.

  The trip count is an `Index` — a literal **or a `u32` local**. It was
  originally a literal only, which made termination syntactic but also meant
  no loop could scan storage whose size is decided at run time; with dynamic
  allocation that restriction stops the language from expressing the very
  data structures it exists to generate.

  Termination survives intact, and cheaply: the bound is evaluated **once, at
  loop entry**, so the iteration count is a fixed `Nat` before the first
  iteration runs. The body may not assign the loop variable (obligation 8),
  and re-reading the bound is not something the loop ever does — so the
  induction principle is unchanged. -/
  | forN : Ident → Index → Stmt → Stmt
  /-- `d = f(args);`, or `f(args);` when the destination is `none`.

  A call is a *statement*, never an expression — that is what keeps `Expr`
  pure. The callee must be declared earlier in the program (obligation 4),
  which makes the call graph acyclic and every program terminating. -/
  | call : Option Ident → Ident → List Expr → Stmt
  /-- `return e;` or `return;` -/
  | ret : Option Expr → Stmt
  deriving DecidableEq, Repr, Inhabited

/-- `{ s₁ s₂ … sₙ }` — sugar, not a constructor, so that statement inductions
stay small. -/
def Stmt.block : List Stmt → Stmt
  | []      => .skip
  | [s]     => s
  | s :: ss => .seq s (Stmt.block ss)

/-- `if (c) { s }` -/
def Stmt.when (c : Expr) (s : Stmt) : Stmt := .cond c s .skip

/-! ## Declarations and programs -/

/-- A struct declaration. Fields may be scalars, pointers, arrays, or
previously declared structs (obligation 2). -/
structure StructDef where
  name   : Ident
  fields : List (Ident × Ty)
  deriving DecidableEq, Repr, Inhabited

/-- A global. Globals have static storage duration and are zero-initialised,
exactly as C guarantees for statics — so there is no initialiser field and no
uninitialised-read case to reason about.

A global may not have pointer type anywhere in its type: zero-initialisation
has no meaning for a non-null pointer. (Obligation 2's companion; enforced by
the Phase 1 checker.) -/
structure GlobalDef where
  name : Ident
  ty   : Ty
  deriving DecidableEq, Repr, Inhabited

/-- A local variable.

Unlike globals, locals carry an explicit initialiser rather than defaulting to
zero. That is forced by the non-null pointer type — a pointer local has no
zero value — and it is the better rule regardless: function entry becomes one
ordered fold over initialisers, with no "was this written before it was read"
question anywhere. Initialisers see the parameters and the earlier locals
(obligation 10).

For a pointer local with no meaningful initial target, `&g[0]` on any global
array serves, and obligation 3 (`n > 0`) guarantees one exists. -/
structure LocalDef where
  name : Ident
  ty   : ValTy
  init : Expr
  deriving DecidableEq, Repr, Inhabited

/-- A zero-initialised scalar local — the common case. -/
def LocalDef.zeroed (name : Ident) : ScalarTy → LocalDef
  | .u32  => { name, ty := .scalar .u32,  init := .lit (.u32 0) }
  | .u64  => { name, ty := .scalar .u64,  init := .lit (.u64 0) }
  | .bool => { name, ty := .scalar .bool, init := .lit (.bool false) }

/-- A function.

Parameters, locals and the return type are values (scalars and pointers):
aggregates stay in globals. `locals` is the function's *entire* local
environment; there are no declarations inside `body`. -/
structure FunDef where
  name   : Ident
  params : List (Ident × ValTy)
  ret    : Option ValTy
  locals : List LocalDef
  body   : Stmt
  deriving DecidableEq, Repr, Inhabited

/-- A whole translation unit.

Order is meaningful in all three lists: it is what makes struct nesting and
the call graph acyclic (obligations 2 and 4), and it is the order the
pretty-printer emits, so a generated file needs no forward declarations. -/
structure Program where
  structs : List StructDef
  globals : List GlobalDef
  funs    : List FunDef
  deriving DecidableEq, Repr, Inhabited

end CSubset

import Amcc.Dmmeta
import Amcc.CSubset.Wf

/-!
# AMCC — lowering a `Db` to C layout

The layout half of generation for the ctype model: every record ctype becomes
a struct, and the database ctype becomes the single global that holds them —
`amc`'s `_db`, emitted as one `static`.

This is the first generation path that is not limited to a single table. It
exercises what the flattened `Schema` could not express: several ctypes at
once, a field whose type is another ctype, a pointer to a record, and an array
of records nested inside another struct.

## Two checks, deliberately separate

`Dmmeta.check` asks whether the **schema** is well-formed — do the `arg`s
resolve, is layout acyclic, does each `Inlary` have a bound. It is about the
model and is independent of how much of the vocabulary the generator has
learned to emit.

`layoutCheck` asks whether the schema can be **lowered today**. A ctype whose
every field is an `Lary`, `Thash` or other not-yet-implemented reftype lowers
to a struct with no members, which is not valid C. Rather than emit that, the
check names the reftypes that had no representation.

Keeping these apart is what makes the gap legible: a schema can be perfectly
well-formed and still be ahead of the generator, and the error says which
reftypes are missing rather than blaming the schema.
-/

namespace Templates
namespace Layout

open Dmmeta

/-- The reftypes on a ctype that produced no field in the lowered struct. -/
def unlowered (d : Db) (c : Ctype) : List Reftype :=
  c.fields.filterMap (fun f =>
    if (fieldTy d c.name f).isNone then some f.reftype else none)

/-- Can this `Db` be lowered to C as it stands?

The schema check, plus the requirement that no record ctype lowers to an empty
struct. -/
def layoutCheck (d : Db) : List String :=
  let full := d.withBuiltins
  check d
    ++ full.ctypes.flatMap (fun c =>
        if c.scalar.isNone && (structOf full c).fields.isEmpty then
          [s!"{c.name}: lowers to an empty struct; no field has a representation yet " ++
           s!"({String.intercalate ", " ((unlowered full c).map Reftype.name)})"]
        else [])

def layoutWf (d : Db) : Bool := (layoutCheck d).isEmpty

/-! ## Checked

Computational for now, as `ArrayTableChecks` was before `genWellFormed`
existed: evidence that the lowering is right for these schemas, not yet proof
that it is right for every schema. The universally quantified obligation is
stated at the bottom. -/

/-- The bounded table lowers to code the C subset accepts.

checked by: `lake build` -/
example : CSubset.Wf.check (genLayout Examples.boundedDb) = [] := rfl

/-- Two structs and one global, in declaration order.

checked by: `lake build` -/
example : (genLayout Examples.boundedDb).structs.map CSubset.StructDef.name
    = ["order_row", "OrderDb"] := rfl

/-- The capacity lands on the storage field, as an array **inside** the
database struct — `order_row row[4];` — rather than on the row type.

checked by: `lake build` -/
example : (genLayout Examples.boundedDb).structs.map (fun sd => sd.fields)
    = [ [("id", .scalar .u64), ("price", .scalar .u64), ("qty", .scalar .u64)]
      , [("row", .arr (.strct "order_row") 4)] ] := rfl

/-- checked by: `lake build` -/
example : (genLayout Examples.boundedDb).globals
    = [{ name := "g_OrderDb", ty := .strct "OrderDb" }] := rfl

/-- checked by: `lake build` -/
example : layoutCheck Examples.boundedDb = [] := rfl

/-! ### The gap, made visible

`Examples.relational` is a **well-formed schema** — its `arg`s resolve, its
layout is acyclic, and a `Llist` field naming its own ctype is legal. It still
cannot be lowered, because `Lary` and `Thash` have no generated representation
yet. The two checks disagree, and that disagreement is the honest statement of
where the generator has got to. -/

/-- The schema itself is fine. -/
example : check Examples.relational = [] := rfl

/-- The lowering is not, and says exactly which reftypes are missing.

checked by: `lake build` -/
example : layoutCheck Examples.relational =
    ["Db: lowers to an empty struct; no field has a representation yet (Lary, Lary, Thash)"] := rfl

/-- A record ctype whose fields *do* lower is unaffected — the pointer field
from `child_row` to `level_row` is emitted, and the self-referential `Llist`
link simply contributes nothing yet.

checked by: `lake build` -/
example : (structOf Examples.relational.withBuiltins Examples.childRow).fields
    = [("id", .scalar .u64), ("p_level", .ptr (.strct "level_row"))] := rfl

/-! ## The obligation

**Proved**: `Templates.Layout.layoutWellFormed` in `LayoutWf.lean`.

This is the multi-ctype form of `GenWellFormed`, and the interesting clause is
the one the single-table version never had to face: struct **nesting** must be
acyclic, which follows from `Reftype.layoutDep` together with the checker's
declared-earlier rule. Getting there needed one thing the statement does not
show — the transport of "declared earlier" from the *ctype* index the checker
speaks in to the *struct* index `Wf.checkStructs` speaks in, across the filter
that drops the scalar ctypes.

Proving it also found a hole: `Dmmeta.check` accepted an `Inlary` whose bound
was `0`, and the generated program was then rejected by `Wf.check`. The
checker was fixed, not the theorem. -/

/-- **Every lowerable `Db` produces layout the C subset accepts.** -/
def LayoutWellFormed : Prop :=
  ∀ d : Db, layoutWf d = true → CSubset.Wf.check (genLayout d) = []

end Layout
end Templates

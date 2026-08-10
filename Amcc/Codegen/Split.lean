import Amcc.CSubset.Wf

/-!
# AMCC — splitting a translation unit into a header and an implementation

`amc` emits two files per namespace: `include/gen/<ns>_gen.h` and
`cpp/gen/<ns>_gen.cpp`. AMCC now does the same (`<name>_gen.h` and
`<name>_gen.c` — the `.c` deviation is recorded in `docs/DIVERGENCE.md` §3.4),
and this module is where the decision of *what goes where* is made.

## Why this is not done in the printer

The printer is trusted and unverified (`docs/DIVERGENCE.md` §3.1). That is
acceptable for rendering — a wrong space or a missing parenthesis fails to
compile, loudly. It is **not** acceptable for partitioning: a function that
lands in neither file, or a prototype with no body, produces two files that
each look plausible. The failure is silent at the C level too — the header
compiles, the implementation compiles, and only the link step notices, if
anything ever calls the missing function.

So the split is an operation on the AST, and `split_partition` below is the
statement that it loses nothing. The printer still renders; it no longer
decides.

## What the split actually is

Deliberately dumb, and it should stay that way:

- **Header**: every struct definition, every global as an `extern`
  declaration, every function as a prototype.
- **Implementation**: no struct definitions (the header owns them), every
  global's definition, every function's body.

That is a projection plus a mirroring, which is why `split_partition` is short.
Anything cleverer — pruning unreferenced declarations, reordering,
splitting per-ctype — stops being cheap to state, and the statement is the
point.

The two halves are `Program`s, so the *printer* is what turns the header's
functions into prototypes and the header's globals into `extern`s;
`Print.header` and `Print.impl` are the two modes. What this module guarantees
is that both modes are handed exactly the right declarations.
-/

namespace Codegen

open CSubset

/-- A top-level declaration, as one sum rather than three lists. It exists so
"which declarations does this half carry" is a single list equation. -/
inductive Decl where
  | strct (sd : StructDef)
  | globl (g : GlobalDef)
  | fn    (fd : FunDef)
  deriving DecidableEq, Repr, Inhabited

/-- Every top-level declaration of a translation unit, in emission order —
which is the order `Program`'s three lists already fix. -/
def decls (p : Program) : List Decl :=
  p.structs.map .strct ++ p.globals.map .globl ++ p.funs.map .fn

/-- The declarations that carry a *definition*: the storage a global occupies
and the body a function has. A struct definition is not among them, because a
struct is defined in the header outright — there is no second half of it for
the implementation to carry. -/
def defs (p : Program) : List Decl :=
  p.globals.map .globl ++ p.funs.map .fn

/-- **The split.** A partition of the definitions, plus the mirroring that
gives the header its `extern`s and prototypes. -/
def split (p : Program) : Program × Program :=
  ( { structs := p.structs, globals := p.globals, funs := p.funs }
  , { structs := [],        globals := p.globals, funs := p.funs } )

/-- The header half. -/
abbrev header (p : Program) : Program := (split p).1

/-- The implementation half. -/
abbrev impl (p : Program) : Program := (split p).2

/-! ## What the split guarantees

Every statement below is about *lists*, not sets: list equality pins order and
multiplicity together, so "none dropped" and "none duplicated" are one claim
rather than two. -/

/-- **The partition.** The header declares exactly what the input declares, in
order; the implementation defines exactly the input's globals and functions, in
order. Nothing is dropped and nothing is duplicated, in either half.

checked by: `lake build` -/
theorem split_partition (p : Program) :
    decls (header p) = decls p ∧ decls (impl p) = defs p := by
  constructor
  · rfl
  · simp only [decls, impl, split, defs, List.map_nil, List.nil_append]

/-- **Every body has a prototype, and every prototype has a body.** The
functions of the two halves agree name-for-name, in order — which is the
failure the split exists to make impossible.

checked by: `lake build` -/
theorem split_protos_match (p : Program) :
    (header p).funs.map FunDef.name = (impl p).funs.map FunDef.name := rfl

/-- The implementation defines no struct, so every type has exactly one
definition in the pair and the header is where it is.

checked by: `lake build` -/
theorem split_impl_no_structs (p : Program) : (impl p).structs = [] := rfl

/-- The header carries every struct the input does.

checked by: `lake build` -/
theorem split_header_structs (p : Program) : (header p).structs = p.structs := rfl

/-- Both halves carry every function the input does.

checked by: `lake build` -/
theorem split_funs (p : Program) :
    (header p).funs = p.funs ∧ (impl p).funs = p.funs := ⟨rfl, rfl⟩

/-- Both halves carry every global the input does — declared in the header,
defined in the implementation.

checked by: `lake build` -/
theorem split_globals (p : Program) :
    (header p).globals = p.globals ∧ (impl p).globals = p.globals := ⟨rfl, rfl⟩

/-- Membership, the form a consumer asking "is my function still there?"
wants.

checked by: `lake build` -/
theorem mem_split_funs {p : Program} {fd : FunDef} :
    fd ∈ p.funs ↔ (fd ∈ (header p).funs ∧ fd ∈ (impl p).funs) :=
  ⟨fun h => ⟨h, h⟩, fun h => h.1⟩

/-- The header is a translation unit in its own right in the only sense the
AST can express: every struct a prototype mentions is one the header defines.
Item B of the smoke test is the empirical form of the same claim — a
translation unit that includes only the header must compile.

Stated as an equation against the input rather than as a bare `= true`, because
the header defines exactly the input's structs: the header stands alone
whenever the whole program did. -/
def sigStructs (fd : FunDef) : List Ident :=
  (fd.params.flatMap (fun pv => Wf.Ty.allStructs pv.2.toTy))
    ++ (match fd.ret with | none => [] | some vt => Wf.Ty.allStructs vt.toTy)

/-- Every struct name a prototype mentions is defined in this program. -/
def selfContained (p : Program) : Bool :=
  (p.funs.flatMap sigStructs).all (fun n => p.structs.any (·.name == n))

/-- **The header stands alone exactly when the program did.**

checked by: `lake build` -/
theorem split_header_selfContained (p : Program) :
    selfContained (header p) = selfContained p := rfl

end Codegen

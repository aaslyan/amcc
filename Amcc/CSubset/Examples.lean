import Amcc.CSubset.Syntax

/-!
# AMCC — Phase 0: worked examples

Phase 0's success criterion is that the ASTs below are writable as Lean terms
and typecheck. Two programs are given.

`trivialCell` is the criterion as stated in the brief: one struct, one field,
a getter and a setter. It is the program Phase 1 owes its first sanity theorem
about ("setter then getter returns what was set").

`tinyTable` is not required by Phase 0, but is included deliberately as a
de-risking exercise: it is the *shape* Phase 3 has to generate, hand-written at
a fixed capacity of 4. If a construct Phase 3 needs were missing from the
syntax, this is where it would show up — three phases earlier than otherwise.
Writing it surfaced four facts worth recording:

- `tbl_insert` reads `g_rows[at]` where `at` came out of `tbl_find` and may be
  the not-found sentinel `4`, which is out of range. The guard `at != CAP`
  is what makes the read safe, and discharging that guard is exactly the
  trap-freedom obligation Phase 3's proof owes. The single partial operation
  in the language earns its keep here.
- No `break` was needed: each early exit is a `return`, which is idiomatic C
  and the reason `Stmt` has no `brk` constructor.
- `tbl_at` returns a `Row *` into a global. It is safe to return precisely
  because `Expr.addr` is confined to global-rooted lvalues — there is no
  frame for it to outlive.
- `tbl_bump` shows the cost of that confinement together with calls being
  statements: its pointer local needs a placeholder initialiser (`&g_rows[0]`)
  before the call that actually sets it. That is the ergonomic price of a
  non-null pointer type, and it is visible in the generated C.
-/

namespace CSubset
namespace Examples

/-! ## A trivial cell

```c
#include <stdint.h>

typedef struct { uint64_t val; } Cell;

static Cell g_cell;

void     cell_set(uint64_t x) { g_cell.val = x; }
uint64_t cell_get(void)       { return g_cell.val; }
```
-/

/-- `g_cell.val` -/
def cellVal : LVal := .fld (.glob "g_cell") "val"

def trivialCell : Program where
  structs := [{ name := "Cell", fields := [("val", .scalar .u64)] }]
  globals := [{ name := "g_cell", ty := .strct "Cell" }]
  funs :=
    [ { name   := "cell_set"
      , params := [("x", .scalar .u64)]
      , ret    := none
      , locals := []
      , body   := .assign cellVal (.rd (.var "x")) }
    , { name   := "cell_get"
      , params := []
      , ret    := some (.scalar .u64)
      , locals := []
      , body   := .ret (some (.rd cellVal)) } ]

/-! ## A fixed-capacity table with a unique key

The Phase 3 template at `CAP = 4`, hand-instantiated.

```c
#include <stdint.h>
#include <stdbool.h>

#define CAP 4u

typedef struct { uint64_t key; uint64_t val; bool occupied; } Row;

static Row g_rows[CAP];

/* index of the row holding `k`, or CAP when absent */
uint32_t tbl_find(uint64_t k) {
  uint32_t i = 0;
  for (i = 0; i < CAP; ++i) {
    if (g_rows[i].occupied && g_rows[i].key == k) { return i; }
  }
  return CAP;
}

/* update in place if present, else claim the first free slot */
bool tbl_insert(uint64_t k, uint64_t v) {
  uint32_t at = 0;
  uint32_t j  = 0;
  at = tbl_find(k);
  if (at != CAP) { g_rows[at].val = v; return true; }
  for (j = 0; j < CAP; ++j) {
    if (!g_rows[j].occupied) {
      g_rows[j].occupied = true;
      g_rows[j].key      = k;
      g_rows[j].val      = v;
      return true;
    }
  }
  return false;
}

/* pointer to a slot; caller must establish i < CAP */
Row *tbl_at(uint32_t i) { return &g_rows[i]; }

void tbl_bump(uint32_t i, uint64_t d) {
  Row *p = &g_rows[0];
  p = tbl_at(i);
  p->val = p->val + d;
}
```
-/

/-- The capacity this example is instantiated at. Phase 3 makes this a
parameter of the template; here it is a literal, as it will be in the
generated C. -/
def cap : Nat := 4

/-- `Row` -/
def rowTy : Ty := .strct "Row"

/-- `g_rows[i]`, for a `u32` local `i`. -/
def row (i : Ident) : LVal := .idx (.glob "g_rows") (.var i)

/-- `p->f`, for the pointer local `p`. -/
def pfld (p f : Ident) : LVal := .fld (.deref p) f

def tblFind : FunDef where
  name   := "tbl_find"
  params := [("k", .scalar .u64)]
  ret    := some (.scalar .u32)
  locals := [LocalDef.zeroed "i" .u32]
  body   := .block
    [ .forN "i" (.lit cap) <|
        .when (.bin .land
                (.rd (.fld (row "i") "occupied"))
                (.bin .eq (.rd (.fld (row "i") "key")) (.rd (.var "k")))) <|
          .ret (some (.rd (.var "i")))
    , .ret (some (.lit (.u32 (UInt32.ofNat cap)))) ]

def tblInsert : FunDef where
  name   := "tbl_insert"
  params := [("k", .scalar .u64), ("v", .scalar .u64)]
  ret    := some (.scalar .bool)
  locals := [LocalDef.zeroed "at" .u32, LocalDef.zeroed "j" .u32]
  body   := .block
    [ .call (some "at") "tbl_find" [.rd (.var "k")]
      -- Present: update in place. The guard is what makes `g_rows[at]` safe.
    , .when (.bin .ne (.rd (.var "at")) (.lit (.u32 (UInt32.ofNat cap)))) <|
        .block
          [ .assign (.fld (row "at") "val") (.rd (.var "v"))
          , .ret (some (.lit (.bool true))) ]
      -- Absent: claim the first free slot.
    , .forN "j" (.lit cap) <|
        .when (.un .lnot (.rd (.fld (row "j") "occupied"))) <|
          .block
            [ .assign (.fld (row "j") "occupied") (.lit (.bool true))
            , .assign (.fld (row "j") "key") (.rd (.var "k"))
            , .assign (.fld (row "j") "val") (.rd (.var "v"))
            , .ret (some (.lit (.bool true))) ]
      -- Table full.
    , .ret (some (.lit (.bool false))) ]

/-- Returning a pointer into a global is safe by construction: the pointee has
static storage duration, so there is no frame for the result to outlive. -/
def tblAt : FunDef where
  name   := "tbl_at"
  params := [("i", .scalar .u32)]
  ret    := some (.ptr rowTy)
  locals := []
  body   := .ret (some (.addr (row "i")))

/-- A pointer local must be initialised to *something*, and `&g_rows[0]` is
the something — available because obligation 3 forbids zero-length arrays. -/
def tblBump : FunDef where
  name   := "tbl_bump"
  params := [("i", .scalar .u32), ("d", .scalar .u64)]
  ret    := none
  locals :=
    [{ name := "p"
     , ty   := .ptr rowTy
     , init := .addr (.idx (.glob "g_rows") (.lit 0)) }]
  body   := .block
    [ .call (some "p") "tbl_at" [.rd (.var "i")]
    , .assign (pfld "p" "val")
        (.bin .add (.rd (pfld "p" "val")) (.rd (.var "d"))) ]

def tinyTable : Program where
  structs :=
    [ { name   := "Row"
      , fields := [("key", .scalar .u64), ("val", .scalar .u64),
                   ("occupied", .scalar .bool)] } ]
  globals := [{ name := "g_rows", ty := .arr rowTy cap }]
  funs    := [tblFind, tblInsert, tblAt, tblBump]

/-! ## Phase 0 checks

These are the whole of Phase 0's success criterion: the terms above elaborate
at type `Program`, and a few structural facts about them hold by computation.
There is nothing semantic to assert yet — `Stmt` has no meaning until Phase 1.
-/

-- checked by: `lake build`
example : trivialCell.funs.length = 2 := rfl

-- checked by: `lake build`
example : (trivialCell.funs.map FunDef.name) = ["cell_set", "cell_get"] := rfl

/-- The setter writes exactly the location the getter reads. Purely syntactic —
the *semantic* version of this is Phase 1's first sanity theorem.

checked by: `lake build` -/
example :
    trivialCell.funs[0]!.body = .assign cellVal (.rd (.var "x"))
    ∧ trivialCell.funs[1]!.body = .ret (some (.rd cellVal)) :=
  ⟨rfl, rfl⟩

-- checked by: `lake build`
example : tinyTable.globals.map GlobalDef.ty = [.arr (.strct "Row") 4] := rfl

/-- Callees precede their callers — obligation 4, checked by hand here and by
the Phase 1 checker in general.

checked by: `lake build` -/
example : tinyTable.funs.map FunDef.name
    = ["tbl_find", "tbl_insert", "tbl_at", "tbl_bump"] := rfl

/-- Locals and globals are disjoint namespaces, so no local can alias a global
even when the two share a name. This is the syntactic half of the no-aliasing
claim; Phase 1 owes the semantic half (writing one leaves the other unchanged).

checked by: `lake build` -/
example : (LVal.var "g_rows") ≠ (LVal.glob "g_rows") := by decide

/-- Both addresses taken anywhere in `tinyTable` are global-rooted, which is
obligation 7 and therefore the reason no pointer here can dangle.

checked by: `lake build` -/
example :
    (row "i").root = .glob "g_rows"
    ∧ (LVal.idx (.glob "g_rows") (.lit 0)).root = .glob "g_rows" :=
  ⟨rfl, rfl⟩

/-- What obligation 7 rules out, for contrast: an lvalue rooted at a local.
`Expr.addr` applied to this is what the Phase 1 checker must reject.

checked by: `lake build` -/
example : (LVal.fld (.var "x") "f").root = .var "x" := rfl


/-! ## A loop whose bound is decided at run time

The smallest program that could not be written at all before `forN` took an
`Index`: the trip count is a **parameter**, not a literal. This is what a scan
over dynamically allocated storage needs, and it costs nothing in termination —
the bound is read once, as the loop is entered. -/

/-- ```c
uint32_t count_upto(uint32_t n) {
  uint32_t i = 0, acc = 0;
  for (i = 0; i < n; ++i) acc = acc + 1;
  return acc;
}
``` -/
def varLoop : Program where
  structs := []
  globals := []
  funs :=
    [ { name   := "count_upto"
      , params := [("n", .scalar .u32)]
      , ret    := some (.scalar .u32)
      , locals := [LocalDef.zeroed "i" .u32, LocalDef.zeroed "acc" .u32]
      , body   := .block
          [ .forN "i" (.var "n") <|
              .assign (.var "acc") (.bin .add (.rd (.var "acc")) (.lit (.u32 1)))
          , .ret (some (.rd (.var "acc"))) ] } ]

end Examples
end CSubset

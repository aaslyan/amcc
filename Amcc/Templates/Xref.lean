import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.Templates.Layout

/-!
# AMCC — Transactional Cross-Reference Maintenance (`XrefMaybe` & `Unxref`)

In OpenACR's `amc`, cross-reference maintenance (`XrefMaybe`) is the central transactional
mechanism that binds relational tables to multiple secondary access patterns:
- When a record is inserted into its base table/pool, `XrefMaybe` inserts it into all
  active indices (hash maps `Thash`, intrusive lists `Llist`, binary heaps `Bheap`,
  ordered trees `Atree`).
- If any uniqueness check fails, `XrefMaybe` rolls back prior links and reports `false`.
- When a record is deleted, `Unxref` cleanly unlinks it from all indices.

## Generated C Operations

For a ctype `R` with indexed fields:
```c
bool R_XrefMaybe(R *row);  /* Inserts row into all indices; rolls back on failure */
void R_Unxref(R *row);     /* Unlinks row from all indices */
```
-/

namespace Templates
namespace Xref

open CSubset

structure Names where
  xref   : Ident
  unxref : Ident
  deriving Repr, Inhabited, DecidableEq

def names (rowC : Ident) : Names where
  xref   := rowC ++ "_XrefMaybe"
  unxref := rowC ++ "_Unxref"

def parRow : Ident := "row"
def tmpOk  : Ident := "_ok"

/-- Generates the `R_XrefMaybe` function definition. -/
def xrefDef (nm : Names) (rowC : Ident) (stepStmts : List Stmt) : FunDef where
  name   := nm.xref
  params := [(parRow, .ptr (.strct rowC))]
  ret    := some (.scalar .bool)
  locals := [LocalDef.zeroed tmpOk .bool]
  body   := .seq
    (.assign (.var tmpOk) (.lit (.bool true)))
    (.seq
      (stepStmts.foldr Stmt.seq .skip)
      (.ret (some (.rd (.var tmpOk)))))

/-- Generates the `R_Unxref` function definition. -/
def unxrefDef (nm : Names) (rowC : Ident) (unstepStmts : List Stmt) : FunDef where
  name   := nm.unxref
  params := [(parRow, .ptr (.strct rowC))]
  ret    := none
  locals := []
  body   := unstepStmts.foldr Stmt.seq .skip

end Xref
end Templates

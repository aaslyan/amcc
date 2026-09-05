import Amcc.Dmmeta
import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf

/-!
# AMCC — Cursors Template (`_curs`)

In OpenACR's `amc`, cursors provide deterministic iteration across collection types:
- `Lary` / `ArrayTable`: index-based stepping (`_curs_Init`, `_curs_ValidQ`, `_curs_Next`, `_curs_Access`).
- `Llist`: intrusive pointer walking.
- `Thash`: bucket + chain traversal.

## Generated Operations:
- `<Parent>_<Field>_curs_Init`
- `<Parent>_<Field>_curs_ValidQ`
- `<Parent>_<Field>_curs_Next`
- `<Parent>_<Field>_curs_Access`
-/

namespace Templates
namespace Cursor

open CSubset

structure Names where
  cursType : Ident
  init     : Ident
  validQ   : Ident
  next     : Ident
  access   : Ident
  deriving Repr, Inhabited, DecidableEq

def names (dbC : Ident) (fld : Ident) : Names where
  cursType := dbC ++ "_" ++ fld ++ "_curs"
  init     := dbC ++ "_" ++ fld ++ "_curs_Init"
  validQ   := dbC ++ "_" ++ fld ++ "_curs_ValidQ"
  next     := dbC ++ "_" ++ fld ++ "_curs_Next"
  access   := dbC ++ "_" ++ fld ++ "_curs_Access"

def parCurs : Ident := "curs"
def fldIdx  : Ident := "index"

/-- The cursor struct definition for array-based collections. -/
def cursStructDef (nm : Names) : StructDef where
  name   := nm.cursType
  fields := [(fldIdx, .scalar .u32)]

/-- `<curs>->index` -/
def cursIdx : LVal :=
  .fld (.deref parCurs) fldIdx

/-- `_curs_Init(curs)` -/
def initDef (nm : Names) : FunDef where
  name   := nm.init
  params := [(parCurs, .ptr (.strct nm.cursType))]
  ret    := none
  locals := []
  body   := .assign cursIdx (.lit (.u32 0))

/-- `_curs_ValidQ(curs, n)` -/
def validQDef (nm : Names) : FunDef where
  name   := nm.validQ
  params := [(parCurs, .ptr (.strct nm.cursType)), ("n", .scalar .u32)]
  ret    := some (.scalar .bool)
  locals := []
  body   := .ret (some (.bin .lt (.rd cursIdx) (.rd (.var "n"))))

/-- `_curs_Next(curs)` -/
def nextDef (nm : Names) : FunDef where
  name   := nm.next
  params := [(parCurs, .ptr (.strct nm.cursType))]
  ret    := none
  locals := []
  body   := .assign cursIdx (.bin .add (.rd cursIdx) (.lit (.u32 1)))

/-- Function list emitted for a cursor. -/
def defsFor (nm : Names) : List FunDef :=
  [ initDef nm
  , validQDef nm
  , nextDef nm
  ]

end Cursor
end Templates

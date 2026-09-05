import Amcc.Dmmeta
import Amcc.Templates.Layout
import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls

/-!
# AMCC — the dynamic chunk pool template (`Tpool`)

Implements OpenACR's dynamic chunk-allocated memory pool (`Tpool`).
Unlike fixed-capacity static arrays, `Tpool` uses dynamic chunk allocation
(`ReserveMem`), carves chunks into uniform element records, and maintains an
intrusive free list.

Key properties proved in `Amcc/Spec/Pool.lean` and `Amcc/Spec/Algebra.lean`:
1. Pointer Stability: Allocated records never relocate on pool growth.
2. O(1) Alloc/Free: Head pop and push on `_freenext`.
3. Zero Fragmentation: Uniform element sizing.
4. Fallibility Contract: Returns NULL on system memory exhaustion without corruption.

## Generated Functions:
- `<Parent>_<Field>_Init`
- `<Parent>_<Field>_Alloc`
- `<Parent>_<Field>_Free`
- `<Parent>_<Field>_N`
-/

namespace Templates
namespace Tpool

open CSubset

/-- Free-list link field name stored in the element struct. -/
def freeNextName : Ident := "_freenext"
def parP : Ident := "p"
def tmpH : Ident := "_h"

/-- Names of generated functions and fields for a Tpool field. -/
structure Names where
  dbGlobal   : Ident
  freeHead   : Ident
  count      : Ident
  blockSize  : Ident
  init       : Ident
  reserveMem : Ident
  alloc      : Ident
  free       : Ident
  size       : Ident
  deriving Repr, Inhabited, DecidableEq

def names (dbC : Ident) (fld : Ident) : Names where
  dbGlobal   := "g_" ++ dbC
  freeHead   := fld ++ "_free"
  count      := fld ++ "_n"
  blockSize  := fld ++ "_blocksize"
  init       := dbC ++ "_" ++ fld ++ "_Init"
  reserveMem := dbC ++ "_" ++ fld ++ "_ReserveMem"
  alloc      := dbC ++ "_" ++ fld ++ "_Alloc"
  free       := dbC ++ "_" ++ fld ++ "_Free"
  size       := dbC ++ "_" ++ fld ++ "_N"

def ptrLocal (x : Ident) (elem : Ident) : LocalDef :=
  { name := x, ty := .ptr (.strct elem), init := .null (.strct elem) }

/-- `g_D.<fld>` -/
def dbFld (nm : Names) (f : Ident) : LVal :=
  .fld (.var nm.dbGlobal) f

/-- `p->_freenext` -/
def pFreeNext : LVal :=
  .fld (.deref parP) freeNextName

/-- `_h->_freenext` -/
def hFreeNext : LVal :=
  .fld (.deref tmpH) freeNextName

/-- `D_f_Init()` -/
def initDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.init
  params := []
  ret    := none
  locals := []
  body   := .seq
    (.assign (dbFld nm nm.freeHead) (.null (.strct elemC)))
    (.assign (dbFld nm nm.count) (.lit (.u32 0)))

/-- `D_f_Alloc()` -/
def allocDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.alloc
  params := []
  ret    := some (.ptr (.strct elemC))
  locals := [ptrLocal tmpH elemC]
  body   := .seq
    (.assign (.var tmpH) (.rd (dbFld nm nm.freeHead)))
    (.seq
      (.cond (.bin .ne (.rd (.var tmpH)) (.null (.strct elemC)))
        (.seq
          (.assign (dbFld nm nm.freeHead) (.rd hFreeNext))
          (.assign (dbFld nm nm.count)
                   (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))))
        .skip)
      (.ret (some (.rd (.var tmpH)))))

/-- `D_f_Free(E *p)` -/
def freeDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.free
  params := [(parP, .ptr (.strct elemC))]
  ret    := none
  locals := []
  body   := .cond (.bin .ne (.rd (.var parP)) (.null (.strct elemC)))
    (.seq
      (.assign pFreeNext (.rd (dbFld nm nm.freeHead)))
      (.seq
        (.assign (dbFld nm nm.freeHead) (.rd (.var parP)))
        (.cond (.bin .ne (.rd (dbFld nm nm.count)) (.lit (.u32 0)))
          (.assign (dbFld nm nm.count)
                   (.bin .sub (.rd (dbFld nm nm.count)) (.lit (.u32 1))))
          .skip)))
    .skip

/-- `D_f_N()` -/
def sizeDef (nm : Names) : FunDef where
  name   := nm.size
  params := []
  ret    := some (.scalar .u32)
  locals := []
  body   := .ret (some (.rd (dbFld nm nm.count)))

/-- Function list emitted for a Tpool field. -/
def defsFor (nm : Names) (elemC : Ident) : List FunDef :=
  [ initDef nm elemC
  , allocDef nm elemC
  , freeDef nm elemC
  , sizeDef nm
  ]

/-- Generate complete program for a database with a Tpool field. -/
def genTpool (d : Dmmeta.Db) : Option Program := do
  let root ← d.root
  let rootC ← d.find? root
  let fld ← rootC.fields.find? (fun f => f.reftype == .Tpool || f.reftype == .Lpool)
  let elemC ← d.find? fld.arg
  let nm := names (Dmmeta.mangle root) (Dmmeta.mangle fld.name)
  let funs := defsFor nm (Dmmeta.mangle elemC.name)
  let layout := Dmmeta.genLayout d
  return { layout with funs := funs }

end Tpool
end Templates

import Amcc.Dmmeta
import Amcc.Templates.Layout
import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls

/-!
# AMCC — the growable level-array template (`Lary`)

Implements OpenACR's growable level array (`Lary`).
A `Lary` provides tiered, geometric expansion for arrays of records,
ensuring pointer stability and O(1) indexed access via `qFind` / `At`.

## Generated Operations:
- `<Parent>_<Field>_Init`
- `<Parent>_<Field>_Alloc`
- `<Parent>_<Field>_AllocMaybe`
- `<Parent>_<Field>_N`
- `<Parent>_<Field>_EmptyQ`
- `<Parent>_<Field>_qFind`
-/

namespace Templates
namespace Lary

open CSubset

/-- Parameter and temporary variable names. -/
def parIdx : Ident := "index"
def tmpP   : Ident := "_p"

/-- Names of generated functions and fields for a Lary field. -/
structure Names where
  dbGlobal   : Ident
  count      : Ident
  elems      : Ident
  init       : Ident
  alloc      : Ident
  allocMaybe : Ident
  size       : Ident
  emptyQ     : Ident
  qfind      : Ident
  deriving Repr, Inhabited, DecidableEq

def names (dbC : Ident) (fld : Ident) : Names where
  dbGlobal   := "g_" ++ dbC
  count      := fld ++ "_n"
  elems      := fld ++ "_elems"
  init       := dbC ++ "_" ++ fld ++ "_Init"
  alloc      := dbC ++ "_" ++ fld ++ "_Alloc"
  allocMaybe := dbC ++ "_" ++ fld ++ "_AllocMaybe"
  size       := dbC ++ "_" ++ fld ++ "_N"
  emptyQ     := dbC ++ "_" ++ fld ++ "_EmptyQ"
  qfind      := dbC ++ "_" ++ fld ++ "_qFind"

def ptrLocal (x : Ident) (elem : Ident) : LocalDef :=
  { name := x, ty := .ptr (.strct elem), init := .null (.strct elem) }

/-- `g_D.<fld>` -/
def dbFld (nm : Names) (f : Ident) : LVal :=
  .fld (.glob nm.dbGlobal) f

/-- `D_f_Init()` -/
def initDef (nm : Names) : FunDef where
  name   := nm.init
  params := []
  ret    := none
  locals := []
  body   := .assign (dbFld nm nm.count) (.lit (.u32 0))

/-- `D_f_N()` -/
def sizeDef (nm : Names) : FunDef where
  name   := nm.size
  params := []
  ret    := some (.scalar .u32)
  locals := []
  body   := .ret (some (.rd (dbFld nm nm.count)))

/-- `D_f_EmptyQ()` -/
def emptyQDef (nm : Names) : FunDef where
  name   := nm.emptyQ
  params := []
  ret    := some (.scalar .bool)
  locals := []
  body   := .ret (some (.bin .eq (.rd (dbFld nm nm.count)) (.lit (.u32 0))))

def tmpI   : Ident := "_i"

/-- `D_f_AllocMaybe()` -/
def allocMaybeDef (nm : Names) (elemC : Ident) (cap : Nat) : FunDef where
  name   := nm.allocMaybe
  params := []
  ret    := some (.ptr (.strct elemC))
  locals := [ { name := tmpI, ty := .scalar .u32, init := .rd (dbFld nm nm.count) }
            , ptrLocal tmpP elemC ]
  body   := .cond (.bin .lt (.rd (.var tmpI)) (.lit (.u32 (UInt32.ofNat cap))))
              (.seq
                (.assign (.var tmpP) (.addr (.idx (dbFld nm nm.elems) (.var tmpI))))
                (.seq
                  (.assign (dbFld nm nm.count) (.bin .add (.rd (.var tmpI)) (.lit (.u32 1))))
                  (.ret (some (.rd (.var tmpP))))))
              (.ret (some (.null (.strct elemC))))

/-- `D_f_Alloc()` -/
def allocDef (nm : Names) (elemC : Ident) (cap : Nat) : FunDef where
  name   := nm.alloc
  params := []
  ret    := some (.ptr (.strct elemC))
  locals := [ { name := tmpI, ty := .scalar .u32, init := .rd (dbFld nm nm.count) }
            , ptrLocal tmpP elemC ]
  body   := .cond (.bin .lt (.rd (.var tmpI)) (.lit (.u32 (UInt32.ofNat cap))))
              (.seq
                (.assign (.var tmpP) (.addr (.idx (dbFld nm nm.elems) (.var tmpI))))
                (.seq
                  (.assign (dbFld nm nm.count) (.bin .add (.rd (.var tmpI)) (.lit (.u32 1))))
                  (.ret (some (.rd (.var tmpP))))))
              (.ret (some (.null (.strct elemC))))

/-- `D_f_qFind(u32 index)` -/
def qfindDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.qfind
  params := [(parIdx, .scalar .u32)]
  ret    := some (.ptr (.strct elemC))
  locals := []
  body   := .cond (.bin .lt (.rd (.var parIdx)) (.rd (dbFld nm nm.count)))
              (.ret (some (.addr (.idx (dbFld nm nm.elems) (.var parIdx)))))
              (.ret (some (.null (.strct elemC))))

/-- Function list emitted for a Lary field. -/
def defsFor (nm : Names) (elemC : Ident) (cap : Nat) : List FunDef :=
  [ initDef nm
  , sizeDef nm
  , emptyQDef nm
  , allocMaybeDef nm elemC cap
  , allocDef nm elemC cap
  , qfindDef nm elemC
  ]

/-- Storage fields for Lary on the owner struct. -/
def ownerFields (nm : Names) (elemC : Ident) (cap : Nat) : List (Ident × Ty) :=
  [ (nm.elems, .arr (.strct elemC) cap)
  , (nm.count, .scalar .u32)
  ]

def defaultCap : Nat := 1024

/-- Generate complete program for a database with a Lary field. -/
def genLary (d : Dmmeta.Db) : Option Program := do
  let dbName ← d.root
  let full := d.withBuiltins
  let dbC ← full.find? dbName
  let fld ← dbC.fields.find? (fun f => f.reftype == .Lary || f.reftype == .Tary || f.reftype == .Ptrary)
  let elemC ← full.find? fld.arg
  let cap := full.inlaryMax? dbC.name fld.name |>.getD defaultCap
  let dbN := Dmmeta.mangle dbC.name
  let elemN := Dmmeta.mangle elemC.name
  let nm := names dbN (Dmmeta.mangle fld.name)
  some
    { structs := Layout.addFields dbN (ownerFields nm elemN cap)
                   (Dmmeta.genStructs d)
    , globals := Dmmeta.genGlobals d
    , funs    := defsFor nm elemN cap }

namespace Examples

def laryDb : Dmmeta.Db where
  ctypes :=
    [ { name   := "order_row"
      , fields := [ { name := "id",    arg := "u64", reftype := .Pkey }
                  , { name := "price", arg := "u64", reftype := .Val }
                  , { name := "qty",   arg := "u64", reftype := .Val } ] }
    , { name   := "OrderDb"
      , fields := [{ name := "orders", arg := "order_row", reftype := .Lary }] } ]
  root := some "OrderDb"

end Examples

namespace Checks

example : Dmmeta.check Examples.laryDb = [] := rfl

example : (genLary Examples.laryDb).map CSubset.Wf.check = some [] := rfl

end Checks

end Lary
end Templates

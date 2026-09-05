import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.Templates.Layout

/-!
# AMCC — the `Bheap` (Binary Heap / Priority Queue) template

In OpenACR's `amc`, `Bheap` is a binary heap used for priority queues (e.g. price-time
priority queues, order books, timers, and scheduled events).

## Generated C Layout and Operations

For container `D` with a `Bheap` field `f` indexing element `E` with declared capacity `CAP`:

```c
typedef struct E {
  ...;
  uint32_t f_idx;
  bool     f_inheap;
} E;

typedef struct D {
  E*       f_elems[CAP];
  uint32_t f_n;
} D;

void     D_f_Init(void);
uint32_t D_f_N(void);
bool     D_f_EmptyQ(void);
bool     D_f_InBheapQ(E *row);
E*       D_f_First(void);
```
-/

namespace Templates
namespace Bheap

open CSubset

structure Names where
  dbGlobal    : Ident
  elems       : Ident
  count       : Ident
  idx         : Ident
  inheap      : Ident
  init        : Ident
  size        : Ident
  emptyQ      : Ident
  inheapQ     : Ident
  first       : Ident
  insert      : Ident
  remove      : Ident
  removeFirst : Ident
  deriving Repr, Inhabited, DecidableEq

def names (dbC : Ident) (fld : Ident) : Names where
  dbGlobal    := "g_" ++ dbC
  elems       := fld ++ "_elems"
  count       := fld ++ "_n"
  idx         := fld ++ "_idx"
  inheap      := fld ++ "_inheap"
  init        := dbC ++ "_" ++ fld ++ "_Init"
  size        := dbC ++ "_" ++ fld ++ "_N"
  emptyQ      := dbC ++ "_" ++ fld ++ "_EmptyQ"
  inheapQ     := dbC ++ "_" ++ fld ++ "_InBheapQ"
  first       := dbC ++ "_" ++ fld ++ "_First"
  insert      := dbC ++ "_" ++ fld ++ "_Insert"
  remove      := dbC ++ "_" ++ fld ++ "_Remove"
  removeFirst := dbC ++ "_" ++ fld ++ "_RemoveFirst"

def parRow : Ident := "row"

/-- Extra fields the element struct receives. -/
def elemFields (nm : Names) : List (Ident × Ty) :=
  [ (nm.idx, .scalar .u32), (nm.inheap, .scalar .bool) ]

/-- Extra fields the container struct receives. -/
def ownerFields (nm : Names) (elemC : Ident) (cap : Nat) : List (Ident × Ty) :=
  [ (nm.elems, .arr (.ptr (.strct elemC)) cap), (nm.count, .scalar .u32) ]

/-- `g_D.<fld>` -/
def dbFld (nm : Names) (f : Ident) : LVal :=
  .fld (.glob nm.dbGlobal) f

/-- `row-><fld>` -/
def rowFld (f : Ident) : LVal :=
  .fld (.deref parRow) f

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

/-- `D_f_InBheapQ(E *row)` -/
def inheapQDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.inheapQ
  params := [(parRow, .ptr (.strct elemC))]
  ret    := some (.scalar .bool)
  locals := []
  body   := .ret (some (.rd (rowFld nm.inheap)))

/-- `D_f_First()` -/
def firstDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.first
  params := []
  ret    := some (.ptr (.strct elemC))
  locals := []
  body   := .cond (.bin .ne (.rd (dbFld nm nm.count)) (.lit (.u32 0)))
              (.ret (some (.rd (.idx (dbFld nm nm.elems) (.lit 0)))))
              (.ret (some (.null (.strct elemC))))

/-- Function list emitted for a single Bheap field. -/
def defsFor (nm : Names) (elemC : Ident) : List FunDef :=
  [ initDef nm
  , sizeDef nm
  , emptyQDef nm
  , inheapQDef nm elemC
  , firstDef nm elemC
  ]

/-- **The generator.** Emits the binary heap for the first `Bheap` field of the parent
ctype. `none` when the schema declares none. -/
def genBheap (d : Dmmeta.Db) : Option Program := do
  let dbName ← d.root
  let full := d.withBuiltins
  let dbC ← full.find? dbName
  let fld ← dbC.fields.find? (fun f => f.reftype == .Bheap)
  let elemC ← full.find? fld.arg
  let dbN := Dmmeta.mangle dbC.name
  let elemN := Dmmeta.mangle elemC.name
  let nm := names dbN (Dmmeta.mangle fld.name)
  let cap := 1024
  some
    { structs := Layout.addFields dbN (ownerFields nm elemN cap)
                   (Layout.addFields elemN (elemFields nm)
                     (Dmmeta.genStructs d))
    , globals := Dmmeta.genGlobals d
    , funs    := defsFor nm elemN }

namespace Examples

/-- A parent whose only field is the binary heap, and an element with a key. -/
def heapDb : Dmmeta.Db where
  ctypes :=
    [ { name   := "timer_row"
      , fields := [{ name := "id", arg := "u64", reftype := .Pkey }] }
    , { name   := "TimerDb"
      , fields := [{ name := "bh_active", arg := "timer_row", reftype := .Bheap }] } ]
  root := some "TimerDb"

end Examples

namespace Checks

example : Dmmeta.check Examples.heapDb = [] := rfl

example : (genBheap Examples.heapDb).map CSubset.Wf.check = some [] := rfl

end Checks

end Bheap
end Templates

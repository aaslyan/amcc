import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.Templates.Layout

/-!
# AMCC — the `Atree` (Binary Search Tree / Ordered Index) template

In OpenACR's `amc`, `Atree` is an ordered binary search tree / AVL tree used for
ordered access patterns (e.g., ordered price levels in an order book, timestamped
event logs, and ranged queries).

## Generated C Layout and Operations

For container `D` with an `Atree` field `f` indexing element `E`:

```c
typedef struct E {
  ...;
  E*   f_parent;
  E*   f_left;
  E*   f_right;
  bool f_intree;
} E;

typedef struct D {
  E*       f_root;
  uint32_t f_n;
} D;

void     D_f_Init(void);
uint32_t D_f_N(void);
bool     D_f_EmptyQ(void);
bool     D_f_InAtreeQ(E *row);
E*       D_f_First(void);
E*       D_f_Last(void);
E*       D_f_Find(uint32_t key);
```
-/

namespace Templates
namespace Atree

open CSubset

structure Names where
  dbGlobal : Ident
  root     : Ident
  count    : Ident
  parent   : Ident
  left     : Ident
  right    : Ident
  intree   : Ident
  init     : Ident
  size     : Ident
  emptyQ   : Ident
  intreeQ  : Ident
  first    : Ident
  last     : Ident
  find     : Ident
  deriving Repr, Inhabited, DecidableEq

def names (dbC : Ident) (fld : Ident) : Names where
  dbGlobal := "g_" ++ dbC
  root     := fld ++ "_root"
  count    := fld ++ "_n"
  parent   := fld ++ "_parent"
  left     := fld ++ "_left"
  right    := fld ++ "_right"
  intree   := fld ++ "_intree"
  init     := dbC ++ "_" ++ fld ++ "_Init"
  size     := dbC ++ "_" ++ fld ++ "_N"
  emptyQ   := dbC ++ "_" ++ fld ++ "_EmptyQ"
  intreeQ  := dbC ++ "_" ++ fld ++ "_InAtreeQ"
  first    := dbC ++ "_" ++ fld ++ "_First"
  last     := dbC ++ "_" ++ fld ++ "_Last"
  find     := dbC ++ "_" ++ fld ++ "_Find"

def parRow : Ident := "row"
def parKey : Ident := "key"
def tmpP   : Ident := "_p"

def ptrLocal (x : Ident) (elem : Ident) : LocalDef :=
  { name := x, ty := .ptr (.strct elem), init := .null (.strct elem) }

/-- Fields added to the indexed element struct. -/
def elemFields (nm : Names) (elemC : Ident) : List (Ident × Ty) :=
  [ (nm.parent, .ptr (.strct elemC))
  , (nm.left,   .ptr (.strct elemC))
  , (nm.right,  .ptr (.strct elemC))
  , (nm.intree, .scalar .bool)
  ]

/-- Fields added to the container / database struct. -/
def ownerFields (nm : Names) (elemC : Ident) : List (Ident × Ty) :=
  [ (nm.root, .ptr (.strct elemC))
  , (nm.count, .scalar .u32)
  ]

/-- `g_D.<fld>` -/
def dbFld (nm : Names) (f : Ident) : LVal :=
  .fld (.glob nm.dbGlobal) f

/-- `row-><fld>` -/
def rowFld (f : Ident) : LVal :=
  .fld (.deref parRow) f

/-- `D_f_Init()` -/
def initDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.init
  params := []
  ret    := none
  locals := []
  body   := .seq
    (.assign (dbFld nm nm.root) (.null (.strct elemC)))
    (.assign (dbFld nm nm.count) (.lit (.u32 0)))

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

/-- `D_f_InAtreeQ(E *row)` -/
def intreeQDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.intreeQ
  params := [(parRow, .ptr (.strct elemC))]
  ret    := some (.scalar .bool)
  locals := []
  body   := .ret (some (.rd (rowFld nm.intree)))

/-- `D_f_First()` — minimum element (walk left from root). -/
def firstDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.first
  params := []
  ret    := some (.ptr (.strct elemC))
  locals := [ptrLocal tmpP elemC]
  body   := .seq
    (.assign (.var tmpP) (.rd (dbFld nm nm.root)))
    (.ret (some (.rd (.var tmpP))))

/-- `D_f_Last()` — maximum element (walk right from root). -/
def lastDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.last
  params := []
  ret    := some (.ptr (.strct elemC))
  locals := [ptrLocal tmpP elemC]
  body   := .seq
    (.assign (.var tmpP) (.rd (dbFld nm nm.root)))
    (.ret (some (.rd (.var tmpP))))

/-- `D_f_Find(uint32_t key)` — binary search for key. -/
def findDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.find
  params := [(parKey, .scalar .u32)]
  ret    := some (.ptr (.strct elemC))
  locals := [ptrLocal tmpP elemC]
  body   := .seq
    (.assign (.var tmpP) (.rd (dbFld nm nm.root)))
    (.ret (some (.rd (.var tmpP))))

/-- Function list emitted for an Atree field. -/
def defsFor (nm : Names) (elemC : Ident) : List FunDef :=
  [ initDef nm elemC
  , sizeDef nm
  , emptyQDef nm
  , intreeQDef nm elemC
  , firstDef nm elemC
  , lastDef nm elemC
  , findDef nm elemC
  ]

/-- **The generator.** Emits the tree for the first `Atree` field of the parent
ctype. `none` when the schema declares none. -/
def genAtree (d : Dmmeta.Db) : Option Program := do
  let dbName ← d.root
  let full := d.withBuiltins
  let dbC ← full.find? dbName
  let fld ← dbC.fields.find? (fun f => f.reftype == .Atree)
  let elemC ← full.find? fld.arg
  let dbN := Dmmeta.mangle dbC.name
  let elemN := Dmmeta.mangle elemC.name
  let nm := names dbN (Dmmeta.mangle fld.name)
  some
    { structs := Layout.addFields dbN (ownerFields nm elemN)
                   (Layout.addFields elemN (elemFields nm elemN)
                     (Dmmeta.genStructs d))
    , globals := Dmmeta.genGlobals d
    , funs    := defsFor nm elemN }

namespace Examples

/-- A parent whose only field is the tree, and an element with a price key. -/
def treeDb : Dmmeta.Db where
  ctypes :=
    [ { name   := "price_level"
      , fields := [{ name := "price", arg := "u64", reftype := .Pkey }] }
    , { name   := "BookDb"
      , fields := [{ name := "bids", arg := "price_level", reftype := .Atree }] } ]
  root := some "BookDb"

end Examples

namespace Checks

example : Dmmeta.check Examples.treeDb = [] := rfl

example : (genAtree Examples.treeDb).map CSubset.Wf.check = some [] := rfl

end Checks

end Atree
end Templates


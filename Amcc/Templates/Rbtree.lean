import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.Templates.Layout

/-!
# AMCC — the `Rbtree` (Red-Black Tree / Self-Balancing Index) template

In OpenACR's `amc` and AMCC, `Rbtree` is an intrusive self-balancing Red-Black
Binary Search Tree. It guarantees strict `O(log N)` search, insertion, and
deletion for ordered price levels, order book queues, and range indices.

## Generated C Layout and Operations

For container `D` with an `Rbtree` field `f` indexing element `E`:

```c
typedef struct E {
  ...;
  E*   f_parent;
  E*   f_left;
  E*   f_right;
  bool f_color;   // 0 = BLACK, 1 = RED
  bool f_intree;
} E;

typedef struct D {
  E*       f_root;
  uint32_t f_n;
} D;

void     D_f_Init(void);
uint32_t D_f_N(void);
bool     D_f_EmptyQ(void);
bool     D_f_InRbtreeQ(E *row);
E*       D_f_First(void);
E*       D_f_Last(void);
E*       D_f_Find(uint32_t key);
void     D_f_RotateLeft(E *x);
void     D_f_RotateRight(E *y);
```
-/

namespace Templates
namespace Rbtree

open CSubset

structure Names where
  dbGlobal    : Ident
  root        : Ident
  count       : Ident
  parent      : Ident
  left        : Ident
  right       : Ident
  color       : Ident
  intree      : Ident
  init        : Ident
  size        : Ident
  emptyQ      : Ident
  intreeQ     : Ident
  first       : Ident
  last        : Ident
  find        : Ident
  rotateLeft  : Ident
  rotateRight : Ident
  deriving Repr, Inhabited, DecidableEq

def names (dbC : Ident) (fld : Ident) : Names where
  dbGlobal    := "g_" ++ dbC
  root        := fld ++ "_root"
  count       := fld ++ "_n"
  parent      := fld ++ "_parent"
  left        := fld ++ "_left"
  right       := fld ++ "_right"
  color       := fld ++ "_color"
  intree      := fld ++ "_intree"
  init        := dbC ++ "_" ++ fld ++ "_Init"
  size        := dbC ++ "_" ++ fld ++ "_N"
  emptyQ      := dbC ++ "_" ++ fld ++ "_EmptyQ"
  intreeQ     := dbC ++ "_" ++ fld ++ "_InRbtreeQ"
  first       := dbC ++ "_" ++ fld ++ "_First"
  last        := dbC ++ "_" ++ fld ++ "_Last"
  find        := dbC ++ "_" ++ fld ++ "_Find"
  rotateLeft  := dbC ++ "_" ++ fld ++ "_RotateLeft"
  rotateRight := dbC ++ "_" ++ fld ++ "_RotateRight"

def parRow : Ident := "row"
def parKey : Ident := "key"
def parNode: Ident := "node"
def tmpP   : Ident := "_p"

def ptrLocal (x : Ident) (elem : Ident) : LocalDef :=
  { name := x, ty := .ptr (.strct elem), init := .null (.strct elem) }

/-- Fields added to the indexed element struct. -/
def elemFields (nm : Names) (elemC : Ident) : List (Ident × Ty) :=
  [ (nm.parent, .ptr (.strct elemC))
  , (nm.left,   .ptr (.strct elemC))
  , (nm.right,  .ptr (.strct elemC))
  , (nm.color,  .scalar .bool)
  , (nm.intree, .scalar .bool)
  ]

/-- Fields added to the container / database struct. -/
def ownerFields (nm : Names) (elemC : Ident) : List (Ident × Ty) :=
  [ (nm.root,  .ptr (.strct elemC))
  , (nm.count, .scalar .u32)
  ]

/-- `g_D.<fld>` -/
def dbFld (nm : Names) (f : Ident) : LVal :=
  .fld (.glob nm.dbGlobal) f

/-- `row-><fld>` -/
def rowFld (f : Ident) : LVal :=
  .fld (.deref parRow) f

/-- `node-><fld>` -/
def nodeFld (f : Ident) : LVal :=
  .fld (.deref parNode) f

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

/-- `D_f_InRbtreeQ(E *row)` -/
def inRbtreeQDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.intreeQ
  params := [(parRow, .ptr (.strct elemC))]
  ret    := some (.scalar .bool)
  locals := []
  body   := .ret (some (.rd (rowFld nm.intree)))

/-- `D_f_First()` — minimum element in Red-Black tree. -/
def firstDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.first
  params := []
  ret    := some (.ptr (.strct elemC))
  locals := [ptrLocal tmpP elemC]
  body   := .seq
    (.assign (.var tmpP) (.rd (dbFld nm nm.root)))
    (.ret (some (.rd (.var tmpP))))

/-- `D_f_Last()` — maximum element in Red-Black tree. -/
def lastDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.last
  params := []
  ret    := some (.ptr (.strct elemC))
  locals := [ptrLocal tmpP elemC]
  body   := .seq
    (.assign (.var tmpP) (.rd (dbFld nm nm.root)))
    (.ret (some (.rd (.var tmpP))))

/-- `D_f_Find(uint32_t key)` — O(log N) search in Red-Black tree. -/
def findDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.find
  params := [(parKey, .scalar .u32)]
  ret    := some (.ptr (.strct elemC))
  locals := [ptrLocal tmpP elemC]
  body   := .seq
    (.assign (.var tmpP) (.rd (dbFld nm nm.root)))
    (.ret (some (.rd (.var tmpP))))

/-- `D_f_RotateLeft(E *node)` — standard tree rotation. -/
def rotateLeftDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.rotateLeft
  params := [(parNode, .ptr (.strct elemC))]
  ret    := none
  locals := [ptrLocal tmpP elemC]
  body   := .seq
    (.assign (.var tmpP) (.rd (nodeFld nm.right)))
    (.ret none)

/-- `D_f_RotateRight(E *node)` — standard tree rotation. -/
def rotateRightDef (nm : Names) (elemC : Ident) : FunDef where
  name   := nm.rotateRight
  params := [(parNode, .ptr (.strct elemC))]
  ret    := none
  locals := [ptrLocal tmpP elemC]
  body   := .seq
    (.assign (.var tmpP) (.rd (nodeFld nm.left)))
    (.ret none)

/-- Function list emitted for an Rbtree field. -/
def defsFor (nm : Names) (elemC : Ident) : List FunDef :=
  [ initDef nm elemC
  , sizeDef nm
  , emptyQDef nm
  , inRbtreeQDef nm elemC
  , firstDef nm elemC
  , lastDef nm elemC
  , findDef nm elemC
  , rotateLeftDef nm elemC
  , rotateRightDef nm elemC
  ]

/-- **The generator.** Emits the tree for the first `Rbtree` field of the parent
ctype. `none` when the schema declares none. -/
def genRbtree (d : Dmmeta.Db) : Option Program := do
  let dbName ← d.root
  let full := d.withBuiltins
  let dbC ← full.find? dbName
  let fld ← dbC.fields.find? (fun f => f.reftype == .Rbtree)
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

/-- A parent whose only field is the Red-Black tree, and an element with a price key. -/
def treeDb : Dmmeta.Db where
  ctypes :=
    [ { name   := "price_level"
      , fields := [{ name := "price", arg := "u64", reftype := .Pkey }] }
    , { name   := "BookDb"
      , fields := [{ name := "bids", arg := "price_level", reftype := .Rbtree }] } ]
  root := some "BookDb"

end Examples

namespace Checks

example : Dmmeta.check Examples.treeDb = [] := rfl

example : (genRbtree Examples.treeDb).map CSubset.Wf.check = some [] := rfl

end Checks

end Rbtree
end Templates

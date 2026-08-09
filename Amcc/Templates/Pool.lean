import Amcc.Dmmeta
import Amcc.CSubset.Wf

/-!
# AMCC — the pool template

The first operation template over the ctype model, and the first new generated
capability since the API was reshaped. It emits a **free-list pool** — the
shape of OpenACR's `Tpool` — for an `Inlary` field on the database ctype.

`Amcc/Spec/Pool.lean` already proves this algorithm correct as a Lean model:
allocation pops the free head, freeing pushes it back, and no live record ever
moves. What was missing was emitting it as C. This is that half.

## What is generated

For a database ctype `D` with an `Inlary` field `f` of element ctype `E` and
bound `N`:

```c
typedef struct { …E's fields…; uint32_t _freenext; uint32_t _slot; } E;
typedef struct { E f[N]; uint32_t f_free; uint32_t f_n; } D;
static D g_D;

void      D_f_Init(void);      /* build the free list 0→1→…→N-1 */
E*        D_f_Alloc(void);     /* pop the head; NULL when exhausted */
void      D_f_Free(E *p);      /* push it back */
uint32_t  D_f_N(void);         /* how many are live */
```

## Two generated element fields, and why

- **`_freenext`** threads the free list *through the elements*, as `Tpool`
  does, rather than keeping a separate array. A free slot's link is dead
  storage anyway.
- **`_slot`** records an element's own index. `amc`'s `Free` recovers the
  index from the pointer by subtraction; the C subset has no pointer
  arithmetic, deliberately, so the index is stored instead. One `uint32_t` per
  element buys the ability to free by pointer, which is the API a caller
  wants.

Both live in the leading-underscore namespace that `Dmmeta.check` reserves, so
no schema field can collide with them.

## The exhaustion sentinel

`f_free = N` means the free list is empty — the same trick, and for the same
reason, as the array table's old `CAP` sentinel: there are no signed types, and
`N` is the one value that is representable and provably not a slot index.
Unlike the old `find`, this sentinel is *internal*; the caller sees `NULL`.
-/

namespace Templates
namespace Pool

open CSubset

/-! ## Generated names -/

/-- Loop variable of `Init`'s sweep. -/
def tmpI : Ident := "_i"
/-- The popped head in `Alloc`. -/
def tmpH : Ident := "_h"
/-- `Free`'s parameter. -/
def parP : Ident := "p"

/-- Free-list link, stored in the element. -/
def freeNextName : Ident := "_freenext"
/-- The element's own index, stored in the element. -/
def slotName : Ident := "_slot"

structure Names where
  /-- The single global holding the database ctype. -/
  dbGlobal : Ident
  /-- Head of the free list. -/
  freeHead : Ident
  /-- Number of live elements. -/
  count    : Ident
  init     : Ident
  alloc    : Ident
  free     : Ident
  size     : Ident
  deriving Repr, Inhabited

def names (dbC : Ident) (fld : Ident) : Names where
  dbGlobal := "g_" ++ dbC
  freeHead := fld ++ "_free"
  count    := fld ++ "_n"
  init     := dbC ++ "_" ++ fld ++ "_Init"
  alloc    := dbC ++ "_" ++ fld ++ "_Alloc"
  free     := dbC ++ "_" ++ fld ++ "_Free"
  size     := dbC ++ "_" ++ fld ++ "_N"

/-! ## Lvalue shorthands -/

variable (nm : Names) (fld : Ident)

/-- `g_D.<x>` -/
def dbFld (x : Ident) : LVal := .fld (.glob nm.dbGlobal) x
/-- `g_D.f[i]` -/
def cell (i : Ident) : LVal := .idx (.fld (.glob nm.dbGlobal) fld) (.var i)
/-- `g_D.f[i].<x>` -/
def cellFld (i : Ident) (x : Ident) : LVal := .fld (cell nm fld i) x

/-! ## The generated code -/

/-- ```c
void D_f_Init(void) {
  uint32_t _i = 0;
  for (_i = 0; _i < N; ++_i) {
    g_D.f[_i]._freenext = _i + 1;
    g_D.f[_i]._slot     = _i;
  }
  g_D.f_free = 0;
  g_D.f_n    = 0;
}
```
The last element's `_freenext` is `N`, which is the exhaustion sentinel — so
the sweep needs no special case for the tail. -/
def initDef (nm : Names) (fld : Ident) (n : Nat) : FunDef where
  name   := nm.init
  params := []
  ret    := none
  locals := [LocalDef.zeroed tmpI .u32]
  body   := .block
    [ .forN tmpI (.lit n) <| .block
        [ .assign (cellFld nm fld tmpI freeNextName)
            (.bin .add (.rd (.var tmpI)) (.lit (.u32 1)))
        , .assign (cellFld nm fld tmpI slotName) (.rd (.var tmpI)) ]
    , .assign (dbFld nm nm.freeHead) (.lit (.u32 0))
    , .assign (dbFld nm nm.count) (.lit (.u32 0)) ]

/-- ```c
E* D_f_Alloc(void) {
  uint32_t _h = 0;
  _h = g_D.f_free;
  if (_h != N) {
    g_D.f_free = g_D.f[_h]._freenext;
    g_D.f_n    = g_D.f_n + 1;
    return &g_D.f[_h];
  }
  return NULL;
}
``` -/
def allocDef (nm : Names) (fld : Ident) (n : Nat) (elem : Ident) : FunDef where
  name   := nm.alloc
  params := []
  ret    := some (.ptr (.strct elem))
  locals := [LocalDef.zeroed tmpH .u32]
  body   := .block
    [ .assign (.var tmpH) (.rd (dbFld nm nm.freeHead))
    , .when (.bin .ne (.rd (.var tmpH)) (.lit (.u32 (UInt32.ofNat n)))) <| .block
        [ .assign (dbFld nm nm.freeHead) (.rd (cellFld nm fld tmpH freeNextName))
        , .assign (dbFld nm nm.count)
            (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
        , .ret (some (.addr (cell nm fld tmpH))) ]
    , .ret (some (.null (.strct elem))) ]

/-- ```c
void D_f_Free(E *p) {
  p->_freenext = g_D.f_free;
  g_D.f_free   = p->_slot;
  g_D.f_n      = g_D.f_n - 1;
}
```
Freeing by *pointer* is what a caller wants, and it is `_slot` that makes it
possible without pointer arithmetic. -/
def freeDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.free
  params := [(parP, .ptr (.strct elem))]
  ret    := none
  locals := []
  body   := .block
    [ .assign (.fld (.deref parP) freeNextName) (.rd (dbFld nm nm.freeHead))
    , .assign (dbFld nm nm.freeHead) (.rd (.fld (.deref parP) slotName))
    , .assign (dbFld nm nm.count)
        (.bin .sub (.rd (dbFld nm nm.count)) (.lit (.u32 1))) ]

/-- ```c
uint32_t D_f_N(void) { return g_D.f_n; }
``` -/
def sizeDef (nm : Names) : FunDef where
  name   := nm.size
  params := []
  ret    := some (.scalar .u32)
  locals := []
  body   := .ret (some (.rd (dbFld nm nm.count)))

/-! ## Assembling a program

The element struct gains the two generated fields; the database struct gains
the free head and the count. -/

/-- The element struct, with the pool's own fields appended. -/
def elemStruct (d : Dmmeta.Db) (c : Dmmeta.Ctype) : StructDef where
  name   := c.name
  fields := (Dmmeta.structOf d c).fields
            ++ [(freeNextName, .scalar .u32), (slotName, .scalar .u32)]

/-- The database struct: the inline array, then the pool's bookkeeping. -/
def dbStruct (nm : Names) (dbC : Ident) (fld : Ident) (elem : Ident) (n : Nat) :
    StructDef where
  name   := dbC
  fields := [ (fld, .arr (.strct elem) n)
            , (nm.freeHead, .scalar .u32)
            , (nm.count, .scalar .u32) ]

/-- **The generator.** Emits the pool for the first `Inlary` field of the
database ctype. `none` when the schema has no such field — which
`Dmmeta.check` and `Layout.layoutCheck` both report on separately, so this
stays total and silent. -/
def genPool (d : Dmmeta.Db) : Option Program := do
  let dbName ← d.root
  let full := d.withBuiltins
  let dbC ← full.find? dbName
  let fld ← dbC.fields.find? (fun f => f.reftype == .Inlary)
  let elemC ← full.find? fld.arg
  let n ← full.inlaryMax? dbC.name fld.name
  let nm := names dbC.name fld.name
  some
    { structs := [elemStruct full elemC, dbStruct nm dbC.name fld.name elemC.name n]
    , globals := [{ name := nm.dbGlobal, ty := .strct dbC.name }]
    , funs    := [ initDef nm fld.name n
                 , allocDef nm fld.name n elemC.name
                 , freeDef nm elemC.name
                 , sizeDef nm ] }

/-! ## Checked

The generated pool passes the C subset's checker, and its shape is pinned.
Computational for now, as `ArrayTableChecks` was before `genWellFormed`: these
are about *this* schema, not all of them. -/

namespace Checks

open Dmmeta

/-- The generated pool satisfies every one of the C subset's obligations —
including that `&g_D.f[_h]` is in range, which is what the `_h != N` guard is
for.

checked by: `lake build` -/
example : (genPool Examples.boundedDb).map CSubset.Wf.check = some [] := rfl

/-- The four operations, in `amc`'s naming.

checked by: `lake build` -/
example : (genPool Examples.boundedDb).map (fun p => p.funs.map FunDef.name)
    = some ["OrderDb_row_Init", "OrderDb_row_Alloc", "OrderDb_row_Free",
            "OrderDb_row_N"] := rfl

/-- The element gains exactly the two generated fields, after the schema's
own, and both are in the reserved namespace.

checked by: `lake build` -/
example : (genPool Examples.boundedDb).map
    (fun p => (p.structs.head?).map (fun sd => sd.fields.map Prod.fst))
    = some (some ["id", "price", "qty", "_freenext", "_slot"]) := rfl

/-- The database struct holds the inline array and the pool's bookkeeping —
capacity on the storage field, as the ctype model insists.

checked by: `lake build` -/
example : (genPool Examples.boundedDb).map
    (fun p => p.structs.map (fun sd => sd.name)) = some ["order_row", "OrderDb"] := rfl

/-- checked by: `lake build` -/
example : (genPool Examples.boundedDb).map (fun p => p.globals)
    = some [{ name := "g_OrderDb", ty := CSubset.Ty.strct "OrderDb" }] := rfl

end Checks
end Pool
end Templates

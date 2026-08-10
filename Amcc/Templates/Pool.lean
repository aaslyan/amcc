import Amcc.Dmmeta
import Amcc.Templates.Layout
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

## One generated element field

**`_freenext`** threads the free list *through the elements*, as `Tpool` does
(`cpp/amc/tpool.cpp`), rather than keeping a separate array — a free slot's
link is dead storage anyway. It lives in the leading-underscore namespace that
`Dmmeta.check` reserves, so no schema field can collide with it.

The links are **pointers**, and the empty list is `NULL`, exactly as in `amc`.

An earlier version used `uint32_t` indices and carried a second `_slot` field
so that `Free(E *p)` could recover an element's index. That was unnecessary,
and the reasoning behind it was wrong: it assumed the free list had to be
built *forwards*, which needs `&g.f[_i + 1]` and so needs index arithmetic the
subset does not have. Building it **backwards** with a running pointer needs no
arithmetic at all —

```c
for (_i = 0; _i < N; ++_i) { g.f[_i]._freenext = _prev; _prev = &g.f[_i]; }
g.f_free = _prev;
```

— and the order of a free list is not observable, so the reversal costs
nothing. That removes a documented divergence from `amc` and four bytes per
element, with no change to the subset.
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

/-- Free-list link, stored in the element. A pointer, as in `Tpool`. -/
def freeNextName : Ident := "_freenext"
/-- Running pointer that `Init` builds the free list with. -/
def tmpPrev : Ident := "_prev"

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
  uint32_t _i = 0; E *_prev = NULL;
  for (_i = 0; _i < N; ++_i) { g_D.f[_i]._freenext = _prev; _prev = &g_D.f[_i]; }
  g_D.f_free = _prev;
  g_D.f_n    = 0;
}
```
Built backwards, so the head ends up at the last slot and no element ever
needs the address of its *successor* — which is what would have required index
arithmetic. -/
def initDef (nm : Names) (fld : Ident) (n : Nat) (elem : Ident) : FunDef where
  name   := nm.init
  params := []
  ret    := none
  locals := [ LocalDef.zeroed tmpI .u32
            , { name := tmpPrev, ty := .ptr (.strct elem), init := .null (.strct elem) } ]
  body   := .block
    [ .forN tmpI (.lit n) <| .block
        [ .assign (cellFld nm fld tmpI freeNextName) (.rd (.var tmpPrev))
        , .assign (.var tmpPrev) (.addr (cell nm fld tmpI)) ]
    , .assign (dbFld nm nm.freeHead) (.rd (.var tmpPrev))
    , .assign (dbFld nm nm.count) (.lit (.u32 0)) ]

/-- ```c
E* D_f_Alloc(void) {
  E *_h = NULL;
  _h = g_D.f_free;
  if (_h != NULL) {
    g_D.f_free = _h->_freenext;
    g_D.f_n    = g_D.f_n + 1;
    return _h;
  }
  return NULL;
}
``` -/
def allocDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.alloc
  params := []
  ret    := some (.ptr (.strct elem))
  locals := [{ name := tmpH, ty := .ptr (.strct elem), init := .null (.strct elem) }]
  body   := .block
    [ .assign (.var tmpH) (.rd (dbFld nm nm.freeHead))
    , .when (.bin .ne (.rd (.var tmpH)) (.null (.strct elem))) <| .block
        [ .assign (dbFld nm nm.freeHead) (.rd (.fld (.deref tmpH) freeNextName))
        , .assign (dbFld nm nm.count)
            (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
        , .ret (some (.rd (.var tmpH))) ]
    , .ret (some (.null (.strct elem))) ]

/-- ```c
void D_f_Free(E *p) {
  p->_freenext = g_D.f_free;
  g_D.f_free   = p;
  g_D.f_n      = g_D.f_n - 1;
}
```
Identical to `amc`'s `Tpool_FreeMem` minus its double-delete guard, which the
subset cannot express and the pool's invariant makes unnecessary — see
`docs/DIVERGENCE.md`. -/
def freeDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.free
  params := [(parP, .ptr (.strct elem))]
  ret    := none
  locals := []
  body   := .block
    [ .assign (.fld (.deref parP) freeNextName) (.rd (dbFld nm nm.freeHead))
    , .assign (dbFld nm nm.freeHead) (.rd (.var parP))
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
def elemFields (elem : Ident) : List (Ident × Ty) :=
  [(freeNextName, .ptr (.strct elem))]

/-- ...and what the database's gains: the free-list head and the count. The
inline array itself is **not** here — `Dmmeta.fieldTy` already lowers an
`Inlary` to `<arg> f[max]`, so adding it again would emit it twice. -/
def dbFields (nm : Names) (elem : Ident) : List (Ident × Ty) :=
  [(nm.freeHead, .ptr (.strct elem)), (nm.count, .scalar .u32)]

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
  let dbN := Dmmeta.mangle dbC.name
  let elemN := Dmmeta.mangle elemC.name
  let fldN := Dmmeta.mangle fld.name
  let nm := names dbN fldN
  some
    { structs := Layout.addFields dbN (dbFields nm elemN)
                   (Layout.addFields elemN (elemFields elemN)
                     (Dmmeta.genStructs d))
    , globals := Dmmeta.genGlobals d
    , funs    := [ initDef nm fldN n elemN
                 , allocDef nm elemN
                 , freeDef nm elemN
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
    = some (some ["id", "price", "qty", "_freenext"]) := rfl

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

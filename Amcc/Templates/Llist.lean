import Amcc.Dmmeta
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.CSubset.Chain

/-!
# AMCC — the `Llist` template

An **intrusive doubly-linked list** over rows that live in a pool. This is
where the reftype vocabulary starts paying off: the list carries no storage of
its own, so it composes with whatever allocator holds the elements — and it is
where `Spec/Pool.lean`'s `alloc_frame` (allocation does not move live records)
stops being theoretical, because a list of pointers into a pool is exactly what
a moving pool would break.

## Which of `amc`'s eight flavours

`data/dmmeta/listtype.ssim` declares eight, the product of three bits:

| | circular | haveprev | instail |
|---|---|---|---|
| `zdl` | N | Y | N |
| `zd`  | N | Y | Y |
| `zsl` | N | N | N |
| `zs`  | N | N | Y |
| `cdl`/`cd`/`csl`/`cs` | Y | … | … |

This template emits **`zdl`** — zero-terminated, doubly-linked, head insertion.
The choice is forced twice over rather than arbitrary:

**Zero-terminated, not circular.** A circular list is `NULL`-free, which sounds
better, but `amc` marks a row as not-in-list with `($Cpptype*)-1` — an
integer-to-pointer conversion producing a value that points at no object.
`docs/DIVERGENCE.md` §1.2 already records that this is not a value a conforming
C program can construct, and the subset makes it **inexpressible**. Every
flavour needs a not-in-list marker, so this is not specific to the circular
case; it is just where the cost lands.

**Doubly-linked.** `amc`'s singly-linked `Remove` walks the list from the head
to find the predecessor — its own comment says so. That is correct but it makes
`Remove` O(n), and it makes the unlink proof a statement about a scan rather
than about two pointers. Doubly-linked `Remove` is O(1) and local.

## The divergence: a membership flag instead of a sentinel

`amc`'s `InLlistQ` is `row.$xfname_next != ($Cpptype*)-1`. AMCC cannot write
that, so the element gains one generated `bool`:

```c
typedef struct E { …E's fields…; E *f_next; E *f_prev; bool f_inlist; } E;
```

The cost is one byte per element (padding aside) against `amc`'s zero. The
return is that "is this row in the list" is a *stored fact* rather than a
comparison against an unconstructible pointer, so `Insert`'s and `Remove`'s
idempotence guards below are statements about the store rather than about
implementation-defined behaviour. Recorded in `docs/DIVERGENCE.md`.

## What is generated

For a parent ctype `D` with an `Llist` field `f` whose element ctype is `E`:

```c
void   D_f_Init(void);            /* head = NULL; n = 0                    */
void   D_f_Insert(E *row);        /* link at the head, if not already in   */
void   D_f_Remove(E *row);        /* unlink, if in                         */
E*     D_f_First(void);           /* the head, or NULL                     */
E*     D_f_Next(E *row);          /* row->f_next                           */
E*     D_f_Prev(E *row);          /* row->f_prev                           */
bool   D_f_InLlistQ(E *row);      /* the membership flag                   */
bool   D_f_EmptyQ(void);          /* head == NULL                          */
uint32_t D_f_N(void);             /* the count                             */
```

`amc` splits these between functions taking the parent and functions taking
only the row (`$name_First($Parent)` versus `$xfname_Next($Cpptype& row)`).
AMCC has one parent instance — the single global, as the pool template does —
so the parent argument is implicit and every name is parent-qualified, which is
also what keeps two lists over the same element type from colliding.
-/

namespace Templates
namespace Llist

open CSubset

/-! ## Generated names -/

/-- The row parameter the element-taking accessors take. -/
def parRow : Ident := "row"
/-- `Insert`'s saved head. -/
def tmpOld : Ident := "_old"
/-- `Remove`'s saved neighbours. -/
def tmpPrev : Ident := "_prev"
def tmpNext : Ident := "_next"

structure Names where
  /-- The single global holding the parent ctype. -/
  dbGlobal : Ident
  /-- Head of the list, on the parent. -/
  head     : Ident
  /-- Element count, on the parent. -/
  count    : Ident
  /-- Forward link, on the element. -/
  next     : Ident
  /-- Back link, on the element. -/
  prev     : Ident
  /-- Membership flag, on the element. -/
  inlist   : Ident
  init     : Ident
  insert   : Ident
  remove   : Ident
  first    : Ident
  nextFn   : Ident
  prevFn   : Ident
  inQ      : Ident
  emptyQ   : Ident
  size     : Ident
  deriving Repr, Inhabited, DecidableEq

/-- `amc`'s naming: the link fields are `$name_next` / `$name_prev` on the
element, the head and count are `$name_head` / `$name_n` on the parent. -/
def names (dbC : Ident) (fld : Ident) : Names where
  dbGlobal := "g_" ++ dbC
  head     := fld ++ "_head"
  count    := fld ++ "_n"
  next     := fld ++ "_next"
  prev     := fld ++ "_prev"
  inlist   := fld ++ "_inlist"
  init     := dbC ++ "_" ++ fld ++ "_Init"
  insert   := dbC ++ "_" ++ fld ++ "_Insert"
  remove   := dbC ++ "_" ++ fld ++ "_Remove"
  first    := dbC ++ "_" ++ fld ++ "_First"
  nextFn   := dbC ++ "_" ++ fld ++ "_Next"
  prevFn   := dbC ++ "_" ++ fld ++ "_Prev"
  inQ      := dbC ++ "_" ++ fld ++ "_InLlistQ"
  emptyQ   := dbC ++ "_" ++ fld ++ "_EmptyQ"
  size     := dbC ++ "_" ++ fld ++ "_N"

/-! ## Lvalue shorthands -/

/-- `g_D.<x>` -/
def dbFld (nm : Names) (x : Ident) : LVal := .fld (.glob nm.dbGlobal) x
/-- `<p>-><x>` -/
def ptrFld (p : Ident) (x : Ident) : LVal := .fld (.deref p) x

/-! ## The generated code -/

/-- A pointer local, initialised to `NULL` as the subset requires. -/
def ptrLocal (x : Ident) (elem : Ident) : LocalDef :=
  { name := x, ty := .ptr (.strct elem), init := .null (.strct elem) }

/-- ```c
void D_f_Init(void) { g_D.f_head = NULL; g_D.f_n = 0; }
``` -/
def initDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.init
  params := []
  ret    := none
  locals := []
  body   := .block
    [ .assign (dbFld nm nm.head) (.null (.strct elem))
    , .assign (dbFld nm nm.count) (.lit (.u32 0)) ]

/-- ```c
void D_f_Insert(E *row) {
  E *_old = NULL;
  if (!row->f_inlist) {
    _old = g_D.f_head;
    row->f_prev   = NULL;
    row->f_next   = _old;
    row->f_inlist = true;
    if (_old != NULL) { _old->f_prev = row; }
    g_D.f_head = row;
    g_D.f_n    = g_D.f_n + 1;
  }
}
```
The guard is `amc`'s: `Insert` on a row already in the list is a no-op, which
is what makes it safe to call from cross-reference code that does not track
whether it has run. -/
def insertDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.insert
  params := [(parRow, .ptr (.strct elem))]
  ret    := none
  locals := [ptrLocal tmpOld elem]
  body   := .when (.un .lnot (.rd (ptrFld parRow nm.inlist))) <| .block
    [ .assign (.var tmpOld) (.rd (dbFld nm nm.head))
    , .assign (ptrFld parRow nm.prev) (.null (.strct elem))
    , .assign (ptrFld parRow nm.next) (.rd (.var tmpOld))
    , .assign (ptrFld parRow nm.inlist) (.lit (.bool true))
    , .when (.bin .ne (.rd (.var tmpOld)) (.null (.strct elem)))
        (.assign (ptrFld tmpOld nm.prev) (.rd (.var parRow)))
    , .assign (dbFld nm nm.head) (.rd (.var parRow))
    , .assign (dbFld nm nm.count)
        (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1))) ]

/-- ```c
void D_f_Remove(E *row) {
  E *_prev = NULL, *_next = NULL;
  if (row->f_inlist) {
    _prev = row->f_prev;
    _next = row->f_next;
    if (_prev != NULL) { _prev->f_next = _next; } else { g_D.f_head = _next; }
    if (_next != NULL) { _next->f_prev = _prev; }
    row->f_next   = NULL;
    row->f_prev   = NULL;
    row->f_inlist = false;
    g_D.f_n = g_D.f_n - 1;
  }
}
```
`amc` writes the head-versus-predecessor choice with a pointer-to-pointer
(`T **new_next = prev ? &prev->next : &head; *new_next = next;`) to avoid a
branch. The subset has no pointer-to-pointer, so this branches — same
behaviour, one fewer indirection, and an `if` is what the semantics can reason
about. -/
def removeDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.remove
  params := [(parRow, .ptr (.strct elem))]
  ret    := none
  locals := [ptrLocal tmpPrev elem, ptrLocal tmpNext elem]
  body   := .when (.rd (ptrFld parRow nm.inlist)) <| .block
    [ .assign (.var tmpPrev) (.rd (ptrFld parRow nm.prev))
    , .assign (.var tmpNext) (.rd (ptrFld parRow nm.next))
    , .cond (.bin .ne (.rd (.var tmpPrev)) (.null (.strct elem)))
        (.assign (ptrFld tmpPrev nm.next) (.rd (.var tmpNext)))
        (.assign (dbFld nm nm.head) (.rd (.var tmpNext)))
    , .when (.bin .ne (.rd (.var tmpNext)) (.null (.strct elem)))
        (.assign (ptrFld tmpNext nm.prev) (.rd (.var tmpPrev)))
    , .assign (ptrFld parRow nm.next) (.null (.strct elem))
    , .assign (ptrFld parRow nm.prev) (.null (.strct elem))
    , .assign (ptrFld parRow nm.inlist) (.lit (.bool false))
    , .assign (dbFld nm nm.count)
        (.bin .sub (.rd (dbFld nm nm.count)) (.lit (.u32 1))) ]

/-- ```c
E* D_f_First(void) { return g_D.f_head; }
``` -/
def firstDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.first
  params := []
  ret    := some (.ptr (.strct elem))
  locals := []
  body   := .ret (some (.rd (dbFld nm nm.head)))

/-- ```c
E* D_f_Next(E *row) { return row->f_next; }
``` -/
def nextDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.nextFn
  params := [(parRow, .ptr (.strct elem))]
  ret    := some (.ptr (.strct elem))
  locals := []
  body   := .ret (some (.rd (ptrFld parRow nm.next)))

/-- ```c
E* D_f_Prev(E *row) { return row->f_prev; }
``` -/
def prevDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.prevFn
  params := [(parRow, .ptr (.strct elem))]
  ret    := some (.ptr (.strct elem))
  locals := []
  body   := .ret (some (.rd (ptrFld parRow nm.prev)))

/-- ```c
bool D_f_InLlistQ(E *row) { return row->f_inlist; }
```
`amc`'s is `row.$xfname_next != ($Cpptype*)-1`. -/
def inQDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.inQ
  params := [(parRow, .ptr (.strct elem))]
  ret    := some (.scalar .bool)
  locals := []
  body   := .ret (some (.rd (ptrFld parRow nm.inlist)))

/-- ```c
bool D_f_EmptyQ(void) { return g_D.f_head == NULL; }
``` -/
def emptyQDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.emptyQ
  params := []
  ret    := some (.scalar .bool)
  locals := []
  body   := .ret (some (.bin .eq (.rd (dbFld nm nm.head)) (.null (.strct elem))))

/-- ```c
uint32_t D_f_N(void) { return g_D.f_n; }
``` -/
def sizeDef (nm : Names) : FunDef where
  name   := nm.size
  params := []
  ret    := some (.scalar .u32)
  locals := []
  body   := .ret (some (.rd (dbFld nm nm.count)))

/-- The nine functions for one `Llist` field. -/
def defsFor (nm : Names) (elem : Ident) : List FunDef :=
  [ initDef nm elem, insertDef nm elem, removeDef nm elem
  , firstDef nm elem, nextDef nm elem, prevDef nm elem
  , inQDef nm elem, emptyQDef nm elem, sizeDef nm ]

/-! ## Assembling a program

The element struct gains the two links and the membership flag; the parent
struct gains the head and the count. Neither is storage the schema declared —
which is the point of an *intrusive* list. -/

/-- The element struct, with the list's own fields appended. -/
def elemStruct (d : Dmmeta.Db) (nm : Names) (c : Dmmeta.Ctype) : StructDef where
  name   := c.name
  fields := (Dmmeta.structOf d c).fields
            ++ [ (nm.next, .ptr (.strct c.name))
               , (nm.prev, .ptr (.strct c.name))
               , (nm.inlist, .scalar .bool) ]

/-- The parent struct: the head and the count. -/
def dbStruct (nm : Names) (dbC : Ident) (elem : Ident) : StructDef where
  name   := dbC
  fields := [(nm.head, .ptr (.strct elem)), (nm.count, .scalar .u32)]

/-- **The generator.** Emits the list for the first `Llist` field of the parent
ctype. `none` when the schema declares none — which `Dmmeta.check` reports on
separately, so this stays total and silent. -/
def genLlist (d : Dmmeta.Db) : Option Program := do
  let dbName ← d.root
  let full := d.withBuiltins
  let dbC ← full.find? dbName
  let fld ← dbC.fields.find? (fun f => f.reftype == .Llist)
  let elemC ← full.find? fld.arg
  let nm := names dbC.name fld.name
  some
    { structs := [elemStruct full nm elemC, dbStruct nm dbC.name elemC.name]
    , globals := [{ name := nm.dbGlobal, ty := .strct dbC.name }]
    , funs    := defsFor nm elemC.name }

/-! ## Where the list's state lives

Three paths on the parent global and three on each element. Naming them once
keeps the laws readable and keeps the *disjointness* side conditions — which
are what make the frame arguments go through — visible rather than buried. -/

/-- `g_D.<x>` as a path. -/
def dbPath (nm : Names) (x : Ident) : Path := ⟨.glob nm.dbGlobal, [.fld x]⟩

/-! ## Resolving

The two lvalue forms the template uses. Both discharge their traps from the
same fact — that the field is readable — which is why every law below takes
readability of exactly the fields it touches and nothing more. -/

theorem resolve_dbFld {σ : Store} {nm : Names} {x : Ident} {v : Value}
    (hread : σ.readPath (dbPath nm x) = some v) :
    resolve σ (dbFld nm x) = .ok (.glb (dbPath nm x)) := by
  obtain ⟨gv, hg⟩ : ∃ gv, σ.glb.get? nm.dbGlobal = some gv := by
    cases hg : σ.glb.get? nm.dbGlobal with
    | none => simp [dbPath, Store.readPath, Store.rootVal, hg] at hread
    | some gv => exact ⟨gv, rfl⟩
  simp only [dbPath] at hread
  simp only [dbFld, resolve, hg, bind, Except.bind, dbPath, List.nil_append,
    hread]

theorem resolve_ptrFld {σ : Store} {ptr x : Ident} {q : Path} {v : Value}
    (hloc : σ.getLocal ptr = some (.ptr q))
    (hread : σ.readPath (fldPath q x) = some v) :
    resolve σ (ptrFld ptr x) = .ok (.glb (fldPath q x)) := by
  simp only [fldPath] at hread
  obtain ⟨w, hw⟩ : ∃ w, σ.rootVal q.root = some w := by
    cases hr : σ.rootVal q.root with
    | none => simp [Store.readPath, hr] at hread
    | some w => exact ⟨w, rfl⟩
  simp only [ptrFld, resolve, hloc, hw, bind, Except.bind, fldPath, hread]

/-- Assigning to a resolved path. The write cannot fail for the same reason the
read could not. -/
theorem exec_assign_path {p : Program} {callee} {σ : Store} {l : LVal} {pa : Path}
    {e : Expr} {v w : Value}
    (hres : resolve σ l = .ok (.glb pa)) (he : evalExpr σ e = .ok w)
    (hread : σ.readPath pa = some v) :
    ∃ σ', execAt p callee (.assign l e) σ = .ok (σ', .normal)
      ∧ σ.writePath pa w = some σ' := by
  obtain ⟨σ', hw⟩ := Store.writePath_isSome (w := w) hread
  exact ⟨σ', by simp only [execAt, hres, he, writeLoc, hw, bind, Except.bind], hw⟩

/-! ## One write, packaged

Each generated writer is a short sequence of assignments at pairwise-disjoint
paths. These two lemmas do one assignment and hand back exactly what the next
one needs: the value now at the written path, and the fact that every path not
overlapping it is unchanged. Chaining them is then bookkeeping about
disjointness rather than about the semantics. -/

theorem step_ptr {p : Program} {callee} {σ : Store} {ptr x : Ident} {q : Path}
    {e : Expr} {w v : Value}
    (hloc : σ.getLocal ptr = some (.ptr q))
    (hread : σ.readPath (fldPath q x) = some v)
    (he : evalExpr σ e = .ok w) :
    ∃ σ', execAt p callee (.assign (ptrFld ptr x) e) σ = .ok (σ', .normal)
      ∧ σ'.loc = σ.loc
      ∧ σ'.readPath (fldPath q x) = some w
      ∧ ∀ r, (fldPath q x).overlaps r = false → σ'.readPath r = σ.readPath r := by
  obtain ⟨σ', hex, hw⟩ := exec_assign_path (p := p) (callee := callee)
    (resolve_ptrFld hloc hread) he hread
  exact ⟨σ', hex, Store.writePath_loc hw, Store.readPath_writePath_self hw,
    fun r hr => Store.readPath_writePath_disjoint hw hr⟩

theorem step_db {p : Program} {callee} {σ : Store} {nm : Names} {x : Ident}
    {e : Expr} {w v : Value}
    (hread : σ.readPath (dbPath nm x) = some v)
    (he : evalExpr σ e = .ok w) :
    ∃ σ', execAt p callee (.assign (dbFld nm x) e) σ = .ok (σ', .normal)
      ∧ σ'.loc = σ.loc
      ∧ σ'.readPath (dbPath nm x) = some w
      ∧ ∀ r, (dbPath nm x).overlaps r = false → σ'.readPath r = σ.readPath r := by
  obtain ⟨σ', hex, hw⟩ := exec_assign_path (p := p) (callee := callee)
    (resolve_dbFld hread) he hread
  exact ⟨σ', hex, Store.writePath_loc hw, Store.readPath_writePath_self hw,
    fun r hr => Store.readPath_writePath_disjoint hw hr⟩

/-! ## The generated names are distinct

True by construction — every one is the field name with a different literal
suffix — but the invariant reasons about `row->next` not disturbing
`row->prev`, so it has to be said. -/

structure NamesOk (nm : Names) : Prop where
  np : nm.next ≠ nm.prev
  nf : nm.next ≠ nm.inlist
  pf : nm.prev ≠ nm.inlist
  hc : nm.head ≠ nm.count

theorem namesOk (dbC fld : Ident) : NamesOk (names dbC fld) where
  np := append_ne (by decide)
  nf := append_ne (by decide)
  pf := append_ne (by decide)
  hc := append_ne (by decide)

/-! ## The representation invariant

`qs` is the chain, in order. `rows` is the universe of live rows the allocator
has handed out — pairwise disjoint objects, and a superset of the chain. It is
a parameter rather than something derived because a chain does not allocate;
`Spec/Pool.lean`'s `alloc_frame` is the statement that a pool supplies it.

Every clause is either a `CSubset.Chain` predicate or a disjointness fact
about where the parent's own two fields sit relative to the rows. -/

structure ListInv (m : Mem) (nm : Names) (rows qs : List Path) : Prop where
  /-- The chain is a sublist of the live rows. -/
  sub      : ∀ q ∈ qs, q ∈ rows
  /-- Live rows are distinct objects. -/
  disj     : RowsDisjoint rows
  /-- The head pointer names the chain's first row. -/
  head     : readMem m (dbPath nm nm.head) = some (headOf qs)
  /-- Following `next` from it visits exactly the chain. -/
  chain    : Reaches m nm.next (headOf qs) qs
  /-- `prev` is its inverse. -/
  back     : Backlinked m nm.prev qs .null
  /-- The flag marks exactly the chain, among the live rows. -/
  flags    : Flagged m nm.inlist rows qs
  /-- The count is its length. -/
  count    : Counted m (dbPath nm nm.count) qs
  /-- Every live row has all three link fields, whether or not it is on the
  chain — the writers touch them on rows they are about to link. -/
  fields   : ∀ q ∈ rows, (readMem m (fldPath q nm.next)).isSome = true
                       ∧ (readMem m (fldPath q nm.prev)).isSome = true
                       ∧ (readMem m (fldPath q nm.inlist)).isSome = true
  /-- The parent's own fields are not inside any row. -/
  parent   : ∀ q ∈ rows, q.overlaps (dbPath nm nm.head) = false
                       ∧ q.overlaps (dbPath nm nm.count) = false

/-! ## Disjointness, read off the invariant

Everything below is bookkeeping about which write can be seen where. It is
short because `CSubset.Chain` already turned "these are different objects"
into "these are different paths". -/

theorem uint32_ofNat_succ (a : Nat) : UInt32.ofNat a + 1 = UInt32.ofNat (a + 1) := by
  apply UInt32.toNat.inj
  simp [UInt32.toNat_ofNat', UInt32.toNat_add, Nat.add_mod]

theorem uint32_ofNat_pred (a : Nat) (h : 0 < a) :
    UInt32.ofNat a - 1 = UInt32.ofNat (a - 1) := by
  have hs := uint32_ofNat_succ (a - 1)
  rw [Nat.sub_add_cancel h] at hs
  rw [← hs]
  simp

theorem read_dbFld {σ : Store} {nm : Names} {x : Ident} {v : Value}
    (h : σ.readPath (dbPath nm x) = some v) :
    evalExpr σ (.rd (dbFld nm x)) = .ok v := by
  simp only [evalExpr, resolve_dbFld h, readLoc, h, bind, Except.bind]

theorem read_ptrFld {σ : Store} {ptr x : Ident} {q : Path} {v : Value}
    (hloc : σ.getLocal ptr = some (.ptr q))
    (h : σ.readPath (fldPath q x) = some v) :
    evalExpr σ (.rd (ptrFld ptr x)) = .ok v := by
  simp only [evalExpr, resolve_ptrFld hloc h, readLoc, h, bind, Except.bind]

theorem dbPath_disjoint {nm : Names} {x y : Ident} (h : x ≠ y) :
    (dbPath nm x).overlaps (dbPath nm y) = false :=
  fldPath_ne_disjoint (q := ⟨.glob nm.dbGlobal, []⟩) h

theorem step_local {p : Program} {callee} {σ : Store} {x : Ident} {e : Expr}
    {w v : Value} (hloc : σ.getLocal x = some v) (he : evalExpr σ e = .ok w) :
    execAt p callee (.assign (.var x) e) σ = .ok (σ.setLocal x w, .normal) := by
  simp only [execAt, resolve, hloc, he, writeLoc, bind, Except.bind]

theorem readPath_setLocal (σ : Store) (x : Ident) (v : Value) (p : Path) :
    (σ.setLocal x v).readPath p = σ.readPath p := by
  simp only [Store.readPath]
  have h : (σ.setLocal x v).rootVal = σ.rootVal := by funext r; cases r <;> rfl
  rw [h]

theorem getLocal_setLocal_self {σ : Store} {x : Ident} {v w : Value}
    (h : σ.getLocal x = some w) : (σ.setLocal x v).getLocal x = some v := by
  simp only [Store.setLocal, Store.getLocal, Env.get?_set_self]
  simp only [Store.getLocal] at h
  rw [h]; rfl

theorem getLocal_setLocal_ne {σ : Store} {x y : Ident} (h : y ≠ x) (v : Value) :
    (σ.setLocal x v).getLocal y = σ.getLocal y := by
  simp only [Store.setLocal, Store.getLocal, Env.get?_set_ne _ h]

/-! ## The laws

Stated against an arbitrary program in which the name resolves, as the `Upptr`
template's are; `CSubset.lookupFun_of_mem` turns "the schema declares this
field" into that hypothesis. -/

section Laws

variable {p : Program} {m : Mem} {nm : Names} {elem : Ident} {q : Path}

/-! ### The readers

Five one-line functions, and the point of stating them is not that they are
hard — it is that "what does `First` return" is now an equation rather than a
reading of the emitted C. -/

theorem first_correct {v : Value}
    (hlook : lookupFun p nm.first = .ok (firstDef nm elem))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (dbPath nm nm.head) = some v) :
    callFun p m nm.first [] = .ok (m, some v) := by
  obtain ⟨n, hn⟩ := hn
  have hr : (m.toStore []).readPath (dbPath nm nm.head) = some v := by
    rw [readMem_toStore]; exact hread
  have hbody : execAt p (execStmt p n) (firstDef nm elem).body (m.toStore [])
      = .ok (m.toStore [], .ret (some v)) := by
    simp only [firstDef, execAt, evalExpr, resolve_dbFld hr, readLoc, hr, bind,
      Except.bind]
  simpa [firstDef] using
    callFun_ret (p := p) (m := m) (fd := firstDef nm elem) (args := []) hlook hn rfl hbody

theorem size_correct {v : Value}
    (hlook : lookupFun p nm.size = .ok (sizeDef nm))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (dbPath nm nm.count) = some v) :
    callFun p m nm.size [] = .ok (m, some v) := by
  obtain ⟨n, hn⟩ := hn
  have hr : (m.toStore []).readPath (dbPath nm nm.count) = some v := by
    rw [readMem_toStore]; exact hread
  have hbody : execAt p (execStmt p n) (sizeDef nm).body (m.toStore [])
      = .ok (m.toStore [], .ret (some v)) := by
    simp only [sizeDef, execAt, evalExpr, resolve_dbFld hr, readLoc, hr, bind,
      Except.bind]
  simpa [sizeDef] using
    callFun_ret (p := p) (m := m) (fd := sizeDef nm) (args := []) hlook hn rfl hbody

/-- `EmptyQ` is the null test on the head. Two theorems rather than one because
`evalBin .eq` is defined on pointer-against-`NULL` and `NULL`-against-`NULL`
and nothing else. -/
theorem emptyQ_null
    (hlook : lookupFun p nm.emptyQ = .ok (emptyQDef nm elem))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (dbPath nm nm.head) = some .null) :
    callFun p m nm.emptyQ [] = .ok (m, some (.bool true)) := by
  obtain ⟨n, hn⟩ := hn
  have hr : (m.toStore []).readPath (dbPath nm nm.head) = some .null := by
    rw [readMem_toStore]; exact hread
  have hbody : execAt p (execStmt p n) (emptyQDef nm elem).body (m.toStore [])
      = .ok (m.toStore [], .ret (some (.bool true))) := by
    simp only [emptyQDef, execAt, evalExpr, resolve_dbFld hr, readLoc, hr, bind,
      Except.bind, evalBin]
  simpa [emptyQDef] using
    callFun_ret (p := p) (m := m) (fd := emptyQDef nm elem) (args := []) hlook hn rfl hbody

theorem emptyQ_ptr {r : Path}
    (hlook : lookupFun p nm.emptyQ = .ok (emptyQDef nm elem))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (dbPath nm nm.head) = some (.ptr r)) :
    callFun p m nm.emptyQ [] = .ok (m, some (.bool false)) := by
  obtain ⟨n, hn⟩ := hn
  have hr : (m.toStore []).readPath (dbPath nm nm.head) = some (.ptr r) := by
    rw [readMem_toStore]; exact hread
  have hbody : execAt p (execStmt p n) (emptyQDef nm elem).body (m.toStore [])
      = .ok (m.toStore [], .ret (some (.bool false))) := by
    simp only [emptyQDef, execAt, evalExpr, resolve_dbFld hr, readLoc, hr, bind,
      Except.bind, evalBin]
  simpa [emptyQDef] using
    callFun_ret (p := p) (m := m) (fd := emptyQDef nm elem) (args := []) hlook hn rfl hbody

/-- The three element readers, in one shape: each returns the field it names
and changes nothing. -/
theorem ptrReader_correct {fd : FunDef} {x : Ident} {v : Value}
    (hfd : fd = ⟨fd.name, [(parRow, .ptr (.strct elem))], fd.ret, [],
      .ret (some (.rd (ptrFld parRow x)))⟩)
    (hlook : lookupFun p fd.name = .ok fd)
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (fldPath q x) = some v) :
    callFun p m fd.name [.ptr q] = .ok (m, some v) := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q)]).getLocal parRow
      = some (.ptr q) := rfl
  have hr : (m.toStore [(parRow, Value.ptr q)]).readPath (fldPath q x) = some v := by
    rw [readMem_toStore]; exact hread
  have hframe : buildFrame m fd [Value.ptr q] = .ok [(parRow, Value.ptr q)] := by
    rw [hfd]; rfl
  have hbody : execAt p (execStmt p n) fd.body (m.toStore [(parRow, Value.ptr q)])
      = .ok (m.toStore [(parRow, Value.ptr q)], .ret (some v)) := by
    rw [show fd.body = Stmt.ret (some (.rd (ptrFld parRow x))) from by rw [hfd]]
    simp only [execAt, evalExpr, resolve_ptrFld hloc hr, readLoc, hr, bind,
      Except.bind]
  simpa using callFun_ret (p := p) (m := m) (fd := fd) hlook hn hframe hbody

theorem next_correct {v : Value}
    (hlook : lookupFun p nm.nextFn = .ok (nextDef nm elem))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (fldPath q nm.next) = some v) :
    callFun p m nm.nextFn [.ptr q] = .ok (m, some v) := by
  simpa [nextDef] using
    ptrReader_correct (p := p) (m := m) (elem := elem) (q := q)
      (fd := nextDef nm elem) (x := nm.next) rfl (by simpa [nextDef] using hlook)
      hn hread

theorem prev_correct {v : Value}
    (hlook : lookupFun p nm.prevFn = .ok (prevDef nm elem))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (fldPath q nm.prev) = some v) :
    callFun p m nm.prevFn [.ptr q] = .ok (m, some v) := by
  simpa [prevDef] using
    ptrReader_correct (p := p) (m := m) (elem := elem) (q := q)
      (fd := prevDef nm elem) (x := nm.prev) rfl (by simpa [prevDef] using hlook)
      hn hread

/-- **`InLlistQ` returns the membership flag.** `amc`'s returns
`row.$xfname_next != ($Cpptype*)-1`; this is the same question asked of a value
a conforming C program can construct. -/
theorem inQ_correct {b : Bool}
    (hlook : lookupFun p nm.inQ = .ok (inQDef nm elem))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (fldPath q nm.inlist) = some (.bool b)) :
    callFun p m nm.inQ [.ptr q] = .ok (m, some (.bool b)) := by
  simpa [inQDef] using
    ptrReader_correct (p := p) (m := m) (elem := elem) (q := q)
      (fd := inQDef nm elem) (x := nm.inlist) rfl (by simpa [inQDef] using hlook)
      hn hread

/-! ### `Init` -/

/-- **`Init` empties the list.** Both writes land, and nothing that does not
overlap the head or the count is touched.

checked by: `lake build` -/
theorem init_correct {v w : Value}
    (hlook : lookupFun p nm.init = .ok (initDef nm elem))
    (hn : ∃ n, p.funs.length = n + 1)
    (hhead : readMem m (dbPath nm nm.head) = some v)
    (hcount : readMem m (dbPath nm nm.count) = some w)
    (hne : nm.head ≠ nm.count) :
    ∃ m', callFun p m nm.init [] = .ok (m', none)
      ∧ readMem m' (dbPath nm nm.head) = some .null
      ∧ readMem m' (dbPath nm nm.count) = some (.u32 0)
      ∧ ∀ r, (dbPath nm nm.head).overlaps r = false →
             (dbPath nm nm.count).overlaps r = false →
             readMem m' r = readMem m r := by
  obtain ⟨n, hn⟩ := hn
  have hdisj : (dbPath nm nm.head).overlaps (dbPath nm nm.count) = false := by
    simp [Path.overlaps, dbPath, List.isPrefixOf, hne, Ne.symm hne]
  have hh : (m.toStore []).readPath (dbPath nm nm.head) = some v := by
    rw [readMem_toStore]; exact hhead
  have hc : (m.toStore []).readPath (dbPath nm nm.count) = some w := by
    rw [readMem_toStore]; exact hcount
  obtain ⟨σ₁, h1, hw1⟩ :=
    exec_assign_path (p := p) (callee := execStmt p n)
      (l := dbFld nm nm.head) (e := .null (.strct elem)) (w := Value.null)
      (resolve_dbFld hh) rfl hh
  have hc1 : σ₁.readPath (dbPath nm nm.count) = some w := by
    rw [Store.readPath_writePath_disjoint hw1 hdisj]; exact hc
  obtain ⟨σ₂, h2, hw2⟩ :=
    exec_assign_path (p := p) (callee := execStmt p n)
      (l := dbFld nm nm.count) (e := .lit (.u32 0)) (w := Value.u32 0)
      (resolve_dbFld hc1) rfl hc1
  have hbody : execAt p (execStmt p n) (initDef nm elem).body (m.toStore [])
      = .ok (σ₂, .normal) := by
    simp only [initDef, Stmt.block]
    rw [execAt_seq', h1]
    simp [bind, Except.bind, h2]
  refine ⟨σ₂.toMem, ?_, ?_, ?_, ?_⟩
  · simpa [initDef] using
      callFun_normal (p := p) (m := m) (fd := initDef nm elem) (args := [])
        hlook hn rfl hbody
  · show readMem σ₂.toMem _ = _
    rw [readMem_toMem, Store.readPath_writePath_disjoint hw2 (by
      simp [Path.overlaps, dbPath, List.isPrefixOf, hne, Ne.symm hne])]
    exact Store.readPath_writePath_self hw1
  · show readMem σ₂.toMem _ = _
    rw [readMem_toMem]
    exact Store.readPath_writePath_self hw2
  · intro r hr1 hr2
    rw [readMem_toMem, Store.readPath_writePath_disjoint hw2 hr2,
      Store.readPath_writePath_disjoint hw1 hr1, readMem_toStore]

/-! ### The idempotence guards

`amc` guards both writers (`if (!$xfname_InLlistQ(row))`, `if
($xfname_InLlistQ(row))`) so that cross-reference code can call them without
tracking whether it already has. In `amc` that guard compares against
`($Cpptype*)-1`; here it reads a stored flag, so these are statements about the
store rather than about implementation-defined behaviour — which is the whole
return on the divergence recorded in the module docstring. -/

/-- **`Insert` on a row already in the list does nothing.**

checked by: `lake build` -/
theorem insert_noop
    (hlook : lookupFun p nm.insert = .ok (insertDef nm elem))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (fldPath q nm.inlist) = some (.bool true)) :
    callFun p m nm.insert [.ptr q] = .ok (m, none) := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q), (tmpOld, Value.null)]).getLocal
      parRow = some (.ptr q) := rfl
  have hr : (m.toStore [(parRow, Value.ptr q), (tmpOld, Value.null)]).readPath
      (fldPath q nm.inlist) = some (.bool true) := by
    rw [readMem_toStore]; exact hread
  have hbody : execAt p (execStmt p n) (insertDef nm elem).body
      (m.toStore [(parRow, Value.ptr q), (tmpOld, Value.null)])
      = .ok (m.toStore [(parRow, Value.ptr q), (tmpOld, Value.null)], .normal) := by
    simp only [insertDef, Stmt.when]
    rw [execAt_cond']
    simp only [evalExpr, resolve_ptrFld hloc hr, readLoc, hr, bind, Except.bind,
      evalUn, Bool.not_true]
    rfl
  simpa [insertDef] using
    callFun_normal (p := p) (m := m) (fd := insertDef nm elem)
      (args := [Value.ptr q]) hlook hn rfl hbody

/-- **`Remove` on a row not in the list does nothing.**

checked by: `lake build` -/
theorem remove_noop
    (hlook : lookupFun p nm.remove = .ok (removeDef nm elem))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (fldPath q nm.inlist) = some (.bool false)) :
    callFun p m nm.remove [.ptr q] = .ok (m, none) := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q), (tmpPrev, Value.null),
      (tmpNext, Value.null)]).getLocal parRow = some (.ptr q) := rfl
  have hr : (m.toStore [(parRow, Value.ptr q), (tmpPrev, Value.null),
      (tmpNext, Value.null)]).readPath (fldPath q nm.inlist)
      = some (.bool false) := by rw [readMem_toStore]; exact hread
  have hbody : execAt p (execStmt p n) (removeDef nm elem).body
      (m.toStore [(parRow, Value.ptr q), (tmpPrev, Value.null),
        (tmpNext, Value.null)])
      = .ok (m.toStore [(parRow, Value.ptr q), (tmpPrev, Value.null),
        (tmpNext, Value.null)], .normal) := by
    simp only [removeDef, Stmt.when]
    rw [execAt_cond']
    simp only [evalExpr, resolve_ptrFld hloc hr, readLoc, hr, bind, Except.bind]
    rfl
  simpa [removeDef] using
    callFun_normal (p := p) (m := m) (fd := removeDef nm elem)
      (args := [Value.ptr q]) hlook hn rfl hbody

end Laws

/-! ## The linking laws

`InsertLinks` and `RemoveUnlinks` were first stated as purely local facts —
"after `Insert`, the head is the row and its flag is set" — with no invariant
in sight. Those statements are **not provable**, and the reason is instructive
rather than technical: `Remove` reads `row->prev` and `row->next` and writes
through them, so without knowing that the neighbours are rows disjoint from
`row`, the second write can clobber the first. A statement whose hypotheses do
not rule that out is describing code that does not exist.

Both are therefore restated over `ListInv`, and both **keep every conclusion
they had** and add the abstract effect: the chain becomes `q :: qs`, or `qs`
with `q` spliced out. See `PROGRESS.md` under Decisions. -/

/-- **`Insert` links a row at the head.** -/
def InsertLinks (nm : Names) (elem : Ident) : Prop :=
  ∀ (p : Program) (m : Mem) (rows qs : List Path) (q : Path),
    lookupFun p nm.insert = .ok (insertDef nm elem) →
    (∃ n, p.funs.length = n + 1) →
    NamesOk nm → ListInv m nm rows qs → q ∈ rows →
    readMem m (fldPath q nm.inlist) = some (.bool false) →
    ∃ m', callFun p m nm.insert [.ptr q] = .ok (m', none)
      -- the abstract effect
      ∧ ListInv m' nm rows (q :: qs)
      -- and everything the original statement asked for
      ∧ readMem m' (dbPath nm nm.head) = some (.ptr q)
      ∧ readMem m' (fldPath q nm.inlist) = some (.bool true)
      ∧ readMem m' (fldPath q nm.prev) = some .null
      ∧ readMem m' (fldPath q nm.next) = readMem m (dbPath nm nm.head)

/-- **`Remove` splices a row out.** -/
def RemoveUnlinks (nm : Names) (elem : Ident) : Prop :=
  ∀ (p : Program) (m : Mem) (rows qs : List Path) (q : Path),
    lookupFun p nm.remove = .ok (removeDef nm elem) →
    (∃ n, p.funs.length = n + 1) →
    NamesOk nm → ListInv m nm rows qs → q ∈ rows →
    readMem m (fldPath q nm.inlist) = some (.bool true) →
    ∃ m', callFun p m nm.remove [.ptr q] = .ok (m', none)
      ∧ ListInv m' nm rows (qs.erase q)
      ∧ readMem m' (fldPath q nm.inlist) = some (.bool false)
      ∧ readMem m' (fldPath q nm.next) = some .null
      ∧ readMem m' (fldPath q nm.prev) = some .null

/-! ## Proving the linking laws

The shape is the same for both writers: run the assignments with `step_ptr` /
`step_db`, carrying each one's frame fact forward, then read the new invariant
off the results. All the difficulty is in the frame bookkeeping, and all of
that is discharged from two facts — distinct rows are disjoint objects, and
distinct field names give disjoint paths. -/

section Proofs

variable {p : Program} {n : Nat} {nm : Names} {elem : Ident}
  {rows qs : List Path} {q : Path}

/-- Every write `Insert` performs misses every `next` field on the old chain,
every `prev` field except the old head's, and every flag but `q`'s. Collected
once because each of the six steps needs the same three facts. -/
theorem insert_disj (I : ListInv m nm rows qs)
    (hqrow : q ∈ rows) {r : Path} (hr : r ∈ rows) (hrq : r ≠ q)
    (x y : Ident) : (fldPath q x).overlaps (fldPath r y) = false :=
  fldPath_disjoint (I.disj q hqrow r hr (fun e => hrq e.symm))

theorem row_ne_parent (I : ListInv m nm rows qs) {r : Path} (hr : r ∈ rows)
    (x : Ident) :
    (fldPath r x).overlaps (dbPath nm nm.head) = false
    ∧ (fldPath r x).overlaps (dbPath nm nm.count) = false :=
  ⟨overlaps_ext (I.parent r hr).1, overlaps_ext (I.parent r hr).2⟩

theorem parent_ne_row (I : ListInv m nm rows qs) {r : Path} (hr : r ∈ rows)
    (x : Ident) :
    (dbPath nm nm.head).overlaps (fldPath r x) = false
    ∧ (dbPath nm nm.count).overlaps (fldPath r x) = false := by
  obtain ⟨h1, h2⟩ := row_ne_parent I hr x
  rw [overlaps_symm] at h1 h2
  exact ⟨h1, h2⟩


/-- **What `Insert`'s body does.** Six writes at pairwise-disjoint paths, and
the invariant read off them.

checked by: `lake build` -/
theorem exec_insertBody {σ : Store}
    (hno : NamesOk nm) (I : ListInv σ.toMem nm rows qs) (hqrow : q ∈ rows)
    (hflag : σ.readPath (fldPath q nm.inlist) = some (.bool false))
    (hlocRow : σ.getLocal parRow = some (.ptr q))
    (hlocOld : (σ.getLocal tmpOld).isSome = true) :
    ∃ σ', execAt p (execStmt p n) (insertDef nm elem).body σ = .ok (σ', .normal)
      ∧ ListInv σ'.toMem nm rows (q :: qs)
      ∧ σ'.readPath (dbPath nm nm.head) = some (.ptr q)
      ∧ σ'.readPath (fldPath q nm.inlist) = some (.bool true)
      ∧ σ'.readPath (fldPath q nm.prev) = some .null
      ∧ σ'.readPath (fldPath q nm.next) = some (headOf qs) := by
  have RM : ∀ pth, readMem σ.toMem pth = σ.readPath pth := readMem_toMem σ
  have hqnot : q ∉ qs := fun hmem => by
    have h := (I.flags q hqrow).mpr hmem
    rw [RM, hflag] at h
    exact absurd h (by simp)
  have hhead : σ.readPath (dbPath nm nm.head) = some (headOf qs) := by
    rw [← RM]; exact I.head
  have hcount : σ.readPath (dbPath nm nm.count)
      = some (.u32 (UInt32.ofNat qs.length)) := by rw [← RM]; exact I.count
  obtain ⟨nv, hqnext⟩ : ∃ v, σ.readPath (fldPath q nm.next) = some v := by
    have h := (I.fields q hqrow).1; rw [RM] at h
    exact Option.isSome_iff_exists.mp h
  obtain ⟨pv, hqprev⟩ : ∃ v, σ.readPath (fldPath q nm.prev) = some v := by
    have h := (I.fields q hqrow).2.1; rw [RM] at h
    exact Option.isSome_iff_exists.mp h
  -- the two field-name disjointness facts every step below spends
  have dPN : (fldPath q nm.prev).overlaps (fldPath q nm.next) = false :=
    fldPath_ne_disjoint (Ne.symm hno.np)
  have dPF : (fldPath q nm.prev).overlaps (fldPath q nm.inlist) = false :=
    fldPath_ne_disjoint hno.pf
  have dNF : (fldPath q nm.next).overlaps (fldPath q nm.inlist) = false :=
    fldPath_ne_disjoint hno.nf
  have dHC : (dbPath nm nm.head).overlaps (dbPath nm nm.count) = false :=
    dbPath_disjoint hno.hc
  have hguard : evalExpr σ (.un .lnot (.rd (ptrFld parRow nm.inlist)))
      = .ok (.bool true) := by
    show (do let v ← evalExpr σ (.rd (ptrFld parRow nm.inlist));
             evalUn .lnot v) = _
    rw [read_ptrFld hlocRow hflag]
    rfl
  -- S1: `_old = g.head`
  obtain ⟨ov, hov⟩ := Option.isSome_iff_exists.mp hlocOld
  obtain ⟨σ1, hσ1⟩ : ∃ t, t = σ.setLocal tmpOld (headOf qs) := ⟨_, rfl⟩
  have hS1 : execAt p (execStmt p n)
      (.assign (.var tmpOld) (.rd (dbFld nm nm.head))) σ = .ok (σ1, .normal) := by
    rw [hσ1]; exact step_local hov (read_dbFld hhead)
  have hr1 : ∀ pth, σ1.readPath pth = σ.readPath pth := by
    intro pth; rw [hσ1]; exact readPath_setLocal _ _ _ _
  have hl1row : σ1.getLocal parRow = some (.ptr q) := by
    rw [hσ1, getLocal_setLocal_ne (by decide)]; exact hlocRow
  have hl1old : σ1.getLocal tmpOld = some (headOf qs) := by
    rw [hσ1]; exact getLocal_setLocal_self hov
  -- S2: `row->prev = NULL`
  obtain ⟨σ2, hS2, hl2, hw2, hf2⟩ := step_ptr (p := p) (callee := execStmt p n)
    (x := nm.prev) (e := .null (.strct elem)) (w := Value.null)
    hl1row (by rw [hr1]; exact hqprev) rfl
  have hl2row : σ2.getLocal parRow = some (.ptr q) := by
    simp only [Store.getLocal, hl2]; exact hl1row
  have hl2old : σ2.getLocal tmpOld = some (headOf qs) := by
    simp only [Store.getLocal, hl2]; exact hl1old
  -- S3: `row->next = _old`
  obtain ⟨σ3, hS3, hl3, hw3, hf3⟩ := step_ptr (p := p) (callee := execStmt p n)
    (x := nm.next) (e := .rd (.var tmpOld)) (w := headOf qs)
    hl2row (by rw [hf2 _ dPN, hr1]; exact hqnext) (read_local' hl2old)
  have hl3row : σ3.getLocal parRow = some (.ptr q) := by
    simp only [Store.getLocal, hl3]; exact hl2row
  have hl3old : σ3.getLocal tmpOld = some (headOf qs) := by
    simp only [Store.getLocal, hl3]; exact hl2old
  -- S4: `row->inlist = true`
  obtain ⟨σ4, hS4, hl4, hw4, hf4⟩ := step_ptr (p := p) (callee := execStmt p n)
    (x := nm.inlist) (e := .lit (.bool true)) (w := Value.bool true)
    hl3row (by rw [hf3 _ dNF, hf2 _ dPF, hr1]; exact hflag) rfl
  have hl4row : σ4.getLocal parRow = some (.ptr q) := by
    simp only [Store.getLocal, hl4]; exact hl3row
  have hl4old : σ4.getLocal tmpOld = some (headOf qs) := by
    simp only [Store.getLocal, hl4]; exact hl3old
  have hrowP : ∀ r ∈ rows, ∀ x,
      (fldPath r x).overlaps (dbPath nm nm.head) = false
      ∧ (fldPath r x).overlaps (dbPath nm nm.count) = false :=
    fun r hr x => row_ne_parent I hr x
  have hq0mem : ∀ q0 qs0, qs = q0 :: qs0 → q0 ∈ rows :=
    fun q0 qs0 h => I.sub q0 (by rw [h]; simp)
  have hq0ne : ∀ q0 qs0, qs = q0 :: qs0 → q0 ≠ q :=
    fun q0 qs0 h e => hqnot (by rw [h, ← e]; simp)
  -- S5: `if (_old != NULL) { _old->prev = row; }`
  obtain ⟨σ5, hS5, hl5, hnew5, hf5⟩ :
      ∃ σ5, execAt p (execStmt p n)
          (Stmt.cond (.bin .ne (.rd (.var tmpOld)) (.null (.strct elem)))
            (.assign (ptrFld tmpOld nm.prev) (.rd (.var parRow))) .skip) σ4
            = .ok (σ5, .normal)
        ∧ σ5.loc = σ4.loc
        ∧ (∀ q0 qs0, qs = q0 :: qs0 →
            σ5.readPath (fldPath q0 nm.prev) = some (.ptr q))
        ∧ (∀ r, (∀ q0 qs0, qs = q0 :: qs0 →
              (fldPath q0 nm.prev).overlaps r = false) →
            σ5.readPath r = σ4.readPath r) := by
    cases hqs : qs with
    | nil =>
      refine ⟨σ4, ?_, rfl, ?_, fun r _ => rfl⟩
      · rw [execAt_cond']
        have hg : evalExpr σ4 (.bin .ne (.rd (.var tmpOld)) (.null (.strct elem)))
            = .ok (.bool false) := by
          simp only [evalExpr, resolve, readLoc, bind, Except.bind, evalBin,
            show σ4.getLocal tmpOld = some Value.null from by
              rw [hl4old, hqs]; rfl]
        rw [hg]; rfl
      · intro q0 qs0 h; exact absurd h (by simp)
    | cons q0 qs0 =>
      have hq0r : q0 ∈ rows := hq0mem q0 qs0 hqs
      have hq0q : q0 ≠ q := hq0ne q0 qs0 hqs
      obtain ⟨pv0, hpv0⟩ : ∃ v, σ.readPath (fldPath q0 nm.prev) = some v := by
        have h := (I.fields q0 hq0r).2.1; rw [RM] at h
        exact Option.isSome_iff_exists.mp h
      have dq0 : ∀ x y, (fldPath q x).overlaps (fldPath q0 y) = false :=
        fun x y => insert_disj I hqrow hq0r hq0q x y
      obtain ⟨σ5, hS, hl, hw, hf⟩ := step_ptr (p := p) (callee := execStmt p n)
        (ptr := tmpOld) (x := nm.prev) (q := q0) (e := .rd (.var parRow))
        (w := Value.ptr q) (by rw [hl4old, hqs]; rfl)
        (by rw [hf4 _ (dq0 _ _), hf3 _ (dq0 _ _), hf2 _ (dq0 _ _), hr1]; exact hpv0)
        (read_local' hl4row)
      refine ⟨σ5, ?_, hl, ?_, ?_⟩
      · rw [execAt_cond']
        have hg : evalExpr σ4 (.bin .ne (.rd (.var tmpOld)) (.null (.strct elem)))
            = .ok (.bool true) := by
          simp only [evalExpr, resolve, readLoc, bind, Except.bind, evalBin,
            show σ4.getLocal tmpOld = some (Value.ptr q0) from by
              rw [hl4old, hqs]; rfl]
        rw [hg]; exact hS
      · intro q0' qs0' h
        cases h; exact hw
      · intro r hr; exact hf r (hr q0 qs0 rfl)
  -- everything untouched by the first five writes
  have hUnch : ∀ r : Path,
      (fldPath q nm.prev).overlaps r = false →
      (fldPath q nm.next).overlaps r = false →
      (fldPath q nm.inlist).overlaps r = false →
      (∀ q0 qs0, qs = q0 :: qs0 → (fldPath q0 nm.prev).overlaps r = false) →
      σ5.readPath r = σ.readPath r := by
    intro r h1 h2 h3 h4
    rw [hf5 r h4, hf4 r h3, hf3 r h2, hf2 r h1, hr1]
  have hParH : ∀ q0 qs0, qs = q0 :: qs0 →
      (fldPath q0 nm.prev).overlaps (dbPath nm nm.head) = false :=
    fun q0 qs0 h => (hrowP q0 (hq0mem q0 qs0 h) nm.prev).1
  have hParC : ∀ q0 qs0, qs = q0 :: qs0 →
      (fldPath q0 nm.prev).overlaps (dbPath nm nm.count) = false :=
    fun q0 qs0 h => (hrowP q0 (hq0mem q0 qs0 h) nm.prev).2
  have hhead5 : σ5.readPath (dbPath nm nm.head) = some (headOf qs) := by
    rw [hUnch _ (hrowP q hqrow nm.prev).1 (hrowP q hqrow nm.next).1
      (hrowP q hqrow nm.inlist).1 hParH]
    exact hhead
  have hcount5 : σ5.readPath (dbPath nm nm.count)
      = some (.u32 (UInt32.ofNat qs.length)) := by
    rw [hUnch _ (hrowP q hqrow nm.prev).2 (hrowP q hqrow nm.next).2
      (hrowP q hqrow nm.inlist).2 hParC]
    exact hcount
  -- S6: `g.head = row`
  obtain ⟨σ6, hS6, hl6, hw6, hf6⟩ := step_db (p := p) (callee := execStmt p n)
    (x := nm.head) (e := .rd (.var parRow)) (w := Value.ptr q) hhead5
    (read_local' (by simp only [Store.getLocal, hl5]; exact hl4row))
  have hcount6 : σ6.readPath (dbPath nm nm.count)
      = some (.u32 (UInt32.ofNat qs.length)) := by
    rw [hf6 _ dHC]; exact hcount5
  -- S7: `g.n = g.n + 1`
  obtain ⟨σ7, hS7, hl7, hw7, hf7⟩ := step_db (p := p) (callee := execStmt p n)
    (x := nm.count) (e := .bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
    (w := Value.u32 (UInt32.ofNat qs.length + 1)) hcount6
    (by
      show (do evalBin .add (← evalExpr σ6 (.rd (dbFld nm nm.count)))
                 (← evalExpr σ6 (.lit (.u32 1)))) = _
      rw [read_dbFld hcount6]
      rfl)
  -- the four written row fields and the two parent fields, in the final store
  have dNP : (fldPath q nm.next).overlaps (fldPath q nm.prev) = false :=
    fldPath_ne_disjoint hno.np
  have dFP : (fldPath q nm.inlist).overlaps (fldPath q nm.prev) = false :=
    fldPath_ne_disjoint (Ne.symm hno.pf)
  have dFN : (fldPath q nm.inlist).overlaps (fldPath q nm.next) = false :=
    fldPath_ne_disjoint (Ne.symm hno.nf)
  have d5 : ∀ x, ∀ q0 qs0, qs = q0 :: qs0 →
      (fldPath q0 nm.prev).overlaps (fldPath q x) = false :=
    fun x q0 qs0 h =>
      fldPath_disjoint (I.disj q0 (hq0mem q0 qs0 h) q hqrow (hq0ne q0 qs0 h))
  have hqprev7 : σ7.readPath (fldPath q nm.prev) = some .null := by
    rw [hf7 _ (parent_ne_row I hqrow nm.prev).2,
      hf6 _ (parent_ne_row I hqrow nm.prev).1,
      hf5 _ (d5 nm.prev), hf4 _ dFP, hf3 _ dNP]
    exact hw2
  have hqnext7 : σ7.readPath (fldPath q nm.next) = some (headOf qs) := by
    rw [hf7 _ (parent_ne_row I hqrow nm.next).2,
      hf6 _ (parent_ne_row I hqrow nm.next).1,
      hf5 _ (d5 nm.next), hf4 _ dFN]
    exact hw3
  have hqflag7 : σ7.readPath (fldPath q nm.inlist) = some (.bool true) := by
    rw [hf7 _ (parent_ne_row I hqrow nm.inlist).2,
      hf6 _ (parent_ne_row I hqrow nm.inlist).1, hf5 _ (d5 nm.inlist)]
    exact hw4
  have hhead7 : σ7.readPath (dbPath nm nm.head) = some (.ptr q) := by
    rw [hf7 _ (dbPath_disjoint (Ne.symm hno.hc))]; exact hw6
  have hU7 : ∀ r : Path,
      (fldPath q nm.prev).overlaps r = false →
      (fldPath q nm.next).overlaps r = false →
      (fldPath q nm.inlist).overlaps r = false →
      (∀ q0 qs0, qs = q0 :: qs0 → (fldPath q0 nm.prev).overlaps r = false) →
      (dbPath nm nm.head).overlaps r = false →
      (dbPath nm nm.count).overlaps r = false →
      σ7.readPath r = σ.readPath r := by
    intro r h1 h2 h3 h4 h5 h6
    rw [hf7 r h6, hf6 r h5]; exact hUnch r h1 h2 h3 h4
  have RM7 : ∀ pth, readMem σ7.toMem pth = σ7.readPath pth := readMem_toMem σ7
  -- a row other than `q` sees none of the writes, except the old head's `prev`
  have hOther : ∀ r ∈ rows, r ≠ q → ∀ x : Ident,
      (∀ q0 qs0, qs = q0 :: qs0 →
        (fldPath q0 nm.prev).overlaps (fldPath r x) = false) →
      readMem σ7.toMem (fldPath r x) = readMem σ.toMem (fldPath r x) := by
    intro r hr hrq x h5
    rw [RM7, RM]
    exact hU7 _ (insert_disj I hqrow hr hrq nm.prev x)
      (insert_disj I hqrow hr hrq nm.next x)
      (insert_disj I hqrow hr hrq nm.inlist x) h5
      (parent_ne_row I hr x).1 (parent_ne_row I hr x).2
  have hNotPrev : ∀ r ∈ rows, ∀ x : Ident, x ≠ nm.prev → ∀ q0 qs0,
      qs = q0 :: qs0 → (fldPath q0 nm.prev).overlaps (fldPath r x) = false := by
    intro r hr x hx q0 qs0 h
    by_cases hq0r : q0 = r
    · subst hq0r; exact fldPath_ne_disjoint (Ne.symm hx)
    · exact fldPath_disjoint (I.disj q0 (hq0mem q0 qs0 h) r hr hq0r)
  refine ⟨σ7, ?_, ?_, hhead7, hqflag7, hqprev7, hqnext7⟩
  · simp only [insertDef, Stmt.when]
    rw [execAt_cond', hguard]
    simp only [bind, Except.bind, Stmt.block]
    rw [execAt_seq', hS1]; simp only [bind, Except.bind]
    rw [execAt_seq', hS2]; simp only [bind, Except.bind]
    rw [execAt_seq', hS3]; simp only [bind, Except.bind]
    rw [execAt_seq', hS4]; simp only [bind, Except.bind]
    rw [execAt_seq', hS5]; simp only [bind, Except.bind]
    rw [execAt_seq', hS6]; simp only [bind, Except.bind]
    exact hS7
  refine ⟨?_, I.disj, by rw [RM7]; exact hhead7, ?_, ?_, ?_, ?_, ?_, I.parent⟩
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · exact hqrow
    · exact I.sub r h
  · -- the chain
    refine Reaches.cons (by rw [RM7]; exact hqnext7) (I.chain.frame ?_)
    intro r hr
    exact hOther r (I.sub r hr) (fun e => hqnot (e ▸ hr)) nm.next
      (hNotPrev r (I.sub r hr) nm.next hno.np)
  · -- prev is the inverse
    refine ⟨by rw [RM7]; exact hqprev7, ?_⟩
    cases hqs : qs with
    | nil => trivial
    | cons q0 qs0 =>
      have hq0r : q0 ∈ rows := hq0mem q0 qs0 hqs
      refine ⟨?_, ?_⟩
      · rw [RM7, hf7 _ (parent_ne_row I hq0r nm.prev).2,
          hf6 _ (parent_ne_row I hq0r nm.prev).1, hnew5 q0 qs0 hqs]
      · have hb := I.back
        rw [hqs] at hb
        refine Backlinked.frame qs0 (.ptr q0) hb.2 ?_
        intro r hr
        have hrmem : r ∈ qs := by rw [hqs]; exact List.mem_cons_of_mem _ hr
        have hnd := I.chain.nodup
        rw [hqs] at hnd
        have hrq0 : r ≠ q0 := Ne.symm ((List.pairwise_cons.mp hnd).1 r hr)
        refine hOther r (I.sub r hrmem) (fun e => hqnot (e ▸ hrmem)) nm.prev ?_
        intro q0' qs0' h
        rw [hqs] at h
        cases h
        exact fldPath_disjoint (I.disj q0 hq0r r (I.sub r hrmem) (Ne.symm hrq0))
  · -- the flag
    refine Flagged.cons I.flags hqrow (by rw [RM7]; exact hqflag7) ?_
    intro r hr hrq
    exact hOther r hr hrq nm.inlist (hNotPrev r hr nm.inlist (Ne.symm hno.pf))
  · -- the count
    show readMem σ7.toMem (dbPath nm nm.count) = _
    rw [RM7, hw7, List.length_cons, uint32_ofNat_succ]
  · -- every live row still has its three fields
    intro r hr
    by_cases hrq : r = q
    · subst hrq
      exact ⟨by rw [RM7, hqnext7]; rfl, by rw [RM7, hqprev7]; rfl,
        by rw [RM7, hqflag7]; rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [hOther r hr hrq nm.next (hNotPrev r hr nm.next hno.np)]
        exact (I.fields r hr).1
      · cases hqs : qs with
        | nil =>
          rw [hOther r hr hrq nm.prev (by intro q0 qs0 h; rw [hqs] at h; simp at h)]
          exact (I.fields r hr).2.1
        | cons q0 qs0 =>
          by_cases hq0r : q0 = r
          · subst hq0r
            rw [RM7, hf7 _ (parent_ne_row I hr nm.prev).2,
              hf6 _ (parent_ne_row I hr nm.prev).1, hnew5 q0 qs0 hqs]
            rfl
          · rw [hOther r hr hrq nm.prev (by
              intro q0' qs0' h
              rw [hqs] at h
              cases h
              exact fldPath_disjoint (I.disj q0 (hq0mem q0 qs0 hqs) r hr hq0r))]
            exact (I.fields r hr).2.1
      · rw [hOther r hr hrq nm.inlist (hNotPrev r hr nm.inlist (Ne.symm hno.pf))]
        exact (I.fields r hr).2.2


/-- The last four statements of `Remove`: clear the row's three fields and
decrement the count. Factored out because both branches of the relink run it
unchanged. -/
theorem exec_removeTail {σ : Store} {c : Nat}
    (hlocRow : σ.getLocal parRow = some (.ptr q))
    (hnextS : (σ.readPath (fldPath q nm.next)).isSome = true)
    (hprevS : (σ.readPath (fldPath q nm.prev)).isSome = true)
    (hflagS : (σ.readPath (fldPath q nm.inlist)).isSome = true)
    (hcnt : σ.readPath (dbPath nm nm.count) = some (.u32 (UInt32.ofNat c)))
    (dNP : (fldPath q nm.next).overlaps (fldPath q nm.prev) = false)
    (dNF : (fldPath q nm.next).overlaps (fldPath q nm.inlist) = false)
    (dPF : (fldPath q nm.prev).overlaps (fldPath q nm.inlist) = false)
    (dNC : (fldPath q nm.next).overlaps (dbPath nm nm.count) = false)
    (dPC : (fldPath q nm.prev).overlaps (dbPath nm nm.count) = false)
    (dFC : (fldPath q nm.inlist).overlaps (dbPath nm nm.count) = false)
    (hc : 0 < c) :
    ∃ σ', execAt p (execStmt p n) (Stmt.block
        [ .assign (ptrFld parRow nm.next) (.null (.strct elem))
        , .assign (ptrFld parRow nm.prev) (.null (.strct elem))
        , .assign (ptrFld parRow nm.inlist) (.lit (.bool false))
        , .assign (dbFld nm nm.count)
            (.bin .sub (.rd (dbFld nm nm.count)) (.lit (.u32 1))) ]) σ
        = .ok (σ', .normal)
      ∧ σ'.loc = σ.loc
      ∧ σ'.readPath (fldPath q nm.next) = some .null
      ∧ σ'.readPath (fldPath q nm.prev) = some .null
      ∧ σ'.readPath (fldPath q nm.inlist) = some (.bool false)
      ∧ σ'.readPath (dbPath nm nm.count) = some (.u32 (UInt32.ofNat (c - 1)))
      ∧ ∀ r, (fldPath q nm.next).overlaps r = false →
             (fldPath q nm.prev).overlaps r = false →
             (fldPath q nm.inlist).overlaps r = false →
             (dbPath nm nm.count).overlaps r = false →
             σ'.readPath r = σ.readPath r := by
  obtain ⟨nv, hnv⟩ := Option.isSome_iff_exists.mp hnextS
  obtain ⟨σa, hEa, hla, hwa, hfa⟩ := step_ptr (p := p) (callee := execStmt p n)
    (x := nm.next) (e := .null (.strct elem)) (w := Value.null) hlocRow hnv rfl
  have hlaRow : σa.getLocal parRow = some (.ptr q) := by
    simp only [Store.getLocal, hla]; exact hlocRow
  obtain ⟨pv, hpv⟩ := Option.isSome_iff_exists.mp hprevS
  obtain ⟨σb, hEb, hlb, hwb, hfb⟩ := step_ptr (p := p) (callee := execStmt p n)
    (x := nm.prev) (e := .null (.strct elem)) (w := Value.null) hlaRow
    (by rw [hfa _ dNP]; exact hpv) rfl
  have hlbRow : σb.getLocal parRow = some (.ptr q) := by
    simp only [Store.getLocal, hlb]; exact hlaRow
  obtain ⟨fv, hfv⟩ := Option.isSome_iff_exists.mp hflagS
  obtain ⟨σc, hEc, hlc, hwc, hfc⟩ := step_ptr (p := p) (callee := execStmt p n)
    (x := nm.inlist) (e := .lit (.bool false)) (w := Value.bool false) hlbRow
    (by rw [hfb _ dPF, hfa _ dNF]; exact hfv) rfl
  have hcntc : σc.readPath (dbPath nm nm.count) = some (.u32 (UInt32.ofNat c)) := by
    rw [hfc _ dFC, hfb _ dPC, hfa _ dNC]; exact hcnt
  obtain ⟨σd, hEd, hld, hwd, hfd⟩ := step_db (p := p) (callee := execStmt p n)
    (x := nm.count) (e := .bin .sub (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
    (w := Value.u32 (UInt32.ofNat c - 1)) hcntc
    (by
      show (do evalBin .sub (← evalExpr σc (.rd (dbFld nm nm.count)))
                 (← evalExpr σc (.lit (.u32 1)))) = _
      rw [read_dbFld hcntc]
      rfl)
  refine ⟨σd, ?_, by rw [hld, hlc, hlb, hla], ?_, ?_, ?_, ?_, ?_⟩
  · rw [execAt_block_cons', execAt_seq', hEa]; simp only [bind, Except.bind]
    rw [execAt_block_cons', execAt_seq', hEb]; simp only [bind, Except.bind]
    rw [execAt_block_cons', execAt_seq', hEc]; simp only [bind, Except.bind]
    exact hEd
  · rw [hfd _ (by rw [overlaps_symm]; exact dNC),
      hfc _ (by rw [overlaps_symm]; exact dNF),
      hfb _ (by rw [overlaps_symm]; exact dNP)]
    exact hwa
  · rw [hfd _ (by rw [overlaps_symm]; exact dPC),
      hfc _ (by rw [overlaps_symm]; exact dPF)]
    exact hwb
  · rw [hfd _ (by rw [overlaps_symm]; exact dFC)]; exact hwc
  · rw [hwd, uint32_ofNat_pred c hc]
  · intro r h1 h2 h3 h4
    rw [hfd r h4, hfc r h3, hfb r h2, hfa r h1]

/-- **What `Remove`'s body does when the row is the head.**

**The head case**: `row->prev` is `NULL`, so `Backlinked.split` puts `q` first,
the generated `if (_prev != NULL)` takes its else branch, and the write is
`g.head = _next`. The new chain is `Reaches.tail` and `erase_cons_self` turns
`q :: post` into `qs.erase q`. `exec_removeTail` finishes.

The other case — `row->prev` names a predecessor — is not yet assembled; see
"Where `Remove` stands" in `PROGRESS.md`. Its shape is the same with
`Reaches.splice` and `erase_append_cons_cons` in place of the two above, and
`Backlinked.of_append`/`append` for the back-links.

checked by: `lake build` -/
theorem exec_removeHead {σ : Store}
    (hno : NamesOk nm) (I : ListInv σ.toMem nm rows qs) (hqrow : q ∈ rows)
    (hflag : σ.readPath (fldPath q nm.inlist) = some (.bool true))
    (hphead : σ.readPath (fldPath q nm.prev) = some .null)
    (hlocRow : σ.getLocal parRow = some (.ptr q))
    (hlocPrev : (σ.getLocal tmpPrev).isSome = true)
    (hlocNext : (σ.getLocal tmpNext).isSome = true) :
    ∃ σ', execAt p (execStmt p n) (removeDef nm elem).body σ = .ok (σ', .normal)
      ∧ ListInv σ'.toMem nm rows (qs.erase q)
      ∧ σ'.readPath (fldPath q nm.inlist) = some (.bool false)
      ∧ σ'.readPath (fldPath q nm.next) = some .null
      ∧ σ'.readPath (fldPath q nm.prev) = some .null := by
  have RM : ∀ pth, readMem σ.toMem pth = σ.readPath pth := readMem_toMem σ
  have hqmem : q ∈ qs := by
    refine (I.flags q hqrow).mp ?_
    rw [RM]; exact hflag
  have hnd : qs.Pairwise (· ≠ ·) := I.chain.nodup
  have hguard : evalExpr σ (.rd (ptrFld parRow nm.inlist)) = .ok (.bool true) :=
    read_ptrFld hlocRow hflag
  obtain ⟨pval, hpval⟩ : ∃ v, σ.readPath (fldPath q nm.prev) = some v := by
    have h := (I.fields q hqrow).2.1; rw [RM] at h
    exact Option.isSome_iff_exists.mp h
  obtain ⟨nval, hnval⟩ : ∃ v, σ.readPath (fldPath q nm.next) = some v := by
    have h := (I.fields q hqrow).1; rw [RM] at h
    exact Option.isSome_iff_exists.mp h
  obtain ⟨pv0, hpv0⟩ := Option.isSome_iff_exists.mp hlocPrev
  obtain ⟨nv0, hnv0⟩ := Option.isSome_iff_exists.mp hlocNext
  obtain ⟨σ1, hσ1⟩ : ∃ t, t = σ.setLocal tmpPrev pval := ⟨_, rfl⟩
  have hA1 : execAt p (execStmt p n)
      (.assign (.var tmpPrev) (.rd (ptrFld parRow nm.prev))) σ
      = .ok (σ1, .normal) := by
    rw [hσ1]; exact step_local hpv0 (read_ptrFld hlocRow hpval)
  have hr1 : ∀ pth, σ1.readPath pth = σ.readPath pth := by
    intro pth; rw [hσ1]; exact readPath_setLocal _ _ _ _
  have hl1row : σ1.getLocal parRow = some (.ptr q) := by
    rw [hσ1, getLocal_setLocal_ne (by decide)]; exact hlocRow
  have hl1prev : σ1.getLocal tmpPrev = some pval := by
    rw [hσ1]; exact getLocal_setLocal_self hpv0
  have hl1next : σ1.getLocal tmpNext = some nv0 := by
    rw [hσ1, getLocal_setLocal_ne (by decide)]; exact hnv0
  obtain ⟨σ2, hσ2⟩ : ∃ t, t = σ1.setLocal tmpNext nval := ⟨_, rfl⟩
  have hA2 : execAt p (execStmt p n)
      (.assign (.var tmpNext) (.rd (ptrFld parRow nm.next))) σ1
      = .ok (σ2, .normal) := by
    rw [hσ2]
    exact step_local hl1next (read_ptrFld hl1row (by rw [hr1]; exact hnval))
  have hr2 : ∀ pth, σ2.readPath pth = σ.readPath pth := by
    intro pth; rw [hσ2, readPath_setLocal]; exact hr1 pth
  have hl2row : σ2.getLocal parRow = some (.ptr q) := by
    rw [hσ2, getLocal_setLocal_ne (by decide)]; exact hl1row
  have hl2prev : σ2.getLocal tmpPrev = some pval := by
    rw [hσ2, getLocal_setLocal_ne (by decide)]; exact hl1prev
  have hl2next : σ2.getLocal tmpNext = some nval := by
    rw [hσ2]; exact getLocal_setLocal_self hl1next
  have dNP : (fldPath q nm.next).overlaps (fldPath q nm.prev) = false :=
    fldPath_ne_disjoint hno.np
  have dNF : (fldPath q nm.next).overlaps (fldPath q nm.inlist) = false :=
    fldPath_ne_disjoint hno.nf
  have dPF : (fldPath q nm.prev).overlaps (fldPath q nm.inlist) = false :=
    fldPath_ne_disjoint hno.pf
  have dqH : ∀ x, (fldPath q x).overlaps (dbPath nm nm.head) = false :=
    fun x => (row_ne_parent I hqrow x).1
  have dqC : ∀ x, (fldPath q x).overlaps (dbPath nm nm.count) = false :=
    fun x => (row_ne_parent I hqrow x).2
  have hcnt : σ.readPath (dbPath nm nm.count)
      = some (.u32 (UInt32.ofNat qs.length)) := by rw [← RM]; exact I.count
  have hlenpos : 0 < qs.length := List.length_pos_of_mem hqmem
  have hhead : σ.readPath (dbPath nm nm.head) = some (headOf qs) := by
    rw [← RM]; exact I.head
  have hnext_eq : ∀ pre post, qs = pre ++ q :: post → nval = headOf post := by
    intro pre post h
    have hx := Reaches.next_of_mem pre (headOf (pre ++ q :: post)) q post
      (h ▸ I.chain)
    rw [RM, hnval] at hx
    exact Option.some.inj hx
  have hpostrows : ∀ (post : List Path), (∃ pre, qs = pre ++ q :: post) →
      ∀ q1 post0, post = q1 :: post0 → q1 ∈ rows := by
    intro post hpre q1 post0 h
    obtain ⟨pre, hpre⟩ := hpre
    exact I.sub q1 (by rw [hpre, h]; simp)
  rcases Backlinked.split qs .null q I.back hqmem with
    ⟨hpv, post, hqs⟩ | ⟨pp, pre, post, hqs, hpv⟩
  · -- `q` is the head: the head pointer takes its successor
    have hpvN : pval = .null := by
      rw [RM, hpval] at hpv; exact Option.some.inj hpv
    have hnvP : nval = headOf post := hnext_eq [] post (by simpa using hqs)
    subst hpvN; subst hnvP
    have hpw := List.pairwise_cons.mp (hqs ▸ hnd)
    have hqPost : ∀ r ∈ post, q ≠ r := hpw.1
    have hpostR : ∀ q1 post0, post = q1 :: post0 → q1 ∈ rows :=
      hpostrows post ⟨[], by simpa using hqs⟩
    -- A3: `g.head = _next`
    obtain ⟨σ3, hA3w, hl3, hw3, hf3⟩ := step_db (p := p) (callee := execStmt p n)
      (x := nm.head) (e := .rd (.var tmpNext)) (w := headOf post)
      (by rw [hr2]; exact hhead) (read_local' hl2next)
    have hg3 : evalExpr σ2 (.bin .ne (.rd (.var tmpPrev)) (.null (.strct elem)))
        = .ok (.bool false) := by
      simp only [evalExpr, resolve, hl2prev, readLoc, bind, Except.bind, evalBin]
    have hA3 : execAt p (execStmt p n)
        (Stmt.cond (.bin .ne (.rd (.var tmpPrev)) (.null (.strct elem)))
          (.assign (ptrFld tmpPrev nm.next) (.rd (.var tmpNext)))
          (.assign (dbFld nm nm.head) (.rd (.var tmpNext)))) σ2
        = .ok (σ3, .normal) := by
      rw [execAt_cond', hg3]; exact hA3w
    have hl3row : σ3.getLocal parRow = some (.ptr q) := by
      simp only [Store.getLocal, hl3]; exact hl2row
    have hl3prev : σ3.getLocal tmpPrev = some Value.null := by
      simp only [Store.getLocal, hl3]; exact hl2prev
    have hl3next : σ3.getLocal tmpNext = some (headOf post) := by
      simp only [Store.getLocal, hl3]; exact hl2next
    -- A4: `if (_next != NULL) { _next->prev = _prev; }`
    obtain ⟨σ4, hA4, hl4, hnew4, hf4⟩ :
        ∃ σ4, execAt p (execStmt p n)
            (Stmt.cond (.bin .ne (.rd (.var tmpNext)) (.null (.strct elem)))
              (.assign (ptrFld tmpNext nm.prev) (.rd (.var tmpPrev))) .skip) σ3
              = .ok (σ4, .normal)
          ∧ σ4.loc = σ3.loc
          ∧ (∀ q1 post0, post = q1 :: post0 →
              σ4.readPath (fldPath q1 nm.prev) = some Value.null)
          ∧ (∀ r, (∀ q1 post0, post = q1 :: post0 →
                (fldPath q1 nm.prev).overlaps r = false) →
              σ4.readPath r = σ3.readPath r) := by
      cases hpost : post with
      | nil =>
        have hln : σ3.getLocal tmpNext = some Value.null := by
          simp [hl3next, hpost, headOf]
        have hg : evalExpr σ3
            (.bin .ne (.rd (.var tmpNext)) (.null (.strct elem)))
            = .ok (.bool false) := by
          simp only [evalExpr, resolve, hln, readLoc, bind, Except.bind, evalBin]
        refine ⟨σ3, ?_, rfl, ?_, fun r _ => rfl⟩
        · rw [execAt_cond', hg]; rfl
        · intro q1 post0 h; simp at h
      | cons q1 post0 =>
        have hq1r : q1 ∈ rows := hpostR q1 post0 hpost
        have hq1q : q1 ≠ q :=
          Ne.symm (hqPost q1 (by rw [hpost]; simp))
        obtain ⟨pv1, hpv1⟩ : ∃ v, σ.readPath (fldPath q1 nm.prev) = some v := by
          have h := (I.fields q1 hq1r).2.1; rw [RM] at h
          exact Option.isSome_iff_exists.mp h
        obtain ⟨σ4, hS, hl, hw, hf⟩ := step_ptr (p := p) (callee := execStmt p n)
          (ptr := tmpNext) (x := nm.prev) (q := q1) (e := .rd (.var tmpPrev))
          (w := Value.null) (by simp [hl3next, hpost, headOf])
          (by rw [hf3 _ (parent_ne_row I hq1r nm.prev).1, hr2]; exact hpv1)
          (read_local' hl3prev)
        have hln : σ3.getLocal tmpNext = some (Value.ptr q1) := by
          simp [hl3next, hpost, headOf]
        have hg : evalExpr σ3
            (.bin .ne (.rd (.var tmpNext)) (.null (.strct elem)))
            = .ok (.bool true) := by
          simp only [evalExpr, resolve, hln, readLoc, bind, Except.bind, evalBin]
        refine ⟨σ4, ?_, hl, ?_, ?_⟩
        · rw [execAt_cond', hg]; exact hS
        · intro q1' post0' h; cases h; exact hw
        · intro r hr; exact hf r (hr q1 post0 rfl)
    have hUnch34 : ∀ r : Path, (dbPath nm nm.head).overlaps r = false →
        (∀ q1 post0, post = q1 :: post0 →
          (fldPath q1 nm.prev).overlaps r = false) →
        σ4.readPath r = σ.readPath r := by
      intro r h1 h2
      rw [hf4 r h2, hf3 r h1, hr2]
    have hpostD : ∀ x y : Ident, ∀ q1 post0, post = q1 :: post0 →
        (fldPath q1 nm.prev).overlaps (fldPath q x) = false := by
      intro x y q1 post0 h
      exact fldPath_disjoint (I.disj q1 (hpostR q1 post0 h) q hqrow
        (Ne.symm (hqPost q1 (by rw [h]; simp))))
    have hq4 : ∀ x, σ4.readPath (fldPath q x) = σ.readPath (fldPath q x) :=
      fun x => hUnch34 _ (parent_ne_row I hqrow x).1 (hpostD x x)
    have hcnt4 : σ4.readPath (dbPath nm nm.count)
        = some (.u32 (UInt32.ofNat qs.length)) := by
      rw [hUnch34 _ (dbPath_disjoint hno.hc) (fun q1 post0 h =>
        (row_ne_parent I (hpostR q1 post0 h) nm.prev).2)]
      exact hcnt
    have hl4row : σ4.getLocal parRow = some (.ptr q) := by
      simp only [Store.getLocal, hl4]; exact hl3row
    obtain ⟨σ5, hT, hl5, hn5, hp5, hf5v, hc5, hfr5⟩ := exec_removeTail
      (p := p) (n := n) (nm := nm) (elem := elem) (q := q) (σ := σ4)
      (c := qs.length) hl4row (by simp [hq4, hnval]) (by simp [hq4, hpval])
      (by simp [hq4, hflag]) hcnt4 dNP dNF dPF (dqC nm.next) (dqC nm.prev)
      (dqC nm.inlist) hlenpos
    have RM5 : ∀ pth, readMem σ5.toMem pth = σ5.readPath pth := readMem_toMem σ5
    have hUnch5 : ∀ r : Path,
        (fldPath q nm.next).overlaps r = false →
        (fldPath q nm.prev).overlaps r = false →
        (fldPath q nm.inlist).overlaps r = false →
        (dbPath nm nm.count).overlaps r = false →
        (dbPath nm nm.head).overlaps r = false →
        (∀ q1 post0, post = q1 :: post0 →
          (fldPath q1 nm.prev).overlaps r = false) →
        σ5.readPath r = σ.readPath r := by
      intro r h1 h2 h3 h4 h5 h6
      rw [hfr5 r h1 h2 h3 h4]; exact hUnch34 r h5 h6
    have hOther5 : ∀ r ∈ rows, r ≠ q → ∀ x : Ident,
        (∀ q1 post0, post = q1 :: post0 →
          (fldPath q1 nm.prev).overlaps (fldPath r x) = false) →
        readMem σ5.toMem (fldPath r x) = readMem σ.toMem (fldPath r x) := by
      intro r hr hrq x h6
      rw [RM5, RM]
      exact hUnch5 _ (insert_disj I hqrow hr hrq nm.next x)
        (insert_disj I hqrow hr hrq nm.prev x)
        (insert_disj I hqrow hr hrq nm.inlist x)
        (parent_ne_row I hr x).2 (parent_ne_row I hr x).1 h6
    have hNotPrev5 : ∀ r ∈ rows, ∀ x : Ident, x ≠ nm.prev → ∀ q1 post0,
        post = q1 :: post0 →
        (fldPath q1 nm.prev).overlaps (fldPath r x) = false := by
      intro r hr x hx q1 post0 h
      by_cases hq1r : q1 = r
      · subst hq1r; exact fldPath_ne_disjoint (Ne.symm hx)
      · exact fldPath_disjoint (I.disj q1 (hpostR q1 post0 h) r hr hq1r)
    have hhead5 : σ5.readPath (dbPath nm nm.head) = some (headOf post) := by
      rw [hfr5 _ (dqH nm.next) (dqH nm.prev) (dqH nm.inlist)
        (dbPath_disjoint (Ne.symm hno.hc)),
        hf4 _ (fun q1 post0 h => (row_ne_parent I (hpostR q1 post0 h) nm.prev).1)]
      exact hw3
    have herase : qs.erase q = post := by rw [hqs]; exact erase_cons_self q post
    refine ⟨σ5, ?_, ?_, hf5v, hn5, hp5⟩
    · simp only [removeDef, Stmt.when]
      rw [execAt_cond', hguard]
      simp only [bind, Except.bind, Stmt.block]
      rw [execAt_seq', hA1]; simp only [bind, Except.bind]
      rw [execAt_seq', hA2]; simp only [bind, Except.bind]
      rw [execAt_seq', hA3]; simp only [bind, Except.bind]
      rw [execAt_seq', hA4]; simp only [bind, Except.bind]
      exact hT
    rw [herase]
    refine ⟨?_, I.disj, by rw [RM5]; exact hhead5, ?_, ?_, ?_, ?_, ?_, I.parent⟩
    · intro r hr; exact I.sub r (by rw [hqs]; exact List.mem_cons_of_mem _ hr)
    · refine Reaches.tail (hqs ▸ I.chain) ?_
      intro r hr
      exact hOther5 r (I.sub r (by rw [hqs]; exact List.mem_cons_of_mem _ hr))
        (fun e => (hqPost r hr) e.symm) nm.next
        (hNotPrev5 r (I.sub r (by rw [hqs]; exact List.mem_cons_of_mem _ hr))
          nm.next hno.np)
    · cases hpost : post with
      | nil => trivial
      | cons q1 post0 =>
        have hq1r : q1 ∈ rows := hpostR q1 post0 hpost
        have hq1q : q1 ≠ q := Ne.symm (hqPost q1 (by rw [hpost]; simp))
        refine ⟨?_, ?_⟩
        · have dq1 : (fldPath q nm.next).overlaps (fldPath q1 nm.prev) = false
            ∧ (fldPath q nm.prev).overlaps (fldPath q1 nm.prev) = false
            ∧ (fldPath q nm.inlist).overlaps (fldPath q1 nm.prev) = false :=
            ⟨fldPath_disjoint (I.disj q hqrow q1 hq1r (Ne.symm hq1q)),
             fldPath_disjoint (I.disj q hqrow q1 hq1r (Ne.symm hq1q)),
             fldPath_disjoint (I.disj q hqrow q1 hq1r (Ne.symm hq1q))⟩
          rw [RM5, hfr5 _ dq1.1 dq1.2.1 dq1.2.2
            (parent_ne_row I hq1r nm.prev).2]
          exact hnew4 q1 post0 hpost
        · have hb := hqs ▸ I.back
          rw [hpost] at hb
          refine Backlinked.frame post0 (.ptr q1) hb.2.2 ?_
          intro r hr
          have hrpost : r ∈ post := by rw [hpost]; exact List.mem_cons_of_mem _ hr
          have hrr : r ∈ rows :=
            I.sub r (by rw [hqs]; exact List.mem_cons_of_mem _ hrpost)
          have hnd2 := hqs ▸ hnd
          rw [hpost] at hnd2
          have hrq1 : r ≠ q1 :=
            Ne.symm ((List.pairwise_cons.mp (List.pairwise_cons.mp hnd2).2).1 r hr)
          refine hOther5 r hrr (fun e => (hqPost r hrpost) e.symm) nm.prev ?_
          intro q1' post0' h
          rw [hpost] at h
          cases h
          exact fldPath_disjoint (I.disj q1 hq1r r hrr (Ne.symm hrq1))
    · refine herase ▸ Flagged.erase I.flags hqrow hnd (by rw [RM5]; exact hf5v) ?_
      intro r hr hrq
      exact hOther5 r hr hrq nm.inlist
        (hNotPrev5 r hr nm.inlist (Ne.symm hno.pf))
    · show readMem σ5.toMem (dbPath nm nm.count) = _
      rw [RM5, hc5, hqs]
      simp
    · intro r hr
      by_cases hrq : r = q
      · subst hrq
        exact ⟨by rw [RM5, hn5]; rfl, by rw [RM5, hp5]; rfl,
          by rw [RM5, hf5v]; rfl⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [hOther5 r hr hrq nm.next (hNotPrev5 r hr nm.next hno.np)]
          exact (I.fields r hr).1
        · cases hpost : post with
          | nil =>
            have hnone : ∀ q1 post0, post = q1 :: post0 →
                (fldPath q1 nm.prev).overlaps (fldPath r nm.prev) = false := by
              intro q1 post0 h; rw [hpost] at h; simp at h
            rw [hOther5 r hr hrq nm.prev hnone]
            exact (I.fields r hr).2.1
          | cons q1 post0 =>
            by_cases hq1r : q1 = r
            · subst hq1r
              rw [RM5, hfr5 _ (insert_disj I hqrow hr hrq nm.next nm.prev)
                (insert_disj I hqrow hr hrq nm.prev nm.prev)
                (insert_disj I hqrow hr hrq nm.inlist nm.prev)
                (parent_ne_row I hr nm.prev).2, hnew4 q1 post0 hpost]
              rfl
            · have hne5 : ∀ q1' post0', post = q1' :: post0' →
                  (fldPath q1' nm.prev).overlaps (fldPath r nm.prev) = false := by
                intro q1' post0' h
                rw [hpost] at h
                cases h
                exact fldPath_disjoint
                  (I.disj q1 (hpostR q1 post0 hpost) r hr hq1r)
              rw [hOther5 r hr hrq nm.prev hne5]
              exact (I.fields r hr).2.1
        · rw [hOther5 r hr hrq nm.inlist (hNotPrev5 r hr nm.inlist
            (Ne.symm hno.pf))]
          exact (I.fields r hr).2.2
  · rw [RM, hphead] at hpv
    exact absurd hpv (by simp)

/-- **`Insert` links a row at the head.**

checked by: `lake build` -/
theorem insertLinks {nm : Names} {elem : Ident} : InsertLinks nm elem := by
  intro p m rows qs q hlook hn hno I hqrow hflag
  obtain ⟨n, hn⟩ := hn
  have hI : ListInv (m.toStore [(parRow, Value.ptr q),
      (tmpOld, Value.null)]).toMem nm rows qs := by rw [Mem.toStore_toMem]; exact I
  obtain ⟨σ', hbody, I', hhead', hflag', hprev', hnext'⟩ :=
    exec_insertBody (p := p) (n := n) (elem := elem)
      (σ := m.toStore [(parRow, Value.ptr q), (tmpOld, Value.null)])
      hno hI hqrow (by rw [readMem_toStore]; exact hflag) rfl rfl
  refine ⟨σ'.toMem, ?_, I', ?_, ?_, ?_, ?_⟩
  · exact callFun_normal (p := p) (m := m) (fd := insertDef nm elem)
      (args := [Value.ptr q]) hlook hn rfl hbody
  · rw [readMem_toMem]; exact hhead'
  · rw [readMem_toMem]; exact hflag'
  · rw [readMem_toMem]; exact hprev'
  · rw [readMem_toMem, hnext', I.head]

end Proofs

/-! ## Checked -/

namespace Examples

/-- A parent whose only field is the list, and an element with a key. The
smallest schema that has an `Llist` at all. -/
def listDb : Dmmeta.Db where
  ctypes :=
    [ { name   := "task_row"
      , fields := [{ name := "id", arg := "u64", reftype := .Pkey }] }
    , { name   := "TaskDb"
      , fields := [{ name := "zdl_todo", arg := "task_row", reftype := .Llist }] } ]
  root := some "TaskDb"

end Examples

namespace Checks

/-- checked by: `lake build` -/
example : Dmmeta.check Examples.listDb = [] := rfl

/-- The generated program satisfies every C-subset obligation. Two pointer
locals are dereferenced (`_prev->f_next`, `_next->f_prev`), which is the form
neither the array table nor the pool produced.

checked by: `lake build` -/
example : (genLlist Examples.listDb).map CSubset.Wf.check = some [] := rfl

/-- The nine operations, in `amc`'s naming.

checked by: `lake build` -/
example : (genLlist Examples.listDb).map (fun p => p.funs.map FunDef.name)
    = some ["TaskDb_zdl_todo_Init", "TaskDb_zdl_todo_Insert",
            "TaskDb_zdl_todo_Remove", "TaskDb_zdl_todo_First",
            "TaskDb_zdl_todo_Next", "TaskDb_zdl_todo_Prev",
            "TaskDb_zdl_todo_InLlistQ", "TaskDb_zdl_todo_EmptyQ",
            "TaskDb_zdl_todo_N"] := rfl

/-- The element carries the links and the flag; the parent carries the head and
the count. Neither is storage the schema declared.

checked by: `lake build` -/
example : (genLlist Examples.listDb).map
    (fun p => p.structs.map (fun sd => (sd.name, sd.fields.map Prod.fst)))
    = some [("task_row", ["id", "zdl_todo_next", "zdl_todo_prev",
                          "zdl_todo_inlist"]),
            ("TaskDb", ["zdl_todo_head", "zdl_todo_n"])] := rfl

end Checks

end Llist
end Templates

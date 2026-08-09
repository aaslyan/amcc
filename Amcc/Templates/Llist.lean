import Amcc.Dmmeta
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls

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

/-- `<row>-><x>` as a path, given the path the row pointer names. -/
def fldPath (q : Path) (x : Ident) : Path := ⟨q.root, q.steps ++ [.fld x]⟩

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

/-! ## Still owed: the list invariant, and what the writers do to it

The readers and the two idempotence guards above are proved. The *linking*
laws are not, and the reason is worth stating precisely rather than leaving as
a gap in a list of theorems.

`RepInv` for the array table is a statement about a `List Value` — the storage
array — and every clause is a quantifier over indices. A linked list has no
such carrier: its shape is a property of a **graph in the heap**, and the
invariant that makes `Remove` correct is

- the chain from `head` along `next` is finite, acyclic and `NULL`-terminated;
- `prev` is its inverse on that chain, and `NULL` at the head;
- `inlist` is `true` exactly on the chain's members;
- `n` is the chain's length.

Stating that needs a *reachability* predicate over the store, and proving that
`Insert` and `Remove` preserve it needs the frame reasoning to be
compositional over that predicate — which `Store.readPath_writePath_disjoint`
supports but does not by itself supply. That is the missing piece, and it is a
piece the `Thash` template will need in the same form (a bucket is a chain), so
it is worth building once rather than twice.

Until it exists, what stands behind the writers is `scripts/smoke.sh`, which
runs the emitted C through a real compiler and checks link, unlink from the
head, the middle and the tail, and both guards. That is a differential test,
not a proof, and this section exists so that it is not mistaken for one.

`docs/PLAN.md` carries this as the next proof obligation. -/

/-- **What `Insert` should be proved to do.** Stated so the obligation is on
record and can be cited, in the same style as the array table's milestone
obligations were before they were discharged. -/
def InsertLinks (nm : Names) (elem : Ident) : Prop :=
  ∀ (p : Program) (m : Mem) (q : Path),
    lookupFun p nm.insert = .ok (insertDef nm elem) →
    (∃ n, p.funs.length = n + 1) →
    readMem m (fldPath q nm.inlist) = some (.bool false) →
    ∃ m', callFun p m nm.insert [.ptr q] = .ok (m', none)
      -- the row is now the head, and is in the list
      ∧ readMem m' (dbPath nm nm.head) = some (.ptr q)
      ∧ readMem m' (fldPath q nm.inlist) = some (.bool true)
      ∧ readMem m' (fldPath q nm.prev) = some .null
      -- and it points at what the head used to be
      ∧ readMem m' (fldPath q nm.next) = readMem m (dbPath nm nm.head)

/-- **What `Remove` should be proved to do.** -/
def RemoveUnlinks (nm : Names) (elem : Ident) : Prop :=
  ∀ (p : Program) (m : Mem) (q : Path),
    lookupFun p nm.remove = .ok (removeDef nm elem) →
    (∃ n, p.funs.length = n + 1) →
    readMem m (fldPath q nm.inlist) = some (.bool true) →
    ∃ m', callFun p m nm.remove [.ptr q] = .ok (m', none)
      ∧ readMem m' (fldPath q nm.inlist) = some (.bool false)
      ∧ readMem m' (fldPath q nm.next) = some .null
      ∧ readMem m' (fldPath q nm.prev) = some .null

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

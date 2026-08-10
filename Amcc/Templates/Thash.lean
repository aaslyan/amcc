import Amcc.Dmmeta
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.CSubset.Chain
import Amcc.Templates.Layout

/-!
# AMCC — the `Thash` template

`amc`'s most-used access pattern: a hash index from a key to a row, chained
through a link field the element carries. This is the template that turns the
project's "one table" surface into an *index* — the thing `amc` schemas are
mostly made of.

## What is generated

For a parent ctype `D` with a `Thash` field `f`, element ctype `E` whose `Pkey`
field is `k`, and a declared bucket count `NB`:

```c
typedef struct E { …E's fields…; E *f_next; bool f_inhash; } E;
typedef struct D { E *f_buckets[NB]; uint32_t f_n; } D;
static D g_D;

void     D_f_Init(void);              /* every bucket NULL; n = 0        */
E*       D_f_Find(uint32_t key);      /* the row with that key, or NULL  */
bool     D_f_InsertMaybe(E *row);     /* false on a duplicate key        */
void     D_f_Remove(E *row);          /* unlink                          */
uint32_t D_f_N(void);                 /* how many are indexed            */
```

## Three divergences, all forced by the subset

**Fixed capacity, no rehash, no growth.** `amc`'s `Thash` keeps its buckets in
a `Tary` and calls `$name_Reserve` to grow, rehashing every element. AMCC's
bucket array is an inline array of a size the schema declares. This is the same
gap `docs/DIVERGENCE.md` §2.2 records for the pool — `Stmt.alloc`/`Stmt.free`
and the allocator oracle are not written, so nothing generated can allocate —
and it is unfinished work rather than a design position. Recorded as §3.2.

**The hash is a mask, not a hash.** The subset has no division and no shifts,
so `key % nbuckets` is inexpressible. `key & (NB-1)` is, and it is exact when
`NB` is a power of two — which the generator therefore requires. It also means
the *bound* on the bucket index is an algebraic fact about `land` rather than a
comparison the code performs, which is where the no-trap obligation for the
subscript now lives.

**The chain walk is bounded.** The subset has no `while` and no `break`: the
only loop is `forN` with a bound read once. A hash chain has no static length,
so the walk runs `CAP` iterations — the element capacity, an upper bound on any
chain — with the body guarded by `_p != NULL` and, for `Find`, by
`_hit == NULL` so that it stops at the *first* match rather than the last.
Functionally this is `amc`'s walk; operationally it is O(CAP) rather than
O(chain). Recorded as §3.2.

The `_inhash` flag is the same divergence `Llist` carries and for the same
reason: `amc` marks a row not-in-index by comparing against `($Cpptype*)-1`,
which the subset makes inexpressible (§1.2, §2.4).
-/

namespace Templates
namespace Thash

open CSubset

/-! ## Generated names -/

def parRow : Ident := "row"
def parKey : Ident := "key"
def tmpB    : Ident := "_b"
def tmpP    : Ident := "_p"
def tmpHit  : Ident := "_hit"
def tmpPrev : Ident := "_prev"
def tmpI    : Ident := "_i"

structure Names where
  dbGlobal : Ident
  buckets  : Ident
  count    : Ident
  next     : Ident
  inhash   : Ident
  init     : Ident
  find     : Ident
  insert   : Ident
  remove   : Ident
  size     : Ident
  deriving Repr, Inhabited, DecidableEq

/-- `amc`'s naming, in C. -/
def names (dbC : Ident) (fld : Ident) : Names where
  dbGlobal := "g_" ++ dbC
  buckets  := fld ++ "_buckets"
  count    := fld ++ "_n"
  next     := fld ++ "_next"
  inhash   := fld ++ "_inhash"
  init     := dbC ++ "_" ++ fld ++ "_Init"
  find     := dbC ++ "_" ++ fld ++ "_Find"
  insert   := dbC ++ "_" ++ fld ++ "_InsertMaybe"
  remove   := dbC ++ "_" ++ fld ++ "_Remove"
  size     := dbC ++ "_" ++ fld ++ "_N"

/-! ## Lvalue shorthands -/

/-- `g_D.<x>` -/
def dbFld (nm : Names) (x : Ident) : LVal := .fld (.glob nm.dbGlobal) x
/-- `<p>-><x>` -/
def ptrFld (p : Ident) (x : Ident) : LVal := .fld (.deref p) x
/-- `g_D.f_buckets[<i>]` -/
def bucket (nm : Names) (i : Ident) : LVal := .idx (dbFld nm nm.buckets) (.var i)

/-- A pointer local, initialised to `NULL`. -/
def ptrLocal (x : Ident) (elem : Ident) : LocalDef :=
  { name := x, ty := .ptr (.strct elem), init := .null (.strct elem) }

/-! ## The generated code -/

/-- ```c
void D_f_Init(void) {
  uint32_t _i = 0;
  for (_i = 0; _i < NB; ++_i) { g_D.f_buckets[_i] = NULL; }
  g_D.f_n = 0;
}
``` -/
def initDef (nm : Names) (elem : Ident) (nb : Nat) : FunDef where
  name   := nm.init
  params := []
  ret    := none
  locals := [LocalDef.zeroed tmpI .u32]
  body   := .block
    [ .forN tmpI (.lit nb) (.assign (bucket nm tmpI) (.null (.strct elem)))
    , .assign (dbFld nm nm.count) (.lit (.u32 0)) ]

/-- One iteration of `Find`'s walk, named so the loop-invariant proof in
`Templates/ThashFind.lean` has something to induct over. Inlining it in
`findDef` changes nothing about the emitted C — `Stmt` is a value — but it
makes the loop body a term the proof can quote rather than repeat. -/
def findLoopBody (nm : Names) (elem : Ident) (key : Ident) : Stmt :=
  .when (.bin .eq (.rd (.var tmpHit)) (.null (.strct elem))) <|
    .when (.bin .ne (.rd (.var tmpP)) (.null (.strct elem))) <| .block
      [ .when (.bin .eq (.rd (ptrFld tmpP key)) (.rd (.var parKey)))
          (.assign (.var tmpHit) (.rd (.var tmpP)))
      , .assign (.var tmpP) (.rd (ptrFld tmpP nm.next)) ]

/-- ```c
E* D_f_Find(uint32_t key) {
  uint32_t _b = 0; E *_p = NULL; E *_hit = NULL; uint32_t _i = 0;
  _b = (key & MASK);
  _p = g_D.f_buckets[_b];
  for (_i = 0; _i < CAP; ++_i) {
    if (_hit == NULL) {
      if (_p != NULL) {
        if (_p->k == key) { _hit = _p; }
        _p = _p->f_next;
      }
    }
  }
  return _hit;
}
```
The `_hit == NULL` guard is what makes this the *first* match: without it the
walk would keep going and report the last. -/
def findDef (nm : Names) (elem : Ident) (key : Ident) (mask cap : Nat) : FunDef where
  name   := nm.find
  params := [(parKey, .scalar .u32)]
  ret    := some (.ptr (.strct elem))
  locals := [ LocalDef.zeroed tmpB .u32
            , ptrLocal tmpP elem
            , ptrLocal tmpHit elem
            , LocalDef.zeroed tmpI .u32 ]
  body   := .block
    [ .assign (.var tmpB)
        (.bin .band (.rd (.var parKey)) (.lit (.u32 (UInt32.ofNat mask))))
    , .assign (.var tmpP) (.rd (bucket nm tmpB))
    , .forN tmpI (.lit cap) (findLoopBody nm elem key)
    , .ret (some (.rd (.var tmpHit))) ]

/-- ```c
bool D_f_InsertMaybe(E *row) {
  uint32_t _b = 0; E *_dup = NULL;
  if (!row->f_inhash) {
    _dup = D_f_Find(row->k);
    if (_dup == NULL) {
      _b = (row->k & MASK);
      row->f_next   = g_D.f_buckets[_b];
      row->f_inhash = true;
      g_D.f_buckets[_b] = row;
      g_D.f_n = g_D.f_n + 1;
      return true;
    }
  }
  return false;
}
```
`amc`'s `InsertMaybe` reports failure the same way, and the duplicate check is
a call to the index's own `Find` there too. -/
def insertDef (nm : Names) (elem : Ident) (key : Ident) (mask : Nat) : FunDef where
  name   := nm.insert
  params := [(parRow, .ptr (.strct elem))]
  ret    := some (.scalar .bool)
  locals := [LocalDef.zeroed tmpB .u32, ptrLocal tmpP elem]
  body   := .block
    [ .when (.un .lnot (.rd (ptrFld parRow nm.inhash))) <| .block
        [ .call (some tmpP) nm.find [.rd (ptrFld parRow key)]
        , .when (.bin .eq (.rd (.var tmpP)) (.null (.strct elem))) <| .block
            [ .assign (.var tmpB)
                (.bin .band (.rd (ptrFld parRow key))
                  (.lit (.u32 (UInt32.ofNat mask))))
            , .assign (ptrFld parRow nm.next) (.rd (bucket nm tmpB))
            , .assign (ptrFld parRow nm.inhash) (.lit (.bool true))
            , .assign (bucket nm tmpB) (.rd (.var parRow))
            , .assign (dbFld nm nm.count)
                (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
            , .ret (some (.lit (.bool true))) ] ]
    , .ret (some (.lit (.bool false))) ]

/-- ```c
void D_f_Remove(E *row) {
  uint32_t _b = 0; E *_p = NULL; E *_prev = NULL; uint32_t _i = 0;
  if (row->f_inhash) {
    _b = (row->k & MASK);
    _p = g_D.f_buckets[_b];
    for (_i = 0; _i < CAP; ++_i) {
      if (_p != NULL) { if (_p->f_next == row) { _prev = _p; } _p = _p->f_next; }
    }
    if (_prev != NULL) { _prev->f_next = row->f_next; }
    else { g_D.f_buckets[_b] = row->f_next; }
    row->f_next   = NULL;
    row->f_inhash = false;
    g_D.f_n = g_D.f_n - 1;
  }
}
```
The chain is singly linked, so the predecessor is found by walking — which is
what `amc`'s singly-linked `Llist_Remove` does, and for the same reason. -/
def removeDef (nm : Names) (elem : Ident) (key : Ident) (mask cap : Nat) : FunDef where
  name   := nm.remove
  params := [(parRow, .ptr (.strct elem))]
  ret    := none
  locals := [ LocalDef.zeroed tmpB .u32
            , ptrLocal tmpP elem
            , ptrLocal tmpPrev elem
            , LocalDef.zeroed tmpI .u32 ]
  body   := .when (.rd (ptrFld parRow nm.inhash)) <| .block
    [ .assign (.var tmpB)
        (.bin .band (.rd (ptrFld parRow key)) (.lit (.u32 (UInt32.ofNat mask))))
    , .assign (.var tmpP) (.rd (bucket nm tmpB))
    , .forN tmpI (.lit cap) <|
        .when (.bin .ne (.rd (.var tmpP)) (.null (.strct elem))) <| .block
          [ .when (.bin .eq (.rd (ptrFld tmpP nm.next)) (.rd (.var parRow)))
              (.assign (.var tmpPrev) (.rd (.var tmpP)))
          , .assign (.var tmpP) (.rd (ptrFld tmpP nm.next)) ]
    , .cond (.bin .ne (.rd (.var tmpPrev)) (.null (.strct elem)))
        (.assign (ptrFld tmpPrev nm.next) (.rd (ptrFld parRow nm.next)))
        (.assign (bucket nm tmpB) (.rd (ptrFld parRow nm.next)))
    , .assign (ptrFld parRow nm.next) (.null (.strct elem))
    , .assign (ptrFld parRow nm.inhash) (.lit (.bool false))
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

/-- The five operations. `Find` is emitted before `InsertMaybe`, which calls
it. -/
def defsFor (nm : Names) (elem key : Ident) (mask cap nb : Nat) : List FunDef :=
  [ initDef nm elem nb
  , findDef nm elem key mask cap
  , insertDef nm elem key mask
  , removeDef nm elem key mask cap
  , sizeDef nm ]

/-! ## Assembling a program -/

/-- The element struct, with the chain link and the membership flag. -/
def elemFields (nm : Names) (elem : Ident) : List (Ident × Ty) :=
  [(nm.next, .ptr (.strct elem)), (nm.inhash, .scalar .bool)]

/-- ...and what the parent's gains: the bucket array and the count. -/
def dbFields (nm : Names) (elem : Ident) (nb : Nat) : List (Ident × Ty) :=
  [ (nm.buckets, .arr (.ptr (.strct elem)) nb), (nm.count, .scalar .u32) ]

/-- `some e` when `n = 2 ^ e` for some `e ≤ fuel`, `none` otherwise.

Written as a structural search rather than `2 ^ Nat.log2 n == n` because
`Nat.log2` is defined by well-founded recursion and does not reduce in the
kernel, which would cost every schema check in this file its `rfl` proof. The
search *returns the exponent*, so accepting a schema hands the proofs a witness
instead of leaving them to recover one from a bit trick. -/
def pow2Exp? (fuel n : Nat) : Option Nat :=
  match fuel with
  | 0      => if n == 1 then some 0 else none
  | e + 1  => if n == 2 ^ (e + 1) then some (e + 1) else pow2Exp? e n

/-- Bucket counts are searched up to `2 ^ 31`, which also keeps `NB - 1` inside
a `uint32_t` — the mask is a `u32` literal, so a larger count would truncate. -/
def pow2Fuel : Nat := 31

theorem pow2_of_exp? : ∀ (fuel n e : Nat), pow2Exp? fuel n = some e → n = 2 ^ e
  | 0, n, e, h => by
    simp only [pow2Exp?] at h
    split at h
    · next hn => cases h; simpa using hn
    · exact Option.noConfusion h
  | f + 1, n, e, h => by
    simp only [pow2Exp?] at h
    split at h
    · next hn => cases h; simpa using hn
    · exact pow2_of_exp? f n e h

theorem exp?_le : ∀ (fuel n e : Nat), pow2Exp? fuel n = some e → e ≤ fuel
  | 0, n, e, h => by
    simp only [pow2Exp?] at h
    split at h
    · cases h; omega
    · exact Option.noConfusion h
  | f + 1, n, e, h => by
    simp only [pow2Exp?] at h
    split at h
    · cases h; omega
    · exact Nat.le_succ_of_le (exp?_le f n e h)

/-- The element's `Pkey` field, which is what the index is keyed by. -/
def keyField? (c : Dmmeta.Ctype) : Option Dmmeta.Field :=
  c.fields.find? (fun f => f.reftype == .Pkey)

/-- **The generator.** Emits the index for the first `Thash` field of the
parent ctype.

`none` when the schema declares no such field, when the element has no `Pkey`,
when the key is not a `u32` (the mask needs a scalar the subset can `band`), or
when the bucket count is not a power of two — the last is what makes
`key & (NB-1)` the same function as `key % NB`. Each of those is a real
precondition rather than a silent fallback. -/
def genThash (d : Dmmeta.Db) : Option Program := do
  let dbName ← d.root
  let full := d.withBuiltins
  let dbC ← full.find? dbName
  let fld ← dbC.fields.find? (fun f => f.reftype == .Thash)
  let elemC ← full.find? fld.arg
  let key ← keyField? elemC
  guard (key.arg == "u32")
  let nb ← full.inlaryMax? dbC.name fld.name
  guard (pow2Exp? pow2Fuel nb).isSome
  -- An upper bound on any chain: no more elements can be indexed than the
  -- schema declares room for.
  let cap ← full.inlaryMax? dbC.name fld.name
  let dbN := Dmmeta.mangle dbC.name
  let elemN := Dmmeta.mangle elemC.name
  let nm := names dbN (Dmmeta.mangle fld.name)
  some
    { structs := Layout.addFields dbN (dbFields nm elemN nb)
                   (Layout.addFields elemN (elemFields nm elemN)
                     (Dmmeta.genStructs d))
    , globals := Dmmeta.genGlobals d
    , funs    := defsFor nm elemN (Dmmeta.mangle key.name) (nb - 1) cap nb }

/-! ## Where the index's state lives -/

def dbPath (nm : Names) (x : Ident) : Path := ⟨.glob nm.dbGlobal, [.fld x]⟩

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

/-! ## The laws

Stated against an arbitrary program in which the name resolves, as the `Upptr`
and `Llist` templates' are; `CSubset.lookupFun_of_mem` turns "the schema
declares this field" into that hypothesis. -/

section Laws

variable {p : Program} {m : Mem} {nm : Names} {elem key : Ident} {q : Path}
  {mask cap nb : Nat}

/-- **`N` reports the count.**

checked by: `lake build` -/
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

/-- **`InsertMaybe` on a row already in the index reports failure and does
nothing.** `amc`'s guard, with the sentinel replaced by the stored flag.

checked by: `lake build` -/
theorem insert_noop
    (hlook : lookupFun p nm.insert = .ok (insertDef nm elem key mask))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (fldPath q nm.inhash) = some (.bool true)) :
    callFun p m nm.insert [.ptr q] = .ok (m, some (.bool false)) := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0),
      (tmpP, Value.null)]).getLocal parRow = some (.ptr q) := rfl
  have hr : (m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0),
      (tmpP, Value.null)]).readPath (fldPath q nm.inhash)
      = some (.bool true) := by rw [readMem_toStore]; exact hread
  have hbody : execAt p (execStmt p n) (insertDef nm elem key mask).body
      (m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0), (tmpP, Value.null)])
      = .ok (m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0),
          (tmpP, Value.null)], .ret (some (.bool false))) := by
    simp only [insertDef, Stmt.block, Stmt.when]
    rw [execAt_seq', execAt_cond']
    simp only [evalExpr, resolve_ptrFld hloc hr, readLoc, hr, bind, Except.bind,
      evalUn, Bool.not_true]
    rfl
  simpa [insertDef] using
    callFun_ret (p := p) (m := m) (fd := insertDef nm elem key mask)
      (args := [Value.ptr q]) hlook hn rfl hbody

/-- **`Remove` on a row not in the index does nothing.**

checked by: `lake build` -/
theorem remove_noop
    (hlook : lookupFun p nm.remove = .ok (removeDef nm elem key mask cap))
    (hn : ∃ n, p.funs.length = n + 1)
    (hread : readMem m (fldPath q nm.inhash) = some (.bool false)) :
    callFun p m nm.remove [.ptr q] = .ok (m, none) := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0),
      (tmpP, Value.null), (tmpPrev, Value.null),
      (tmpI, .u32 0)]).getLocal parRow = some (.ptr q) := rfl
  have hr : (m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0),
      (tmpP, Value.null), (tmpPrev, Value.null),
      (tmpI, .u32 0)]).readPath (fldPath q nm.inhash)
      = some (.bool false) := by rw [readMem_toStore]; exact hread
  have hbody : execAt p (execStmt p n) (removeDef nm elem key mask cap).body
      (m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0), (tmpP, Value.null),
        (tmpPrev, Value.null), (tmpI, .u32 0)])
      = .ok (m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0),
          (tmpP, Value.null), (tmpPrev, Value.null), (tmpI, .u32 0)],
        .normal) := by
    simp only [removeDef, Stmt.when]
    rw [execAt_cond']
    simp only [evalExpr, resolve_ptrFld hloc hr, readLoc, hr, bind, Except.bind]
    rfl
  simpa [removeDef] using
    callFun_normal (p := p) (m := m) (fd := removeDef nm elem key mask cap)
      (args := [Value.ptr q]) hlook hn rfl hbody

end Laws

/-! ## Still owed: the index invariant

`size_correct` and the two idempotence guards are proved. `Find`, and the
linking half of `InsertMaybe` and `Remove`, are not — for the same reason the
`Llist` template's linking laws are not, and it is the same missing piece.

A hash index's shape is a property of `NB` **chains** in the heap:

- each bucket's chain from `buckets[i]` along `next` is finite, acyclic and
  `NULL`-terminated;
- every row on bucket `i`'s chain has `key & MASK = i` — the clause that makes
  looking in one bucket sufficient, and the one that would break under a
  rehash;
- `inhash` is `true` exactly on rows that are on some chain;
- keys are distinct across all chains — which is what makes `Find`'s answer
  unique and `InsertMaybe`'s refusal correct;
- `n` is the total length.

Every clause needs the same reachability predicate over the store that
`Templates/Llist.lean` says it needs, which is why that one is worth building
before either. `docs/PLAN.md` carries it.

There is one obligation here that `Llist` did not have, and it is worth
naming separately because it is the *no-trap* obligation for this template:
`g_D.f_buckets[_b]` is in range because `_b = key & (NB-1)` and `NB` is a power
of two. That is an algebraic fact about `UInt32.land`, not a consequence of any
invariant, and it is the one place where the generator's power-of-two
precondition is cashed. -/

/-- **The subscript never traps.** `_b = key & (NB-1)` is always a legal index
into an `NB`-bucket array. Stated separately from the index invariant because
it depends on nothing but the mask.

The `0 < nb` hypothesis was missing when this was first stated, and the
statement was false without it: `Nat` subtraction makes the mask `0` when
`nb = 0`, and `0 < 0` does not hold. `genThash` already refuses `nb = 0`, so
nothing generated was ever at risk — but the obligation as written could not
have been discharged, which is exactly the failure mode stating obligations is
meant to prevent. -/
def BucketInRange (nb : Nat) : Prop :=
  0 < nb → ∀ k : UInt32, (k &&& UInt32.ofNat (nb - 1)).toNat < nb

/-- **Proved.** And it needs *only* positivity — not the power-of-two
condition. Masking clears bits, so `key & (NB-1) ≤ NB-1 < NB` whatever `NB`
is; `UInt32`'s truncation of the mask can only make it smaller.

That is worth stating plainly, because the module docstring could be read as
claiming the power-of-two requirement is what keeps the subscript in range. It
is not. What the power-of-two requirement buys is `mask_eq_mod` below — that
the mask *is* the modulus, so the index is a hash bucket rather than an
arbitrary function of the key.

checked by: `lake build` -/
theorem bucketInRange (nb : Nat) : BucketInRange nb := by
  intro hpos k
  have h1 : (k &&& UInt32.ofNat (nb - 1)).toNat
      = k.toNat &&& (UInt32.ofNat (nb - 1)).toNat := rfl
  have h2 : (UInt32.ofNat (nb - 1)).toNat = (nb - 1) % 4294967296 := by
    simp [UInt32.toNat_ofNat']
  have h3 : k.toNat &&& ((nb - 1) % 4294967296) ≤ (nb - 1) % 4294967296 :=
    Nat.and_le_right
  have h4 : (nb - 1) % 4294967296 ≤ nb - 1 := Nat.mod_le _ _
  rw [h1, h2]
  omega

/-- **The mask is the modulus.** This is what the power-of-two requirement
actually buys, and what `docs/DIVERGENCE.md` §3.2 claims when it says
`key & (NB-1)` "is the same function when `NB` is a power of two". Now checked
rather than asserted.

`e ≤ pow2Fuel` keeps `NB ≤ 2 ^ 31`, so `NB - 1` survives the `u32` literal the
generator emits — a larger bucket count would truncate the mask and this would
be false.

checked by: `lake build` -/
theorem mask_eq_mod {nb e : Nat} (hp : nb = 2 ^ e) (he : e ≤ pow2Fuel)
    (k : UInt32) : (k &&& UInt32.ofNat (nb - 1)).toNat = k.toNat % nb := by
  have hlt : nb - 1 < 4294967296 := by
    have : (2 : Nat) ^ e ≤ 2 ^ pow2Fuel := Nat.pow_le_pow_right (by omega) he
    simp only [pow2Fuel] at this
    omega
  have h1 : (k &&& UInt32.ofNat (nb - 1)).toNat
      = k.toNat &&& (UInt32.ofNat (nb - 1)).toNat := rfl
  have h2 : (UInt32.ofNat (nb - 1)).toNat = nb - 1 := by
    simp [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  rw [h1, h2, hp]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

/-- **Every schema `genThash` accepts has both.** The guard is what carries
`0 < nb` and the exponent, so acceptance is the hypothesis both theorems above
need — nothing is left to the caller.

checked by: `lake build` -/
theorem accepted_bucket_facts {nb e : Nat} (h : pow2Exp? pow2Fuel nb = some e) :
    0 < nb ∧ (∀ k : UInt32,
      (k &&& UInt32.ofNat (nb - 1)).toNat = k.toNat % nb
      ∧ (k &&& UInt32.ofNat (nb - 1)).toNat < nb) := by
  have hpow := pow2_of_exp? _ _ _ h
  have hle := exp?_le _ _ _ h
  have hpos : 0 < nb := by rw [hpow]; exact Nat.two_pow_pos e
  exact ⟨hpos, fun k => ⟨mask_eq_mod hpow hle k, bucketInRange nb hpos k⟩⟩

/-! ## The bucket invariant

`Find` looks in exactly one bucket, so what it needs is not the whole index
invariant but the *chain* hanging off one subscript. Every clause is a
`CSubset.Chain` predicate with the bucket head in place of a list head — which
is the sense in which `Llist` and `Thash` share a proof: the `Reaches` here is
the same `Reaches`, instantiated at `nm.next` and `buckets[b]`. -/

/-- `g_D.f_buckets[b]` as a path. -/
def bucketPath (nm : Names) (b : Nat) : Path :=
  ⟨.glob nm.dbGlobal, [.fld nm.buckets, .idx b]⟩

/-- **One bucket, as a chain.** A hash index is `NB` of these plus the clauses
that tie them together; `Find` needs only this one.

`fits` is the clause the subset forces: the walk is a `forN` bounded by the
capacity, because there is no `while` and no `break`
(`docs/DIVERGENCE.md` §3.2). It is not an artifact of the proof — a chain
longer than `cap` really would be walked incompletely by the emitted C. -/
structure BucketInv (m : Mem) (nm : Names) (key : Ident) (b cap : Nat)
    (qs : List Path) : Prop where
  /-- The bucket array holds this chain's head. -/
  head  : readMem m (bucketPath nm b) = some (headOf qs)
  /-- Following `next` from it visits exactly the chain. -/
  chain : Reaches m nm.next (headOf qs) qs
  /-- Every row on it has a readable `u32` key. -/
  keys  : ∀ q ∈ qs, ∃ k', readMem m (fldPath q key) = some (.u32 k')
  /-- The chain fits in the capacity the emitted walk is bounded by. -/
  fits  : qs.length ≤ cap

/-- **What `Find` computes.** Not "null or something with the right key" — that
was the first statement here and it is satisfied by a function that always
returns `NULL`. This says `Find` returns *the first row on the bucket's chain
whose key matches*, which pins both the hit and the miss.

`firstSat (keyAt m key k)` is `CSubset.Chain`'s search over a list; the content
of the theorem is that the generated counted walk computes it. `firstSat_spec`
and `firstSat_none` then turn either answer back into a statement about the
store. -/
def FindCorrect (nm : Names) (elem key : Ident) (mask cap : Nat) : Prop :=
  ∀ (p : Program) (m : Mem) (k : UInt32) (qs : List Path),
    lookupFun p nm.find = .ok (findDef nm elem key mask cap) →
    (∃ n, p.funs.length = n + 1) →
    BucketInv m nm key (k &&& UInt32.ofNat mask).toNat cap qs →
    callFun p m nm.find [.u32 k]
      = .ok (m, some (ptrOf (firstSat (keyAt m key k) qs)))

/-! ## Checked -/

namespace Examples

/-- A parent holding one hash index, and an element keyed by a `u32`. Eight
buckets — a power of two, as the mask requires. -/
def hashDb : Dmmeta.Db where
  ctypes :=
    [ { name   := "item_row"
      , fields := [ { name := "id",  arg := "u32", reftype := .Pkey }
                  , { name := "qty", arg := "u32", reftype := .Val } ] }
    , { name   := "ItemDb"
      , fields := [{ name := "ind_item", arg := "item_row", reftype := .Thash }] } ]
  inlary := [{ ctype := "ItemDb", field := "ind_item", max := 8 }]
  root   := some "ItemDb"

/-- **Regression: an element ctype with a record-typed field.** This schema is
accepted by `Dmmeta.check` and used to generate a program `Wf.check` rejected
with `"item_row.loc: unknown struct pt"` — the generator emitted two structs
of its own and `pt` was in neither. It is here as a schema the generator is
*run against*, not as prose. -/
def nestedDb : Dmmeta.Db where
  ctypes :=
    [ { name := "pt", fields := [{ name := "x", arg := "u32", reftype := .Val }] }
    , { name   := "item_row"
      , fields := [ { name := "id",  arg := "u32", reftype := .Pkey }
                  , { name := "loc", arg := "pt",  reftype := .Val }
                  , { name := "qty", arg := "u32", reftype := .Val } ] }
    , { name   := "ItemDb"
      , fields := [{ name := "ind_item", arg := "item_row", reftype := .Thash }] } ]
  inlary := [{ ctype := "ItemDb", field := "ind_item", max := 8 }]
  root   := some "ItemDb"

/-- **Regression: a ctype indexing itself.** `elemC = dbC`, so the two
hand-built structs took the same name and `Wf.check` reported
`duplicate struct: ItemDb` plus ten type errors. Extending the lowered table
makes both contributions land on one struct, which is what a self-index
should produce. -/
def selfDb : Dmmeta.Db where
  ctypes :=
    [ { name   := "ItemDb"
      , fields := [ { name := "id",       arg := "u32",    reftype := .Pkey }
                  , { name := "ind_item", arg := "ItemDb", reftype := .Thash } ] } ]
  inlary := [{ ctype := "ItemDb", field := "ind_item", max := 8 }]
  root   := some "ItemDb"

end Examples

namespace Checks

/-- checked by: `lake build` -/
example : Dmmeta.check Examples.hashDb = [] := rfl

/-- **Both regression schemas are accepted and both generate accepted
programs.** Before the layout rework the second half of each was false.

checked by: `lake build` -/
example : Dmmeta.check Examples.nestedDb = [] := rfl
example : (genThash Examples.nestedDb).map CSubset.Wf.check = some [] := rfl
example : Dmmeta.check Examples.selfDb = [] := rfl
example : (genThash Examples.selfDb).map CSubset.Wf.check = some [] := rfl

/-- The nested case emits **three** structs, `pt` among them — which is the
whole content of the fix.

checked by: `lake build` -/
example : (genThash Examples.nestedDb).map (fun p => p.structs.map StructDef.name)
    = some ["pt", "item_row", "ItemDb"] := rfl

/-- And the self-indexing case emits **one**, carrying both contributions.

checked by: `lake build` -/
example : (genThash Examples.selfDb).map
    (fun p => p.structs.map (fun sd => (sd.name, sd.fields.map Prod.fst)))
    = some [("ItemDb", ["id", "ind_item_next", "ind_item_inhash",
                        "ind_item_buckets", "ind_item_n"])] := rfl

/-- The generated program satisfies every C-subset obligation — including the
one the array table's scan also had to satisfy, that a subscript through a
`u32` local is in range, and the new one that a called function's own frame is
built correctly (`InsertMaybe` calls `Find`).

checked by: `lake build` -/
example : (genThash Examples.hashDb).map CSubset.Wf.check = some [] := rfl

/-- The five operations, in `amc`'s naming.

checked by: `lake build` -/
example : (genThash Examples.hashDb).map (fun p => p.funs.map FunDef.name)
    = some ["ItemDb_ind_item_Init", "ItemDb_ind_item_Find",
            "ItemDb_ind_item_InsertMaybe", "ItemDb_ind_item_Remove",
            "ItemDb_ind_item_N"] := rfl

/-- The element carries the chain link and the flag; the parent carries the
bucket array and the count.

checked by: `lake build` -/
example : (genThash Examples.hashDb).map
    (fun p => p.structs.map (fun sd => (sd.name, sd.fields.map Prod.fst)))
    = some [("item_row", ["id", "qty", "ind_item_next", "ind_item_inhash"]),
            ("ItemDb", ["ind_item_buckets", "ind_item_n"])] := rfl

/-- The example schema's bucket count is accepted with its exponent, so
`accepted_bucket_facts` applies to it: the mask is the modulus and the
subscript is in range.

checked by: `lake build` -/
example : pow2Exp? pow2Fuel 8 = some 3 := rfl

/-- A bucket count that is not a power of two is refused, because the mask
would not be the modulus.

checked by: `lake build` -/
example : (genThash { Examples.hashDb with
    inlary := [{ ctype := "ItemDb", field := "ind_item", max := 6 }] }) = none :=
  rfl

/-- So is a key the mask cannot be applied to.

checked by: `lake build` -/
example : (genThash { Examples.hashDb with
    ctypes :=
      [ { name := "item_row"
        , fields := [{ name := "id", arg := "u64", reftype := .Pkey }] }
      , { name   := "ItemDb"
        , fields := [{ name := "ind_item", arg := "item_row"
                     , reftype := .Thash }] } ] }) = none := rfl

end Checks

end Thash
end Templates

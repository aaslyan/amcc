import Amcc.Templates.Thash

/-!
# AMCC — `Thash.Find` is a chain search

`Templates/Thash.lean` states `FindCorrect`; this module proves it.

The shape is the array table's `forLoop_scan` with the carrier swapped: there
the loop ranged over indices of a `List Value` and `firstMatch` was the
specification, here it walks a `CSubset.Chain` and `firstSat (keyAt …)` is. The
packaging — a body lemma, an induction over the trip count, a prologue that
builds the frame and an epilogue that returns — is the same, and so are the
local-store lemmas, which is why they now live in `CSubset.Calls`.

## What makes this easier than `Llist`'s writers

`Find` writes **only locals**. `Store.setLocal` leaves `toMem` alone, so the
whole aliasing apparatus `Llist.exec_removeMiddle` needed — row disjointness,
path overlap, six frame conditions per step — collapses to one equation,
`σ'.toMem = σ.toMem`. The invariant is carried unchanged through every
iteration for free, and all the work is in the loop's arithmetic.

## The one subtlety: `_hit` freezes the walk

```c
if (_hit == NULL) { if (_p != NULL) { … } }
```
Once `_hit` is set the outer guard fails and the body is a no-op — including
the advance of `_p`. So `_p` does **not** track `qs.drop j` after a hit; it
freezes wherever it was. The invariant therefore states the `_p` clause
*conditionally*, under `firstSat … = none`, and that condition is exactly when
the body still runs. Stating it unconditionally is the version that does not
go through, and it is the first thing that went wrong here.
-/

namespace Templates
namespace Thash

open CSubset

/-! ## The bucket subscript

`g_D.f_buckets[_b]` is the one place `Find` touches memory, and it is the one
place it could trap. `bucketInRange` already says it cannot; this turns that
into a resolution. -/

/-- Resolving `g_D.f_buckets[i]` when `i` holds `b` and the bucket is
readable. The readability hypothesis is what discharges the `oob` case — the
same discipline `ArrayTableFind.resolve_slot` uses, and the reason `TypeSound`
is not on this template's critical path either. -/
theorem resolve_bucket {σ : Store} {nm : Names} {i : Ident} {b : Nat} {v : Value}
    (hloc : σ.getLocal i = some (.u32 (UInt32.ofNat b)))
    (hround : (UInt32.ofNat b).toNat = b)
    (hread : σ.readPath (bucketPath nm b) = some v) :
    resolve σ (bucket nm i) = .ok (.glb (bucketPath nm b)) := by
  -- the bucket *array* is readable because one of its elements is
  obtain ⟨vs, harr⟩ : ∃ vs, σ.readPath (dbPath nm nm.buckets) = some (.arr vs)
      ∧ b < vs.length := by
    simp only [bucketPath, Store.readPath, Value.getPath] at hread
    simp only [dbPath, Store.readPath, Value.getPath]
    cases hr : σ.rootVal (Root.glob nm.dbGlobal) with
    | none => rw [hr] at hread; simp at hread
    | some w =>
      rw [hr] at hread
      simp only [] at hread ⊢
      cases hs : Value.getStep w (.fld nm.buckets) with
      | none => rw [hs] at hread; simp at hread
      | some w' =>
        rw [hs] at hread
        simp only [] at hread
        cases hw' : w' with
        | arr vs =>
          refine ⟨vs, rfl, ?_⟩
          rw [hw'] at hread
          simp only [Value.getStep] at hread
          cases hlt : decide (b < vs.length) with
          | true => exact of_decide_eq_true hlt
          | false =>
            rw [List.getElem?_eq_none (by simp at hlt; omega)] at hread
            simp at hread
        | _ => rw [hw'] at hread; simp [Value.getStep] at hread
  obtain ⟨harr, hlt⟩ := harr
  simp only [bucket, resolve, evalIndex, hloc, hround, bind, Except.bind,
    resolve_dbFld harr, harr]
  rw [if_pos hlt]
  rfl

/-- Reading the bucket, packaged the way the prologue wants it. -/
theorem read_bucket {σ : Store} {nm : Names} {i : Ident} {b : Nat} {v : Value}
    (hloc : σ.getLocal i = some (.u32 (UInt32.ofNat b)))
    (hround : (UInt32.ofNat b).toNat = b)
    (hread : σ.readPath (bucketPath nm b) = some v) :
    evalExpr σ (.rd (bucket nm i)) = .ok v := by
  simp only [evalExpr, resolve_bucket hloc hround hread, readLoc, hread, bind,
    Except.bind]

/-- Reading `<p>-><x>`, the walk's two reads. -/
theorem read_ptrFld {σ : Store} {ptr x : Ident} {q : Path} {v : Value}
    (hloc : σ.getLocal ptr = some (.ptr q))
    (hread : σ.readPath (fldPath q x) = some v) :
    evalExpr σ (.rd (ptrFld ptr x)) = .ok v := by
  simp only [evalExpr, resolve_ptrFld hloc hread, readLoc, hread, bind,
    Except.bind]

/-! ## The loop invariant, as a predicate

Naming it keeps the body lemma's statement readable and — more to the point —
keeps the `_p` clause's conditional form in one place, where the reason for it
can be written down once. -/

/-- After `j` steps of the walk: `_hit` holds the search's answer over the
first `j` rows, and — *only while that answer is still `none`* — `_p` holds the
head of what is left. See the module docstring: once `_hit` is set the body
stops running, so `_p` freezes and nothing may be claimed about it. -/
structure WalkAt (m : Mem) (nm : Names) (key : Ident) (k : UInt32)
    (qs : List Path) (j : Nat) (σ : Store) : Prop where
  mem  : σ.toMem = m
  pkey : σ.getLocal parKey = some (.u32 k)
  hit  : σ.getLocal tmpHit = some (ptrOf (firstSat (keyAt m key k) (qs.take j)))
  ptr  : ∃ pv, σ.getLocal tmpP = some pv
           ∧ (firstSat (keyAt m key k) (qs.take j) = none → pv = headOf (qs.drop j))
  idx  : (σ.getLocal tmpI).isSome = true

/-! ## One iteration -/

/-- **The body advances the walk by one row**, and touches nothing but the
three locals.

checked by: `lake build` -/
theorem exec_findLoopBody {p : Program} {callee} {m : Mem} {nm : Names}
    {elem key : Ident} {k : UInt32} {qs : List Path} {j : Nat} {σ : Store}
    (hchain : Reaches m nm.next (headOf qs) qs)
    (hkeys : ∀ q ∈ qs, ∃ k', readMem m (fldPath q key) = some (.u32 k'))
    (W : WalkAt m nm key k qs j σ) :
    ∃ σ', execAt p callee (findLoopBody nm elem key) σ = .ok (σ', .normal)
      ∧ WalkAt m nm key k qs (j + 1) σ' := by
  have RM : ∀ pth, readMem σ.toMem pth = σ.readPath pth := readMem_toMem σ
  obtain ⟨pv, hpv, hpvEq⟩ := W.ptr
  cases hf : firstSat (keyAt m key k) (qs.take j) with
  | some q =>
    -- `_hit` is already set: the outer guard fails and the body is a no-op
    have hhit : σ.getLocal tmpHit = some (.ptr q) := by rw [W.hit, hf]; rfl
    have hg : evalExpr σ (.bin .eq (.rd (.var tmpHit)) (.null (.strct elem)))
        = .ok (.bool false) := by
      simp only [evalExpr, resolve, hhit, readLoc, bind, Except.bind, evalBin]
    have hnext : firstSat (keyAt m key k) (qs.take (j + 1)) = some q := by
      rw [firstSat_take_add_one, hf]
    refine ⟨σ, ?_, ⟨W.mem, W.pkey, by rw [W.hit, hf, hnext], ⟨pv, hpv, ?_⟩, W.idx⟩⟩
    · simp only [findLoopBody, Stmt.when]
      rw [execAt_cond', hg]; rfl
    · intro hnone; rw [hnext] at hnone; exact absurd hnone (by simp)
  | none =>
    have hhit : σ.getLocal tmpHit = some Value.null := by rw [W.hit, hf]; rfl
    have hg : evalExpr σ (.bin .eq (.rd (.var tmpHit)) (.null (.strct elem)))
        = .ok (.bool true) := by
      simp only [evalExpr, resolve, hhit, readLoc, bind, Except.bind, evalBin]
    have hpvH : pv = headOf (qs.drop j) := hpvEq hf
    cases hd : qs.drop j with
    | nil =>
      -- the walk has run off the end: `_p` is NULL, the inner guard fails
      have hlen : qs.length ≤ j := by
        have := List.drop_eq_nil_iff.mp hd; omega
      have hpn : σ.getLocal tmpP = some Value.null := by
        rw [hpv, hpvH, hd]; rfl
      have hg2 : evalExpr σ (.bin .ne (.rd (.var tmpP)) (.null (.strct elem)))
          = .ok (.bool false) := by
        simp only [evalExpr, resolve, hpn, readLoc, bind, Except.bind, evalBin]
      have hsame : firstSat (keyAt m key k) (qs.take (j + 1))
          = firstSat (keyAt m key k) (qs.take j) := by
        rw [firstSat_take_of_le hlen, firstSat_take_of_le (by omega)]
      have hd1 : qs.drop (j + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
      refine ⟨σ, ?_, ⟨W.mem, W.pkey, by rw [W.hit, hsame], ⟨pv, hpv, ?_⟩, W.idx⟩⟩
      · simp only [findLoopBody, Stmt.when]
        rw [execAt_cond', hg]
        simp only [bind, Except.bind]
        rw [execAt_cond', hg2]; rfl
      · intro _; rw [hpvH, hd, hd1]
    | cons q rest =>
      -- one real step: test this row's key, then follow `next`
      have hlt : j < qs.length := by
        rcases Nat.lt_or_ge j qs.length with h | h
        · exact h
        · rw [List.drop_eq_nil_iff.mpr h] at hd; exact absurd hd (by simp)
      have hcd := List.getElem_cons_drop hlt
      rw [hd] at hcd
      have hq : qs[j]? = some q := by
        rw [List.getElem?_eq_getElem hlt]
        exact congrArg some (List.cons.inj hcd).1
      have hd1 : qs.drop (j + 1) = rest := (List.cons.inj hcd).2
      have hqmem : q ∈ qs :=
        List.mem_of_mem_drop (a := q) (by rw [hd]; simp)
      have hpq : σ.getLocal tmpP = some (.ptr q) := by rw [hpv, hpvH, hd]; rfl
      have hg2 : evalExpr σ (.bin .ne (.rd (.var tmpP)) (.null (.strct elem)))
          = .ok (.bool true) := by
        simp only [evalExpr, resolve, hpq, readLoc, bind, Except.bind, evalBin]
      obtain ⟨k', hk'⟩ := hkeys q hqmem
      have hk'σ : σ.readPath (fldPath q key) = some (.u32 k') := by
        rw [← RM, W.mem]; exact hk'
      -- the generated guard is exactly `keyAt`, which is why the search
      -- predicate was defined as a `Bool` in the first place
      have hkeyAt : keyAt m key k q = (k' == k) := by simp only [keyAt, hk']
      have hg3 : evalExpr σ (.bin .eq (.rd (ptrFld tmpP key)) (.rd (.var parKey)))
          = .ok (.bool (k' == k)) := by
        simp only [evalExpr, resolve_ptrFld hpq hk'σ, readLoc, hk'σ, resolve,
          W.pkey, bind, Except.bind, evalBin]
      -- ...and the advance is one step down the chain
      have hnx : σ.readPath (fldPath q nm.next) = some (headOf rest) := by
        rw [← RM, W.mem, ← hd1]; exact hchain.next_at hq
      have hstep : firstSat (keyAt m key k) (qs.take (j + 1))
          = if k' == k then some q else none := by
        rw [firstSat_take_add_one, hf, hq]
        simp [Option.toList, firstSat, hkeyAt]
      cases hkk : (k' == k) with
      | true =>
        -- the key matched: `_hit = _p`, then `_p = _p->next`
        have hfirst : execAt p callee
            (Stmt.when (.bin .eq (.rd (ptrFld tmpP key)) (.rd (.var parKey)))
              (.assign (.var tmpHit) (.rd (.var tmpP)))) σ
            = .ok (σ.setLocal tmpHit (.ptr q), .normal) := by
          simp only [Stmt.when]
          rw [execAt_cond', hg3, hkk]
          simp only [bind, Except.bind]
          exact step_local (v := Value.null) hhit (read_local' hpq)
        refine ⟨(σ.setLocal tmpHit (.ptr q)).setLocal tmpP (headOf rest), ?_, ?_⟩
        · simp only [findLoopBody, Stmt.when, Stmt.block]
          rw [execAt_cond', hg]
          simp only [bind, Except.bind]
          rw [execAt_cond', hg2]
          simp only [bind, Except.bind]
          rw [execAt_seq']
          simp only [Stmt.when] at hfirst
          rw [hfirst]
          simp only [bind, Except.bind]
          refine step_local (v := Value.ptr q) ?_ ?_
          · rw [getLocal_setLocal_ne (by decide)]; exact hpq
          · refine read_ptrFld (q := q) ?_ ?_
            · rw [getLocal_setLocal_ne (by decide)]; exact hpq
            · rw [readPath_setLocal]; exact hnx
        · refine ⟨?_, ?_, ?_, ⟨headOf rest, ?_, ?_⟩, ?_⟩
          · rw [Store.setLocal_toMem, Store.setLocal_toMem]; exact W.mem
          · rw [getLocal_setLocal_ne (by decide),
              getLocal_setLocal_ne (by decide)]
            exact W.pkey
          · rw [getLocal_setLocal_ne (by decide), getLocal_setLocal_self hhit]
            simp [hstep, hkk, ptrOf]
          · refine getLocal_setLocal_self (w := Value.ptr q) ?_
            rw [getLocal_setLocal_ne (by decide)]; exact hpq
          · intro hnone
            rw [hstep, hkk] at hnone
            exact absurd hnone (by simp)
          · rw [getLocal_setLocal_ne (by decide),
              getLocal_setLocal_ne (by decide)]
            exact W.idx
      | false =>
        -- the key did not match: only the advance runs
        have hfirst : execAt p callee
            (Stmt.when (.bin .eq (.rd (ptrFld tmpP key)) (.rd (.var parKey)))
              (.assign (.var tmpHit) (.rd (.var tmpP)))) σ = .ok (σ, .normal) := by
          simp only [Stmt.when]
          rw [execAt_cond', hg3, hkk]
          rfl
        refine ⟨σ.setLocal tmpP (headOf rest), ?_, ?_⟩
        · simp only [findLoopBody, Stmt.when, Stmt.block]
          rw [execAt_cond', hg]
          simp only [bind, Except.bind]
          rw [execAt_cond', hg2]
          simp only [bind, Except.bind]
          rw [execAt_seq']
          simp only [Stmt.when] at hfirst
          rw [hfirst]
          simp only [bind, Except.bind]
          exact step_local (v := Value.ptr q) hpq (read_ptrFld hpq hnx)
        · refine ⟨?_, ?_, ?_, ⟨headOf rest, ?_, ?_⟩, ?_⟩
          · rw [Store.setLocal_toMem]; exact W.mem
          · rw [getLocal_setLocal_ne (by decide)]; exact W.pkey
          · rw [getLocal_setLocal_ne (by decide), W.hit, hf]
            simp [hstep, hkk, ptrOf]
          · exact getLocal_setLocal_self hpq
          · intro _; rw [hd1]
          · rw [getLocal_setLocal_ne (by decide)]; exact W.idx

/-! ## The whole walk -/

/-- **The counted walk is a chain search.** `rem` iterations starting at step
`j` leave `_hit` holding the answer over the first `j + rem` rows, and leave
memory alone.

This is where per-iteration reasoning becomes a statement about the loop, and
it is the same induction `ArrayTableFind.forLoop_scan` runs — over the trip
count, with the invariant carried through.

checked by: `lake build` -/
theorem forLoop_walk {p : Program} {callee} {m : Mem} {nm : Names}
    {elem key : Ident} {k : UInt32} {qs : List Path}
    (hchain : Reaches m nm.next (headOf qs) qs)
    (hkeys : ∀ q ∈ qs, ∃ k', readMem m (fldPath q key) = some (.u32 k')) :
    ∀ (rem j : Nat) (σ : Store), WalkAt m nm key k qs j σ →
      ∃ σ', forLoop (execAt p callee (findLoopBody nm elem key)) tmpI j rem σ
              = .ok (σ', .normal)
        ∧ σ'.toMem = m
        ∧ σ'.getLocal tmpHit
            = some (ptrOf (firstSat (keyAt m key k) (qs.take (j + rem)))) := by
  intro rem
  induction rem with
  | zero =>
    intro j σ W
    refine ⟨σ.setLocal tmpI (.u32 (UInt32.ofNat j)), rfl, ?_, ?_⟩
    · rw [Store.setLocal_toMem]; exact W.mem
    · rw [getLocal_setLocal_ne (by decide)]; simpa using W.hit
  | succ rem ih =>
    intro j σ W
    -- the counter is written before the body runs; it is not one of the three
    -- locals the invariant mentions, so the invariant survives verbatim
    have W0 : WalkAt m nm key k qs j (σ.setLocal tmpI (.u32 (UInt32.ofNat j))) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [Store.setLocal_toMem]; exact W.mem
      · rw [getLocal_setLocal_ne (by decide)]; exact W.pkey
      · rw [getLocal_setLocal_ne (by decide)]; exact W.hit
      · obtain ⟨pv, h1, h2⟩ := W.ptr
        exact ⟨pv, by rw [getLocal_setLocal_ne (by decide)]; exact h1, h2⟩
      · rw [Store.getLocal, Store.setLocal, Env.isSome_get?_set]; exact W.idx
    obtain ⟨σ1, hbody, W1⟩ :=
      exec_findLoopBody (p := p) (callee := callee) (elem := elem) hchain hkeys W0
    obtain ⟨σ', hloop, hmem, hhit⟩ := ih (j + 1) σ1 W1
    refine ⟨σ', ?_, hmem, ?_⟩
    · simp only [forLoop]
      rw [hbody]
      simpa using hloop
    · rw [hhit, show j + 1 + rem = j + (rem + 1) from by omega]

/-! ## The prologue, and the answer

What is left is the frame `Find` runs against, the two assignments before the
loop, and the `return` after it. -/

/-- **`Find`'s body computes the search.**

checked by: `lake build` -/
theorem exec_findBody {p : Program} {n : Nat} {m : Mem} {nm : Names}
    {elem key : Ident} {mask cap : Nat} {k : UInt32} {qs : List Path}
    (B : BucketInv m nm key (k &&& UInt32.ofNat mask).toNat cap qs) :
    ∃ σ', execAt p (execStmt p n) (findDef nm elem key mask cap).body
        (m.toStore [(parKey, Value.u32 k), (tmpB, .u32 0), (tmpP, Value.null),
          (tmpHit, Value.null), (tmpI, .u32 0)])
        = .ok (σ', .ret (some (ptrOf (firstSat (keyAt m key k) qs))))
      ∧ σ'.toMem = m := by
  obtain ⟨σ0, hσ0⟩ : ∃ t, t = m.toStore [(parKey, Value.u32 k), (tmpB, .u32 0),
    (tmpP, Value.null), (tmpHit, Value.null), (tmpI, .u32 0)] := ⟨_, rfl⟩
  have hkey0 : σ0.getLocal parKey = some (.u32 k) := by rw [hσ0]; rfl
  have hm0 : σ0.toMem = m := by rw [hσ0]; rfl
  -- A1: `_b = key & MASK`
  have hev1 : evalExpr σ0
      (.bin .band (.rd (.var parKey)) (.lit (.u32 (UInt32.ofNat mask))))
      = .ok (.u32 (k &&& UInt32.ofNat mask)) := by
    simp only [evalExpr, resolve, hkey0, readLoc, bind, Except.bind, evalBin]
  obtain ⟨σ1, hσ1⟩ : ∃ t, t = σ0.setLocal tmpB (.u32 (k &&& UInt32.ofNat mask)) :=
    ⟨_, rfl⟩
  have hA1 : execAt p (execStmt p n)
      (.assign (.var tmpB)
        (.bin .band (.rd (.var parKey)) (.lit (.u32 (UInt32.ofNat mask))))) σ0
      = .ok (σ1, .normal) := by
    rw [hσ1]; exact step_local (v := Value.u32 0) (by rw [hσ0]; rfl) hev1
  have hm1 : σ1.toMem = m := by rw [hσ1, Store.setLocal_toMem]; exact hm0
  -- `_b` now holds the bucket index, and `UInt32` round-trips through `Nat`
  have hround : (UInt32.ofNat (k &&& UInt32.ofNat mask).toNat)
      = (k &&& UInt32.ofNat mask) := UInt32.ofNat_toNat
  have hbloc : σ1.getLocal tmpB
      = some (.u32 (UInt32.ofNat (k &&& UInt32.ofNat mask).toNat)) := by
    rw [hσ1, getLocal_setLocal_self (w := Value.u32 0) (by rw [hσ0]; rfl), hround]
  have hbucket : σ1.readPath (bucketPath nm (k &&& UInt32.ofNat mask).toNat)
      = some (headOf qs) := by rw [← readMem_toMem, hm1]; exact B.head
  -- A2: `_p = g_D.f_buckets[_b]`
  obtain ⟨σ2, hσ2⟩ : ∃ t, t = σ1.setLocal tmpP (headOf qs) := ⟨_, rfl⟩
  have hA2 : execAt p (execStmt p n)
      (.assign (.var tmpP) (.rd (bucket nm tmpB))) σ1 = .ok (σ2, .normal) := by
    rw [hσ2]
    exact step_local (v := Value.null)
      (by rw [hσ1, getLocal_setLocal_ne (by decide), hσ0]; rfl)
      (read_bucket hbloc (by rw [hround]) hbucket)
  -- the loop starts at step 0, with `_hit` null and `_p` at the chain's head
  have W0 : WalkAt m nm key k qs 0 σ2 := by
    refine ⟨?_, ?_, ?_, ⟨headOf qs, ?_, fun _ => rfl⟩, ?_⟩
    · rw [hσ2, Store.setLocal_toMem]; exact hm1
    · rw [hσ2, getLocal_setLocal_ne (by decide), hσ1,
        getLocal_setLocal_ne (by decide), hσ0]; rfl
    · rw [hσ2, getLocal_setLocal_ne (by decide), hσ1,
        getLocal_setLocal_ne (by decide), hσ0]; rfl
    · rw [hσ2]
      exact getLocal_setLocal_self (w := Value.null)
        (by rw [hσ1, getLocal_setLocal_ne (by decide), hσ0]; rfl)
    · rw [hσ2, getLocal_setLocal_ne (by decide), hσ1,
        getLocal_setLocal_ne (by decide), hσ0]
      rfl
  obtain ⟨σ3, hloop, hm3, hhit3⟩ :=
    forLoop_walk (p := p) (callee := execStmt p n) (elem := elem)
      B.chain B.keys cap 0 σ2 W0
  have hhit : σ3.getLocal tmpHit = some (ptrOf (firstSat (keyAt m key k) qs)) := by
    rw [hhit3, firstSat_take_of_le (by simpa using B.fits)]
  refine ⟨σ3, ?_, hm3⟩
  rw [← hσ0]
  simp only [findDef, Stmt.block]
  rw [execAt_seq', hA1]
  simp only [bind, Except.bind]
  rw [execAt_seq', hA2]
  simp only [bind, Except.bind]
  rw [execAt_seq']
  show (do
    match ← execAt p (execStmt p n) (Stmt.forN tmpI (.lit cap) (findLoopBody nm elem key)) σ2 with
    | (σ₁, .normal) => execAt p (execStmt p n) (Stmt.ret (some (.rd (.var tmpHit)))) σ₁
    | (σ₁, .ret v)  => .ok (σ₁, .ret v)) = _
  simp only [execAt, evalIndex, bind, Except.bind]
  rw [hloop]
  simp only [bind, Except.bind, evalExpr, resolve, hhit, readLoc]

/-- **`Find` returns the first row on the bucket's chain whose key matches.**

checked by: `lake build` -/
theorem findCorrect {nm : Names} {elem key : Ident} {mask cap : Nat} :
    FindCorrect nm elem key mask cap := by
  intro p m k qs hlook hn B
  obtain ⟨n, hn⟩ := hn
  obtain ⟨σ', hbody, hmem⟩ :=
    exec_findBody (p := p) (n := n) (nm := nm) (elem := elem) (key := key)
      (mask := mask) (cap := cap) (k := k) B
  have := callFun_ret (p := p) (m := m) (fd := findDef nm elem key mask cap)
    (args := [Value.u32 k]) hlook hn rfl hbody
  simpa [findDef, hmem] using this

/-! ## What the answer means

`firstSat` is a list search; these two turn it back into a statement about the
store, which is what a consumer of the generated `Find` actually wants to
cite. -/

/-- A non-`NULL` answer is a row on the bucket's chain, and its key is the one
asked for.

checked by: `lake build` -/
theorem find_hit {p : Program} {m : Mem} {nm : Names} {elem key : Ident}
    {mask cap : Nat} {k : UInt32} {qs : List Path} {q : Path}
    (hlook : lookupFun p nm.find = .ok (findDef nm elem key mask cap))
    (hn : ∃ n, p.funs.length = n + 1)
    (B : BucketInv m nm key (k &&& UInt32.ofNat mask).toNat cap qs)
    (hq : firstSat (keyAt m key k) qs = some q) :
    callFun p m nm.find [.u32 k] = .ok (m, some (.ptr q))
      ∧ q ∈ qs ∧ readMem m (fldPath q key) = some (.u32 k) := by
  obtain ⟨hmem, hkey⟩ := firstSat_spec hq
  exact ⟨by rw [findCorrect p m k qs hlook hn B, hq]; rfl,
    hmem, keyAt_iff.mp hkey⟩

/-- A `NULL` answer means **no** row on the bucket's chain has that key. This
is the half the original statement of `FindCorrect` did not have, and it is the
half a caller relies on when it treats `NULL` as "absent" rather than as "not
found by this search".

checked by: `lake build` -/
theorem find_miss {p : Program} {m : Mem} {nm : Names} {elem key : Ident}
    {mask cap : Nat} {k : UInt32} {qs : List Path}
    (hlook : lookupFun p nm.find = .ok (findDef nm elem key mask cap))
    (hn : ∃ n, p.funs.length = n + 1)
    (B : BucketInv m nm key (k &&& UInt32.ofNat mask).toNat cap qs)
    (hq : firstSat (keyAt m key k) qs = none) :
    callFun p m nm.find [.u32 k] = .ok (m, some .null)
      ∧ ∀ q ∈ qs, readMem m (fldPath q key) ≠ some (.u32 k) := by
  refine ⟨by rw [findCorrect p m k qs hlook hn B, hq]; rfl, fun q hqm hk => ?_⟩
  have := firstSat_none hq q hqm
  rw [keyAt_iff.mpr hk] at this
  exact absurd this (by simp)

end Thash
end Templates

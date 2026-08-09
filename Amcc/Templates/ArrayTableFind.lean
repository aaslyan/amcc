import Amcc.Templates.ArrayTableWf

/-!
# AMCC — `find`, proved against the semantics

The first refinement proof in the project: reasoning about `execStmt` on a
*generated* body, under `RepInv`, to establish what the function computes.

Everything proved so far about generated code has been **structural** —
`GenWellFormed` says the checker accepts it, `Wf.check` says the shapes fit.
Nothing has said what any generated function *does*. This file is where that
starts, and `find` is the right place to start it: `insert`, `erase` and the
abstraction all call `find`, so no other clause of `Simulates` is reachable
without it.

## Why this order

The plan deferred this behind `TypeSound` and the semantics rework. That was
the wrong call, for a reason worth recording: the technique — loop-invariant
reasoning over `forLoop`, with the error cases discharged from `RepInv` — is
what transfers to every later template. Deferring it left the project's
central claim untested while everything else was built on the assumption that
it would work.

`TypeSound` is deliberately **not** used. It is a general
progress-and-preservation argument over `Step`; for one template the shapes are
pinned by `RepInv` directly, so the structural errors are discharged where they
arise rather than by a theorem that does not exist yet.

## The obligations, bottom up

1. `resolve_slot` — the loop's `g_<t>[_i]` resolves to the path it should.
2. `resolve_field` / `read_field` — a field of that slot reads back what the
   invariant says is there.
3. the guard evaluates to the occupancy-and-key test.
4. `forLoop` induction: scanning `[i, i+rem)` returns the first match.
5. `FindCorrect`.

All five are established: `findCorrect` at the bottom discharges
`ArrayTable.FindCorrect`. It is the project's first theorem about what
generated code **computes**, as opposed to whether the checker accepts it.
-/

namespace Templates
namespace ArrayTable

open CSubset

variable {s : Schema} {σ : Store}

/-! ## Reading the loop variable

`evalIndex` goes through `UInt32.toNat`, so every slot lemma needs the
round-trip. It holds because `Schema.check` bounds the capacity by `2³²`, which
is exactly why that clause is in the checker. -/

/-- The loop variable, read back as the `Nat` it stands for. -/
theorem evalIndex_var {i : Nat} {x : Ident}
    (hloc : σ.getLocal x = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i) :
    evalIndex σ (.var x) = .ok i := by
  simp only [evalIndex, hloc, hround]

/-! ## Resolving a slot

The first genuine step: `g_<t>[_i]` denotes slot `i` of the storage array.
Every clause of `RepInv` that matters shows up here — `storage` gives the
array, and the length clause is what turns `i < capacity` into an in-range
subscript, which is the whole no-trap argument for this template. -/

/-- **The slot resolves, and does not trap.**

The `oob` case is discharged by `RepInv.length`: the array really is
`capacity` long, so a loop bounded by the capacity cannot leave it.

checked by: `lake build` -/
theorem resolve_slot {i : Nat} (R : RepInv s σ.glb)
    (hlt : i < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpI = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i) :
    resolve σ (slot s tmpI)
      = .ok (.glb ⟨.glob (Schema.names s).storage, [.idx i]⟩) := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  simp only [slot, resolve, evalIndex, hloc, hround, Store.readPath,
    Store.rootVal, hglb, Value.getPath, bind, Except.bind]
  rw [if_pos hlt]
  simp

/-- Reading through a resolved slot gives the row the invariant names. -/
theorem readLoc_slot {i : Nat} {row : Value} (R : RepInv s σ.glb)
    (hrow : (rowsOf s σ.glb)[i]? = some row) :
    readLoc σ (.glb ⟨.glob (Schema.names s).storage, [.idx i]⟩) = .ok row := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  simp only [readLoc, Store.readPath, Store.rootVal, hglb, Value.getPath,
    Value.getStep, hrow]

/-! ## Resolving a field of a slot

`g_<t>[_i].f`. This is where `RepInv.rows` earns its place: without it the
field lookup could fail and the read would be a `typeErr` rather than a value.
Discharging that here, from the invariant, is what makes `TypeSound`
unnecessary for this template. -/

/-- **A field of a slot resolves**, provided the row really has that field —
which for the generated struct's fields is `RowOk`. -/
theorem resolve_field {i : Nat} {row : Value} {f : Ident} {v : Value}
    (R : RepInv s σ.glb)
    (hlt : i < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpI = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i)
    (hrow : (rowsOf s σ.glb)[i]? = some row)
    (hfld : row.getStep (.fld f) = some v) :
    resolve σ (field s tmpI f)
      = .ok (.glb ⟨.glob (Schema.names s).storage, [.idx i, .fld f]⟩) := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  have hstep : (Value.arr (rowsOf s σ.glb)).getStep (.idx i) = some row := by
    simp only [Value.getStep, hrow]
  have hpath : (Value.arr (rowsOf s σ.glb)).getPath [.idx i, .fld f] = some v := by
    show (match (Value.arr (rowsOf s σ.glb)).getStep (.idx i) with
          | some v' => Value.getPath v' [.fld f]
          | none => none) = some v
    rw [hstep]
    show (match row.getStep (.fld f) with
          | some v' => Value.getPath v' []
          | none => none) = some v
    rw [hfld]
    rfl
  simp only [field, resolve, resolve_slot R hlt hloc hround, bind, Except.bind,
    Store.readPath, Store.rootVal, hglb, List.cons_append, List.nil_append]
  rw [hpath]

/-- **And reading it gives the field's value.**

checked by: `lake build` -/
theorem read_field {i : Nat} {row : Value} {f : Ident} {v : Value}
    (R : RepInv s σ.glb)
    (hlt : i < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpI = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i)
    (hrow : (rowsOf s σ.glb)[i]? = some row)
    (hfld : row.getStep (.fld f) = some v) :
    evalExpr σ (.rd (field s tmpI f)) = .ok v := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  have hstep : (Value.arr (rowsOf s σ.glb)).getStep (.idx i) = some row := by
    simp only [Value.getStep, hrow]
  have hpath : (Value.arr (rowsOf s σ.glb)).getPath [.idx i, .fld f] = some v := by
    show (match (Value.arr (rowsOf s σ.glb)).getStep (.idx i) with
          | some v' => Value.getPath v' [.fld f]
          | none => none) = some v
    rw [hstep]
    show (match row.getStep (.fld f) with
          | some v' => Value.getPath v' []
          | none => none) = some v
    rw [hfld]
    rfl
  simp only [evalExpr, resolve_field R hlt hloc hround hrow hfld, bind,
    Except.bind, readLoc, Store.readPath, Store.rootVal, hglb,
    List.cons_append, List.nil_append]
  rw [hpath]

/-! ## What `RepInv` gives about a row

Turning the invariant's existential clauses into the equations the guard needs. -/

/-- The occupancy flag of a live row is a `bool`, and it is the one `absOf`
reads. -/
theorem occupied_of_rowOk {row : Value} (h : RowOk s row) :
    row.getStep (.fld (Schema.names s).occupied)
      = some (.bool (rowOccupied s row)) := by
  obtain ⟨b, hb⟩ := h.occupied
  cases row with
  | strct fs =>
    simp only [Value.getStep]
    simp only at hb
    rw [hb]
    congr 1
    simp only [rowOccupied, hb]
  | u32 _ => simp at hb
  | u64 _ => simp at hb
  | bool _ => simp at hb
  | null => simp at hb
  | ptr _ => simp at hb
  | arr _ => simp at hb

/-! ## Keys

`find` compares the row's key field against the argument with `==`, and
`evalBin .eq` is only defined when both operands are the *same* scalar
constructor. So the comparison only evaluates at all when the key argument has
the primary key's type — which is a precondition `FindCorrect` does not
currently carry. See the note at the bottom. -/

/-- `Key.ofValue?` recovers exactly the value it was built from. The converse
of `Interface.Key.ofValue_toValue`. -/
theorem toValue_ofValue {v : Value} {k : Interface.Key}
    (h : Interface.Key.ofValue? v = some k) : k.toValue = v := by
  cases v with
  | u32 a  => cases h; rfl
  | u64 a  => cases h; rfl
  | bool b => cases h; rfl
  | null   => exact Option.noConfusion h
  | ptr _  => exact Option.noConfusion h
  | strct _ => exact Option.noConfusion h
  | arr _  => exact Option.noConfusion h

/-- **Comparing two keys of the same type is the key comparison.**

At *different* types it is not an equation at all — `evalBin .eq` errors —
which is why the type agreement is a hypothesis rather than something to be
wished away. -/
theorem evalBin_eq_keys {k k' : Interface.Key} (hty : k'.ty = k.ty) :
    evalBin .eq k'.toValue k.toValue = .ok (.bool (k' == k)) := by
  cases k' <;> cases k <;> first
    | rfl
    | exact absurd hty (by simp [Interface.Key.ty])

/-! ## The loop guard

`g[_i].occupied && g[_i].pk == k`, as a single equation. This is where the two
halves of `RepInv` meet: `rows` makes both reads succeed, and the key
round-trip makes the comparison mean what `absOf` means by it. -/

/-- The row's key field, as the key `absOf` reads off it. -/
theorem rowKey_eq {row : Value} {pk : Schema.Field} {fs : List (Ident × Value)}
    {v : Value} {k' : Interface.Key}
    (hpk : Schema.pkey? s = some pk)
    (hrow : row = .strct fs)
    (hfld : Env.get? fs pk.name = some v)
    (hk : Interface.Key.ofValue? v = some k') :
    rowKey? s row = some k' := by
  subst hrow
  simp [rowKey?, hpk, hfld, hk]

/-- Reading a resolved field path. Stated separately from `read_field` because
the guard proof needs it *after* `evalExpr` has been unfolded, at which point
the `evalExpr`-level equation no longer matches. -/
theorem readLoc_field {i : Nat} {row : Value} {f : Ident} {v : Value}
    (R : RepInv s σ.glb)
    (hrow : (rowsOf s σ.glb)[i]? = some row)
    (hfld : row.getStep (.fld f) = some v) :
    readLoc σ (.glb ⟨.glob (Schema.names s).storage, [.idx i, .fld f]⟩)
      = .ok v := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  have hstep : (Value.arr (rowsOf s σ.glb)).getStep (.idx i) = some row := by
    simp only [Value.getStep, hrow]
  have hpath : (Value.arr (rowsOf s σ.glb)).getPath [.idx i, .fld f] = some v := by
    show (match (Value.arr (rowsOf s σ.glb)).getStep (.idx i) with
          | some v' => Value.getPath v' [.fld f]
          | none => none) = some v
    rw [hstep]
    show (match row.getStep (.fld f) with
          | some v' => Value.getPath v' []
          | none => none) = some v
    rw [hfld]
    rfl
  simp only [readLoc, Store.readPath, Store.rootVal, hglb, hpath]

/-- Reading a local. -/
theorem read_local {x : Ident} {v : Value} (h : σ.getLocal x = some v) :
    evalExpr σ (.rd (.var x)) = .ok v := by
  simp only [evalExpr, resolve, h, bind, Except.bind, readLoc]

/-- **The loop guard, as one equation.**

`g[_i].occupied && g[_i].pk == k` evaluates to exactly "slot `i` is occupied
and holds key `k`" — which is the condition `absOf` uses to decide whether the
key is in the table. That the generated C and the abstraction function agree
on this is the whole content of the step.

checked by: `lake build` -/
theorem eval_guard {i : Nat} {row : Value} {fs : List (Ident × Value)}
    {pk : Schema.Field} {k k' : Interface.Key} {kv : Value} {b : Bool}
    (R : RepInv s σ.glb)
    (hlt : i < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpI = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i)
    (hrow : (rowsOf s σ.glb)[i]? = some row)
    (hstrct : row = .strct fs)
    (hocc : Env.get? fs (Schema.names s).occupied = some (.bool b))
    (hkfld : Env.get? fs pk.name = some kv)
    (hk' : Interface.Key.ofValue? kv = some k')
    (hty : k'.ty = k.ty)
    (hkloc : σ.getLocal pk.name = some k.toValue) :
    evalExpr σ (.bin .land
        (.rd (field s tmpI (Schema.names s).occupied))
        (.bin .eq (.rd (field s tmpI pk.name)) (.rd (.var pk.name))))
      = .ok (.bool (b && (k' == k))) := by
  have hfo : row.getStep (.fld (Schema.names s).occupied) = some (.bool b) := by
    subst hstrct; simpa [Value.getStep] using hocc
  have hfk : row.getStep (.fld pk.name) = some kv := by
    subst hstrct; simpa [Value.getStep] using hkfld
  have hkv : kv = k'.toValue := (toValue_ofValue hk').symm
  subst hkv
  have hro := resolve_field R hlt hloc hround hrow hfo
  have hrk := resolve_field R hlt hloc hround hrow hfk
  have hlo := readLoc_field R hrow hfo
  have hlk := readLoc_field R hrow hfk
  have hrv : resolve σ (.var pk.name) = .ok (.lcl pk.name) := by
    simp only [resolve, hkloc]
  have hlv : readLoc σ (.lcl pk.name) = .ok k.toValue := by
    simp only [readLoc, hkloc]
  cases b with
  | false =>
    simp only [evalExpr, hro, hlo, bind, Except.bind, Bool.false_and]
  | true =>
    simp only [evalExpr, hro, hlo, hrk, hlk, hrv, hlv, bind, Except.bind,
      evalBin_eq_keys hty, Bool.true_and]

/-! ## What a well-formed row is, unpacked

`RowOk` states its clauses existentially. The scan needs them as equations, and
in particular needs to know that a live row **is** a struct — which the
occupancy clause forces, since the match it quantifies over yields `none` on
every other constructor. -/

/-- A row satisfying `RowOk` is a struct with a boolean occupancy flag. -/
theorem strct_of_rowOk {row : Value} (h : RowOk s row) :
    ∃ fs b, row = .strct fs
      ∧ Env.get? fs (Schema.names s).occupied = some (.bool b)
      ∧ rowOccupied s row = b := by
  obtain ⟨b, hb⟩ := h.occupied
  cases row with
  | strct fs =>
    refine ⟨fs, b, rfl, hb, ?_⟩
    simp only [rowOccupied, hb]
  | u32 _ => exact Option.noConfusion hb
  | u64 _ => exact Option.noConfusion hb
  | bool _ => exact Option.noConfusion hb
  | null => exact Option.noConfusion hb
  | ptr _ => exact Option.noConfusion hb
  | arr _ => exact Option.noConfusion hb

/-- And its key field is present, converts, and stands at the primary key's
declared type. -/
theorem key_of_rowOk {row : Value} {fs : List (Ident × Value)} {pk : Schema.Field}
    (h : RowOk s row) (hpk : Schema.pkey? s = some pk) (hstrct : row = .strct fs) :
    ∃ kv k', Env.get? fs pk.name = some kv
      ∧ Interface.Key.ofValue? kv = some k'
      ∧ rowKey? s row = some k'
      ∧ k'.ty = pk.ty := by
  have hks := h.key
  subst hstrct
  cases hkv : Env.get? fs pk.name with
  | none => simp [rowKey?, hpk, hkv] at hks
  | some kv =>
    cases hcv : Interface.Key.ofValue? kv with
    | none => simp [rowKey?, hpk, hkv, hcv] at hks
    | some k' =>
      have hrk : rowKey? s (Value.strct fs) = some k' := by
        simp [rowKey?, hpk, hkv, hcv]
      exact ⟨kv, k', rfl, hcv, hrk, h.keyTy pk k' hpk hrk⟩

/-! ## The scan

`slotMatches` is the abstract test the generated guard implements, and
`firstMatch` is what the whole loop computes: the first slot in a range that
passes it. -/

/-- Slot `i` is occupied and holds key `k`. -/
def slotMatches (s : Schema) (glb : Env) (k : Interface.Key) (i : Nat) : Bool :=
  match (rowsOf s glb)[i]? with
  | some r => rowOccupied s r && (rowKey? s r == some k)
  | none   => false

/-- The first matching slot in `[i, i + rem)`. -/
def firstMatch (s : Schema) (glb : Env) (k : Interface.Key) : Nat → Nat → Option Nat
  | _, 0       => none
  | i, rem + 1 =>
    if slotMatches s glb k i then some i else firstMatch s glb k (i + 1) rem

/-- **One iteration.** Either it returns a pointer to this slot, or it falls
through — and either way it leaves the store alone. -/
theorem exec_loopBody {p : Program} {callee} {pk : Schema.Field}
    {k : Interface.Key} {i : Nat}
    (R : RepInv s σ.glb)
    (hpk : Schema.pkey? s = some pk)
    (hlt : i < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpI = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i)
    (hkloc : σ.getLocal pk.name = some k.toValue)
    (hkty : k.ty = pk.ty) :
    execAt p callee (findLoopBody s pk) σ
      = .ok (σ, if slotMatches s σ.glb k i
                then .ret (some (.ptr ⟨.glob (Schema.names s).storage, [.idx i]⟩))
                else .normal) := by
  have hrow : (rowsOf s σ.glb)[i]? = some ((rowsOf s σ.glb)[i]'hlt) :=
    List.getElem?_eq_getElem hlt
  have hok : RowOk s ((rowsOf s σ.glb)[i]'hlt) := R.rows _ (List.getElem_mem hlt)
  obtain ⟨fs, b, hstrct, hocc, hrocc⟩ := strct_of_rowOk hok
  obtain ⟨kv, k', hkfld, hcv, hrk, hkty'⟩ := key_of_rowOk hok hpk hstrct
  have hg := eval_guard R hlt hloc hround hrow hstrct hocc hkfld hcv
    (by rw [hkty', hkty]) hkloc
  have hsm : slotMatches s σ.glb k i = (b && (k' == k)) := by
    simp only [slotMatches, hrow, hrocc, hrk]
    simp
  simp only [findLoopBody, Stmt.when, execAt, findGuard, hg, bind, Except.bind,
    hsm]
  cases hb : b && (k' == k) with
  | false => simp
  | true =>
    simp only [evalExpr, resolve_slot R hlt hloc hround, bind, Except.bind]
    simp

/-- **The scan is a search.**

Running the generated loop over `[i, i + rem)` returns a pointer to the first
matching slot, or falls through when there is none — and preserves the globals
throughout, which is what keeps `RepInv` alive across iterations and makes the
induction go.

This is the step where per-iteration reasoning becomes a statement about the
function: everything above it is one slot, this is the search.

checked by: `lake build` -/
theorem forLoop_scan {p : Program} {callee} {pk : Schema.Field}
    {k : Interface.Key} (hpk : Schema.pkey? s = some pk) (hne : pk.name ≠ tmpI)
    (hkty : k.ty = pk.ty) :
    ∀ (rem i : Nat) (σ : Store),
      RepInv s σ.glb →
      σ.getLocal pk.name = some k.toValue →
      (σ.getLocal tmpI).isSome = true →
      i + rem ≤ (rowsOf s σ.glb).length →
      (∀ j, j < (rowsOf s σ.glb).length → (UInt32.ofNat j).toNat = j) →
      ∃ σ', forLoop (execAt p callee (findLoopBody s pk)) tmpI i rem σ
              = .ok (σ', match firstMatch s σ.glb k i rem with
                         | some j =>
                           .ret (some (.ptr ⟨.glob (Schema.names s).storage,
                                             [.idx j]⟩))
                         | none => .normal)
            ∧ σ'.toMem = σ.toMem := by
  intro rem
  induction rem with
  | zero =>
    intro i σ _ _ _ _ _
    exact ⟨σ.setLocal tmpI (.u32 (UInt32.ofNat i)), rfl, rfl⟩
  | succ rem ih =>
    intro i σ R hkloc htmp hbnd hrnd
    have hlt : i < (rowsOf s σ.glb).length := by omega
    -- the loop writes only `_i`, so everything the invariant needs survives
    have hglb : (σ.setLocal tmpI (.u32 (UInt32.ofNat i))).glb = σ.glb :=
      Store.setLocal_glb _ _ _
    have h0 : (σ.setLocal tmpI (.u32 (UInt32.ofNat i))).getLocal tmpI
        = some (.u32 (UInt32.ofNat i)) := by
      show (σ.loc.set tmpI _).get? tmpI = _
      rw [Env.get?_set_self]
      cases hg : σ.loc.get? tmpI with
      | none => rw [Store.getLocal, hg] at htmp; exact absurd htmp (by simp)
      | some _ => rfl
    have hk0 : (σ.setLocal tmpI (.u32 (UInt32.ofNat i))).getLocal pk.name
        = some k.toValue := by
      show (σ.loc.set tmpI _).get? pk.name = _
      rw [Env.get?_set_ne _ hne]; exact hkloc
    have hbody := exec_loopBody (p := p) (callee := callee) (hglb ▸ R) hpk
      (hglb ▸ hlt) h0 (hrnd i hlt) hk0 hkty
    simp only [forLoop]
    rw [hbody]
    simp only [firstMatch, hglb]
    cases hm : slotMatches s σ.glb k i with
    | true =>
      simp only [if_pos trivial]
      exact ⟨_, rfl, rfl⟩
    | false =>
      obtain ⟨σ', heq, hgl⟩ := ih (i + 1)
        (σ.setLocal tmpI (.u32 (UInt32.ofNat i))) (hglb ▸ R) hk0
        (by rw [Store.getLocal, Store.setLocal, Env.isSome_get?_set]; exact htmp)
        (by rw [hglb]; omega) (by rw [hglb]; exact hrnd)
      rw [hglb] at heq
      refine ⟨σ', ?_, hgl⟩
      simpa using heq

/-! ## What the scan found, in the abstraction's terms

`firstMatch` is an index; `absOf` is a `List.find?`. Relating them is what
turns "the loop stopped at slot `j`" into "the key is in the table". -/

theorem firstMatch_none {glb : Env} {k : Interface.Key} :
    ∀ (rem i : Nat), firstMatch s glb k i rem = none →
      ∀ j, i ≤ j → j < i + rem → slotMatches s glb k j = false := by
  intro rem
  induction rem with
  | zero => intro i _ j _ hj; omega
  | succ rem ih =>
    intro i h j hij hj
    cases hm : slotMatches s glb k i with
    | true => simp [firstMatch, hm] at h
    | false =>
      simp only [firstMatch, hm, Bool.false_eq_true, if_false] at h
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact hm
      · exact ih (i + 1) h j hlt (by omega)

theorem firstMatch_some {glb : Env} {k : Interface.Key} :
    ∀ (rem i j : Nat), firstMatch s glb k i rem = some j →
      slotMatches s glb k j = true := by
  intro rem
  induction rem with
  | zero => intro i j h; exact Option.noConfusion h
  | succ rem ih =>
    intro i j h
    cases hm : slotMatches s glb k i with
    | true =>
      simp only [firstMatch, hm, if_true] at h
      cases h; exact hm
    | false =>
      simp only [firstMatch, hm, Bool.false_eq_true, if_false] at h
      exact ih (i + 1) j h

/-- **The scan agrees with the abstraction.**

A scan of the whole array finds a slot exactly when `absOf` says the key is
present. This is the one place the generated loop and the abstraction function
— written independently of one another — are forced to agree.

checked by: `lake build` -/
theorem firstMatch_isSome_iff {glb : Env} {k : Interface.Key} (R : RepInv s glb) :
    (firstMatch s glb k 0 (rowsOf s glb).length).isSome
      ↔ (absOf s glb k).isSome := by
  constructor
  · intro h
    cases hf : firstMatch s glb k 0 (rowsOf s glb).length with
    | none => rw [hf] at h; simp at h
    | some j =>
      have hj := firstMatch_some _ _ _ hf
      simp only [slotMatches] at hj
      cases hr : (rowsOf s glb)[j]? with
      | none => rw [hr] at hj; simp at hj
      | some r =>
        rw [hr] at hj
        have hmem : r ∈ rowsOf s glb := List.mem_of_getElem? hr
        simp only [absOf]
        cases hfd : (rowsOf s glb).find?
            (fun r => rowOccupied s r && rowKey? s r == some k) with
        | none =>
          have hno := List.find?_eq_none.mp hfd r hmem
          exact absurd hj (by simpa using hno)
        | some r' => exact (R.rows r' (find?_pred hfd).2).vals
  · intro h
    simp only [absOf] at h
    cases hfd : (rowsOf s glb).find?
        (fun r => rowOccupied s r && rowKey? s r == some k) with
    | none => rw [hfd] at h; simp at h
    | some r' =>
      obtain ⟨hp, hm'⟩ := find?_pred hfd
      obtain ⟨j, hjlt, hjr⟩ := List.getElem_of_mem hm'
      cases hf : firstMatch s glb k 0 (rowsOf s glb).length with
      | some _ => simp
      | none =>
        have hno := firstMatch_none _ _ hf j (Nat.zero_le j) (by omega)
        simp only [slotMatches, List.getElem?_eq_getElem hjlt, hjr] at hno
        exact absurd hp (by simpa using hno)

/-! ## The function, end to end

The loop is the interesting part; what remains is the prologue that builds the
frame and the epilogue the loop falls through to. -/

/-- The frame `find` runs against: the key parameter, then the zeroed loop
variable. -/
theorem buildFrame_find {m : Mem} {pk : Schema.Field} {k : Interface.Key} :
    buildFrame m (findDef s pk) [k.toValue]
      = .ok [(pk.name, k.toValue), (tmpI, .u32 0)] := by
  rfl

/-- `pkey?` returning a field is the singleton filter. -/
theorem filter_of_pkey {pk : Schema.Field} (hpk : Schema.pkey? s = some pk) :
    s.fields.filter (fun f => f.reftype == .Pkey) = [pk] := by
  cases hf : s.fields.filter (fun f => f.reftype == .Pkey) with
  | nil => rw [Schema.pkey?, hf] at hpk; exact Option.noConfusion hpk
  | cons a tl =>
    cases tl with
    | nil => rw [Schema.pkey?, hf] at hpk; cases hpk; rfl
    | cons b tl2 => rw [Schema.pkey?, hf] at hpk; exact Option.noConfusion hpk

/-- **The body**: the scan, and the `return NULL` it falls through to. -/
theorem exec_findBody {p : Program} {callee} {pk : Schema.Field}
    {k : Interface.Key} (hpk : Schema.pkey? s = some pk) (hne : pk.name ≠ tmpI)
    (hkty : k.ty = pk.ty)
    (R : RepInv s σ.glb)
    (hk0 : σ.getLocal pk.name = some k.toValue)
    (ht0 : (σ.getLocal tmpI).isSome = true)
    (hcap : s.capacity ≤ (rowsOf s σ.glb).length)
    (hrnd : ∀ j, j < (rowsOf s σ.glb).length → (UInt32.ofNat j).toNat = j) :
    ∃ σ', execAt p callee (findDef s pk).body σ
        = .ok (σ', .ret (some (match firstMatch s σ.glb k 0 s.capacity with
                               | some j =>
                                 .ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩
                               | none => .null)))
      ∧ σ'.toMem = σ.toMem := by
  obtain ⟨σ', hloop, hmem⟩ :=
    forLoop_scan (p := p) (callee := callee) hpk hne hkty s.capacity 0 σ R hk0
      ht0 (by omega) hrnd
  refine ⟨σ', ?_, hmem⟩
  show (do
    match ← execAt p callee (.forN tmpI (.lit s.capacity) (findLoopBody s pk)) σ with
    | (σ₁, .normal) => execAt p callee (.ret (some (nullRow s))) σ₁
    | (σ₁, .ret v)  => .ok (σ₁, .ret v)) = _
  simp only [execAt, evalIndex, bind, Except.bind]
  rw [hloop]
  cases firstMatch s σ.glb k 0 s.capacity with
  | some j => rfl
  | none => simp only [execAt, evalExpr, nullRow, bind, Except.bind]

/-- **`find` is correct.**

It returns a pointer to a slot, or `NULL`, and it is a pointer exactly when
`absOf` says the key is present. The memory it was handed comes back
unchanged, because the scan writes only the loop variable and nothing else in
the function writes at all.

This is the project's first theorem about what generated code *computes*, as
opposed to whether the checker accepts it.

checked by: `lake build` -/
theorem findCorrect : FindCorrect s := by
  intro m pk k hwf hpk hkty R
  have hchk : Schema.check s = [] := List.isEmpty_iff.mp hwf
  have F := facts_of_check hchk
  have hfl := filter_of_pkey hpk
  have hne : pk.name ≠ tmpI :=
    ne_of_reserved (F.notReserved pk (pk_mem hfl)) (by decide)
  have hlen : (rowsOf s m.glb).length = s.capacity := R.length
  have hrnd : ∀ j, j < (rowsOf s m.glb).length → (UInt32.ofNat j).toNat = j := by
    intro j hj
    have hlt : j < 4294967296 := by
      have hc := F.capLt; simp only [Wf.u32Bound] at hc; omega
    simpa [UInt32.toNat_ofNat'] using Nat.mod_eq_of_lt hlt
  have hgenC : (genC s).funs = [findDef s pk, insertDef s pk, eraseDef s pk] := by
    simp only [genC, hpk]
  have hlook : lookupFun (genC s) (Schema.names s).find = .ok (findDef s pk) := by
    simp [lookupFun, hgenC, findDef]
  have hk0 : (m.toStore [(pk.name, k.toValue), (tmpI, .u32 0)]).getLocal pk.name
      = some k.toValue := by
    simp [Mem.toStore, Store.getLocal, Env.get?]
  have ht0 : ((m.toStore [(pk.name, k.toValue), (tmpI, .u32 0)]).getLocal
      tmpI).isSome = true := by
    simp [Mem.toStore, Store.getLocal, Env.get?, hne]
  obtain ⟨σ', hbody, hmem⟩ :=
    exec_findBody (p := genC s) (callee := execStmt (genC s) 2)
      hpk hne hkty (σ := m.toStore [(pk.name, k.toValue), (tmpI, .u32 0)]) R hk0 ht0
      (by simp [Mem.toStore_glb, hlen]) (by simp only [Mem.toStore_glb]; exact hrnd)
  refine ⟨firstMatch s m.glb k 0 s.capacity, ?_, by rw [← hlen]; exact firstMatch_isSome_iff R⟩
  have hn : (genC s).funs.length = 2 + 1 := by rw [hgenC]; rfl
  simp only [call, callFun, hlook, buildFrame_find, bind, Except.bind, hn]
  rw [show execStmt (genC s) (2 + 1)
        = execAt (genC s) (execStmt (genC s) 2) from rfl]
  rw [hbody]
  simp only [hmem, Mem.toStore_toMem, Mem.toStore_glb]
  rfl

/-! ## Still owed

What this file does **not** prove, stated plainly so the gap is not mistaken
for progress:

- The other four clauses of `Simulates`: `NoTrap`, `InsertRefines`,
  `EraseRefines`, `RepInvPreserved`. `find` was the prerequisite — the other
  three operations all call it — so they are now reachable, but they are not
  done.

`NoTrap` should now be close to free for `find`: `findCorrect` returns `.ok`,
which is exactly what `NoTrap` asks. `insert` and `erase` additionally write
through the returned pointer, so they need a write-side counterpart of
`read_field` and the fact that `RepInv` survives a field update — neither of
which is new technique.

## Two findings about `FindCorrect` as currently stated

Both are defects in the *statement*, discovered by trying to prove it, and
both must be fixed before it can be true.

**It describes the old API.** `ArrayTable.FindCorrect` says `find` returns
`.u32 (UInt32.ofNat i)` with `i ≤ capacity` and `i < capacity` meaning
"present". `find` now returns a row pointer, or `NULL` when absent. The clause
needs restating in those terms.

**It is false as written.** It quantifies over *every* `Interface.Key`, with
no constraint relating the key to the primary key's type. `evalBin .eq` is
defined only on matching scalar constructors, so searching a `u64`-keyed table
with a `.bool` key does not return "absent" — it raises `typeErr`. The
statement needs `k.ty = pk.ty` as a hypothesis, which `eval_guard` above
already carries. A clause that cannot be discharged is worth more than one
that looks discharged, and this one was hiding in plain sight until the
comparison had to be evaluated. -/

end ArrayTable
end Templates

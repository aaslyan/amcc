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

/-- `==` and `decide (· = ·)` agree wherever `BEq` is lawful. The generated
comparison produces the former; `absOf` is stated with the latter, because
`decide` is the one that talks to propositional equality without a detour. -/
private theorem beq_eq_decide' {α : Type _} [BEq α] [LawfulBEq α]
    [DecidableEq α] (a b : α) : (a == b) = decide (a = b) := by
  cases h : a == b
  · simp [beq_eq_false_iff_ne.mp h]
  · simp [eq_of_beq h]

/-- **Comparing two keys of the same type is the key comparison.**

At *different* types it is not an equation at all — `evalBin .eq` errors —
which is why the type agreement is a hypothesis rather than something to be
wished away. -/
theorem evalBin_eq_keys {k k' : Interface.Key} (hty : k'.ty = k.ty) :
    evalBin .eq k'.toValue k.toValue = .ok (.bool (decide (k' = k))) := by
  cases k' <;> cases k <;>
    simp_all [evalBin, Interface.Key.toValue, Interface.Key.ty, beq_eq_decide']

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
      = .ok (.bool (b && decide (k' = k))) := by
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
  | some r => rowOccupied s r && decide (rowKey? s r = some k)
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
  have hsm : slotMatches s σ.glb k i = (b && decide (k' = k)) := by
    simp only [slotMatches, hrow, hrocc, hrk]
    simp
  simp only [findLoopBody, Stmt.when, execAt, findGuard, hg, bind, Except.bind,
    hsm]
  cases hb : b && decide (k' = k) with
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
            (fun r => rowOccupied s r && decide (rowKey? s r = some k)) with
        | none =>
          have hno := List.find?_eq_none.mp hfd r hmem
          exact absurd hj (by simpa using hno)
        | some r' => exact (R.rows r' (find?_pred hfd).2).vals
  · intro h
    simp only [absOf] at h
    cases hfd : (rowsOf s glb).find?
        (fun r => rowOccupied s r && decide (rowKey? s r = some k)) with
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

/-- **`find` never traps** — an immediate corollary, since `findCorrect`
concludes `.ok`, which is exactly what `NoTrapFind` asks.

checked by: `lake build` -/
theorem noTrapFind : NoTrapFind s := by
  intro m pk k hwf hpk hkty R
  obtain ⟨r, hcall, _⟩ := findCorrect m pk k hwf hpk hkty R
  exact ⟨_, hcall⟩

/-! ## Writing through the returned pointer

`insert` and `erase` both do their work through the pointer `find` handed
back: `_at->f = v`. Resolving that is the write-side counterpart of
`resolve_field`, and the interesting difference is which errors have to be
discharged — a `deref` can fail with `nullDeref` or `useAfterFree`, neither of
which arises for the index-rooted `g[_i].f` form. Both are ruled out here by
the pointer coming from `find`: it points at a live slot of the storage
array. -/

/-- **`p->f` resolves** when `p` holds a pointer to a slot of the storage
array. -/
theorem resolve_ptrField {i : Nat} {row : Value} {f : Ident} {v : Value}
    {ptr : Ident} (R : RepInv s σ.glb)
    (hptr : σ.getLocal ptr
      = some (.ptr ⟨.glob (Schema.names s).storage, [.idx i]⟩))
    (hrow : (rowsOf s σ.glb)[i]? = some row)
    (hfld : row.getStep (.fld f) = some v) :
    resolve σ (ptrField ptr f)
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
  simp only [ptrField, resolve, hptr, Store.readPath, Store.rootVal, hglb,
    bind, Except.bind, List.cons_append, List.nil_append]
  rw [hpath]

/-- **And reading through it gives the field.**

checked by: `lake build` -/
theorem read_ptrField {i : Nat} {row : Value} {f : Ident} {v : Value}
    {ptr : Ident} (R : RepInv s σ.glb)
    (hptr : σ.getLocal ptr
      = some (.ptr ⟨.glob (Schema.names s).storage, [.idx i]⟩))
    (hrow : (rowsOf s σ.glb)[i]? = some row)
    (hfld : row.getStep (.fld f) = some v) :
    evalExpr σ (.rd (ptrField ptr f)) = .ok v := by
  simp only [evalExpr, resolve_ptrField R hptr hrow hfld, bind, Except.bind]
  exact readLoc_field R hrow hfld

/-! ## Writing a slot's field

What a write through `_at->f` does to the storage array, as an equation about
`rowsOf`. This is the shared foundation for `insert` and `erase`: both do
exactly one field write per affected slot, and both then have to argue that
`RepInv` survives it. -/

/-- **A field write updates exactly that slot, and nothing else.**

The frame content — that the rest of the array is untouched and the local
frame is untouched — is what makes the invariant's other clauses survive, and
it comes from `List.set` rather than from any aliasing analysis, because the
path is rooted at a global and resolved.

checked by: `lake build` -/
theorem write_slotField {i : Nat} {row : Value} {fs : List (Ident × Value)}
    {f : Ident} {w : Value} (R : RepInv s σ.glb)
    (hrow : (rowsOf s σ.glb)[i]? = some row)
    (hstrct : row = .strct fs)
    (hfld : (Env.get? fs f).isSome = true) :
    ∃ σ', writeLoc σ (.glb ⟨.glob (Schema.names s).storage, [.idx i, .fld f]⟩) w
            = .ok σ'
      ∧ rowsOf s σ'.glb
          = (rowsOf s σ.glb).set i (.strct (Env.set fs f w))
      ∧ σ'.loc = σ.loc
      ∧ σ'.hp = σ.hp := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  have hlt : i < (rowsOf s σ.glb).length := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hrow; exact h
  subst hstrct
  -- the value the array becomes
  have hset : (Value.arr (rowsOf s σ.glb)).setPath [.idx i, .fld f] w
      = some (.arr ((rowsOf s σ.glb).set i (.strct (Env.set fs f w)))) := by
    show (match (Value.arr (rowsOf s σ.glb)).getStep (.idx i) with
          | none => none
          | some v' =>
            match v'.setPath [.fld f] w with
            | none => none
            | some v'' => (Value.arr (rowsOf s σ.glb)).setStep (.idx i) v'') = _
    rw [show (Value.arr (rowsOf s σ.glb)).getStep (.idx i)
          = some (.strct fs) from by simp only [Value.getStep, hrow]]
    show (match (Value.strct fs).setPath [.fld f] w with
          | none => none
          | some v'' => (Value.arr (rowsOf s σ.glb)).setStep (.idx i) v'') = _
    rw [show (Value.strct fs).setPath [.fld f] w
          = some (.strct (Env.set fs f w)) from by
      show (match (Value.strct fs).getStep (.fld f) with
            | none => none
            | some v' =>
              match v'.setPath [] w with
              | none => none
              | some v'' => (Value.strct fs).setStep (.fld f) v'') = _
      cases hg : Env.get? fs f with
      | none => rw [hg] at hfld; exact absurd hfld (by simp)
      | some x =>
        simp only [Value.getStep, hg, Value.setPath, Value.setStep]
        rw [if_pos (by simp [hg])]]
    simp only [Value.setStep]
    rw [if_pos hlt]
  refine ⟨σ.setRoot (.glob (Schema.names s).storage)
            (.arr ((rowsOf s σ.glb).set i (.strct (Env.set fs f w)))), ?_, ?_, ?_, ?_⟩
  · simp only [writeLoc, Store.writePath, Store.rootVal, hglb, hset]
  · have hget : (σ.glb.set (Schema.names s).storage
        (Value.arr ((rowsOf s σ.glb).set i (.strct (Env.set fs f w))))).get?
        (Schema.names s).storage
        = some (.arr ((rowsOf s σ.glb).set i (.strct (Env.set fs f w)))) := by
      rw [Env.get?_set_self, hglb]; rfl
    show (match (σ.glb.set (Schema.names s).storage
            (Value.arr ((rowsOf s σ.glb).set i (.strct (Env.set fs f w))))).get?
            (Schema.names s).storage with
          | some (.arr vs) => vs
          | _ => []) = _
    rw [hget]
  · rfl
  · rfl

/-! ## Clearing occupancy

What `erase` does to a row. The point of these is that writing the occupancy
flag disturbs **nothing else** about the row — not its key, not its value
fields — which is what makes `RepInv`'s `rows` clause survive and what makes
`absOf` change in exactly the way `Abs.erase` says.

They rest on the schema check's no-`occupied`-collision rule: a field named
`occupied` would make the write clobber a real field instead. That rule has
been in `Schema.check` since Phase 2 and this is the first place it is
*used*. -/

/-- Writing the occupancy flag leaves the key alone. -/
theorem rowKey_set_occupied {fs : List (Ident × Value)} {pk : Schema.Field}
    {w : Value} (hpk : Schema.pkey? s = some pk)
    (hne : pk.name ≠ (Schema.names s).occupied) :
    rowKey? s (.strct (Env.set fs (Schema.names s).occupied w))
      = rowKey? s (.strct fs) := by
  simp [rowKey?, hpk, Env.get?_set_ne _ hne]

/-- And leaves the value fields alone. -/
theorem rowVals_set_occupied {fs : List (Ident × Value)} {w : Value}
    (hne : ∀ f ∈ Schema.valFields s, f.name ≠ (Schema.names s).occupied) :
    rowVals? s (.strct (Env.set fs (Schema.names s).occupied w))
      = rowVals? s (.strct fs) := by
  simp only [rowVals?]
  have key : ∀ (l : List Schema.Field),
      (∀ f ∈ l, f.name ≠ (Schema.names s).occupied) →
      l.mapM (fun f => Env.get? (Env.set fs (Schema.names s).occupied w) f.name)
        = l.mapM (fun f => Env.get? fs f.name) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a as ih =>
      intro h
      simp only [List.mapM_cons, Env.get?_set_ne _ (h a (by simp)),
        ih (fun f hf => h f (List.mem_cons_of_mem a hf))]
  exact key _ hne

/-- The written flag is what the row now reports. -/
theorem rowOccupied_set_occupied {fs : List (Ident × Value)} {b : Bool}
    (hocc : (Env.get? fs (Schema.names s).occupied).isSome = true) :
    rowOccupied s (.strct (Env.set fs (Schema.names s).occupied (.bool b))) = b := by
  simp only [rowOccupied, Env.get?_set_self]
  cases hg : Env.get? fs (Schema.names s).occupied with
  | none => rw [hg] at hocc; exact absurd hocc (by simp)
  | some _ => rfl

/-- **A row stays well formed when its occupancy flag is written.**

checked by: `lake build` -/
theorem rowOk_set_occupied {fs : List (Ident × Value)} {pk : Schema.Field}
    {b : Bool} (hpk : Schema.pkey? s = some pk)
    (hnepk : pk.name ≠ (Schema.names s).occupied)
    (hneval : ∀ f ∈ Schema.valFields s, f.name ≠ (Schema.names s).occupied)
    (hocc : (Env.get? fs (Schema.names s).occupied).isSome = true)
    (h : RowOk s (.strct fs)) :
    RowOk s (.strct (Env.set fs (Schema.names s).occupied (.bool b))) where
  occupied := ⟨b, by
    show Env.get? (Env.set fs (Schema.names s).occupied (.bool b))
        (Schema.names s).occupied = some (.bool b)
    rw [Env.get?_set_self]
    cases hg : Env.get? fs (Schema.names s).occupied with
    | none => rw [hg] at hocc; exact absurd hocc (by simp)
    | some _ => rfl⟩
  key := by rw [rowKey_set_occupied hpk hnepk]; exact h.key
  keyTy := by
    intro pk' k' hpk' hrk
    rw [rowKey_set_occupied hpk hnepk] at hrk
    exact h.keyTy pk' k' hpk' hrk
  vals := by rw [rowVals_set_occupied hneval]; exact h.vals

/-- **The representation invariant survives an erase.**

All four clauses, and they are not equally hard:

- `storage` and `length` are immediate — `List.set` does not change length.
- `rows` is `rowOk_set_occupied` applied pointwise.
- `distinct` is **free**, and worth spelling out why: clearing a flag can only
  *shrink* the occupied set, so any two occupied slots in the new array were
  occupied in the old one, where the invariant already forced them equal. An
  erase cannot create a key collision. This is the clause that will carry real
  content for `insert`, which writes a key rather than clearing a flag.

checked by: `lake build` -/
theorem repInv_clearOccupied {glb glb' : Env} {i : Nat}
    {fs : List (Ident × Value)} {pk : Schema.Field}
    (R : RepInv s glb)
    (hpk : Schema.pkey? s = some pk)
    (hnepk : pk.name ≠ (Schema.names s).occupied)
    (hneval : ∀ f ∈ Schema.valFields s, f.name ≠ (Schema.names s).occupied)
    (hrow : (rowsOf s glb)[i]? = some (.strct fs))
    (hocc : (Env.get? fs (Schema.names s).occupied).isSome = true)
    (hrows : rowsOf s glb'
      = (rowsOf s glb).set i (.strct (Env.set fs (Schema.names s).occupied (.bool false))))
    (hstore : glb'.get? (Schema.names s).storage = some (.arr (rowsOf s glb'))) :
    RepInv s glb' where
  storage := hstore
  length := by rw [hrows, List.length_set]; exact R.length
  rows := by
    intro r hr
    rw [hrows] at hr
    obtain ⟨j, hj, hjr⟩ := List.getElem_of_mem hr
    have hget : ((rowsOf s glb).set i
        (.strct (Env.set fs (Schema.names s).occupied (.bool false))))[j]? = some r := by
      rw [List.getElem?_eq_getElem hj, hjr]
    rw [List.getElem?_set] at hget
    by_cases hij : i = j
    · rw [if_pos hij] at hget
      rw [List.length_set] at hj
      rw [if_pos (show i < (rowsOf s glb).length by omega)] at hget
      cases hget
      exact rowOk_set_occupied hpk hnepk hneval hocc
        (R.rows _ (List.mem_of_getElem? hrow))
    · rw [if_neg hij] at hget
      exact R.rows r (List.mem_of_getElem? hget)
  distinct := by
    intro i' j' ri rj hri hrj hoi hoj hk
    -- a slot reported occupied in the new array cannot be the cleared one
    have hne : ∀ t r, (rowsOf s glb')[t]? = some r → rowOccupied s r = true →
        t ≠ i ∧ (rowsOf s glb)[t]? = some r := by
      intro t r ht hot
      rw [hrows, List.getElem?_set] at ht
      by_cases hit : i = t
      · rw [if_pos hit] at ht
        by_cases hlt : i < (rowsOf s glb).length
        · rw [if_pos hlt] at ht
          cases ht
          rw [rowOccupied_set_occupied hocc] at hot
          exact absurd hot (by simp)
        · rw [if_neg hlt] at ht; exact Option.noConfusion ht
      · rw [if_neg hit] at ht
        exact ⟨fun e => hit e.symm, ht⟩
    obtain ⟨_, hri'⟩ := hne i' ri hri hoi
    obtain ⟨_, hrj'⟩ := hne j' rj hrj hoj
    exact R.distinct i' j' ri rj hri' hrj' hoi hoj hk

/-! ## What an erase does to the abstraction -/

/-- Replacing an element that the predicate already rejected, with another it
also rejects, leaves `find?` alone. -/
theorem find?_set_of_neg {α : Type _} {p : α → Bool} :
    ∀ {l : List α} {i : Nat} {x : α}, p x = false →
      (∀ y, l[i]? = some y → p y = false) → (l.set i x).find? p = l.find? p
  | [], _, _, _, _ => rfl
  | a :: as, 0, x, hx, hi => by
    have ha : ¬ p a = true := by simp [hi a rfl]
    have hx' : ¬ p x = true := by simp [hx]
    show List.find? p (x :: as) = List.find? p (a :: as)
    rw [List.find?_cons_of_neg hx', List.find?_cons_of_neg ha]
  | a :: as, i + 1, x, hx, hi => by
    show List.find? p (a :: as.set i x) = List.find? p (a :: as)
    cases hpa : p a with
    | true => rw [List.find?_cons_of_pos hpa, List.find?_cons_of_pos hpa]
    | false =>
      have hna : ¬ p a = true := by simp [hpa]
      rw [List.find?_cons_of_neg hna, List.find?_cons_of_neg hna]
      exact find?_set_of_neg hx (fun y hy => hi y (by simpa using hy))

/-- **An erase removes exactly that key from the abstraction.**

Two cases, and only one has content. For the erased key, `distinct` does the
work: slot `i` was the *only* occupied slot holding it, so once its flag is
cleared nothing answers for that key. For every other key, nothing that could
have answered moved — slot `i` did not match those keys before the clear
either, since its key was `k`.

checked by: `lake build` -/
theorem absOf_clearOccupied {glb glb' : Env} {i : Nat}
    {fs : List (Ident × Value)} {k : Interface.Key}
    (R : RepInv s glb)
    (hrow : (rowsOf s glb)[i]? = some (.strct fs))
    (hocc : (Env.get? fs (Schema.names s).occupied).isSome = true)
    -- The slot must actually have been occupied. Without this the statement is
    -- false: clearing an empty slot removes nothing, and some *other* slot
    -- could still be answering for `k`.
    (hoccTrue : rowOccupied s (.strct fs) = true)
    (hkey : rowKey? s (.strct fs) = some k)
    (hrows : rowsOf s glb'
      = (rowsOf s glb).set i (.strct (Env.set fs (Schema.names s).occupied (.bool false)))) :
    absOf s glb' = Interface.Abs.erase (absOf s glb) k := by
  funext k'
  have hclr : rowOccupied s
      (.strct (Env.set fs (Schema.names s).occupied (.bool false))) = false :=
    rowOccupied_set_occupied hocc
  simp only [Interface.Abs.erase]
  by_cases hkk : k' = k
  · subst hkk
    have hnone : (rowsOf s glb').find?
        (fun r => rowOccupied s r && decide (rowKey? s r = some k')) = none := by
      rw [hrows]
      refine List.find?_eq_none.mpr ?_
      intro r hr
      obtain ⟨j, hj, hjr⟩ := List.getElem_of_mem hr
      have hget : ((rowsOf s glb).set i
          (.strct (Env.set fs (Schema.names s).occupied (.bool false))))[j]?
            = some r := by rw [List.getElem?_eq_getElem hj, hjr]
      rw [List.getElem?_set] at hget
      by_cases hij : i = j
      · rw [if_pos hij] at hget
        rw [List.length_set] at hj
        rw [if_pos (show i < (rowsOf s glb).length by omega)] at hget
        cases hget
        simp [hclr]
      · rw [if_neg hij] at hget
        intro hp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        exact hij (R.distinct i j (.strct fs) r hrow hget hoccTrue hp.1
          (by rw [hkey, hp.2]))
    simp [absOf, hnone]
  · have hpi : ∀ y, (rowsOf s glb)[i]? = some y →
        (fun r => rowOccupied s r && decide (rowKey? s r = some k')) y = false := by
      intro y hy
      rw [hrow] at hy
      cases hy
      have hne : ¬ (some k = some k') := fun h => hkk (by cases h; rfl)
      simp [hkey, hne]
    have hfind := find?_set_of_neg
      (p := fun r => rowOccupied s r && decide (rowKey? s r = some k'))
      (x := .strct (Env.set fs (Schema.names s).occupied (.bool false)))
      (by simp [hclr]) hpi
    simp only [absOf, hrows, hfind, if_neg hkk]

/-! ## Calling `find` from another generated function

`insert` and `erase` both begin with `_at = <t>_Find(pk);`. That goes through
`execAt`'s `.call` case, which no proof has needed until now: it evaluates the
arguments, builds the callee's frame, runs the body one call-depth down,
**restores the caller's frame**, and writes the result into the destination
local.

The frame restore is the interesting part, and it is sound for the reason
Phase 0 was designed around: no pointer can name a frame, so discarding the
callee's frame wholesale cannot lose anything the caller could observe. -/

/-- **Calling `find` binds `_at` to what `find` returned, and changes nothing
else.**

checked by: `lake build` -/
theorem exec_callFind {p : Program} {d : Nat} {pk : Schema.Field}
    {k : Interface.Key}
    (hlook : lookupFun p (Schema.names s).find = .ok (findDef s pk))
    (hpk : Schema.pkey? s = some pk) (hne : pk.name ≠ tmpI)
    (hkty : k.ty = pk.ty)
    (R : RepInv s σ.glb)
    (hkloc : σ.getLocal pk.name = some k.toValue)
    (hat : (σ.getLocal tmpAt).isSome = true)
    (hcap : s.capacity ≤ (rowsOf s σ.glb).length)
    (hrnd : ∀ j, j < (rowsOf s σ.glb).length → (UInt32.ofNat j).toNat = j) :
    execAt p (execStmt p (d + 1))
        (.call (some tmpAt) (Schema.names s).find [.rd (.var pk.name)]) σ
      = .ok (σ.setLocal tmpAt
              (match firstMatch s σ.glb k 0 s.capacity with
               | some j => .ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩
               | none   => .null), .normal) := by
  have hargs : [Expr.rd (.var pk.name)].mapM (evalExpr σ) = .ok [k.toValue] := by
    simp [List.mapM_cons, read_local hkloc]
    rfl
  -- the callee runs one depth down, which is where `exec_findBody` applies
  obtain ⟨σ', hbody, hmem⟩ :=
    exec_findBody (p := p) (callee := execStmt p d) hpk hne hkty
      (σ := (σ.toMem).toStore [(pk.name, k.toValue), (tmpI, .u32 0)]) R
      (by simp [Mem.toStore, Store.getLocal, Env.get?])
      (by simp [Mem.toStore, Store.getLocal, Env.get?, hne])
      (by simpa using hcap) (by simpa using hrnd)
  simp only [execAt, hlook, hargs, buildFrame_find, bind, Except.bind,
    execStmt, hbody, hmem, Mem.toStore_toMem, Store.toMem_toStore,
    Mem.toStore_glb, Store.toMem_glb]
  cases hg : σ.getLocal tmpAt with
  | none => rw [hg] at hat; exact absurd hat (by simp)
  | some _ => simp only [writeLoc, hg]

/-! ## The `_at != NULL` guard

The test `insert` and `erase` both make on what `find` returned. Two lemmas
rather than one because `evalBin .ne` is defined by cases on the operands, and
the two cases are what the two branches of the generated `if` correspond to. -/

theorem eval_atGuard_ptr {ptr : Ident} {q : Path}
    (hloc : σ.getLocal ptr = some (.ptr q)) :
    evalExpr σ (.bin .ne (.rd (.var ptr)) (nullRow s)) = .ok (.bool true) := by
  simp only [evalExpr, nullRow, bind, Except.bind, evalBin, resolve, hloc,
    readLoc]

theorem eval_atGuard_null {ptr : Ident} (hloc : σ.getLocal ptr = some .null) :
    evalExpr σ (.bin .ne (.rd (.var ptr)) (nullRow s)) = .ok (.bool false) := by
  simp only [evalExpr, nullRow, read_local hloc, bind, Except.bind, evalBin,
    resolve, hloc, readLoc]

/-! ## Still owed

What this file does **not** prove, stated plainly so the gap is not mistaken
for progress:

- `NoTrapInsert` and `NoTrapErase`, and with them `InsertRefines`,
  `EraseRefines` and `RepInvPreserved`.

For `erase` the state content is now done: `repInv_clearOccupied` says the
representation invariant survives clearing a slot's occupancy flag, all four
clauses. What is left for `erase` is:

**Every piece `erase` needs is now proved separately.** Its state content is
`repInv_clearOccupied`, its abstraction content is `absOf_clearOccupied`, its
first statement is `exec_callFind`, and the write it performs is
`write_slotField` through `resolve_ptrField`. What is left is threading them
together through the `if _at != NULL` and the two returns — the same shape as
`exec_findBody`, with no ingredient still missing.

The reading half of the writers is done: `resolve_ptrField` and
`read_ptrField` handle `_at->f` for a pointer that came from `find`, which is
what rules out `nullDeref` and `useAfterFree` — neither of which could arise
for the index-rooted `g[_i].f` form, so they are genuinely new obligations.

`write_slotField` gives the write itself: a field update replaces exactly that
slot and leaves the rest of the array, the frame and the heap alone. The frame
content comes from `List.set`, not from any aliasing analysis, because the
path is rooted at a global and already resolved.

What is left is that `RepInv` survives it. The invariant has four clauses and
they are not equally hard:

- `storage` and `length` are immediate — `List.set` does not change length.
- `rows` needs the written value to keep the row well formed. For `erase`
  (writing `false` to the occupancy flag) that is trivial; for `insert` it
  needs the written field to match its declared type.
- `distinct` is the one with content. Clearing occupancy can only shrink the
  occupied set, so `erase` preserves it for free. `insert` claiming a slot
  writes a *key*, and preserving key-uniqueness is exactly what the
  find-first-then-claim structure exists to guarantee — so that is where the
  real argument lives, and it is the one place `insert` is harder than
  `erase` rather than merely longer.

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

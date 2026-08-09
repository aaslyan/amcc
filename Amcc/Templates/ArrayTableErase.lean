import Amcc.Templates.ArrayTableFind

/-!
# AMCC — `erase`, proved against the semantics

`find` established the technique; this applies it to an operation that
**writes**. The pieces were proved separately in `ArrayTableFind`:

- `exec_callFind` — the `_at = <t>_Find(pk);` the body opens with, including
  the frame save and restore.
- `eval_atGuard_ptr` / `eval_atGuard_null` — the `_at != NULL` test.
- `resolve_ptrField`, `write_slotField` — resolving and performing
  `_at->occupied = false`.
- `repInv_clearOccupied` — the representation invariant survives it.
- `absOf_clearOccupied` — the abstraction moves exactly as `Abs.erase` says.

What is here is the threading, and then the obligations `Simulates` owes for
`erase`.
-/

namespace Templates
namespace ArrayTable

open CSubset

variable {s : Schema} {σ : Store}

/-- One level of `.seq`, so a body can be peeled a statement at a time without
`simp only [execAt]` unfolding every level at once. -/
theorem execAt_seq {p : Program} {callee} (a b : Stmt) (σ : Store) :
    execAt p callee (.seq a b) σ = (do
      match ← execAt p callee a σ with
      | (σ₁, .normal) => execAt p callee b σ₁
      | (σ₁, .ret v)  => .ok (σ₁, .ret v)) := rfl

/-- One level of `.cond`, for the same reason: the guard has to be rewritten
before `evalExpr` is unfolded, or the guard lemma no longer matches. -/
theorem execAt_cond {p : Program} {callee} (c : Expr) (a b : Stmt) (σ : Store) :
    execAt p callee (.cond c a b) σ = (do
      match ← evalExpr σ c with
      | .bool true  => execAt p callee a σ
      | .bool false => execAt p callee b σ
      | _           => .error .typeErr) := rfl

/-- **The body of `erase`.**

Returns `true` exactly when the scan found a slot, clears that slot's
occupancy flag, and leaves the invariant standing with the abstraction moved
by `Abs.erase`.

checked by: `lake build` -/
theorem exec_eraseBody {p : Program} {d : Nat} {pk : Schema.Field}
    {k : Interface.Key}
    (hlook : lookupFun p (Schema.names s).find = .ok (findDef s pk))
    (hpk : Schema.pkey? s = some pk) (hneI : pk.name ≠ tmpI)
    (hkty : k.ty = pk.ty)
    (hnepk : pk.name ≠ (Schema.names s).occupied)
    (hneval : ∀ f ∈ Schema.valFields s, f.name ≠ (Schema.names s).occupied)
    (R : RepInv s σ.glb)
    (hkloc : σ.getLocal pk.name = some k.toValue)
    (hat : (σ.getLocal tmpAt).isSome = true)
    (hcap : s.capacity ≤ (rowsOf s σ.glb).length)
    (hrnd : ∀ j, j < (rowsOf s σ.glb).length → (UInt32.ofNat j).toNat = j) :
    ∃ σ', execAt p (execStmt p (d + 1)) (eraseDef s pk).body σ
        = .ok (σ', .ret (some (.bool (firstMatch s σ.glb k 0 s.capacity).isSome)))
      ∧ RepInv s σ'.glb
      ∧ absOf s σ'.glb = Interface.Abs.erase (absOf s σ.glb) k
      ∧ σ'.hp = σ.hp ∧ σ'.next = σ.next := by
  have hcall := exec_callFind (d := d) hlook hpk hneI hkty R hkloc hat hcap hrnd
  have hv1 : ∀ v : Value, (σ.setLocal tmpAt v).getLocal tmpAt = some v := by
    intro v
    show (σ.loc.set tmpAt v).get? tmpAt = _
    rw [Env.get?_set_self]
    cases hg : σ.loc.get? tmpAt with
    | none => rw [Store.getLocal, hg] at hat; exact absurd hat (by simp)
    | some _ => rfl
  cases hfm : firstMatch s σ.glb k 0 s.capacity with
  | none =>
    rw [hfm] at hcall
    -- the guard is false; the store is never written
    refine ⟨σ.setLocal tmpAt .null, ?_, R, ?_, rfl, rfl⟩
    · simp only [eraseDef, Stmt.block]
      rw [execAt_seq, hcall]
      simp only [bind, Except.bind]
      rw [execAt_seq, Stmt.when, execAt_cond, eval_atGuard_null (hv1 .null)]
      simp only [bind, Except.bind, execAt, evalExpr, Option.isSome]
    · have hiff := firstMatch_isSome_iff (s := s) (glb := σ.glb) (k := k) R
      rw [R.length, hfm] at hiff
      have habs : absOf s σ.glb k = none := by
        cases hab : absOf s σ.glb k with
        | none => rfl
        | some _ =>
          have : (absOf s σ.glb k).isSome = true := by rw [hab]; rfl
          exact absurd (hiff.mpr this) (by simp)
      exact (Interface.Abs.erase_of_absent habs).symm
  | some j =>
    -- slot j is occupied and holds `k`
    have hsm := firstMatch_some (s := s) _ _ _ hfm
    simp only [slotMatches] at hsm
    cases hrow : (rowsOf s σ.glb)[j]? with
    | none => rw [hrow] at hsm; exact absurd hsm (by simp)
    | some r =>
      rw [hrow] at hsm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsm
      have hok : RowOk s r := R.rows r (List.mem_of_getElem? hrow)
      obtain ⟨fs, b, hstrct, hocc, hrocc⟩ := strct_of_rowOk hok
      have hb : b = true := by rw [← hrocc]; exact hsm.1
      subst hb
      subst hstrct
      have hoccS : (Env.get? fs (Schema.names s).occupied).isSome = true := by
        rw [hocc]; rfl
      have hfld : (Value.strct fs).getStep (.fld (Schema.names s).occupied)
          = some (.bool true) := by simpa [Value.getStep] using hocc
      have hptr := hv1 (Value.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩)
      have hres := resolve_ptrField (s := s) (hglb := R.storage)
        (σ := σ.setLocal tmpAt (.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩))
        hptr hrow hfld
      obtain ⟨σ₂, hwr, hrows2, hstore2, hloc2, hhp2, hnx2⟩ := write_slotField (hglb := R.storage)
        (s := s)
        (σ := σ.setLocal tmpAt (.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩))
        (w := .bool false) hrow rfl hoccS
      rw [hfm] at hcall
      refine ⟨σ₂, ?_, ?_, ?_, hhp2, hnx2⟩
      · simp only [eraseDef, Stmt.block]
        rw [execAt_seq, hcall]
        simp only [bind, Except.bind]
        rw [execAt_seq, Stmt.when, execAt_cond, eval_atGuard_ptr hptr]
        simp only [bind, Except.bind, execAt, hres, evalExpr, hwr, Option.isSome]
      · exact repInv_clearOccupied R hpk hnepk hneval hrow hoccS hrows2 hstore2
      · exact absOf_clearOccupied R hrow hoccS hrocc hsm.2 hrows2

/-! ## The obligations

`buildFrame_erase` is the prologue; `call_erase` runs `exec_eraseBody` through
`callFun`, and the two obligations are then read off it. -/

/-- The frame `erase` runs against: the key parameter, then the row pointer
initialised to `NULL`. -/
theorem buildFrame_erase {m : Mem} {pk : Schema.Field} {k : Interface.Key} :
    buildFrame m (eraseDef s pk) [k.toValue]
      = .ok [(pk.name, k.toValue), (tmpAt, .null)] := rfl

/-- Both generated lookups resolve: `find` is emitted first and `erase` third,
and their names differ in their literal suffixes. -/
theorem lookup_erase {pk : Schema.Field} (hpk : Schema.pkey? s = some pk) :
    lookupFun (genC s) (Schema.names s).find = .ok (findDef s pk)
    ∧ lookupFun (genC s) (Schema.names s).erase = .ok (eraseDef s pk) := by
  have hfuns : (genC s).funs = [findDef s pk, insertDef s pk, eraseDef s pk] := by
    simp only [genC, hpk]
  refine ⟨by simp [lookupFun, hfuns, findDef], ?_⟩
  have h1 : ¬ ((findDef s pk).name = (Schema.names s).erase) := by
    simpa [findDef, Schema.names] using
      append_ne (s := s.name) (by decide : "_Find" ≠ "_Remove")
  have h2 : ¬ ((insertDef s pk).name = (Schema.names s).erase) := by
    simpa [insertDef, Schema.names] using
      append_ne (s := s.name) (by decide : "_InsertMaybe" ≠ "_Remove")
  simp [lookupFun, hfuns, h1, h2, eraseDef]

/-- Facts about a well-formed schema that both `erase` obligations consume. -/
theorem erase_facts {pk : Schema.Field} (hwf : Schema.wf s = true)
    (hpk : Schema.pkey? s = some pk) :
    pk.name ≠ tmpI ∧ pk.name ≠ tmpAt
    ∧ pk.name ≠ (Schema.names s).occupied
    ∧ (∀ f ∈ Schema.valFields s, f.name ≠ (Schema.names s).occupied)
    ∧ s.capacity < 4294967296 := by
  have F := facts_of_check (List.isEmpty_iff.mp hwf)
  have hfl := filter_of_pkey hpk
  have hres := F.notReserved pk (pk_mem hfl)
  refine ⟨ne_of_reserved hres (by decide), ne_of_reserved hres (by decide),
    F.notOccupied pk (pk_mem hfl), fun f hf => F.notOccupied f (val_mem hf).1, ?_⟩
  have := F.capLt; simp only [Wf.u32Bound] at this; omega

/-- **What a call to `erase` does.** The single computation both obligations
are read off: it returns whether a slot matched, it preserves `RepInv`, and the
store it leaves behind abstracts to `Abs.erase`.

checked by: `lake build` -/
theorem call_erase {m : Mem} {pk : Schema.Field} {k : Interface.Key}
    (hwf : Schema.wf s = true) (hpk : Schema.pkey? s = some pk)
    (hkty : k.ty = pk.ty) (R : RepInv s m.glb) :
    ∃ m', call s m (Schema.names s).erase [k.toValue]
        = .ok (m', some (.bool (firstMatch s m.glb k 0 s.capacity).isSome))
      ∧ RepInv s m'.glb
      ∧ absOf s m'.glb = Interface.Abs.erase (absOf s m.glb) k := by
  obtain ⟨hneI, hneAt, hnepk, hneval, hcapLt⟩ := erase_facts hwf hpk
  obtain ⟨hlookF, hlookE⟩ := lookup_erase hpk
  have hlen : (rowsOf s m.glb).length = s.capacity := R.length
  have hrnd : ∀ j, j < (rowsOf s m.glb).length → (UInt32.ofNat j).toNat = j := by
    intro j hj
    have hlt : j < 4294967296 := by omega
    simpa [UInt32.toNat_ofNat'] using Nat.mod_eq_of_lt hlt
  have hk0 : (m.toStore [(pk.name, k.toValue), (tmpAt, Value.null)]).getLocal pk.name
      = some k.toValue := by simp [Mem.toStore, Store.getLocal, Env.get?]
  have ha0 : ((m.toStore [(pk.name, k.toValue), (tmpAt, Value.null)]).getLocal
      tmpAt).isSome = true := by
    simp [Mem.toStore, Store.getLocal, Env.get?, hneAt]
  obtain ⟨σ', hbody, R', habs, _, _⟩ :=
    exec_eraseBody (p := genC s) (d := 1) hlookF hpk hneI hkty hnepk hneval
      (σ := m.toStore [(pk.name, k.toValue), (tmpAt, Value.null)]) R hk0 ha0
      (by simp [Mem.toStore_glb, hlen]) (by simp only [Mem.toStore_glb]; exact hrnd)
  have hn : (genC s).funs.length = 2 + 1 := by simp only [genC, hpk]; rfl
  simp only [Mem.toStore_glb] at hbody R' habs
  refine ⟨σ'.toMem, ?_, ?_, ?_⟩
  · simp only [call, callFun, hlookE, buildFrame_erase, bind, Except.bind, hn]
    rw [show execStmt (genC s) (2 + 1)
          = execAt (genC s) (execStmt (genC s) 2) from rfl, hbody]
  · simpa [Store.toMem_glb] using R'
  · simpa [Store.toMem_glb] using habs

/-- **`erase` refines `Abs.erase`.**

checked by: `lake build` -/
theorem eraseRefines : EraseRefines s := by
  intro m m' pk k b hwf hpk hkty R hc
  obtain ⟨m₀, hcall, _, habs⟩ := call_erase hwf hpk hkty R
  rw [hcall] at hc
  obtain ⟨h₁, h₂⟩ := Prod.mk.injEq _ _ _ _ ▸ Except.ok.inj hc
  cases h₁
  have hb : b = (firstMatch s m.glb k 0 s.capacity).isSome := by
    simpa using (Option.some.inj h₂).symm
  have hiff := firstMatch_isSome_iff (s := s) (glb := m.glb) (k := k) R
  rw [R.length] at hiff
  exact ⟨habs, by rw [hb]; exact hiff⟩

/-- **`erase` never traps.**

checked by: `lake build` -/
theorem noTrapErase : NoTrapErase s := by
  intro m pk k hwf hpk hkty R
  obtain ⟨m₀, hcall, _, _⟩ := call_erase hwf hpk hkty R
  exact ⟨_, hcall⟩

/-- **`erase` preserves the representation invariant.**

checked by: `lake build` -/
theorem repInv_erase {m m' : Mem} {pk : Schema.Field} {k : Interface.Key}
    {r : Option Value} (hwf : Schema.wf s = true) (hpk : Schema.pkey? s = some pk)
    (hkty : k.ty = pk.ty) (R : RepInv s m.glb)
    (hc : call s m (Schema.names s).erase [k.toValue] = .ok (m', r)) :
    RepInv s m'.glb := by
  obtain ⟨m₀, hcall, R', _⟩ := call_erase hwf hpk hkty R
  rw [hcall] at hc
  obtain ⟨h₁, _⟩ := Prod.mk.injEq _ _ _ _ ▸ Except.ok.inj hc
  cases h₁; exact R'

end ArrayTable
end Templates

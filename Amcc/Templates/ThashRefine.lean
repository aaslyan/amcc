import Amcc.Dmmeta
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.CSubset.Chain
import Amcc.Templates.Layout
import Amcc.Templates.Thash
import Amcc.Templates.ThashFind

namespace Templates
namespace Thash

open CSubset

/-!
# AMCC —  representation invariant, abstraction, and refinement

This module formalizes:
1. : Name disjointness for hash index field identifiers.
2. : Complete representation invariant over  hash bucket chains in memory.
3. : Abstract interpretation of hash index contents as key-value pairs .
4.  & : Soundness of unique key lookup.
5. : Rejection of elements already marked in-hash.
6. : Rejection of elements carrying duplicate primary keys without modifying memory.
7. : Operational stepping and full 10-clause  preservation for successful insertion.
-/

/-- Distinctness of generated field names for the hash index. -/
structure NamesOk (nm : Names) : Prop where
  nf : nm.next ≠ nm.inhash
  bc : nm.buckets ≠ nm.count

theorem namesOk (dbC fld : Ident) : NamesOk (names dbC fld) where
  nf := append_ne (by decide)
  bc := append_ne (by decide)

/-- Representation invariant for a hash index with  buckets over live rows . -/
structure RepInv (m : Mem) (nm : Names) (elem key : Ident) (mask cap nb : Nat)
    (rows : List Path) (chains : List (List Path)) : Prop where
  /-- Exactly  bucket chains. -/
  nb_len      : chains.length = nb
  /-- Every row in every bucket is among the live rows. -/
  sub         : ∀ b (hb : b < nb), ∀ q ∈ chains[b]' (by rw [nb_len]; exact hb), q ∈ rows
  /-- Live rows are distinct objects in memory. -/
  disj        : RowsDisjoint rows
  /-- Each bucket satisfies the bucket chain invariant. -/
  buckets     : ∀ b (hb : b < nb), BucketInv m nm key b cap (chains[b]' (by rw [nb_len]; exact hb))
  /-- Key hashing: every row in bucket  hashes to . -/
  hash_mod    : ∀ b (hb : b < nb), ∀ q ∈ chains[b]' (by rw [nb_len]; exact hb),
                  ∀ k, readMem m (fldPath q key) = some (.u32 k) →
                    (k &&& UInt32.ofNat mask).toNat = b
  /-- Key uniqueness: rows with identical keys across all buckets must be identical. -/
  keys_unique : ∀ b1 (hb1 : b1 < nb) b2 (hb2 : b2 < nb),
                  ∀ q1 ∈ chains[b1]' (by rw [nb_len]; exact hb1),
                  ∀ q2 ∈ chains[b2]' (by rw [nb_len]; exact hb2),
                  ∀ k, readMem m (fldPath q1 key) = some (.u32 k) →
                       readMem m (fldPath q2 key) = some (.u32 k) →
                       q1 = q2
  /-- The membership flag  marks exactly the rows in the hash table. -/
  flags       : Flagged m nm.inhash rows chains.flatten
  /-- Total count  equals the total number of indexed rows. -/
  count       : readMem m (dbPath nm nm.count) = some (.u32 (UInt32.ofNat chains.flatten.length))
  /-- Every live row has allocated cells for next, inhash, and key fields. -/
  fields      : ∀ q ∈ rows, (readMem m (fldPath q nm.next)).isSome = true
                          ∧ (readMem m (fldPath q nm.inhash)).isSome = true
                          ∧ (readMem m (fldPath q key)).isSome = true
  /-- Container globals do not overlap any element row. -/
  parent      : ∀ q ∈ rows, (∀ b < nb, q.overlaps (bucketPath nm b) = false)
                          ∧ q.overlaps (dbPath nm nm.count) = false

/-- Abstraction of indexed elements as a list of  pairs. -/
def elems (m : Mem) (key : Ident) (chains : List (List Path)) : List (UInt32 × Path) :=
  chains.flatten.filterMap (fun q =>
    match readMem m (fldPath q key) with
    | some (.u32 k) => some (k, q)
    | _ => none)

theorem mem_elems_iff {m : Mem} {key : Ident} {chains : List (List Path)} {k : UInt32} {q : Path} :
    (k, q) ∈ elems m key chains ↔ q ∈ chains.flatten ∧ readMem m (fldPath q key) = some (.u32 k) := by
  simp only [elems, List.mem_filterMap]
  constructor
  · rintro ⟨q', hq', hmatch⟩
    cases hr : readMem m (fldPath q' key) with
    | none => rw [hr] at hmatch; simp at hmatch
    | some v =>
      rw [hr] at hmatch
      cases v with
      | u32 k' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hmatch
        obtain ⟨rfl, rfl⟩ := hmatch
        exact ⟨hq', hr⟩
      | _ => simp at hmatch
  · rintro ⟨hq, hr⟩
    refine ⟨q, hq, ?_⟩
    simp [hr]

theorem firstSat_eq_some_of_mem {P : Path → Bool} {qs : List Path} {q : Path}
    (hq_mem : q ∈ qs)
    (h_P : P q = true)
    (h_nodup : ∀ q' ∈ qs, P q' = true → q' = q) :
    firstSat P qs = some q := by
  induction qs with
  | nil => simp at hq_mem
  | cons x xs ih =>
    simp only [firstSat]
    by_cases hx : P x = true
    · have hxq : x = q := h_nodup x (by simp) hx
      subst hxq
      rw [if_pos h_P]
    · rw [if_neg hx]
      have hx_ne : x ≠ q := by
        intro heq; subst heq; contradiction
      cases hq_mem with
      | head => contradiction
      | tail _ hq_xs =>
        apply ih hq_xs
        intro q' hq' hk'
        exact h_nodup q' (List.mem_cons_of_mem x hq') hk'

theorem firstSat_eq_none_of_forall {P : Path → Bool} {qs : List Path}
    (h : ∀ q ∈ qs, P q = false) :
    firstSat P qs = none := by
  induction qs with
  | nil => rfl
  | cons x xs ih =>
    simp only [firstSat]
    have hx := h x (by simp)
    rw [hx]
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply ih
    intro q hq
    exact h q (List.mem_cons_of_mem x hq)

/-- **Soundness of  hit under **: If ,  returns . -/
theorem find_hit_unique {p : Program} {m : Mem} {nm : Names} {elem key : Ident}
    {mask cap nb : Nat} {k : UInt32} {rows : List Path} {chains : List (List Path)} {q : Path}
    (hlook : lookupFun p nm.find = .ok (findDef nm elem key mask cap))
    (hn : ∃ n, p.funs.length = n + 1)
    (I : RepInv m nm elem key mask cap nb rows chains)
    (h_in : (k, q) ∈ elems m key chains) :
    ∃ (hb : (k &&& UInt32.ofNat mask).toNat < nb),
      callFun p m nm.find [.u32 k] = .ok (m, some (.ptr q))
      ∧ q ∈ chains[(k &&& UInt32.ofNat mask).toNat]' (by rw [I.nb_len]; exact hb)
      ∧ readMem m (fldPath q key) = some (.u32 k) := by
  rw [mem_elems_iff] at h_in
  obtain ⟨hq_flat, hq_key⟩ := h_in
  have h_mem_chains : ∃ b', ∃ (hb' : b' < chains.length), q ∈ chains[b']'hb' := by
    rw [List.mem_flatten] at hq_flat
    obtain ⟨c, hc_mem, hq_c⟩ := hq_flat
    obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hc_mem
    exact ⟨idx, hidx, hq_c⟩
  obtain ⟨b', hb', hq_b'⟩ := h_mem_chains
  have hb'_nb : b' < nb := by rw [← I.nb_len]; exact hb'
  have hb_eq : (k &&& UInt32.ofNat mask).toNat = b' := I.hash_mod b' hb'_nb q hq_b' k hq_key
  have hb : (k &&& UInt32.ofNat mask).toNat < nb := by rw [hb_eq]; exact hb'_nb
  have hq_in_b : q ∈ chains[(k &&& UInt32.ofNat mask).toNat]' (by rw [I.nb_len]; exact hb) := by
    subst hb_eq; exact hq_b'
  refine ⟨hb, ?_⟩
  have B := I.buckets (k &&& UInt32.ofNat mask).toNat hb
  have h_sat : firstSat (keyAt m key k) (chains[(k &&& UInt32.ofNat mask).toNat]' (by rw [I.nb_len]; exact hb)) = some q := by
    apply firstSat_eq_some_of_mem hq_in_b (keyAt_iff.mpr hq_key)
    intro q' hq' hk'
    have hk'_key := keyAt_iff.mp hk'
    exact I.keys_unique ((k &&& UInt32.ofNat mask).toNat) hb ((k &&& UInt32.ofNat mask).toNat) hb q' hq' q hq_in_b k hk'_key hq_key
  have h_hit := find_hit hlook hn B h_sat
  exact ⟨h_hit.1, hq_in_b, hq_key⟩

/-- **Soundness of  miss under **: If  is not in ,  returns . -/
theorem find_miss_unique {p : Program} {m : Mem} {nm : Names} {elem key : Ident}
    {mask cap nb : Nat} {k : UInt32} {rows : List Path} {chains : List (List Path)}
    (hlook : lookupFun p nm.find = .ok (findDef nm elem key mask cap))
    (hn : ∃ n, p.funs.length = n + 1)
    (I : RepInv m nm elem key mask cap nb rows chains)
    (hb : (k &&& UInt32.ofNat mask).toNat < nb)
    (h_not : ∀ q, (k, q) ∉ elems m key chains) :
    callFun p m nm.find [.u32 k] = .ok (m, some .null) := by
  have B := I.buckets (k &&& UInt32.ofNat mask).toNat hb
  have h_sat : firstSat (keyAt m key k) (chains[(k &&& UInt32.ofNat mask).toNat]' (by rw [I.nb_len]; exact hb)) = none := by
    apply firstSat_eq_none_of_forall
    intro q hq
    cases h_bool : keyAt m key k q with
    | false => rfl
    | true =>
      have hk := keyAt_iff.mp h_bool
      have h_flat : q ∈ chains.flatten := by
        rw [List.mem_flatten]
        refine ⟨chains[(k &&& UInt32.ofNat mask).toNat]' (by rw [I.nb_len]; exact hb), ?_, hq⟩
        exact List.getElem_mem (by rw [I.nb_len]; exact hb)
      have h_in_elems : (k, q) ∈ elems m key chains := mem_elems_iff.mpr ⟨h_flat, hk⟩
      exact absurd h_in_elems (h_not q)
  exact (find_miss hlook hn B h_sat).1

theorem buildFrame_insert (m : Mem) (nm : Names) (elem key : Ident) (mask : Nat) (q : Path) :
    buildFrame m (insertDef nm elem key mask) [.ptr q] =
      .ok [(parRow, Value.ptr q), (tmpB, .u32 0), (tmpP, .null)] := rfl

theorem mapM_evalExpr_singleton (σ : Store) (e : Expr) :
    [e].mapM (evalExpr σ) = (do let v ← evalExpr σ e; Except.ok [v]) := rfl

/-- **In-Hash Row Rejection for **: If  is already in the hash,
     returns  and leaves memory unchanged. -/
theorem insert_inlist_reject {p : Program} {m : Mem} {nm : Names} {elem key : Ident}
    {mask cap nb : Nat} {rows : List Path} {chains : List (List Path)} {q : Path}
    (hlook_ins : lookupFun p nm.insert = .ok (insertDef nm elem key mask))
    (hn : ∃ n, p.funs.length = n + 1)
    (I : RepInv m nm elem key mask cap nb rows chains)
    (hq_row : q ∈ rows)
    (hq_in : q ∈ chains.flatten) :
    callFun p m nm.insert [.ptr q] = .ok (m, some (.bool false)) := by
  have h_flag := (I.flags q hq_row).mpr hq_in
  exact insert_noop hlook_ins hn h_flag

/-- **Duplicate Key Rejection for **: If  carries a key  that already
    exists in the index (), executing  returns 
    and leaves the heap/store completely untouched. -/
theorem insert_duplicate_reject {p : Program} {m : Mem} {nm : Names} {elem key : Ident}
    {mask cap nb n : Nat} {k : UInt32} {rows : List Path} {chains : List (List Path)} {q q' : Path}
    (hlook_ins : lookupFun p nm.insert = .ok (insertDef nm elem key mask))
    (hlook_find : lookupFun p nm.find = .ok (findDef nm elem key mask cap))
    (hn : p.funs.length = n + 2)
    (I : RepInv m nm elem key mask cap nb rows chains)
    (hq_key : readMem m (fldPath q key) = some (.u32 k))
    (h_flag : readMem m (fldPath q nm.inhash) = some (.bool false))
    (h_dup : (k, q') ∈ elems m key chains) :
    callFun p m nm.insert [.ptr q] = .ok (m, some (.bool false)) := by
  have hn_pos : ∃ n', p.funs.length = n' + 1 := ⟨n + 1, hn⟩
  obtain ⟨hb, _, hq'_in_b, hq'_key⟩ :=
    find_hit_unique hlook_find hn_pos I h_dup
  have h_sat : firstSat (keyAt m key k) (chains[(k &&& UInt32.ofNat mask).toNat]' (by rw [I.nb_len]; exact hb)) = some q' := by
    apply firstSat_eq_some_of_mem hq'_in_b (keyAt_iff.mpr hq'_key)
    intro q'' hq'' hk''
    exact I.keys_unique _ hb _ hb q'' hq'' q' hq'_in_b k (keyAt_iff.mp hk'') hq'_key
  have B := I.buckets (k &&& UInt32.ofNat mask).toNat hb
  obtain ⟨σ_find, h_find_body, h_find_mem⟩ :=
    exec_findBody (p := p) (n := n) (nm := nm) (elem := elem) (key := key)
      (mask := mask) (cap := cap) (k := k) B
  have h_ptrOf : ptrOf (firstSat (keyAt m key k) (chains[(k &&& UInt32.ofNat mask).toNat]' (by rw [I.nb_len]; exact hb)))
      = Value.ptr q' := by rw [h_sat]; rfl
  rw [h_ptrOf] at h_find_body
  obtain ⟨σ0, hσ0⟩ : ∃ t, t = m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0), (tmpP, Value.null)] := ⟨_, rfl⟩
  have hlocRow : σ0.getLocal parRow = some (.ptr q) := by rw [hσ0]; rfl
  have hr_inhash : σ0.readPath (fldPath q nm.inhash) = some (.bool false) := by
    rw [hσ0, readMem_toStore]; exact h_flag
  have hr_key : σ0.readPath (fldPath q key) = some (.u32 k) := by
    rw [hσ0, readMem_toStore]; exact hq_key
  have hbody : execAt p (execStmt p (n + 1)) (insertDef nm elem key mask).body σ0
      = .ok (σ0.setLocal tmpP (.ptr q'), .ret (some (.bool false))) := by
    simp only [insertDef, Stmt.block, Stmt.when]
    rw [execAt_seq']
    have hguard1 : evalExpr σ0 (.un .lnot (.rd (ptrFld parRow nm.inhash))) = .ok (.bool true) := by
      simp only [evalExpr, resolve_ptrFld hlocRow hr_inhash, readLoc, hr_inhash, bind, Except.bind, evalUn]
      rfl
    rw [execAt_cond', hguard1]
    simp only [bind, Except.bind]
    rw [execAt_seq']
    have harg : evalExpr σ0 (.rd (ptrFld parRow key)) = .ok (.u32 k) := by
      simp only [evalExpr, resolve_ptrFld hlocRow hr_key, readLoc, hr_key, bind, Except.bind]
    have h_call_step : execAt p (execStmt p (n + 1)) (.call (some tmpP) nm.find [.rd (ptrFld parRow key)]) σ0
        = .ok (σ0.setLocal tmpP (.ptr q'), .normal) := by
      simp only [execAt, hlook_find]
      rw [mapM_evalExpr_singleton, harg]
      simp only [bind, Except.bind]
      rw [show buildFrame σ0.toMem (findDef nm elem key mask cap) [Value.u32 k]
            = .ok [(parKey, .u32 k), (tmpB, .u32 0), (tmpP, .null), (tmpHit, .null), (tmpI, .u32 0)] from rfl]
      dsimp only
      have h_σ0_toMem : σ0.toMem = m := by rw [hσ0]; rfl
      rw [h_σ0_toMem]
      rw [show execStmt p (n + 1) (findDef nm elem key mask cap).body
              (m.toStore [(parKey, Value.u32 k), (tmpB, .u32 0), (tmpP, .null), (tmpHit, .null), (tmpI, .u32 0)])
            = execAt p (execStmt p n) (findDef nm elem key mask cap).body
              (m.toStore [(parKey, Value.u32 k), (tmpB, .u32 0), (tmpP, .null), (tmpHit, .null), (tmpI, .u32 0)]) from rfl]
      rw [h_find_body]
      dsimp only
      have h_restore : σ_find.toMem.toStore σ0.loc = σ0 := by
        rw [h_find_mem, hσ0]; rfl
      rw [h_restore]
      rw [hσ0]
      rfl
    rw [h_call_step]
    simp only [bind, Except.bind]
    have h_locP : (σ0.setLocal tmpP (.ptr q')).getLocal tmpP = some (.ptr q') := by
      exact getLocal_setLocal_self (by rw [hσ0]; rfl)
    have h_guard2 : evalExpr (σ0.setLocal tmpP (.ptr q')) (.bin .eq (.rd (.var tmpP)) (.null (.strct elem)))
        = .ok (.bool false) := by
      show (do
        let v1 ← evalExpr (σ0.setLocal tmpP (.ptr q')) (.rd (.var tmpP))
        let v2 ← evalExpr (σ0.setLocal tmpP (.ptr q')) (.null (.strct elem))
        evalBin .eq v1 v2) = _
      rw [read_local' h_locP]
      rfl
    rw [execAt_cond', h_guard2]
    simp only [bind, Except.bind]
    rfl
  have hframe := buildFrame_insert m nm elem key mask q
  have hcall := callFun_ret (p := p) (m := m) (fd := insertDef nm elem key mask)
    (args := [Value.ptr q]) hlook_ins hn hframe (by rw [← hσ0]; exact hbody)
  have h_toMem : (σ0.setLocal tmpP (.ptr q')).toMem = m := by
    rw [Store.setLocal_toMem]; rw [hσ0]; rfl
  rw [h_toMem] at hcall
  exact hcall

theorem exec_assign_path {p : Program} {callee} {σ : Store} {l : LVal} {pa : Path}
    {e : Expr} {v w : Value}
    (hres : resolve σ l = .ok (.glb pa)) (he : evalExpr σ e = .ok w)
    (hread : σ.readPath pa = some v) :
    ∃ σ', execAt p callee (.assign l e) σ = .ok (σ', .normal)
      ∧ σ.writePath pa w = some σ' := by
  obtain ⟨σ', hw⟩ := Store.writePath_isSome (w := w) hread
  exact ⟨σ', by simp only [execAt, hres, he, writeLoc, hw, bind, Except.bind], hw⟩

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

theorem step_bucket {p : Program} {callee} {σ : Store} {nm : Names} {i : Ident} {b : Nat}
    {e : Expr} {w v : Value}
    (hloc : σ.getLocal i = some (.u32 (UInt32.ofNat b)))
    (hround : (UInt32.ofNat b).toNat = b)
    (hread : σ.readPath (bucketPath nm b) = some v)
    (he : evalExpr σ e = .ok w) :
    ∃ σ', execAt p callee (.assign (bucket nm i) e) σ = .ok (σ', .normal)
      ∧ σ'.loc = σ.loc
      ∧ σ'.readPath (bucketPath nm b) = some w
      ∧ ∀ r, (bucketPath nm b).overlaps r = false → σ'.readPath r = σ.readPath r := by
  have hres := resolve_bucket hloc hround hread
  obtain ⟨σ', hex, hw⟩ := exec_assign_path (p := p) (callee := callee)
    hres he hread
  exact ⟨σ', hex, Store.writePath_loc hw, Store.readPath_writePath_self hw,
    fun r hr => Store.readPath_writePath_disjoint hw hr⟩

theorem bucketPath_disjoint_count {nm : Names} (hno : NamesOk nm) (b : Nat) :
    (bucketPath nm b).overlaps (dbPath nm nm.count) = false := by
  have hne1 : (PathStep.fld nm.buckets == PathStep.fld nm.count) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro e; injection e with e; exact hno.bc e
  have hne2 : (PathStep.fld nm.count == PathStep.fld nm.buckets) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro e; injection e with e; exact (Ne.symm hno.bc) e
  simp only [Path.overlaps, bucketPath, dbPath, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · simp [List.isPrefixOf, hne1]
  · simp [List.isPrefixOf, hne2]

theorem bucketPath_ne_disjoint {nm : Names} {b1 b2 : Nat} (h : b1 ≠ b2) :
    (bucketPath nm b1).overlaps (bucketPath nm b2) = false := by
  have hne1 : (PathStep.idx b1 == PathStep.idx b2) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro e; injection e with e; exact h e
  have hne2 : (PathStep.idx b2 == PathStep.idx b1) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro e; injection e with e; exact (Ne.symm h) e
  simp only [Path.overlaps, bucketPath, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · simp [List.isPrefixOf, hne1]
  · simp [List.isPrefixOf, hne2]

theorem row_fld_disjoint_bucket {m : Mem} {nm : Names} {elem key : Ident} {mask cap nb : Nat}
    {rows : List Path} {chains : List (List Path)}
    (I : RepInv m nm elem key mask cap nb rows chains)
    {r : Path} (hr : r ∈ rows) (x : Ident) {b : Nat} (hb : b < nb) :
    (fldPath r x).overlaps (bucketPath nm b) = false :=
  overlaps_ext ((I.parent r hr).1 b hb)

theorem row_fld_disjoint_count {m : Mem} {nm : Names} {elem key : Ident} {mask cap nb : Nat}
    {rows : List Path} {chains : List (List Path)}
    (I : RepInv m nm elem key mask cap nb rows chains)
    {r : Path} (hr : r ∈ rows) (x : Ident) :
    (fldPath r x).overlaps (dbPath nm nm.count) = false :=
  overlaps_ext (I.parent r hr).2

theorem row_disjoint_row {m : Mem} {nm : Names} {elem key : Ident} {mask cap nb : Nat}
    {rows : List Path} {chains : List (List Path)}
    (I : RepInv m nm elem key mask cap nb rows chains)
    {r1 r2 : Path} (hr1 : r1 ∈ rows) (hr2 : r2 ∈ rows) (hne : r1 ≠ r2) (x y : Ident) :
    (fldPath r1 x).overlaps (fldPath r2 y) = false :=
  fldPath_disjoint (I.disj r1 hr1 r2 hr2 hne)

theorem mem_flatten_set_cons {α : Type _} {chains : List (List α)} {b : Nat} {q : α}
    (hb : b < chains.length) (r : α) :
    r ∈ (chains.set b (q :: chains[b])).flatten ↔ r = q ∨ r ∈ chains.flatten := by
  constructor
  · intro h
    rw [List.mem_flatten] at h
    obtain ⟨c, hc_mem, hr_c⟩ := h
    obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hc_mem
    have hidx_orig : idx < chains.length := by
      have : (chains.set b (q :: chains[b])).length = chains.length := List.length_set
      rw [this] at hidx
      exact hidx
    by_cases heq : idx = b
    · cases heq
      have h_get : (chains.set b (q :: chains[b]))[b] = q :: chains[b] :=
        List.getElem_set_self (by rw [List.length_set]; exact hb)
      rw [h_get] at hr_c
      cases hr_c with
      | head => exact Or.inl rfl
      | tail _ hr_tail =>
        refine Or.inr ?_
        rw [List.mem_flatten]
        refine ⟨chains[b], List.getElem_mem hb, hr_tail⟩
    · have h_get : (chains.set b (q :: chains[b]))[idx] = chains[idx]'hidx_orig :=
        List.getElem_set_ne (Ne.symm heq) hidx
      rw [h_get] at hr_c
      refine Or.inr ?_
      rw [List.mem_flatten]
      refine ⟨chains[idx], List.getElem_mem hidx_orig, hr_c⟩
  · intro hr
    cases hr with
    | inl hr_eq =>
      rw [hr_eq, List.mem_flatten]
      have h_len : b < (chains.set b (q :: chains[b])).length := by
        rw [List.length_set]; exact hb
      have h_get := List.getElem_set_self (l := chains) (i := b) (a := q :: chains[b]) h_len
      have h_mem := List.getElem_mem h_len
      rw [h_get] at h_mem
      refine ⟨q :: chains[b], h_mem, by simp⟩
    | inr h =>
      rw [List.mem_flatten] at h ⊢
      obtain ⟨c, hc_mem, hr_c⟩ := h
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hc_mem
      by_cases heq : idx = b
      · cases heq
        have h_len : b < (chains.set b (q :: chains[b])).length := by
          rw [List.length_set]; exact hb
        have h_get := List.getElem_set_self (l := chains) (i := b) (a := q :: chains[b]) h_len
        have h_mem := List.getElem_mem h_len
        rw [h_get] at h_mem
        refine ⟨q :: chains[b], h_mem, by simp [hr_c]⟩
      · have h_len : idx < (chains.set b (q :: chains[b])).length := by
          rw [List.length_set]; exact hidx
        have h_get := List.getElem_set_ne (Ne.symm heq) (a := q :: chains[b]) h_len
        have h_mem := List.getElem_mem h_len
        rw [h_get] at h_mem
        refine ⟨chains[idx], h_mem, hr_c⟩

theorem length_flatten_set_cons {α : Type _} : ∀ {chains : List (List α)} {b : Nat} {q : α},
    (hb : b < chains.length) →
    (chains.set b (q :: chains[b])).flatten.length = chains.flatten.length + 1
  | [], b, q, hb => by simp at hb
  | c :: cs, 0, q, hb => by
    simp only [List.set, List.getElem_cons_zero, List.flatten_cons, List.length_append, List.length_cons]
    omega
  | c :: cs, b + 1, q, hb => by
    have hb' : b < cs.length := by simp at hb; omega
    have h_get : (c :: cs)[b + 1] = cs[b] := rfl
    have h_set : (c :: cs).set (b + 1) (q :: (c :: cs)[b + 1]) = c :: cs.set b (q :: cs[b]) := rfl
    rw [h_set]
    simp only [List.flatten_cons, List.length_append]
    rw [length_flatten_set_cons hb']
    omega

/-- **Successful Insertion for **: If  is a valid row not yet in the index,
    its key  is fresh, and bucket  has remaining capacity, then
     succeeds (returns ), correctly links  at the head of bucket ,
    sets  to , increments count, and preserves  for the updated chains. -/
theorem insert_success {p : Program} {m : Mem} {nm : Names} {elem key : Ident}
    {mask cap nb n : Nat} {k : UInt32} {rows : List Path} {chains : List (List Path)} {q : Path}
    (hlook_ins : lookupFun p nm.insert = .ok (insertDef nm elem key mask))
    (hlook_find : lookupFun p nm.find = .ok (findDef nm elem key mask cap))
    (hn : p.funs.length = n + 2)
    (hno : NamesOk nm)
    (hkey_next : key ≠ nm.next)
    (hkey_inhash : key ≠ nm.inhash)
    (I : RepInv m nm elem key mask cap nb rows chains)
    (hq_row : q ∈ rows)
    (hq_not_in : q ∉ chains.flatten)
    (h_flag : readMem m (fldPath q nm.inhash) = some (.bool false))
    (hq_key : readMem m (fldPath q key) = some (.u32 k))
    (hb : (k &&& UInt32.ofNat mask).toNat < nb)
    (hfits : (chains[(k &&& UInt32.ofNat mask).toNat]' (by rw [I.nb_len]; exact hb)).length < cap)
    (h_fresh : ∀ q', (k, q') ∉ elems m key chains) :
    ∃ m', callFun p m nm.insert [.ptr q] = .ok (m', some (.bool true))
      ∧ RepInv m' nm elem key mask cap nb rows
          (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'(by rw [I.nb_len]; exact hb)))
      ∧ readMem m' (fldPath q nm.inhash) = some (.bool true)
      ∧ readMem m' (fldPath q nm.next) = some (headOf (chains[(k &&& UInt32.ofNat mask).toNat]'(by rw [I.nb_len]; exact hb)))
      ∧ readMem m' (bucketPath nm (k &&& UInt32.ofNat mask).toNat) = some (.ptr q)
      ∧ readMem m' (dbPath nm nm.count) = some (.u32 (UInt32.ofNat (chains.flatten.length + 1))) := by
  have hn_pos : ∃ n', p.funs.length = n' + 1 := ⟨n + 1, hn⟩
  have hb_len : (k &&& UInt32.ofNat mask).toNat < chains.length := by rw [I.nb_len]; exact hb
  have B := I.buckets (k &&& UInt32.ofNat mask).toNat hb
  have h_sat : firstSat (keyAt m key k) (chains[(k &&& UInt32.ofNat mask).toNat]'hb_len) = none := by
    apply firstSat_eq_none_of_forall
    intro q' hq'
    cases h_bool : keyAt m key k q' with
    | false => rfl
    | true =>
      have hk' := keyAt_iff.mp h_bool
      have h_flat : q' ∈ chains.flatten := by
        rw [List.mem_flatten]
        refine ⟨chains[(k &&& UInt32.ofNat mask).toNat]'hb_len, List.getElem_mem hb_len, hq'⟩
      have h_in_elems : (k, q') ∈ elems m key chains := mem_elems_iff.mpr ⟨h_flat, hk'⟩
      exact absurd h_in_elems (h_fresh q')
  obtain ⟨σ_find, h_find_body, h_find_mem⟩ :=
    exec_findBody (p := p) (n := n) (nm := nm) (elem := elem) (key := key)
      (mask := mask) (cap := cap) (k := k) B
  rw [h_sat] at h_find_body
  have h_ptrOf : ptrOf none = Value.null := rfl
  rw [h_ptrOf] at h_find_body
  obtain ⟨σ0, hσ0⟩ : ∃ t, t = m.toStore [(parRow, Value.ptr q), (tmpB, .u32 0), (tmpP, Value.null)] := ⟨_, rfl⟩
  have hlocRow : σ0.getLocal parRow = some (.ptr q) := by rw [hσ0]; rfl
  have hr_inhash : σ0.readPath (fldPath q nm.inhash) = some (.bool false) := by
    rw [hσ0, readMem_toStore]; exact h_flag
  have hr_key : σ0.readPath (fldPath q key) = some (.u32 k) := by
    rw [hσ0, readMem_toStore]; exact hq_key

  have dNF : (fldPath q nm.next).overlaps (fldPath q nm.inhash) = false :=
    fldPath_ne_disjoint hno.nf
  have dNB : (fldPath q nm.next).overlaps (bucketPath nm (k &&& UInt32.ofNat mask).toNat) = false :=
    row_fld_disjoint_bucket I hq_row nm.next hb
  have dNC : (fldPath q nm.next).overlaps (dbPath nm nm.count) = false :=
    row_fld_disjoint_count I hq_row nm.next
  have dFB : (fldPath q nm.inhash).overlaps (bucketPath nm (k &&& UInt32.ofNat mask).toNat) = false :=
    row_fld_disjoint_bucket I hq_row nm.inhash hb
  have dFC : (fldPath q nm.inhash).overlaps (dbPath nm nm.count) = false :=
    row_fld_disjoint_count I hq_row nm.inhash
  have dBC : (bucketPath nm (k &&& UInt32.ofNat mask).toNat).overlaps (dbPath nm nm.count) = false :=
    bucketPath_disjoint_count hno _

  have dNK : (fldPath q nm.next).overlaps (fldPath q key) = false :=
    fldPath_ne_disjoint (Ne.symm hkey_next)
  have dFK : (fldPath q nm.inhash).overlaps (fldPath q key) = false :=
    fldPath_ne_disjoint (Ne.symm hkey_inhash)
  have dBK : (bucketPath nm (k &&& UInt32.ofNat mask).toNat).overlaps (fldPath q key) = false := by
    rw [overlaps_symm]; exact row_fld_disjoint_bucket I hq_row key hb
  have dCK : (dbPath nm nm.count).overlaps (fldPath q key) = false := by
    rw [overlaps_symm]; exact row_fld_disjoint_count I hq_row key

  obtain ⟨nv, hq_next_val⟩ : ∃ v, σ0.readPath (fldPath q nm.next) = some v := by
    have h := (I.fields q hq_row).1
    rw [← readMem_toStore m [(parRow, Value.ptr q), (tmpB, .u32 0), (tmpP, Value.null)]] at h
    rw [← hσ0] at h
    exact Option.isSome_iff_exists.mp h

  have hguard1 : evalExpr σ0 (.un .lnot (.rd (ptrFld parRow nm.inhash))) = .ok (.bool true) := by
    simp only [evalExpr, resolve_ptrFld hlocRow hr_inhash, readLoc, hr_inhash, bind, Except.bind, evalUn]
    rfl
  have harg : evalExpr σ0 (.rd (ptrFld parRow key)) = .ok (.u32 k) := by
    simp only [evalExpr, resolve_ptrFld hlocRow hr_key, readLoc, hr_key, bind, Except.bind]
  have h_call_step : execAt p (execStmt p (n + 1)) (.call (some tmpP) nm.find [.rd (ptrFld parRow key)]) σ0
      = .ok (σ0, .normal) := by
    simp only [execAt, hlook_find]
    rw [mapM_evalExpr_singleton, harg]
    simp only [bind, Except.bind]
    rw [show buildFrame σ0.toMem (findDef nm elem key mask cap) [Value.u32 k]
          = .ok [(parKey, .u32 k), (tmpB, .u32 0), (tmpP, .null), (tmpHit, .null), (tmpI, .u32 0)] from rfl]
    dsimp only
    have h_σ0_toMem : σ0.toMem = m := by rw [hσ0]; rfl
    rw [h_σ0_toMem]
    rw [show execStmt p (n + 1) (findDef nm elem key mask cap).body
            (m.toStore [(parKey, Value.u32 k), (tmpB, .u32 0), (tmpP, .null), (tmpHit, .null), (tmpI, .u32 0)])
          = execAt p (execStmt p n) (findDef nm elem key mask cap).body
            (m.toStore [(parKey, Value.u32 k), (tmpB, .u32 0), (tmpP, .null), (tmpHit, .null), (tmpI, .u32 0)]) from rfl]
    rw [h_find_body]
    dsimp only
    have h_restore : σ_find.toMem.toStore σ0.loc = σ0 := by
      rw [h_find_mem, hσ0]; rfl
    rw [h_restore]
    rw [hσ0]
    rfl

  have h_locP : σ0.getLocal tmpP = some .null := by rw [hσ0]; rfl
  have h_guard2 : evalExpr σ0 (.bin .eq (.rd (.var tmpP)) (.null (.strct elem))) = .ok (.bool true) := by
    show (do
      let v1 ← evalExpr σ0 (.rd (.var tmpP))
      let v2 ← evalExpr σ0 (.null (.strct elem))
      evalBin .eq v1 v2) = _
    rw [read_local' h_locP]
    rfl

  -- Inner block assignments:
  -- S1: 
  obtain ⟨σ1, hσ1⟩ : ∃ t, t = σ0.setLocal tmpB (.u32 (k &&& UInt32.ofNat mask)) := ⟨_, rfl⟩
  have he_b : evalExpr σ0 (.bin .band (.rd (ptrFld parRow key)) (.lit (.u32 (UInt32.ofNat mask))))
      = .ok (.u32 (k &&& UInt32.ofNat mask)) := by
    simp only [evalExpr, resolve_ptrFld hlocRow hr_key, readLoc, hr_key, bind, Except.bind, evalBin]
  have hS1 : execAt p (execStmt p (n + 1))
      (.assign (.var tmpB) (.bin .band (.rd (ptrFld parRow key)) (.lit (.u32 (UInt32.ofNat mask))))) σ0
      = .ok (σ1, .normal) := by
    rw [hσ1]; exact step_local (by rw [hσ0]; rfl) he_b

  have hl1row : σ1.getLocal parRow = some (.ptr q) := by
    rw [hσ1, getLocal_setLocal_ne (by decide)]; exact hlocRow
  have hl1b : σ1.getLocal tmpB = some (.u32 (k &&& UInt32.ofNat mask)) := by
    rw [hσ1]; exact getLocal_setLocal_self (by rw [hσ0]; rfl)
  have hr1 : ∀ pth, σ1.readPath pth = σ0.readPath pth := by
    intro pth; rw [hσ1]; exact readPath_setLocal _ _ _ _

  have hround : (UInt32.ofNat (k &&& UInt32.ofNat mask).toNat).toNat = (k &&& UInt32.ofNat mask).toNat := by
    rw [UInt32.ofNat_toNat]
  have hr1_bkt : σ1.readPath (bucketPath nm (k &&& UInt32.ofNat mask).toNat) = some (headOf (chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)) := by
    rw [hr1, hσ0, readMem_toStore]; exact (I.buckets (k &&& UInt32.ofNat mask).toNat hb).head
  have hl1b_ofNat : σ1.getLocal tmpB = some (.u32 (UInt32.ofNat (k &&& UInt32.ofNat mask).toNat)) := by
    rw [UInt32.ofNat_toNat]; exact hl1b
  have he_bkt : evalExpr σ1 (.rd (bucket nm tmpB)) = .ok (headOf (chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)) :=
    read_bucket hl1b_ofNat hround hr1_bkt

  -- S2: 
  obtain ⟨σ2, hS2, hl2, hw2, hf2⟩ := step_ptr (p := p) (callee := execStmt p (n + 1))
    (x := nm.next) (e := .rd (bucket nm tmpB)) (w := headOf (chains[(k &&& UInt32.ofNat mask).toNat]'hb_len))
    hl1row (by rw [hr1]; exact hq_next_val) he_bkt
  have hl2row : σ2.getLocal parRow = some (.ptr q) := by simp only [Store.getLocal, hl2]; exact hl1row
  have hl2b : σ2.getLocal tmpB = some (.u32 (k &&& UInt32.ofNat mask)) := by simp only [Store.getLocal, hl2]; exact hl1b

  -- S3: 
  obtain ⟨σ3, hS3, hl3, hw3, hf3⟩ := step_ptr (p := p) (callee := execStmt p (n + 1))
    (x := nm.inhash) (e := .lit (.bool true)) (w := .bool true)
    hl2row (by rw [hf2 _ dNF, hr1]; exact hr_inhash) rfl
  have hl3row : σ3.getLocal parRow = some (.ptr q) := by simp only [Store.getLocal, hl3]; exact hl2row
  have hl3b : σ3.getLocal tmpB = some (.u32 (k &&& UInt32.ofNat mask)) := by simp only [Store.getLocal, hl3]; exact hl2b

  -- S4: 
  have hr3_bkt : σ3.readPath (bucketPath nm (k &&& UInt32.ofNat mask).toNat) = some (headOf (chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)) := by
    rw [hf3 _ dFB,
        hf2 _ dNB,
        hr1_bkt]
  have hl3b_nat : σ3.getLocal tmpB = some (.u32 (UInt32.ofNat (k &&& UInt32.ofNat mask).toNat)) := by
    rw [UInt32.ofNat_toNat]; exact hl3b
  obtain ⟨σ4, hS4, hl4, hw4, hf4⟩ := step_bucket (p := p) (callee := execStmt p (n + 1))
    (nm := nm) (i := tmpB) (b := (k &&& UInt32.ofNat mask).toNat)
    (e := .rd (.var parRow)) (w := .ptr q)
    hl3b_nat hround hr3_bkt (read_local' hl3row)
  have hl4row : σ4.getLocal parRow = some (.ptr q) := by simp only [Store.getLocal, hl4]; exact hl3row
  have hl4b : σ4.getLocal tmpB = some (.u32 (k &&& UInt32.ofNat mask)) := by simp only [Store.getLocal, hl4]; exact hl3b

  -- S5: 
  have hr4_cnt : σ4.readPath (dbPath nm nm.count) = some (.u32 (UInt32.ofNat chains.flatten.length)) := by
    rw [hf4 _ dBC,
        hf3 _ dFC,
        hf2 _ dNC,
        hr1, hσ0, readMem_toStore]
    exact I.count
  have he_cnt : evalExpr σ4 (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
      = .ok (.u32 (UInt32.ofNat (chains.flatten.length + 1))) := by
    simp only [evalExpr, resolve_dbFld hr4_cnt, readLoc, hr4_cnt, bind, Except.bind, evalBin]
    show Except.ok (Value.u32 (UInt32.ofNat chains.flatten.length + 1)) = Except.ok (Value.u32 (UInt32.ofNat (chains.flatten.length + 1)))
    simp only [UInt32.ofNat_add]
    rfl
  obtain ⟨σ5, hS5, hl5, hw5, hf5⟩ := step_db (p := p) (callee := execStmt p (n + 1))
    (nm := nm) (x := nm.count)
    (e := .bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
    (w := .u32 (UInt32.ofNat (chains.flatten.length + 1)))
    hr4_cnt he_cnt

  -- Block execution assembly:
  have hbody : execAt p (execStmt p (n + 1)) (insertDef nm elem key mask).body σ0
      = .ok (σ5, .ret (some (.bool true))) := by
    simp only [insertDef, Stmt.block, Stmt.when]
    rw [execAt_seq']
    have h_when1 : execAt p (execStmt p (n + 1))
        (.cond (.un .lnot (.rd (ptrFld parRow nm.inhash)))
          ((Stmt.call (some tmpP) nm.find [Expr.rd (ptrFld parRow key)]).seq
            (Stmt.cond (Expr.bin BinOp.eq (Expr.rd (LVal.var tmpP)) (Expr.null (Ty.strct elem)))
              ((Stmt.assign (LVal.var tmpB)
                    (Expr.bin BinOp.band (Expr.rd (ptrFld parRow key)) (Expr.lit (Lit.u32 (UInt32.ofNat mask))))).seq
                ((Stmt.assign (ptrFld parRow nm.next) (Expr.rd (bucket nm tmpB))).seq
                  ((Stmt.assign (ptrFld parRow nm.inhash) (Expr.lit (Lit.bool true))).seq
                    ((Stmt.assign (bucket nm tmpB) (Expr.rd (LVal.var parRow))).seq
                      ((Stmt.assign (dbFld nm nm.count)
                            (Expr.bin BinOp.add (Expr.rd (dbFld nm nm.count)) (Expr.lit (Lit.u32 1)))).seq
                        (Stmt.ret (some (Expr.lit (Lit.bool true)))))))))
              Stmt.skip))
          Stmt.skip) σ0 = .ok (σ5, .ret (some (.bool true))) := by
      rw [execAt_cond', hguard1]
      simp only [bind, Except.bind]
      rw [execAt_seq', h_call_step]
      simp only [bind, Except.bind]
      rw [execAt_cond', h_guard2]
      simp only [bind, Except.bind]
      rw [execAt_seq', hS1]
      simp only [bind, Except.bind]
      rw [execAt_seq', hS2]
      simp only [bind, Except.bind]
      rw [execAt_seq', hS3]
      simp only [bind, Except.bind]
      rw [execAt_seq', hS4]
      simp only [bind, Except.bind]
      rw [execAt_seq', hS5]
      simp only [bind, Except.bind]
      rfl
    rw [h_when1]
    rfl

  have hframe := buildFrame_insert m nm elem key mask q
  have hcall := callFun_ret (p := p) (m := m) (fd := insertDef nm elem key mask)
    (args := [Value.ptr q]) hlook_ins hn hframe (by rw [← hσ0]; exact hbody)

  have h_unch_fld : ∀ r ∈ rows, r ≠ q → ∀ x, readMem σ5.toMem (fldPath r x) = readMem m (fldPath r x) := by
    intro r hr hne x
    rw [readMem_toMem,
        hf5 _ (by rw [overlaps_symm]; exact row_fld_disjoint_count I hr x),
        hf4 _ (by rw [overlaps_symm]; exact row_fld_disjoint_bucket I hr x hb),
        hf3 _ (row_disjoint_row I hq_row hr (Ne.symm hne) nm.inhash x),
        hf2 _ (row_disjoint_row I hq_row hr (Ne.symm hne) nm.next x),
        hr1, hσ0, readMem_toStore]

  have h_unch_key : ∀ r ∈ rows, readMem σ5.toMem (fldPath r key) = readMem m (fldPath r key) := by
    intro r hr
    by_cases hrq : r = q
    · cases hrq
      rw [readMem_toMem,
          hf5 _ dCK,
          hf4 _ dBK,
          hf3 _ dFK,
          hf2 _ dNK,
          hr1, hσ0, readMem_toStore]
    · exact h_unch_fld r hr hrq key

  have hRep : RepInv σ5.toMem nm elem key mask cap nb rows
      (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)) := {
    nb_len := List.length_set.trans I.nb_len
    sub := by
      intro b' hb' r hr
      have hb'_len : b' < (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).length := by
        rw [List.length_set, I.nb_len]; exact hb'
      by_cases hb_eq : b' = (k &&& UInt32.ofNat mask).toNat
      · cases hb_eq
        have h_get : (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len))[(k &&& UInt32.ofNat mask).toNat]'hb'_len
            = q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len :=
          List.getElem_set_self (by rw [List.length_set]; exact hb_len)
        rw [h_get] at hr
        cases hr with
        | head => exact hq_row
        | tail _ hr_tail => exact I.sub _ hb _ hr_tail
      · have h_get : (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len))[b']'hb'_len
            = chains[b']'(by rw [I.nb_len]; exact hb') :=
          List.getElem_set_ne (Ne.symm hb_eq) (by rw [List.length_set, I.nb_len]; exact hb')
        rw [h_get] at hr
        exact I.sub b' hb' r hr
    disj := I.disj
    buckets := by
      intro b' hb'
      have hb'_len : b' < (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).length := by
        rw [List.length_set, I.nb_len]; exact hb'
      by_cases hb_eq : b' = (k &&& UInt32.ofNat mask).toNat
      · cases hb_eq
        have h_get : (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len))[(k &&& UInt32.ofNat mask).toNat]'hb'_len
            = q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len :=
          List.getElem_set_self (by rw [List.length_set]; exact hb_len)
        have B_old := I.buckets (k &&& UInt32.ofNat mask).toNat hb
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- head
          rw [h_get, headOf, readMem_toMem,
              hf5 _ (by rw [overlaps_symm]; exact dBC), hw4]
        · -- chain
          rw [h_get, headOf]
          have hag : ∀ r ∈ chains[(k &&& UInt32.ofNat mask).toNat]'hb_len,
              readMem σ5.toMem (fldPath r nm.next) = readMem m (fldPath r nm.next) := by
            intro r hr
            have hr_row := I.sub _ hb r hr
            have hr_ne : r ≠ q := by
              intro heq; cases heq
              have : q ∈ chains.flatten := by
                rw [List.mem_flatten]
                refine ⟨chains[(k &&& UInt32.ofNat mask).toNat]'hb_len, List.getElem_mem hb_len, hr⟩
              exact absurd this hq_not_in
            exact h_unch_fld r hr_row hr_ne nm.next
          refine Reaches.cons ?_ ((B_old.chain).frame hag)
          rw [readMem_toMem,
              hf5 _ (by rw [overlaps_symm]; exact dNC),
              hf4 _ (by rw [overlaps_symm]; exact dNB),
              hf3 _ (by rw [overlaps_symm]; exact dNF), hw2]
        · -- keys
          rw [h_get]
          intro r hr
          cases hr with
          | head =>
            refine ⟨k, ?_⟩
            rw [h_unch_key q hq_row, hq_key]
          | tail _ hr_tail =>
            obtain ⟨k', hk'⟩ := B_old.keys r hr_tail
            have hr_row := I.sub _ hb r hr_tail
            refine ⟨k', ?_⟩
            rw [h_unch_key r hr_row, hk']
        · -- fits
          rw [h_get, List.length_cons]
          omega
      · have h_get : (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len))[b']'hb'_len
            = chains[b']'(by rw [I.nb_len]; exact hb') :=
          List.getElem_set_ne (Ne.symm hb_eq) (by rw [List.length_set, I.nb_len]; exact hb')
        have B_old := I.buckets b' hb'
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- head
          rw [h_get]
          have d_bkt_ne : (bucketPath nm b').overlaps (bucketPath nm (k &&& UInt32.ofNat mask).toNat) = false :=
            bucketPath_ne_disjoint hb_eq
          rw [readMem_toMem,
              hf5 _ (by rw [overlaps_symm]; exact bucketPath_disjoint_count hno b'),
              hf4 _ (by rw [overlaps_symm]; exact d_bkt_ne),
              hf3 _ (row_fld_disjoint_bucket I hq_row nm.inhash hb'),
              hf2 _ (row_fld_disjoint_bucket I hq_row nm.next hb'),
              hr1, hσ0, readMem_toStore]
          exact B_old.head
        · -- chain
          rw [h_get]
          have hag : ∀ r ∈ chains[b']'(by rw [I.nb_len]; exact hb'),
              readMem σ5.toMem (fldPath r nm.next) = readMem m (fldPath r nm.next) := by
            intro r hr
            have hr_row := I.sub b' hb' r hr
            have hr_ne : r ≠ q := by
              intro heq; cases heq
              have : q ∈ chains.flatten := by
                rw [List.mem_flatten]
                refine ⟨chains[b']'(by rw [I.nb_len]; exact hb'), List.getElem_mem (by rw [I.nb_len]; exact hb'), hr⟩
              exact absurd this hq_not_in
            exact h_unch_fld r hr_row hr_ne nm.next
          exact (B_old.chain).frame hag
        · -- keys
          rw [h_get]
          intro r hr
          obtain ⟨k', hk'⟩ := B_old.keys r hr
          have hr_row := I.sub b' hb' r hr
          refine ⟨k', ?_⟩
          rw [h_unch_key r hr_row, hk']
        · -- fits
          rw [h_get]
          exact B_old.fits
    hash_mod := by
      intro b' hb' r hr k' hk'
      have hb'_len : b' < (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).length := by
        rw [List.length_set, I.nb_len]; exact hb'
      by_cases hb_eq : b' = (k &&& UInt32.ofNat mask).toNat
      · cases hb_eq
        have h_get : (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len))[(k &&& UInt32.ofNat mask).toNat]'hb'_len
            = q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len :=
          List.getElem_set_self (by rw [List.length_set]; exact hb_len)
        rw [h_get] at hr
        cases hr with
        | head =>
          rw [h_unch_key q hq_row, hq_key] at hk'
          cases hk'
          rfl
        | tail _ hr_tail =>
          have hr_row := I.sub _ hb r hr_tail
          rw [h_unch_key r hr_row] at hk'
          exact I.hash_mod _ hb r hr_tail k' hk'
      · have h_get : (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len))[b']'hb'_len
            = chains[b']'(by rw [I.nb_len]; exact hb') :=
          List.getElem_set_ne (Ne.symm hb_eq) (by rw [List.length_set, I.nb_len]; exact hb')
        rw [h_get] at hr
        have hr_row := I.sub b' hb' r hr
        rw [h_unch_key r hr_row] at hk'
        exact I.hash_mod b' hb' r hr k' hk'
    keys_unique := by
      intro b1 hb1 b2 hb2 q1 hq1 q2 hq2 k' hk1 hk2
      have hb1_len : b1 < (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).length := by
        rw [List.length_set, I.nb_len]; exact hb1
      have hb2_len : b2 < (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).length := by
        rw [List.length_set, I.nb_len]; exact hb2
      have h_mem1 : q1 ∈ (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).flatten := by
        rw [List.mem_flatten]
        refine ⟨(chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len))[b1]'hb1_len, List.getElem_mem hb1_len, hq1⟩
      have h_mem2 : q2 ∈ (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).flatten := by
        rw [List.mem_flatten]
        refine ⟨(chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len))[b2]'hb2_len, List.getElem_mem hb2_len, hq2⟩
      have hr1_flat : q1 ∈ (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).flatten ↔ q1 = q ∨ q1 ∈ chains.flatten :=
        mem_flatten_set_cons hb_len q1
      have hr2_flat : q2 ∈ (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).flatten ↔ q2 = q ∨ q2 ∈ chains.flatten :=
        mem_flatten_set_cons hb_len q2
      rw [hr1_flat] at h_mem1
      rw [hr2_flat] at h_mem2
      cases h_mem1 with
      | inl hq1_eq =>
        cases h_mem2 with
        | inl hq2_eq =>
          rw [hq1_eq, hq2_eq]
        | inr hq2_flat =>
          rw [hq1_eq] at hk1
          rw [h_unch_key q hq_row, hq_key] at hk1
          cases hk1
          have hq2_row : q2 ∈ rows := by
            rw [List.mem_flatten] at hq2_flat
            obtain ⟨c, hc_mem, hq2_c⟩ := hq2_flat
            obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hc_mem
            exact I.sub idx (by rw [← I.nb_len]; exact hidx) q2 hq2_c
          rw [h_unch_key q2 hq2_row] at hk2
          have h_in : (k, q2) ∈ elems m key chains := mem_elems_iff.mpr ⟨hq2_flat, hk2⟩
          exact absurd h_in (h_fresh q2)
      | inr hq1_flat =>
        cases h_mem2 with
        | inl hq2_eq =>
          rw [hq2_eq] at hk2
          have hq1_row : q1 ∈ rows := by
            rw [List.mem_flatten] at hq1_flat
            obtain ⟨c, hc_mem, hq1_c⟩ := hq1_flat
            obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hc_mem
            exact I.sub idx (by rw [← I.nb_len]; exact hidx) q1 hq1_c
          rw [h_unch_key q hq_row, hq_key] at hk2
          cases hk2
          rw [h_unch_key q1 hq1_row] at hk1
          have h_in : (k, q1) ∈ elems m key chains := mem_elems_iff.mpr ⟨hq1_flat, hk1⟩
          exact absurd h_in (h_fresh q1)
        | inr hq2_flat =>
          have hq1_row : q1 ∈ rows := by
            rw [List.mem_flatten] at hq1_flat
            obtain ⟨c, hc_mem, hq1_c⟩ := hq1_flat
            obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hc_mem
            exact I.sub idx (by rw [← I.nb_len]; exact hidx) q1 hq1_c
          have hq2_row : q2 ∈ rows := by
            rw [List.mem_flatten] at hq2_flat
            obtain ⟨c, hc_mem, hq2_c⟩ := hq2_flat
            obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hc_mem
            exact I.sub idx (by rw [← I.nb_len]; exact hidx) q2 hq2_c
          rw [h_unch_key q1 hq1_row] at hk1
          rw [h_unch_key q2 hq2_row] at hk2
          rw [List.mem_flatten] at hq1_flat hq2_flat
          obtain ⟨c1, hc1, hq1_c1⟩ := hq1_flat
          obtain ⟨idx1, hidx1, rfl⟩ := List.mem_iff_getElem.mp hc1
          obtain ⟨c2, hc2, hq2_c2⟩ := hq2_flat
          obtain ⟨idx2, hidx2, rfl⟩ := List.mem_iff_getElem.mp hc2
          have hidx1_nb : idx1 < nb := by rw [← I.nb_len]; exact hidx1
          have hidx2_nb : idx2 < nb := by rw [← I.nb_len]; exact hidx2
          exact I.keys_unique idx1 hidx1_nb idx2 hidx2_nb q1 hq1_c1 q2 hq2_c2 k' hk1 hk2
    flags := by
      intro r hr
      have hr_flat : r ∈ (chains.set (k &&& UInt32.ofNat mask).toNat (q :: chains[(k &&& UInt32.ofNat mask).toNat]'hb_len)).flatten ↔ r = q ∨ r ∈ chains.flatten :=
        mem_flatten_set_cons hb_len r
      rw [hr_flat]
      by_cases hrq : r = q
      · cases hrq
        constructor
        · intro _
          exact Or.inl rfl
        · intro _
          have h_mem_q : readMem σ5.toMem (fldPath q nm.inhash) = some (.bool true) := by
            rw [readMem_toMem,
                hf5 _ (by rw [overlaps_symm]; exact dFC),
                hf4 _ (by rw [overlaps_symm]; exact dFB),
                hw3]
          exact h_mem_q
      · rw [h_unch_fld r hr hrq nm.inhash]
        have h_flag_old := I.flags r hr
        constructor
        · intro h
          exact Or.inr (h_flag_old.mp h)
        · intro h
          cases h with
          | inl hrq_eq => exact absurd hrq_eq hrq
          | inr h_in => exact h_flag_old.mpr h_in
    count := by
      rw [length_flatten_set_cons hb_len]
      rw [readMem_toMem, hw5]
    fields := by
      intro r hr
      by_cases hrq : r = q
      · cases hrq
        refine ⟨?_, ?_, ?_⟩
        · rw [readMem_toMem,
              hf5 _ (by rw [overlaps_symm]; exact dNC),
              hf4 _ (by rw [overlaps_symm]; exact dNB),
              hf3 _ (by rw [overlaps_symm]; exact dNF), hw2]
          simp
        · rw [readMem_toMem,
              hf5 _ (by rw [overlaps_symm]; exact dFC),
              hf4 _ (by rw [overlaps_symm]; exact dFB),
              hw3]
          simp
        · rw [h_unch_key q hq_row, hq_key]
          simp
      · refine ⟨?_, ?_, ?_⟩
        · rw [h_unch_fld r hr hrq nm.next]; exact (I.fields r hr).1
        · rw [h_unch_fld r hr hrq nm.inhash]; exact (I.fields r hr).2.1
        · rw [h_unch_key r hr]; exact (I.fields r hr).2.2
    parent := by
      intro r hr
      exact I.parent r hr
  }

  refine ⟨σ5.toMem, hcall, hRep, ?_, ?_, ?_, ?_⟩
  · -- readMem m' q.inhash = true
    rw [readMem_toMem, hf5 _ (by rw [overlaps_symm]; exact dFC),
        hf4 _ (by rw [overlaps_symm]; exact dFB), hw3]
  · -- readMem m' q.next = headOf (chains[b])
    rw [readMem_toMem, hf5 _ (by rw [overlaps_symm]; exact dNC),
        hf4 _ (by rw [overlaps_symm]; exact dNB),
        hf3 _ (by rw [overlaps_symm]; exact dNF), hw2]
  · -- readMem m' bucket = .ptr q
    rw [readMem_toMem, hf5 _ (by rw [overlaps_symm]; exact dBC), hw4]
  · -- readMem m' count = chains.flatten.length + 1
    rw [readMem_toMem, hw5]

end Thash
end Templates

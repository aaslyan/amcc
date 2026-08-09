import Amcc.Spec.Pool

/-!
# AMCC — the stack instantiated, end to end

The first thing that connects `Spec.Algebra` to `Spec.Pool`. Until now the two
were separate: an interface with no instance, and an instance implementing no
interface. An uninhabited specification is worth nothing, so this file exists
to show that one exists — and to force the specification to survive contact
with a real allocator.

## What is built

A table whose records live in the proved free-list pool, carrying one
independently stored index. The index is a **`Count`** — one of the seven
reftypes OpenACR implements cross-references with — chosen because it has
genuine storage of its own (a counter in the database, maintained by hand),
so `Coherent` is a real obligation rather than a tautology. An index that were
merely *derived* from the record list would make coherence true by definition
and prove nothing.

Insert is built with the **two-phase** discipline: `prepare` reserves a slot
in the pool, `commit` allocates and bumps the counter. `commit` cannot fail,
because `Pool.reserve_sound` says the reservation guarantees a free slot.
That is the design from `Spec.Algebra` cashed out against a real pool.

## What it produced

`twoPhaseLaws` — the instance — and with it `insert_retrievable` and
`insert_invisible` come straight from the generic theorems, with no further
work. That is the point: prove the laws once at the interface, and every
instance inherits the promise.

## What it cost

One correction to `Spec.Algebra`. The original `insert_ok` claimed
`records db' = rec :: records db`. That is **false** for any pool with slot
reuse: a record is allocated into whatever slot the free list hands back, so
the extracted record list is a *permutation* of `rec :: old`, not literally
that. The law now uses `List.Perm`, and `Indexes` carries `spec_perm`.

The correction has teeth. `spec_perm` holds for every keyed access pattern —
`Thash`, `Count`, `Atree`, `Bheap` all derive their contents, and their order
where they have one, from the records themselves. It does **not** hold for a
FIFO `Llist`, whose order is insertion order and therefore is not a function
of the record set at all. That index needs an abstract state threaded through
the operations, which is a genuine extension of the interface. Better to have
found that here than in the middle of the list template.
-/

namespace Amcc
namespace Spec
namespace CountTable

variable {Rec Key B : Type}

/-! ## The database -/

/-- A table: records in a pool, plus one index with storage of its own. -/
structure Db (Rec B : Type) where
  pool : Pool.Heap Rec B
  /-- The `Count` index: how many records the table holds. Maintained by the
  operations, *not* computed from the pool — which is what makes coherence a
  real obligation. -/
  cnt  : Nat

/-- The table's contents, read out of the pool. Slot order, which is not
insertion order — hence the permutations. -/
def records (db : Db Rec B) : List Rec := Pool.liveRecs db.pool

/-! ## The two phases -/

/-- **Prepare.** Reserve one slot. Fails when the base provider is out of
memory; when it succeeds it has changed nothing anyone can observe. -/
def prep (take : B → Nat → Option B) (db : Db Rec B) : Db Rec B × Option Unit :=
  match Pool.reserve take db.pool 1 with
  | none    => (db, none)
  | some p' => ({ db with pool := p' }, some ())

/-- **Commit.** Allocate the reserved slot and maintain the index. The `none`
branch is unreachable after a successful `prepare`; it exists only because the
type of `allocRef` admits it. -/
def comm (db : Db Rec B) (rec : Rec) : Db Rec B :=
  match Pool.allocRef db.pool rec with
  | none         => db
  | some (p', _) => { pool := p', cnt := db.cnt + 1 }

def twoPhase (take : B → Nat → Option B) : TwoPhase (Db Rec B) Rec where
  W       := Unit
  prepare := fun db _ => prep take db
  commit  := fun db rec _ => comm db rec

/-- The access patterns: one `Count`, observing a `Nat`, specified as the
number of records. Permutation-invariant, as `spec_perm` requires. -/
def indexes : Indexes (Db Rec B) Rec where
  Ix        := Unit
  Obs       := fun _ => Nat
  cond      := fun _ _ => true
  obs       := fun _ db => db.cnt
  spec      := fun _ recs => recs.length
  spec_perm := by intro _ _ _ h; exact h.length_eq

/-- The table. `erase` is a stub that always reports failure: this file is
about insert, and `TwoPhaseLaws` says nothing about erase, so a stub is honest
rather than misleading. -/
def tbl (keyOf : Rec → Key) (take : B → Nat → Option B) :
    Table (Db Rec B) Rec Key where
  keyOf   := keyOf
  records := records
  insert  := (twoPhase take).insert
  erase   := fun db _ => (db, false)
  CanIns  := fun db _ => (Pool.reserve take db.pool 1).isSome = true

/-! ## Coherence, unfolded -/

private theorem filter_true (l : List Rec) : l.filter (fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [ih]

/-- Coherence for this table says exactly what you would hope: the counter
equals the number of records. -/
theorem coherent_iff {keyOf : Rec → Key} {take : B → Nat → Option B}
    {db : Db Rec B} :
    Coherent (tbl keyOf take) indexes db ↔ db.cnt = (records db).length := by
  constructor
  · intro h
    have h0 := h ()
    simpa [tbl, indexes, filter_true] using h0
  · intro h _
    simpa [tbl, indexes, filter_true] using h

/-! ## The laws -/

/-- **Preparation is invisible.** Reserving may ask the base provider for a
new block, but it adds no record and moves no counter. -/
theorem prepare_neutral {keyOf : Rec → Key} {take : B → Nat → Option B}
    {db : Db Rec B} {rec : Rec} {db' : Db Rec B} {w? : Option Unit}
    (hp : (twoPhase take).prepare db rec = (db', w?)) :
    Obseq (tbl keyOf take) indexes db db' := by
  have hp' : prep take db = (db', w?) := hp
  unfold prep at hp'
  split at hp'
  · rw [Prod.mk.injEq] at hp'
    obtain ⟨h1, _⟩ := hp'
    subst h1
    exact ⟨rfl, fun _ => rfl⟩
  · next p' hres =>
    rw [Prod.mk.injEq] at hp'
    obtain ⟨h1, _⟩ := hp'
    subst h1
    refine ⟨?_, fun _ => rfl⟩
    show Pool.liveRecs p' = Pool.liveRecs db.pool
    exact Pool.liveRecs_reserve hres

/-- **Commit adds the record and restores coherence** — and, crucially,
cannot fail. `Pool.reserve_sound` turns the reservation into a free slot, and
`Pool.alloc_isSome` turns a free slot into a successful allocation. -/
theorem commit_ok {keyOf : Rec → Key} {take : B → Nat → Option B}
    {db : Db Rec B} {rec : Rec} {db' : Db Rec B} {w : Unit}
    (hc : Coherent (tbl keyOf take) indexes db)
    (hp : (twoPhase take).prepare db rec = (db', some w)) :
    (records ((twoPhase take).commit db' rec w)).Perm (rec :: records db)
      ∧ Coherent (tbl keyOf take) indexes ((twoPhase take).commit db' rec w) := by
  have hp' : prep take db = (db', some w) := hp
  unfold prep at hp'
  split at hp'
  · rw [Prod.mk.injEq] at hp'
    exact absurd hp'.2 (by simp)
  · next p' hres =>
    rw [Prod.mk.injEq] at hp'
    obtain ⟨h1, _⟩ := hp'
    subst h1
    have hne : p'.1.free ≠ [] := Pool.free_ne_nil_of_reserve hres (by omega)
    have hsome := Pool.alloc_isSome hne rec
    cases hA : Pool.allocRef p' rec with
    | none => rw [hA] at hsome; exact absurd hsome (by simp)
    | some pr =>
      obtain ⟨p'', r⟩ := pr
      have hcomm : (twoPhase take).commit { db with pool := p' } rec w
          = { pool := p'', cnt := db.cnt + 1 } := by
        show comm { db with pool := p' } rec = _
        simp only [comm, hA]
      have hperm : (Pool.liveRecs p'').Perm (rec :: Pool.liveRecs p') :=
        Pool.liveRecs_alloc hA
      have hres' : Pool.liveRecs p' = Pool.liveRecs db.pool :=
        Pool.liveRecs_reserve hres
      rw [hcomm]
      refine ⟨?_, ?_⟩
      · show (Pool.liveRecs p'').Perm (rec :: Pool.liveRecs db.pool)
        rw [← hres']
        exact hperm
      · rw [coherent_iff]
        rw [coherent_iff] at hc
        show db.cnt + 1 = (Pool.liveRecs p'').length
        have hlen : (Pool.liveRecs p'').length = (Pool.liveRecs p').length + 1 := by
          rw [hperm.length_eq]; simp
        have hc' : db.cnt = (Pool.liveRecs db.pool).length := hc
        rw [hlen, hres']
        omega

/-- **The instance.** A concrete table over the proved pool satisfies the
two-phase contract.

checked by: `lake build` -/
theorem twoPhaseLaws (keyOf : Rec → Key) (take : B → Nat → Option B) :
    TwoPhaseLaws (tbl keyOf take) indexes (twoPhase take) where
  prepare_neutral := prepare_neutral
  commit_ok       := commit_ok

/-! ## The payoff

Nothing below is proved here. Each is the generic theorem from `Spec.Algebra`
applied to the instance above — which is what having an interface is for. -/

/-- **A successful insert adds the record and every access pattern agrees.**

checked by: `lake build` -/
theorem insert_retrievable (keyOf : Rec → Key) (take : B → Nat → Option B)
    {db db' : Db Rec B} {rec : Rec}
    (hc : Coherent (tbl keyOf take) indexes db)
    (h : (twoPhase take).insert db rec = (db', true)) :
    (records db').Perm (rec :: records db)
      ∧ Coherent (tbl keyOf take) indexes db' :=
  twoPhase_insert_ok (twoPhaseLaws keyOf take) hc h

/-- **A failed insert is invisible** — no rollback path anywhere in this file,
because the failure path never reaches `commit`.

checked by: `lake build` -/
theorem insert_invisible (keyOf : Rec → Key) (take : B → Nat → Option B)
    {db db' : Db Rec B} {rec : Rec}
    (h : (twoPhase take).insert db rec = (db', false)) :
    Obseq (tbl keyOf take) indexes db db' :=
  twoPhase_insert_fail (twoPhaseLaws keyOf take) h

/-- **The count is right after an insert** — the `Count` index maintained, as
a plain consequence of coherence.

checked by: `lake build` -/
theorem count_after_insert (keyOf : Rec → Key) (take : B → Nat → Option B)
    {db db' : Db Rec B} {rec : Rec}
    (hc : Coherent (tbl keyOf take) indexes db)
    (h : (twoPhase take).insert db rec = (db', true)) :
    db'.cnt = db.cnt + 1 := by
  obtain ⟨hperm, hcoh⟩ := insert_retrievable keyOf take hc h
  rw [coherent_iff] at hc hcoh
  rw [hcoh, hperm.length_eq]
  simp [hc]

end CountTable
end Spec
end Amcc

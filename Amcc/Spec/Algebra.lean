/-!
# AMCC — the algebra

The axiomatic core, stated abstractly and checked by the kernel. This file
depends on **nothing** — not the C subset, not the semantics, not the schema.
It is deliberately parameterised over opaque types so the algebra can be
settled before the semantics is rebuilt to support allocation, and then
instantiated afterwards.

## The shape of the whole system

Two statements, one lifted from the other:

- **Memory.** Before you may read a location you must have written it, and
  what you wrote is what you read back.
- **Relations.** Before you may find a record you must have inserted it, and
  if the insert reported success then *every* access pattern finds it.

The second is the first carried through a data structure. Everything in this
file exists to make that lifting precise, and `retrieval` at the bottom
derives the relational promise from the layer laws in three lines — which is
the evidence that the layering composes at all.

## What is assumed and what is proved

`RawAllocLaws` is **assumed**: `malloc`/`sbrk` are not ours and proving them is
not our concern. Everything above it is **proved**, layer by layer, each layer
assuming only the contract directly below:

```
  TableLaws      insert / erase / find, coherent across all access patterns
  ObjStoreLaws   typed live records with stable identity
  RawAllocLaws   raw memory, or failure                       ← ASSUMED
```

## The closed-world assumption

Nothing here defends against another party corrupting our storage. That is
deliberate and it is free: the model has no adversary, so "our code is the
only writer of its own storage" holds by construction rather than by proof.
It is a scoping decision, recorded here so that it is a decision and not an
oversight.

## Two design points that are encoded rather than proved

- **Allocation failure is inert by typing.** `alloc` returns
  `Option (Mem × Blk)`, not `Mem × Option Blk`. On failure there is no new
  memory to have been damaged, so "a failed allocation changes nothing" is
  true because it cannot be stated otherwise. One fewer law to prove, one
  fewer law to get wrong.
- **There is no uninitialised state.** `ObjStore.alloc` takes the record's
  initial value, so a reachable record always has one. "Read only what you
  wrote" is therefore structural, not a side condition.
-/

namespace Amcc
namespace Spec

/-! ## Level 0 — the postulated allocator

The trust boundary, and the whole of it. In OpenACR this is `Sbrk` (one use)
and `Malloc` (two); everything else in the allocation universe is built on
top and is fair game for proof. -/

/-- Raw memory: blocks that are live or not. No types, no contents — reading
structure into a block is the next layer's job. -/
structure RawAlloc (Mem Blk : Type) where
  live  : Mem → Blk → Prop
  alloc : Mem → Nat → Option (Mem × Blk)
  free  : Mem → Blk → Mem

/-- **Assumed, never proved.** What we require of `malloc`, and nothing more:
a successful allocation yields a live block that was not live before, and does
not disturb the blocks that were. Failure needs no law — see the header. -/
structure RawAllocLaws {Mem Blk : Type} (A : RawAlloc Mem Blk) : Prop where
  alloc_live   : ∀ {m n m' b}, A.alloc m n = some (m', b) → A.live m' b
  alloc_fresh  : ∀ {m n m' b}, A.alloc m n = some (m', b) → ¬ A.live m b
  alloc_keeps  : ∀ {m n m' b b'}, A.alloc m n = some (m', b) → A.live m b' → A.live m' b'
  free_dead    : ∀ {m b}, ¬ A.live (A.free m b) b
  free_keeps   : ∀ {m b b'}, b' ≠ b → A.live m b' → A.live (A.free m b) b'

/-! ## Level 1 — structured memory

"Before I read I must have written; what I wrote I read back exactly." Stated
over an abstract address space so it can be discharged once against the real
store model. -/

structure Mem (H A V : Type) where
  valid : H → A → Prop
  read  : H → A → Option V
  write : H → A → V → H

/-- The two axioms, plus the frame law that makes them usable: writing one
address disturbs no other. Without `read_write_ne` the theory says nothing
about any program with two variables in it. -/
structure MemLaws {H A V : Type} (M : Mem H A V) : Prop where
  read_valid    : ∀ {h a}, M.valid h a → (M.read h a).isSome
  read_write_eq : ∀ {h a v}, M.valid h a → M.read (M.write h a v) a = some v
  read_write_ne : ∀ {h a b v}, b ≠ a → M.read (M.write h a v) b = M.read h b
  valid_write   : ∀ {h a b v}, M.valid h a → M.valid (M.write h b v) a

/-! ## Level 2 — the object store

The bridge from "the allocator returned a chunk" to "I hold a live, typed
record". Everything above this layer speaks of `Ref`s and values; nothing
above it mentions memory. -/

structure ObjStore (Heap Ref Val : Type) where
  live  : Heap → Ref → Prop
  get   : Heap → Ref → Option Val
  set   : Heap → Ref → Val → Heap
  alloc : Heap → Val → Option (Heap × Ref)
  free  : Heap → Ref → Heap

/-- **Proved for each pool provider**, assuming `RawAllocLaws` of its base.

`alloc_frame` is the load-bearing one: allocating a new record does not
disturb the records already there. That *is* the stable-address property —
`Lary` satisfies it (it adds levels rather than moving elements), `Tary` does
not (growth may move memory). A provider that cannot prove `alloc_frame`
implements a strictly weaker interface, and the structures that need stability
cannot be instantiated over it. -/
structure ObjStoreLaws {Heap Ref Val : Type} (S : ObjStore Heap Ref Val) : Prop where
  alloc_live   : ∀ {h v h' r}, S.alloc h v = some (h', r) → S.live h' r
  alloc_fresh  : ∀ {h v h' r}, S.alloc h v = some (h', r) → ¬ S.live h r
  alloc_get    : ∀ {h v h' r}, S.alloc h v = some (h', r) → S.get h' r = some v
  alloc_frame  : ∀ {h v h' r r'}, S.alloc h v = some (h', r) → S.live h r' →
                   S.get h' r' = S.get h r'
  set_get_self : ∀ {h r v}, S.live h r → S.get (S.set h r v) r = some v
  set_frame    : ∀ {h r r' v}, r' ≠ r → S.get (S.set h r v) r' = S.get h r'
  free_dead    : ∀ {h r}, ¬ S.live (S.free h r) r
  free_frame   : ∀ {h r r'}, r' ≠ r → S.get (S.free h r) r' = S.get h r'

/-! ## Level 3 — access patterns as views

The generalisation that makes the relational promise uniform. A hash index, an
intrusive list, a heap and a tree do not support the same queries — but each
*observes* the record set as some abstract thing (a map, a sequence, a
priority multiset, a sorted map). An access pattern is therefore a pair: what
the generated structure actually looks like, and what the record set says it
ought to look like. -/

/-- The family of access patterns declared over one table. `Ix` names them,
`Obs i` is the abstract type the `i`-th one observes.

A **cross-reference** in OpenACR's sense needs no extra machinery here. amc
calls an xref "a partitioned index, and an incremental group-by — those two
concepts refer to the same thing", and a group-by is just a view whose
observed type is `Parent → List Rec`. So `Ptr`, `Ptrary`, `Thash`, `Bheap`,
`Atree`, `Llist` and `Count` — the seven reftypes amc implements xrefs with —
are seven choices of `Obs`, not seven separate theories. -/
structure Indexes (Db Rec : Type) where
  Ix   : Type
  Obs  : Ix → Type
  /-- amc's `inscond`. An access pattern may cover only a subset of the
  records; the default is `true`, but the condition is an arbitrary predicate,
  so every index is potentially a *filtered* index. Coherence has to respect
  that or it would demand indexes contain records they deliberately skip. -/
  cond : Ix → Rec → Bool
  /-- What the generated data structure actually holds. -/
  obs  : (i : Ix) → Db → Obs i
  /-- What it *should* hold, as a function of the records alone. -/
  spec : (i : Ix) → List Rec → Obs i
  /-- **An access pattern does not depend on the order records happen to sit
  in storage.**

  Forced by trying to instantiate this over a real pool: a record is allocated
  into whatever slot the free list hands back, so after an insert the extracted
  record list is a *permutation* of `rec :: old`, not literally that. Anything
  an index observes must therefore be permutation-invariant.

  This is satisfied by every keyed access pattern — `Thash`, `Count`,
  `Atree`, `Bheap` all derive their contents (and their order, where they have
  one) from the records themselves. It is **not** satisfied by a FIFO
  `Llist`, whose order is insertion order and so is not a function of the
  record set at all. Such an index needs an abstract state that is threaded
  through the operations rather than derived; that is a genuine extension of
  this interface and it is deferred, deliberately and visibly, rather than
  papered over. -/
  spec_perm : ∀ (i : Ix) {l₁ l₂ : List Rec}, l₁.Perm l₂ → spec i l₁ = spec i l₂

/-- A table: a pool of records, the operations, and the precondition under
which an insert is required to succeed.

Erasure takes a **key**, not a record — that is what the generated code can
actually be handed, and it is what forces the key/record distinction to appear
in the laws rather than being smuggled in later. -/
structure Table (Db Rec Key : Type) where
  keyOf   : Rec → Key
  records : Db → List Rec
  insert  : Db → Rec → Db × Bool
  erase   : Db → Key → Db × Bool
  /-- Memory is available *and* the structural preconditions hold (key not
  already present when the index is unique, and so on). -/
  CanIns  : Db → Rec → Prop

/-- **Coherence.** Every access pattern is a correct projection of the record
set. This is the representation invariant of the whole relational layer, and
it is what makes "all the indexes agree" a statement rather than a hope —
OpenACR's xref maintenance promises exactly this and never proves it. -/
def Coherent {Db Rec Key : Type} (T : Table Db Rec Key) (X : Indexes Db Rec)
    (db : Db) : Prop :=
  ∀ i : X.Ix, X.obs i db = X.spec i ((T.records db).filter (X.cond i))

/-- **The relational contract.** Four clauses, and each one is load-bearing:

- `insert_ok` — a successful insert adds the record *and restores coherence*,
  so every access pattern is updated, not merely the one the caller had in
  mind. This is the clause that makes the promise hold for all access
  patterns at once.
- `insert_fail` — a failed insert changes **nothing**. No half-linked row, no
  index entry without a record. Insert is transactional across all of them.
- `insert_iff` — success is *exactly* the declared precondition. Without the
  reverse direction a generator that refuses every insert satisfies the other
  three clauses vacuously.
- `erase_ok` — the dual, so that `find` cannot report records that were
  removed. `insert_ok` alone gives completeness ("what went in can be found");
  this gives soundness ("what comes out went in and has not left"). Both
  directions are needed or the theory admits a `find` that invents records. -/
structure TableLaws {Db Rec Key : Type} [BEq Key] (T : Table Db Rec Key)
    (X : Indexes Db Rec) : Prop where
  insert_ok :
    ∀ {db rec db'}, Coherent T X db → T.insert db rec = (db', true) →
      (T.records db').Perm (rec :: T.records db) ∧ Coherent T X db'
  insert_fail :
    ∀ {db rec db'}, T.insert db rec = (db', false) → db' = db
  insert_iff :
    ∀ {db rec}, T.CanIns db rec ↔ (T.insert db rec).2 = true
  erase_ok :
    ∀ {db k db'}, Coherent T X db → T.erase db k = (db', true) →
      (T.records db').Perm ((T.records db).filter (fun r => T.keyOf r != k))
        ∧ Coherent T X db'
  erase_fail :
    ∀ {db k db'}, T.erase db k = (db', false) → db' = db

/-! ## Level 3½ — cross-referencing, and why insert is not atomic by itself

Read from amc's generated `XrefMaybe`, which is where OpenACR's relational
promise actually lives. A representative one, lightly trimmed:

```c
bool abt::targsrc_XrefMaybe(abt::FTargsrc &row) {
    abt::FTarget* p_target = abt::ind_target_Find(target_Get(row));
    if (UNLIKELY(!p_target)) return false;          // ① parent not found
    c_targsrc_Insert(*p_target, row);               // ② linked into parent
    if (!ind_targsrc_InsertMaybe(row)) return false; // ③ duplicate key
    row.p_target = p_target;                        // ④ up-pointer set
    return true;
}
```

Two things follow, and neither is visible from the schema alone.

**Insert has four distinct failure modes**, not one: allocation failure
(before this function is even called), parent not found ①, duplicate key on a
unique index ③, and — per amc's documentation — a parent index that is full,
as when the parent side is a plain `Ptr` that can hold a single child.

**`XrefMaybe` is not atomic.** When ③ fails, the row is *already* linked into
the parent's `Ptrary` by ②, and its up-pointer is *not yet* set, because ④
never runs. amc's documentation is explicit that recovery is the caller's
job — "the child record should be deleted" — so atomicity is a property of
the composite operation, and it rests on the delete path correctly unwinding
a partially cross-referenced row whose up-pointer may still be null. That
obligation is real, subtle, and currently carried by convention plus a
hand-written checker (`cpp/amc/checkxref.cpp`, which for instance refuses an
xref on a deletable ctype unless a `cascdel` exists). It is exactly the class
of condition this project should be discharging by proof.

So the model separates the two, and `TableLaws.insert_fail` becomes something
*derived* rather than assumed. -/

/-- The state between allocating a record and cross-referencing it: the record
is in the pool, but no access pattern knows about it yet.

Named deliberately, because it is the one moment when the database is
legitimately **not** coherent, and every correctness argument has to pass
through it. -/
def Pending {Db Rec Key : Type} (T : Table Db Rec Key) (X : Indexes Db Rec)
    (db₀ db₁ : Db) (rec : Rec) : Prop :=
  T.records db₁ = rec :: T.records db₀ ∧ ∀ i : X.Ix, X.obs i db₁ = X.obs i db₀

/-- amc's `XrefMaybe` and its inverse. `link` may fail *after* having
established some of the cross-references; `unwind` removes whatever was
established, however far `link` got. -/
structure Xref (Db Rec : Type) where
  link   : Db → Rec → Db × Bool
  unwind : Db → Rec → Db

/-- The contract that makes a partial `link` safe.

`unwind_link` is the whole of it, and it is stronger than it looks: unwinding
returns the database to its pre-link state **whether the link succeeded or
failed**. One law, because rollback-after-failure and delete-an-existing-row
are the same operation — which is why amc can delegate failure recovery to the
ordinary delete path, and why that path must tolerate a row that was linked
into some indexes but not others and whose up-pointer was never assigned. -/
structure XrefLaws {Db Rec Key : Type} (T : Table Db Rec Key)
    (X : Indexes Db Rec) (R : Xref Db Rec) : Prop where
  unwind_link :
    ∀ {db rec db' ok}, R.link db rec = (db', ok) → R.unwind db' rec = db
  link_ok :
    ∀ {db₀ db₁ db₂ rec}, Coherent T X db₀ → Pending T X db₀ db₁ rec →
      R.link db₁ rec = (db₂, true) → Coherent T X db₂

/-- **Rollback restores exactly.** A failed cross-reference leaves no trace
once unwound — no half-linked row, no index entry without a record.

The proof is one step; the *statement* is the deliverable. This is the
obligation amc's generated code carries implicitly, and writing it down is
what turns `TableLaws.insert_fail` from an assumption into something a
template has to earn.

checked by: `lake build` -/
theorem rollback_restores {Db Rec Key : Type} {T : Table Db Rec Key}
    {X : Indexes Db Rec} {R : Xref Db Rec} (L : XrefLaws T X R)
    {db db' : Db} {rec : Rec} (h : R.link db rec = (db', false)) :
    R.unwind db' rec = db := L.unwind_link h

/-! ## Level 3¾ — transactional insert, by construction

amc gets atomicity by *unwinding*: link eagerly, and when a link fails, delete
the child to undo whatever was established. That works, but it puts the
correctness burden in the worst possible place — the delete path must be
correct for every partial state the link phase can leave behind, and there are
as many such states as there are indexes.

We control the generator, so we can choose the other design, and it is strictly
easier to verify: **decide everything that can fail before changing anything.**

The observation that makes it work is that every structural failure mode is a
*pure query*:

| failure mode | decidable in advance? |
| --- | --- |
| parent record not found | yes — the `via` lookup is a read |
| duplicate key on a unique index | yes — a find on the same bucket |
| parent index full (a plain `Ptr`) | yes — read the slot |
| out of memory | yes, if each index is asked to **reserve** first |

So the operation splits in two:

- **prepare** — resolve the parents, check every structural precondition, and
  reserve capacity in the pool and in every index that could need it. This
  phase can fail, and it is *observationally neutral*: reserving may allocate
  chunks, but it changes no record and nothing any access pattern can see.
- **commit** — populate the record and link it into every index, using the
  witnesses prepare already computed. Given a successful prepare, this phase
  **cannot fail**.

Two consequences. Atomicity is by construction rather than by rollback: the
failure path never reaches commit, so there is nothing to undo and no unwind
path to get right. And it costs essentially nothing at run time, because
prepare hands commit the work it already did — the parent pointer is resolved
once, the hash bucket is walked once — which is the same total work amc's
fused `InsertMaybe` does.

The price is more generated code per reftype (each index must expose a
"can insert" and a "reserve") and one real proof obligation: *prepare
succeeded ⟹ commit cannot fail*. That obligation is local to each index, which
is exactly where we want it. -/

/-- Two databases no access pattern can tell apart, holding the same records.

The right notion of "changed nothing" for a failed insert. Bit-for-bit
equality would be too strong: a failed prepare may legitimately leave reserved
capacity behind, and capacity is invisible to every observer. -/
def Obseq {Db Rec Key : Type} (T : Table Db Rec Key) (X : Indexes Db Rec)
    (db db' : Db) : Prop :=
  T.records db' = T.records db ∧ ∀ i : X.Ix, X.obs i db' = X.obs i db

/-- The prepare/commit split. `W` is whatever prepare computes that commit
needs — resolved parent pointers, hash buckets, reserved slots. -/
structure TwoPhase (Db Rec : Type) where
  W       : Type
  prepare : Db → Rec → Db × Option W
  commit  : Db → Rec → W → Db

/-- The two obligations a generated template owes, and the whole of them. -/
structure TwoPhaseLaws {Db Rec Key : Type} (T : Table Db Rec Key)
    (X : Indexes Db Rec) (P : TwoPhase Db Rec) : Prop where
  /-- Preparation cannot be observed. It may reserve, it may not change the
  contents — which is what makes a failed insert invisible without any
  rollback. -/
  prepare_neutral :
    ∀ {db rec db' w?}, P.prepare db rec = (db', w?) → Obseq T X db db'
  /-- Commit, handed a witness from a successful prepare, adds the record and
  restores coherence — for *every* access pattern at once. This is where
  "prepare checked it, so this cannot fail" is discharged. -/
  commit_ok :
    ∀ {db rec db' w}, Coherent T X db → P.prepare db rec = (db', some w) →
      (T.records (P.commit db' rec w)).Perm (rec :: T.records db)
        ∧ Coherent T X (P.commit db' rec w)

/-- Insert, assembled from the two phases. -/
def TwoPhase.insert {Db Rec : Type} (P : TwoPhase Db Rec)
    (db : Db) (rec : Rec) : Db × Bool :=
  match P.prepare db rec with
  | (db', some w) => (P.commit db' rec w, true)
  | (db', none)   => (db', false)

section TwoPhaseThms

variable {Db Rec Key : Type} {T : Table Db Rec Key} {X : Indexes Db Rec}
  {P : TwoPhase Db Rec}

/-- **A failed insert is invisible — with no rollback path at all.**

Derived, not assumed. The failure path never reaches commit, so the only thing
that ran was prepare, and prepare cannot be observed. Contrast amc, where this
property depends on the delete path correctly unwinding a partially linked
row.

checked by: `lake build` -/
theorem twoPhase_insert_fail (L : TwoPhaseLaws T X P) {db db' : Db} {rec : Rec}
    (h : P.insert db rec = (db', false)) : Obseq T X db db' := by
  unfold TwoPhase.insert at h
  cases hp : P.prepare db rec with
  | mk dbp w? =>
    rw [hp] at h
    cases w? with
    | some w => rw [Prod.mk.injEq] at h; exact absurd h.2 (by simp)
    | none   => rw [Prod.mk.injEq] at h; exact h.1 ▸ L.prepare_neutral hp

/-- **A successful insert adds the record and leaves every access pattern
coherent.**

checked by: `lake build` -/
theorem twoPhase_insert_ok (L : TwoPhaseLaws T X P) {db db' : Db} {rec : Rec}
    (hc : Coherent T X db) (h : P.insert db rec = (db', true)) :
    (T.records db').Perm (rec :: T.records db) ∧ Coherent T X db' := by
  unfold TwoPhase.insert at h
  cases hp : P.prepare db rec with
  | mk dbp w? =>
    rw [hp] at h
    cases w? with
    | none   => rw [Prod.mk.injEq] at h; exact absurd h.2 (by simp)
    | some w => rw [Prod.mk.injEq] at h; exact h.1 ▸ L.commit_ok hc hp

end TwoPhaseThms

/-! ## The promise, derived

The point of the file. Everything above is definitions and assumptions; the
theorems below are what a caller actually gets, and they follow from coherence
in a few lines each. That they are this short is the evidence that the layer
boundaries are drawn in the right places — the memory reasoning was spent at
levels 0–2 and none of it appears here. -/

variable {Db Rec Key : Type} [BEq Key] {T : Table Db Rec Key} {X : Indexes Db Rec}

/-- **Retrieval — the headline promise.**

If insert reported success, then *every* declared access pattern observes the
record set with the new record in it. "If it went in, you can find it by
whatever access pattern you have" — for all of them simultaneously, which is
what makes a table with a hash index, an ordered list and a heap over the same
records a coherent thing rather than three structures that happen to be
updated nearby.

checked by: `lake build` -/
theorem retrieval (L : TableLaws T X) {db db' : Db} {rec : Rec}
    (hc : Coherent T X db) (h : T.insert db rec = (db', true)) :
    ∀ i : X.Ix, X.obs i db' = X.spec i ((rec :: T.records db).filter (X.cond i)) := by
  obtain ⟨hperm, hcoh⟩ := L.insert_ok hc h
  intro i
  rw [hcoh i]
  exact X.spec_perm i (List.Perm.filter (X.cond i) hperm)

omit [BEq Key] in
/-- **Nothing is retrievable that was not inserted.** The soundness direction:
under coherence, what an access pattern observes is a function of the record
set alone — so it cannot report a record that is not in the pool.

Trivial here by construction, and that is the point: coherence was chosen as
the invariant precisely so that this direction needs no argument.

checked by: `lake build` -/
theorem no_phantoms {db : Db} (hc : Coherent T X db) (i : X.Ix) :
    X.obs i db = X.spec i ((T.records db).filter (X.cond i)) := hc i

/-- **A failed insert is invisible.** No partially linked row, no index entry
without a record, no observable difference of any kind.

checked by: `lake build` -/
theorem insert_failure_inert (L : TableLaws T X) {db db' : Db} {rec : Rec}
    (h : T.insert db rec = (db', false)) :
    db' = db := L.insert_fail h

/-- **A failure has a reason, and the reason is exactly the precondition.**

Contrapositive of `insert_iff`: if the insert failed, the declared
precondition did not hold — memory was unavailable, or a structural condition
such as key uniqueness was violated. Paired with `insert_iff`'s forward
direction, this rules out a generator that reports failure whenever it likes.

checked by: `lake build` -/
theorem insert_failure_reason (L : TableLaws T X) {db db' : Db} {rec : Rec}
    (h : T.insert db rec = (db', false)) :
    ¬ T.CanIns db rec := by
  intro hcan
  have : (T.insert db rec).2 = true := L.insert_iff.mp hcan
  rw [h] at this
  exact Bool.noConfusion this

/-- **Erase is retrievable-dual**: after a successful erase every access
pattern observes the record set without it.

checked by: `lake build` -/
theorem retrieval_erase (L : TableLaws T X) {db db' : Db} {k : Key}
    (hc : Coherent T X db) (h : T.erase db k = (db', true)) :
    ∀ i : X.Ix,
      X.obs i db' = X.spec i
        (((T.records db).filter (fun r => T.keyOf r != k)).filter (X.cond i)) := by
  obtain ⟨hperm, hcoh⟩ := L.erase_ok hc h
  intro i
  rw [hcoh i]
  exact X.spec_perm i (List.Perm.filter (X.cond i) hperm)

/-! ## What is still owed

This file states the algebra; it does not connect it to anything yet. The
obligations, in the order the roadmap takes them:

1. Instantiate `Mem` at the real store model, and prove `MemLaws`.
2. Build `ObjStore` over `RawAlloc`, and prove `ObjStoreLaws` for each
   provider — arena (assuming nothing), then `Lary` and `Inlary` (with
   `alloc_frame`), then `Tpool`, `Lpool`, `Tary` (without it).
3. Instantiate `Indexes` per access pattern — `Thash` observes a map,
   `Llist` a sequence, `Bheap` a priority multiset, `Atree` a sorted map.
4. Prove `TableLaws` for the generated code, which is where the two-phase
   structure of insert (allocate-and-populate, then link into every index)
   has to be shown transactional.
5. Show the generated C implements the whole of it.

Step 4 is where the real work is: `insert_ok`'s coherence clause is the
statement that every index was maintained, and `insert_fail` is the statement
that a half-done insert is impossible. -/

end Spec
end Amcc

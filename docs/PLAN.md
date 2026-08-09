# AMCC — architecture and scope, ground up

*Supersedes both earlier drafts. Written against
`docs/ALLOCATOR_REQUIREMENT.md` and `~/openacr-mine` (dmmeta @ 2026-06-09).*

> AMCC is a verified schema-to-C generator for relational data structures
> **parameterized over memory management**. It proves generated relational code
> correct for any allocator satisfying an explicit contract.

## The algebra is now formal

`Amcc/Spec/Algebra.lean` states the axiomatic core and **typechecks today**
(in the build closure, no `sorry`, no dependency on the C subset or the
semantics — it is parameterized over opaque types so it could be settled
before the semantics is rebuilt).

It records the two-level statement the whole system rests on:

- **Memory** — before you read a location you must have written it, and what
  you wrote is what you read back.
- **Relations** — before you find a record you must have inserted it, and if
  insert reported success then *every* access pattern finds it.

The second is the first lifted through a data structure. The lifting is made
precise by **coherence**: every access pattern is a correct projection of the
record set, `∀ i, obs i db = spec i (records db)`. Given that, `retrieval` —
the headline promise — is a three-line derivation, and `no_phantoms` is
immediate. The shortness is the evidence that the layer boundaries are in the
right place: all the memory reasoning was spent below, and none of it appears
in the relational proofs.

Three things the formalization forced that prose had hidden:

- **Insert has two phases and two failure modes.** Allocate-and-populate can
  fail for want of memory; linking into the indexes can fail on a structural
  precondition (a duplicate key in a unique index). Both must leave the
  database *bit-for-bit unchanged* — no half-linked row, no index entry
  without a record. Insert is transactional across every access pattern.
- **Failure needs an `iff`.** "It failed because a precondition was violated"
  is vacuous on its own — a generator that refuses every insert satisfies it.
  `insert_iff` pins success to *exactly* the declared precondition.
- **Retrieval alone is not enough.** It gives completeness (what went in can
  be found). Soundness — `find` never reports a record that was not inserted,
  or that has since been erased — needs the erase law as its dual. Without it
  the theory admits a `find` that invents records.

## Cross-references are the centre of the library

Studied from `~/openacr-mine`: `txt/exe/amc/xref.md`, the generated
`XrefMaybe` functions in `cpp/gen/`, and `cpp/amc/checkxref.cpp`.

amc's own definition: an xref is *"a partitioned index, and an incremental
group-by — those two concepts refer to the same thing."* It is implemented
with seven reftypes — `Ptr`, `Ptrary`, `Thash`, `Bheap`, `Atree`, `Llist`,
`Count` — and the generated `<row>_XrefMaybe` establishes **all** of a
record's cross-references at once. It is called automatically on insert.

**This needs no new theory.** A group-by is a view whose observed type is
`Parent → List Rec`, so the seven reftypes are seven choices of `Obs`, not
seven separate theories. What the study *did* force into the model:

**Operation inventory to cover.** Per access pattern: `Insert` / `InsertMaybe`
· `Find` / `qFind` · `Last` / `qLast` · `N` · `RemoveAll` / `RemoveLast` · a
cursor (`_curs` with `Access`/`Next`/`Reset`). Per record: `XrefMaybe` ·
delete-with-`cascdel` propagation · the up-pointer assignment. Plus the pool
operations underneath. All of these are the table's public surface and all of
them must appear in `TableLaws` or its per-view refinements.

**Four failure modes, not one.** Allocation failure; parent record not found
(the `via` index lookup returns null); duplicate key on a unique index; parent
index full (a plain `Ptr` holds one child). Only the first is allocator-level;
the rest are structural preconditions.

**`inscond` makes every index potentially filtered.** An xref carries a
user-defined insert condition, so coherence must be stated over
`records.filter (cond i)`, not over all records. Now encoded in `Indexes.cond`.

**`XrefMaybe` is not atomic, by design.** In the generated code the row is
linked into the parent's `Ptrary` *before* the unique-hash insert that can
fail, and the up-pointer is assigned *after* it. So on failure the row is
half-linked with a null up-pointer, and amc's documentation delegates recovery
to the caller: "the child record should be deleted." Atomicity is therefore a
property of the *composite* insert, resting on a delete path that tolerates
partially cross-referenced rows. `Amcc/Spec/Algebra.lean` now models this
explicitly (`Pending`, `Xref`, `XrefLaws`), and the single law
`unwind_link` — *unwinding restores the pre-link state whether the link
succeeded or failed* — captures the fact that **rollback and delete are the
same operation**.

**amc already has a hand-written checker for this.** `cpp/amc/checkxref.cpp`
refuses an xref on a deletable ctype unless a `cascdel` exists, and rejects
ambiguous cascade targets. Those are precisely the conditions that become
proof obligations here — the strongest available evidence that the obligations
are real and that today they are enforced by convention and a C++ pass.

## Two corrections to the previous plan

**1. Fixed capacity was wrongly promoted to the foundation.** The previous
plan excluded every heap provider (`Lary`, `Lpool`, `Malloc`, `Tary`,
`Blkpool`, `Delptr`) because "the C subset cannot express `malloc`, by
design." That inverted the dependency — the subset is our artifact and does
not get to constrain the requirement. Fixed capacity is demoted to one
backend: the existing array table becomes the `Inlary` instance.

**2. There was no layer between the allocators and the data structures.**
Allocators hand out untyped, possibly-failing chunks. Data structures want
live, typed records with stable identity. With nothing in between, every
list/hash/tree proof re-derives aliasing and disjointness against the raw
heap. That is where projects of this kind die. The fix is an explicit
intermediate layer — **the object store** — described below.

## The stack, bottom to top

```
  L6  Codegen           C-subset emission · GenWellFormed · printer · smoke
  L5  Relational        tables · Pkey/FK · xref · cursors        (amc schema)
  L4  Collections       Llist · Thash · Bheap · Atree · Ptrary
      ══════════════ no memory reasoning above this line ══════════════
  L3  OBJECT STORE      Ref τ · live · typed records · stable identity
  L2  Separation core   footprints · disjointness · points-to · frame rule
      ─────────────── the lemma mass lives here, proved once ──────────
  L1  Chunk contract    ChunkSpec: disjoint raw memory, or failure
                        arena (proved) · Lary/Tpool/Lpool (proved)
                        Sbrk/Malloc (POSTULATED — the trust boundary)
  L0  Store model       values · blocks · paths · frames · the C subset
```

L2 and L3 are the answer to "we need another layer in between." L2 is the
reasoning apparatus; L3 is the interface it exports. They can be built as one
module with two faces, but they are distinct jobs: L2 is generic and reusable,
L3 is the contract the collections program against.

## L3 — the object store, in detail

The bridge from "the allocator gave me a chunk" to "I have a live
`order_row`". Its exported interface is deliberately tiny:

```lean
structure ObjStore (τ : Ty) where
  Heap  : Type
  Ref   : Type
  live  : Heap → Ref → Prop
  get   : Heap → Ref → Option Value
  set   : Heap → Ref → Value → Heap
  alloc : Heap → Value → Option (Heap × Ref)   -- none = allocation failed
  free  : Heap → Ref → Heap

structure ObjStoreLaws (S : ObjStore τ) : Prop where
  alloc_live   : alloc h v = some (h', r) → live h' r
  alloc_fresh  : alloc h v = some (h', r) → ¬ live h r
  alloc_get    : alloc h v = some (h', r) → get h' r = some v
  alloc_frame  : alloc h v = some (h', r) → ∀ r', live h r' → get h' r' = get h r'
  set_get_self : live h r → get (set h r v) r = some v
  set_frame    : r' ≠ r → get (set h r v) r' = get h r'
  free_dead    : ¬ live (free h r) r
  free_frame   : r' ≠ r → get (free h r) r' = get h r'
```

**`alloc_frame` is the stable-address property.** It is not a bolt-on
side condition; it is a law of the interface. `Lary` (390 uses) satisfies it —
it allocates new levels rather than moving old elements. `Tary` (69 uses) does
**not** — growth may move memory. So `Tary` implements a strictly weaker
interface, and any structure requiring `alloc_frame` simply cannot be
instantiated over it. amc's most important compatibility rule — *intrusive
links and up-pointers require a pool with stable addresses* — stops being a
convention and becomes a typing obligation. Given `Ptrary` at 136 uses and
`Upptr`/`Llist` everywhere, this is the single most common structural
dependency in the entire schema.

**What L3 buys L4.** Above the object store a pool is just a finite map
`Ref ⇀ Value`, and a data structure is a pure relation over that map plus
some designated roots. The `zd` list proof becomes: *following `next` from
`head` yields the abstract sequence* — induction over a finite map, no
aliasing anywhere. That is the difference between an XL proof and an L one,
repeated for every structure.

This is the standard shape for verified systems (CompCert's memory-model
interface, separation logic's frame rule); we are not inventing it, only
choosing to have it rather than not.

## L1 — the allocation layer

Provider usage from `dmmeta/field.ssim`, and the `dmmeta.basepool` chains:

| Provider | Uses | Role |
|---|---:|---|
| `Lary` | 390 | growable, **stable addresses** — the workhorse |
| `Ptrary` | 136 | consumer; requires stability |
| `Tary` | 69 | growable, **moving** — weaker interface |
| `Tpool` | 40 | fixed-size free list over a base pool |
| `Bheap` | 23 | consumer |
| `Inlary` | 20 | bounded inline — *what we already have* |
| `Lpool` | 10 | size-class allocator over a base |
| `Delptr` | 3 | owned lazy value |
| `Atree` | 3 | consumer |
| `Malloc` | 2 | **postulated leaf** |
| `Sbrk` | 1 | **postulated leaf** |

The entire allocation universe bottoms out in one or two leaves. That is the
whole trust boundary. `dmmeta.basepool` composition is shallow in practice
(7 records, depth ≤ 3: `sbrk ← lpool ← cstring`), so the composition theorem
— *base satisfies `ChunkSpec` ⟹ the pool over it satisfies `ObjStoreLaws`* —
is tractable.

**One leaf should be proved, not postulated.** A bump/arena allocator over a
static byte array satisfies `ChunkSpec` with no assumptions. That gives a
fully closed, assumption-free proof for the static-arena deployment, and the
postulated-`malloc` configuration for the dynamic one — same structure proofs,
two instantiations.

## L0 — what the C subset must gain

The largest single item, and the previous plan omitted it entirely.

- **A heap.** `Path.root` becomes `Global name | Block id`; `Store` gains a
  block heap. Frame lemmas in `Sanity.lean` generalize from "preserves
  globals" to "preserves globals and heap".
- **Null, and more partial operations.** Allocation can fail, so null must be
  representable. Phase 0's headline claim weakens honestly from "exactly one
  partial operation" to **three**: out-of-range subscript, null dereference,
  use-after-free. All three stay *proof obligations on generated code* — the
  same discipline, a bigger surface.
- **The allocator as an oracle.** `execStmt` takes an allocator parameter;
  theorems become `∀ oracle, AllocatorLaws oracle → …`. The evaluator stays
  total, deterministic and **executable** given an oracle, so `#guard` and the
  differential harness still work — instantiated with a concrete test
  allocator, including one with deterministic failure injection.
- **The loop story** — the one genuinely hard choice. `forN` currently carries
  a *literal* trip count, which is what makes `execStmt` structurally
  recursive. Data-dependent iteration needs either variable-bound `forN` +
  `break` (termination stays syntactic; covers bucket walks, level loops,
  capacity-bounded scans) or `while` + fuel (needed for true pointer chasing,
  where termination follows from list acyclicity — a `RepInv` property, not a
  syntactic one). *Recommendation: variable-bound now, fuel when L4's list
  template demands it.*
- **Pointer links, not index links.** The previous plan's `uint32_t`-index
  scheme was justified only by fixed capacity. With a real heap, pointer links
  are the semantic model, matching amc; index links remain an `Inlary`
  optimization.

## Scope map

**L0 foundation** *(blocking)* — heap · null · oracle · loop story ·
`capacity` out of the schema core · fallible operations in `MapLaws` ·
multi-table `Db` with foreign keys.

**L1 allocation** — `ChunkSpec` with the distinctions the requirement doc
enumerates (fixed vs. variable size · stable vs. moving · fallible vs. fatal ·
zeroed vs. uninitialized · owned vs. shared · what freeing returns).
Providers in priority order: **arena** (proved leaf) → **Lary** → **Tpool** →
**Inlary** *(mostly exists)* → **Lpool** → **Tary** → **Delptr** → **Blkpool**.

**L2/L3 object store** — the layer above; plus provider instances proving
`ObjStoreLaws` (and which of them satisfy `alloc_frame`).

**L4 collections** — `Upptr` · `Llist` (`zd` first; 8 flavors in
`dmmeta.listtype`) · `Count` · `Thash` · `Ptrary` · then `Bheap`, `Atree`.

**L5 relational + access patterns** — tables, FKs, xref auto-maintenance,
`cascdel`, and **cursors**. Cursors are a real gap today: `MapLaws` has *no
traversal law at all*, so nothing proved so far says anything about ordered
iteration — which any ordered access pattern needs.

**L6 codegen** — extends to the new statement forms; `GenWellFormed` restated
for the multi-table generator.

**Field-level, anytime** — `fconst` · `Base` · `Bitfld` · `Smallstr` ·
`Varlen` · `substr` · `fdec`. Independent of the allocator work.

**Out of scope** — process model (`fstep`, dispatch, `Fbuf`), `Regx`, the ssim
persistence layer.

## Build order

Ground up, with one vertical validation slice at the end of the foundation:

| Step | Deliverable | Effort |
|---|---|---|
| L0.1 | Heap, null, block paths; frame lemmas regeneralized | L |
| L0.2 | Allocator oracle; `AllocatorLaws`; executable test oracle | M |
| L0.3 | Loop story (variable-bound `forN`) | M |
| L1.1 | `ChunkSpec` + **proved arena leaf** | M |
| L2/L3 | Separation core + **object store** + laws | **L — the linchpin** |
| L3.1 | `Lary` instance (with `alloc_frame`) · `Inlary` instance | M |
| — | **spine**: arena → Lary → one `zd` list → one cursor → C → smoke | M |
| L0.4 | Schema v2 (multi-table, FKs) + `GenWellFormed` v2 | M |
| L4+ | Tpool, Lpool, Tary, Thash, Bheap, Atree, xrefs, cursors | XL total |

The spine exists to falsify the foundation early: if L0–L3 are wrong, a thin
slice through to compiled C reveals it in weeks rather than after months of
breadth.

`TypeSound` stays parked until L0 settles — proving it against semantics we
are about to change is wasted work.

## What survives from existing work

| Asset | Fate |
|---|---|
| `ArrayTableWf.lean` infrastructure (LawfulBEq, `find?_keyed`, pairwise, ctx-generic lemmas) | **Survives whole** — built generic, reusable for every template |
| `GenWellFormed` proof structure | Survives; restated for multi-table |
| Array table template | Becomes the `Inlary` instance |
| `InsertRefines`'s two-case shape | Survives — its `b = false` clause (store unchanged) is already the allocation-failure shape; only the justification changes |
| Printer, goldens, smoke harness, `amc` exe | Survive; extended |
| `Value` / `Eval` / `SmallStep` / `Sanity` | **Substantially reworked** (heap, oracle, fuel) |
| `MapLaws` | Extended: fallible insert + traversal laws |

Roughly half of L0 is rebuilt; nearly all of the proof engineering carries
over.

## Effort framing

This is a multi-quarter project. It always was — the previous plan concealed
that by excluding the hard half. The object store changes the *risk profile*
more than the total: it front-loads one L-sized proof effort and in exchange
turns each of `Llist`, `Thash`, `Bheap`, `Atree` from XL into L or M, because
each becomes mathematics over a finite map instead of aliasing reasoning over
a heap. Four structures in, it has paid for itself; `Atree` alone would
justify it.

## Transactional insert: yes, and by construction

amc gets atomicity by *unwinding* — link eagerly, and on failure delete the
child to undo whatever was established. That puts the burden in the worst
place: the delete path must be correct for every partial state the link phase
can leave, and there are as many such states as there are indexes.

We control the generator, so we take the other design. The observation that
makes it work is that **every structural failure mode is a pure query**:

| failure mode | decidable before mutating? |
|---|---|
| parent record not found | yes — the `via` lookup is a read |
| duplicate key on a unique index | yes — a find on the same bucket |
| parent index full (a plain `Ptr`) | yes — read the slot |
| out of memory | yes, if each index is asked to **reserve** first |

So insert splits into **prepare** (resolve parents, check every precondition,
reserve capacity — can fail, and is *observationally neutral*: reserving may
allocate chunks but changes no record and nothing any access pattern can see)
and **commit** (populate and link, using the witnesses prepare computed —
which, given a successful prepare, **cannot fail**).

Two consequences: atomicity is by construction rather than by rollback, so
there is no unwind path to get right; and it costs essentially nothing at run
time, because prepare hands commit the work it already did — the parent
pointer resolved once, the hash bucket walked once — the same total work
amc's fused `InsertMaybe` does.

Formalized in `Amcc/Spec/Algebra.lean` as `TwoPhase` / `TwoPhaseLaws`, with
both halves **derived, not assumed**:

- `twoPhase_insert_fail` — a failed insert is observationally invisible.
- `twoPhase_insert_ok` — a successful insert adds the record and leaves every
  access pattern coherent.

The price is more generated code per reftype (each index exposes a
"can insert" and a "reserve") and one genuine obligation per index: *prepare
succeeded ⟹ commit cannot fail*. That obligation is local to each index,
which is exactly where it should be. `Obseq` — same records, same
observations — is the right notion of "changed nothing"; bit-for-bit equality
would be too strong, since leftover reserved capacity is invisible to every
observer.

## Done: the pool allocator is proved

`Amcc/Spec/Pool.lean` — a model of `Tpool`/`Lary`: slot-indexed cells, a free
list, growth from a base provider. In the build closure, no `sorry`, and
`#print axioms` shows nothing beyond Lean's standard three.

- **`objStore_laws`** — the free-list pool satisfies every clause of
  `ObjStoreLaws`, `alloc_frame` included. Stable addresses, proved.
- **`grow_frame`** — growth appends and never relocates, so every live record
  keeps its handle *and* its contents. This is the `Lary` property.
- **`reserve_sound`** — after a successful `reserve n` the pool holds at least
  `n` free slots, so `n` allocations cannot fail. This is exactly what the
  two-phase insert's *prepare* phase buys, and why *commit* is infallible.
- **`moving_not_stable`** — a moving pool **cannot** satisfy `alloc_frame`, by
  concrete counterexample. `Tary` is unusable under intrusive structures as a
  theorem, not as a style rule.

**The composition result is stronger than planned.** `objStore_laws` is proved
for an *arbitrary* base provider with **no laws assumed about it at all** —
`take` is just a function that may fail whenever it likes. The pool's
correctness does not depend on anything about `malloc` beyond its returning a
value when it succeeds, because the pool never moves a cell it has handed out.
`RawAllocLaws` turns out not to be needed for this layer; it will be needed
where a provider's *own* freshness matters.

## Done: the stack is instantiated end to end

`Amcc/Spec/Table.lean` joins the algebra to the pool — until now an interface
with no instance and an instance implementing no interface. An uninhabited
specification is worth nothing; this proves one exists.

A table whose records live in the proved free-list pool, carrying one
independently stored **`Count`** index (a counter maintained by hand, so
`Coherent` is a real obligation rather than a tautology — a *derived* index
would make coherence true by definition and prove nothing). Insert is built
two-phase: `prepare` reserves a slot, `commit` allocates and bumps the
counter, and `commit` cannot fail because `Pool.reserve_sound` guarantees the
slot. The design cashed out against a real allocator.

- **`twoPhaseLaws`** — the instance, proved.
- **`insert_retrievable`**, **`insert_invisible`** — *not proved here*. They
  are the generic theorems from `Spec.Algebra` applied to the instance, with
  no further work. That is what having the interface is for.
- **`count_after_insert`** — the index is maintained, as a plain consequence
  of coherence.

## A bug the instantiation found

Attempting to build a concrete table over the proved pool immediately falsified
a clause of `TableLaws`. It said a successful insert gives

```
T.records db' = rec :: T.records db
```

which assumes storage order equals insertion order. It does not: a pool
allocates into whatever slot the **free list** hands back, so after slot reuse
the new record lands in the middle. The extracted record list is a
*permutation* of `rec :: old`, never literally that.

Corrected: the law now uses `List.Perm`, and `Indexes` carries a `spec_perm`
field requiring every access pattern to be permutation-invariant. `retrieval`
still goes through, now via `List.Perm.filter` and `spec_perm`.

That correction has a consequence worth stating plainly: **`spec_perm` holds
for every keyed access pattern** — `Thash`, `Count`, `Atree`, `Bheap` all
derive their contents, and their order where they have one, from the records
themselves — **but it does not hold for a FIFO `Llist`**, whose order is
insertion order and therefore is not a function of the record set at all.
A FIFO index needs an abstract state threaded through the operations rather
than derived from `records`. That is a real extension of the interface, it is
what any insertion-ordered access pattern needs, and it is now
recorded as deferred rather than silently assumed to work.

## C types and structures

Already first-class, and unaffected by any of the above. The C subset has
`Ty.strct`, `StructDef` (fields in declaration order), `Value.strct`, nested
structs with declare-before-use acyclicity, arrays of structs, and pointers to
structs; `rowStructDef` already synthesises a row type from a schema. The pool
is parameterized over an arbitrary `Val`, so instantiating `Val` at the C
subset's struct values is a connection step that changes nothing in the pool
proofs — records are C structs in the end, but that is a fact about the
instantiation, not about the allocator.

What the row struct still has to gain is *fields*, not new type machinery: the
intrusive link fields (`next`/`prev`, hash chain, up-pointer) that Tier 2's
templates emit. Genuinely absent from the subset and deferred to Tier 4:
`Bitfld`, `Smallstr`, `Varlen`, unions.

## The immediate next step

**Prove the allocator properties — but against a Lean model, not against
generated C.**

Proving `ObjStoreLaws` for *generated code* requires the L0 rework first
(heap, null, allocator oracle), which is the largest item on the board. But
proving them for a **pure Lean model** of each provider requires nothing that
does not already exist: `Amcc/Spec/Algebra.lean` typechecks today with no
dependency on the semantics. So the cheapest way to find out whether the
contract design is right is to build the pools as Lean data structures and
prove the laws about them, before a line of the semantics is touched.

Concretely, `Amcc/Spec/Pool.lean`:

1. A **free-list pool** over an abstract chunk provider — `alloc` pops the
   free head, `free` pushes it — and a proof of `ObjStoreLaws`, including
   `alloc_frame`. This is `Tpool`, and it is the shape `Lary` shares.
2. The **composition theorem**: a pool built over any base satisfying
   `RawAllocLaws` satisfies `ObjStoreLaws`. That is `dmmeta.basepool` as a
   theorem, and it is what lets providers be chained without redoing the
   structure proofs.
3. A **negative result**: a moving array (`Tary`) satisfies every law
   *except* `alloc_frame`, and a proof that it cannot satisfy it. This is
   worth as much as the positive results — it demonstrates that the interface
   actually discriminates, which is the whole basis for refusing to
   instantiate intrusive structures over `Tary`.

If the free-list pool cannot be made to satisfy the interface as stated, the
interface is wrong, and we learn that in days rather than after the semantics
rework. That is the point of doing this first.

## Decisions needed

1. **Confirm the object store as L2/L3** — one intermediate interface,
   `ObjStoreLaws` as stated, with `alloc_frame` carrying stability.
2. **Loop story** — variable-bound `forN` now, `while` + fuel deferred?
3. **Null representation** — real `Value.null` + proof obligation
   (recommended: matches C and the requirement doc's own wording), or a
   fallible allocation statement that never yields null?
4. **Proved arena leaf in v1** — recommended: yes, it closes one
   configuration completely.
5. **Spine content** — is `arena → Lary → zd list → cursor` the right first
   vertical slice?

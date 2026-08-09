# AMCC — where we are and what is next

*Roadmap. Not canonical — `docs/GOALS.md` is. If this file and the goal
disagree, the goal wins and this file is wrong.*

**Keep this short and current.** It was allowed to grow to ~500 lines
describing an architecture whose upper levels did not exist, which is how the
route drifted three times without anyone noticing. Update it in the same commit
that changes the route, or delete the part that went stale.

Design rationale is **not** kept here. It lives where it can be checked:
`Amcc/Spec/Algebra.lean` (the axiomatic core), `Amcc/Spec/Pool.lean` (the
allocator layer), `docs/ALLOCATOR_REQUIREMENT.md` (the allocator contract),
`docs/DIVERGENCE.md` (every departure from `amc`, with citations).

---

## Status

**Emitted C** — two templates, seven functions.

| Template | Functions |
|---|---|
| Array table (`Templates/ArrayTable`) | `<t>_Find` → row pointer or `NULL`, `<t>_InsertMaybe`, `<t>_Remove` |
| Pool (`Templates/Pool`) | `D_f_Init`, `D_f_Alloc`, `D_f_Free`, `D_f_N` |

Both compile under `cc -Wall -Wextra -Werror` and are differentially tested
against a real compiler by `scripts/smoke.sh`.

**Proved for every accepted schema**

- `genWellFormed` — the generated program satisfies every C-subset obligation.
  Structural.
- `findCorrect` — `find` returns a pointer exactly when `absOf` says the key is
  present, and returns the memory it was given. **Behavioural**, and the first
  theorem about what generated code computes.
- `noTrapFind` — corollary.

**Proved about the algorithms, as Lean models**

`Spec/Pool.lean` — the free-list pool satisfies `ObjStoreLaws` over an
arbitrary base with no laws assumed about it, including `alloc_frame` (stable
addresses); `moving_not_stable` proves a relocating pool cannot.
`Spec/Algebra.lean` — transactional two-phase insert, coherence across access
patterns, retrieval derived. `Spec/Table.lean` — an instance, so the specs are
known inhabitable.

**Schema model** — `Dmmeta.lean`: `Ctype`, `Field` whose `arg` names another
ctype, `Db` in declaration order, all 20 reftypes with their `dmmeta` flags.
Six lower to C. Layout lowering emits multi-ctype structs and the database
global.

**Semantics** — heap with block-rooted paths, `NULL`, runtime-sized storage,
runtime loop bounds. Three partial operations, all proof obligations:
out-of-range subscript, null dereference, use-after-free.

**The measure that is not met.** There is no artifact certified end to end. The
pool has a proved model and a tested implementation with **no formal link
between them**; `MilestoneTheorem` is open. Everything above is real progress
against that measure and none of it reaches it.

---

## Next, in order

1. **`Upptr` accessors.** Small — the ctype model already lowers `Upptr` to a
   pointer field.
2. **`Llist` link/unlink** over the pool. Where the reftype vocabulary starts
   paying off, and where `alloc_frame` stops being theoretical. Unblocked by
   the printer emitting struct tags, which is what makes a self-referential
   link field legal.
3. **`Thash`.** The bucket walk fits the capacity-bounded `forN` we already
   have; correctness does not depend on hash quality, only the expected-time
   claim does. No subset extension needed.
4. **Xref maintenance** tying them together, using the prepare/commit design
   from `Spec/Algebra.lean`.
5. **Proofs for the above**, drawing on the machinery `ArrayTableFind.lean`
   already banked: slot resolution, the pointer-deref path with `nullDeref` and
   `useAfterFree` discharged, field writes with their frame property, and the
   call path with frame save/restore.

---

## Deliberately deferred, with the reason

- **The array table's remaining `Simulates` clauses** (`InsertRefines`,
  `EraseRefines`, `RepInvPreserved`). Every ingredient for `erase` is proved;
  only the assembly is left. Deferred because it would prove more about a
  template already known to be provable, while the emitted surface stands
  still. Resume when a *second* template needs the same argument, so the work
  is shared.
- **`Stmt.alloc` / `Stmt.free` and the allocator oracle.** The store model
  supports them; no statement exposes them to generated code, so emitted pools
  are still fixed-capacity. This is the gap between `Spec/Pool.lean`'s
  arbitrary base provider and what can actually be generated.
- **`Wf.TypeSound`.** `findCorrect` established it is *not* on the critical
  path — structural errors are dischargeable from `RepInv` where they arise.
  Worth having eventually; not blocking anything.
- **Insertion-ordered indexes.** `Indexes.spec_perm` requires
  permutation-invariance, which every keyed access pattern satisfies and a FIFO
  `Llist` does not. That needs an abstract state threaded through the
  operations — a real interface extension, recorded rather than assumed away.
- **Concurrency, the ssim layer, `Bheap`/`Atree`.** Not started. See
  `docs/DIVERGENCE.md` §3 for the full list of what `amc` does that we have not
  attempted.

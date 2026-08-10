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

**Emitted C** — five templates, twenty-five functions.

| Template | Functions |
|---|---|
| Array table (`Templates/ArrayTable`) | `<t>_Find` → row pointer or `NULL`, `<t>_InsertMaybe`, `<t>_Remove` |
| Pool (`Templates/Pool`) | `D_f_Init`, `D_f_Alloc`, `D_f_Free`, `D_f_N` |
| Up-pointer (`Templates/Upptr`) | `C_f_Init`, `C_f_Get`, `C_f_Set`, `C_f_Q` |
| Intrusive list (`Templates/Llist`) | `D_f_Init`, `_Insert`, `_Remove`, `_First`, `_Next`, `_Prev`, `_InLlistQ`, `_EmptyQ`, `_N` |
| Hash index (`Templates/Thash`) | `D_f_Init`, `_Find`, `_InsertMaybe`, `_Remove`, `_N` |

All five compile under `cc -Wall -Wextra -Werror` and are differentially
tested against a real compiler by `scripts/smoke.sh`.

**Proved for every accepted schema**

- `genWellFormed` — the generated program satisfies every C-subset obligation.
  Structural.
- `findCorrect` — `find` returns a pointer exactly when `absOf` says the key is
  present, and returns the memory it was given. **Behavioural**, and the first
  theorem about what generated code computes.
- `eraseRefines` / `insertRefines` — the writers refine `Abs.erase` /
  `Abs.insert`, including that a failed insert changes nothing and only
  happens on a full table.
- `repInvPreserved` — both writers preserve the representation invariant, all
  four clauses, including `distinct` (key uniqueness).
- `noTrapFind` / `noTrapErase` / `noTrapInsert` — none of the three operations
  can raise `oob`, `nullDeref`, `useAfterFree`, or any structural error.
- **`milestoneTheorem`** — the conjunction: *every* well-formed schema's
  generated table simulates the abstract map. One proof, quantified over
  schemas.
- `Upptr.get_set` — read-back for the up-pointer accessors: a `Get` after a
  `Set` returns exactly what was set, and the `Set` is invisible at every path
  that does not overlap the field. `init_correct`, `test_null` and `test_ptr`
  cover the other three functions.
- `Llist.init_correct`, the five readers, and both idempotence guards
  (`insert_noop`, `remove_noop`). The linking laws are **stated and not
  proved** — `InsertLinks` / `RemoveUnlinks`; see below.
- `Thash.size_correct` and both idempotence guards.
- **`Thash.bucketInRange`** — the bucket subscript is always in range, so the
  only partial operation the hash index introduced cannot trap. Needs only
  `0 < NB`, not the power-of-two condition. `Thash.mask_eq_mod` proves what
  the power-of-two condition *does* buy: the mask is the modulus, which is the
  claim `docs/DIVERGENCE.md` §3.2 makes. `accepted_bucket_facts` ties both to
  the generator's own guard. `Thash.FindCorrect` remains **stated and not
  proved**.
- `Store.readPath_writePath_disjoint` — the frame law the above rests on, and
  the first thing that makes `Path.overlaps` mean something: a prefix test on
  access paths *is* a sufficient aliasing analysis, because a path names an
  object rather than an address.

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

**The measure, and what still misses it.** `MilestoneTheorem` is closed, so
the array table is the first artifact certified end to end — schema in,
C-subset AST out, with a machine-checked statement of what the emitted
functions guarantee.

Two gaps remain against the full measure, both recorded in
`docs/DIVERGENCE.md` §3:

- **The pretty-printer is unverified.** `MilestoneTheorem` certifies the
  *AST*. `Codegen/Print.lean` turns that AST into C text and is covered only
  by goldens and `scripts/smoke.sh`.
- **The pool has a proved model and a tested implementation with no formal
  link between them.** `Spec/Pool.lean` proves the algorithm; `Templates/Pool`
  emits it; nothing connects the two the way `ArrayTableInsert` connects
  `genC` to `absOf`.

---

## Next, in order

1. **The chain invariant, and with it `Llist.InsertLinks` / `RemoveUnlinks`
   and `Thash.FindCorrect`.**
   A linked list's shape is a property of a graph in the heap, not of a
   carrier list, so the invariant needs a *reachability* predicate over the
   store — the chain from a head along `next` is finite, acyclic and
   `NULL`-terminated, `prev` is its inverse, the membership flag marks exactly
   its members, the count is its length.
   `Store.readPath_writePath_disjoint` supports the frame reasoning but does
   not supply that predicate. A `Thash` bucket *is* a chain, so one predicate
   serves both templates — which is the whole argument for building it in its
   own module rather than inside either.
2. **The C-name uniqueness obligation the `Upptr` laws push onto the checker.**
   Those laws assume a program in which the field name resolves.
   `child ++ "_" ++ fld` is not injective in the pair, so `a`/`b_c` and
   `a_b`/`c` generate the same C name. If `Dmmeta.check` does not reject that,
   the laws are vacuous for a legal schema and nothing would notice.
3. **Xref maintenance** tying the templates together, using the
   prepare/commit design from `Spec/Algebra.lean`.
4. **The remaining reftypes** — `Bheap`, `Atree`, `Ptrary`, `Count`, the other
   seven `Llist` flavours, and cursors for all of them. `docs/GOALS.md` puts
   the whole vocabulary in scope; `docs/DIVERGENCE.md` §3 is the standing list
   of what is not attempted.

---

## Deliberately deferred, with the reason

- ~~**The array table's remaining `Simulates` clauses**~~ — **done.**
  `InsertRefines`, `EraseRefines` and `RepInvPreserved` are proved, and with
  them `MilestoneTheorem`. The deferral was wrong on its own terms: assembling
  them produced the reusable bank (`exec_assignFields`, `setFields`,
  `repInv_update`, `repInv_setRow`, `absOf_setRow`) that a second template
  would otherwise have had to invent, so the sharing argument favoured doing
  it first, not later.
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

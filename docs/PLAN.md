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

**Measured** — `docs/CONFORMANCE.md` is the first number: against `amc`'s own
`data/dmmeta`, 79.9% of fields have a reftype AMCC handles and **one** is
generated, because the corpus's namespace-qualified names are not C
identifiers. Regenerate with `scripts/conformance/run.sh`; the verdicts come
from `Ssim.Conformance` in Lean, the Python only slices and counts.

**Input** — schemas may be written as `amc` ssimfiles, not only as Lean terms.
`Amcc/Ssim/` reads four record types (`dmmeta.ctype`, `dmmeta.field`,
`dmmeta.inlary`, `amcc.root`) and eight of the twenty reftypes — everything no
template can emit is rejected by name. Nothing about the reader is proved; the
kernel-checked round trip in both directions is what stands in
(`docs/DIVERGENCE.md` §3.6). `scripts/ssim/` holds one schema per template, and
`scripts/smoke.sh` checks both that they round-trip and that they *are* the
schemas the templates are proved about.

**Emitted C** — five templates, twenty-five functions, in `amc`'s two-file
layout (`<name>_gen.h` + `<name>_gen.c`; `lake exe amcc all --out <dir>`), with
the single-file mode kept. The goldens are committed under `scripts/gen/`.

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
- `Llist.init_correct`, the five readers, both idempotence guards, and **both
  linking laws**: `Llist.insertLinks` — `Insert` links the row at the head and
  preserves the representation invariant, with the chain becoming `q :: qs` —
  and **`Llist.removeUnlinks`** — `Remove` splices the row out, whichever
  branch the generated `if (_prev != NULL)` takes, with the chain becoming
  `qs.erase q` and all eight invariant clauses re-established. The two branches
  are `exec_removeHead` and `exec_removeMiddle`, sharing `exec_removeTail`;
  `exec_removeBody` dispatches on `Backlinked.split`.
- **`Upptr.lookups_of_wf`** — a program `Wf.check` accepts has distinct
  function names, so the resolution hypothesis every accessor law assumes is
  supplied by acceptance. `Dmmeta.check` gained the matching schema-level
  clause: two fields whose `<ctype>_<field>` collide are rejected, because
  `c ++ "_" ++ f` is not injective in the pair.
- **The chain invariant** (`CSubset.Chain`): `Reaches` with `det`, `nodup`,
  `frame`, `tail`, `splice`, `next_of_mem`; `Backlinked` with `split`;
  `Flagged` with `cons`/`erase`; `Counted`; `RowsDisjoint`; and the
  path-disjointness lemmas that turn "different objects" into "different
  paths". `Thash` uses it unchanged.
- `Thash.size_correct` and both idempotence guards.
- **`Thash.findCorrect`** — `Find` returns *the first row on the bucket's chain
  whose key matches*, over `CSubset.Chain`'s `Reaches` with the bucket head in
  place of a list head. `find_hit` and `find_miss` turn either answer back into
  a statement about the store: a pointer is a row on the chain with that key,
  and `NULL` means **no** row on the chain has it. The original statement of
  `FindCorrect` claimed only "null or something with the right key" and was
  satisfied by a function that always returns `NULL`; it is strengthened, not
  weakened, to close.
- **`Thash.bucketInRange`** — the bucket subscript is always in range, so the
  only partial operation the hash index introduced cannot trap. Needs only
  `0 < NB`, not the power-of-two condition. `Thash.mask_eq_mod` proves what
  the power-of-two condition *does* buy: the mask is the modulus, which is the
  claim `docs/DIVERGENCE.md` §3.2 makes. `accepted_bucket_facts` ties both to
  the generator's own guard.
- **`Codegen.split_partition`** — the header/implementation split is an AST
  operation, and the two halves together carry exactly the input's
  declarations: none dropped, none duplicated, order preserved.
  `split_protos_match` adds that every body has a prototype and every prototype
  a body. The printer stays trusted (`docs/DIVERGENCE.md` §3.1, §3.4); the
  partition — the part that could silently lose a function — does not have to
  be.
- **`Upptr.genWellFormed`** — every schema `Dmmeta.check` accepts generates a
  program `Wf.check` accepts. The first of the three ctype-model templates to
  match what the generated headers already claim. `Templates/NameWf.lean`
  carries the function-name half for all three.
- **`Layout.layoutWellFormed`** — every schema `layoutCheck` accepts lowers to
  structs and globals `Wf.check` accepts: names distinct on both levels, sizes
  legal, every mentioned struct emitted, and every layout dependency emitted
  *earlier*. The multi-ctype form of `genWellFormed`, and the shared half of
  the every-schema gap — `Upptr`, `Llist` and `Thash` all emit this layout, so
  each is left with only its own functions. Proving it found and closed a hole
  in `Dmmeta.check`: an `Inlary` bound of `0` was accepted by the schema
  checker and rejected by the C-subset checker.
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

Three gaps remain against the full measure, all recorded in
`docs/DIVERGENCE.md` §3:

- **The front end is unverified.** `Amcc/Ssim/` turns ssim text into
  `Dmmeta.Db` and nothing is proved about it. This is the *worst-placed* of the
  three untrusted links, because a misread schema is invisible downstream —
  `Dmmeta.check` accepts it, every theorem proves, every smoke test passes.
  The round trip is what stands in. `docs/DIVERGENCE.md` §3.6 says what would
  discharge it, and it is the cheapest of the three: both sides are AMCC's own,
  so no C semantics is needed.
- **The pretty-printer is unverified.** `MilestoneTheorem` certifies the
  *AST*. `Codegen/Print.lean` turns that AST into C text and is covered only
  by goldens and `scripts/smoke.sh`. The *partition* into header and
  implementation is proved (`Codegen.split_partition`); the *rendering* of
  either half is not.
- **The pool has a proved model and a tested implementation with no formal
  link between them.** `Spec/Pool.lean` proves the algorithm; `Templates/Pool`
  emits it; nothing connects the two the way `ArrayTableInsert` connects
  `genC` to `absOf`.

---

## Next, in order

**Reordered by `docs/CONFORMANCE.md`**, which measured the generator against
`amc`'s own `data/dmmeta` for the first time. The measurement moved item 1 from
nowhere on this list to the top and demoted the remaining reftypes, because
79.9% of real fields already have a reftype AMCC handles and all but one of
them is blocked by something else entirely.

1. **A namespace-to-C-identifier mapping.** `dmmeta` names are qualified —
   `abt.FArch`, `dmmeta.Ctype` — and `Dmmeta.isCIdent` rejects a dot, so
   **4518 of 5659 real fields (79.8%) and 1381 of 1420 real ctypes (97.3%)**
   are out of reach for a reason that has nothing to do with data structures.
   It gates eleven times as many fields as the largest missing reftype
   (`Lary`, 390). This was not on the roadmap at all before the corpus was
   measured; it is now the single highest-value thing to build.
2. **`GenWellFormed` for `Llist` and `Thash`.** `Upptr` is done; the array
   table was already. These two are **blocked on a generator defect** rather
   than on proof effort: they emit two hand-built structs instead of the
   lowered layout, so an element ctype with a record-typed field references a
   struct that is not emitted, and a self-indexing `Thash` emits a duplicate
   struct name. Both are accepted by `Dmmeta.check` and rejected by
   `Wf.check`. The fix is to emit `genStructs` with the element and parent
   structs *extended*, which is also what cross-references will need.
   `PROGRESS.md` carries the handoff. Ahead of the reftypes because it
   is about whether the *existing* templates' guarantee is what the generated
   headers claim.
3. **Xref maintenance** tying the templates together, using the
   prepare/commit design from `Spec/Algebra.lean`. `dmmeta.xref` has 789
   records in the corpus, and `docs/CONFORMANCE.md` is explicit that a field
   counted "generated" today gets its accessors and *not* its participation in
   the indexes — so the conformance percentage overstates what a user gets
   until this exists.
4. **The remaining reftypes, in corpus order rather than alphabetical.**
   `Lary` (390 fields), `Smallstr` (140), `Ptrary` (136), `Bitfld` (75),
   `Tary` (69), `Global` (60) — then the tail. `Bheap` (23) and `Atree` (3)
   were named first on the old list and are near the bottom of the real
   distribution. `docs/GOALS.md` puts the whole vocabulary in scope;
   `docs/DIVERGENCE.md` §3 is the standing list of what is not attempted.

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

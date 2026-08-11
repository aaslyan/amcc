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

**Measured** — `docs/CONFORMANCE.md`, against `amc`'s own `data/dmmeta`:
**3909 of 5659 fields (69.1%) would be generated**, up from one before
`Dmmeta.mangle` landed, and 1419 of 1420 ctypes are nameable. What is left is
reftypes, not names. Regenerate with `scripts/conformance/run.sh`; the
verdicts come from `Ssim.Conformance` in Lean, the Python only slices and
counts.

**Names** — `Dmmeta.mangle` is `amc::strptr_PrintCppIdent`, applied at the
generator's boundary so the schema keeps its qualified names and the ssim
round trip is untouched. It is not injective, and `Dmmeta.check` rejects the
collisions it reintroduces rather than the mapping dodging them.

**Input** — schemas may be written as `amc` ssimfiles, not only as Lean terms.
`Amcc/Ssim/` reads five record types (`dmmeta.ctype`, `dmmeta.field`,
`dmmeta.inlary`, `dmmeta.smallstr`, `amcc.root`) and eight of the thirty-five
reftypes — everything no template can emit is rejected by name. The two
attribute tables go through **one** reader/printer registry keyed by
`Dmmeta.AttrTag`, which is the join `bitfld`, `charset`, `lenfld`, `substr`
and `fconst` all need. Nothing about the reader is proved; the
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
- **`Llist.genWellFormed`** — every schema `Dmmeta.check` accepts generates a
  program `Wf.check` accepts, **including a ctype that threads itself**. All
  nine `checkFun` obligations, both struct halves, and a field-lookup bundle
  with a branch for each of the two struct topologies.
- **`Thash.genWellFormed`** — the same for the hash index, the self-indexing
  case included. Two things are new there: `InsertMaybe` **calls** `Find`, so
  `Wf.Ctx.fun?` has to resolve a callee out of `funs.take i` — the first
  generated body to exercise that — and the bucket count's legality comes from
  the *generator's* `pow2Exp?` guard rather than from `Dmmeta.check`, since a
  `Thash` field is not an `Inlary` and the schema checker's array-bound clause
  never reaches it (`accepted_bucket_fits`).
  **With this, the banner every generated header carries is true for all five
  templates**, for every schema a user may write, not only for the samples.
- **The attribute join** (`Dmmeta.AttrTag`, `AttrData`, `Db.attr?`,
  `checkAttr`, `Ssim.attrHeads`) — a field's shape lives in a table of its own
  keyed by the field, and joining one on is now a mechanism rather than a
  per-reftype chore. One checker clause gives **every** table the named error
  "field claims a reftype whose attribute record is missing", and one registry
  gives every table its reader, printer and round trip.
  `inlary_facts_of_checkAttr` reads `Inlary`'s facts back out in the shape
  `Layout` and the templates already consumed.
- **The reftype vocabulary is complete** — 35 constructors, matching
  `dmmeta/reftype.ssim` row for row. It was 20, and the 15 missing ones were
  reported by the census as `unknown reftype`, which reads as a typo in the
  corpus rather than as a gap in AMCC.
- **`Templates.Smallstr`** — all three `strtype` abstractions stated;
  `absRpascal_encode` (the read-back law, no side condition) and
  `encodeRpascal_injective` proved; `rightpad_ambiguous` and
  `leftpad_ambiguous` are **checked witnesses** that the padded forms are
  lossy, so `docs/DIVERGENCE.md` §3.7's central claim is a fact in the build.
  Nothing is emitted yet: §3.8 is why.
- **`laws_apply`** in all three ctype-model templates — the resolution
  hypothesis every law assumes (`lookupFun p nm.x = .ok (xDef …)`) is now
  discharged **once, from `Dmmeta.check`**, instead of per schema by computing
  `Wf.check` on the generated program. `CSubset.lookupFun_of_wf` is the shared
  bridge: obligation 3 of `Wf.check` *is* `lookupFun_of_mem`'s side condition.
- **`Llist`'s struct and global obligations** — `checkStructs_gen_llist` and
  `checkGlobals_gen_llist`, over the *extended* table, with
  `Layout.field_ne_generated` spending the `clashesGenerated` clause to make
  the added link names distinct from the element's own. `checkFun` for the
  nine bodies is what is left.
- **`Layout.addFields`** and `checkStructs_addFields` /
  `checkGlobals_addFields` — `Llist`, `Thash` and `Pool` now **extend** the
  lowered struct table instead of emitting two structs of their own, and
  extending is proved to preserve every struct obligation. Five schemas that
  `Dmmeta.check` accepted and `Wf.check` rejected are closed and checked in as
  regressions; `PROGRESS.md` lists all five.
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
ctype, `Db` in declaration order, **all 35 reftypes** with their `dmmeta`
flags, and the per-field attribute join (`AttrTag`, `AttrData`, `Db.attr?`,
`checkAttr`) that carries `dmmeta.inlary` and `dmmeta.smallstr`. Six reftypes
lower to C. Layout lowering emits multi-ctype structs and the database
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

**Reordered again by `docs/CONFORMANCE.md`**, remeasured after mangling
landed. The generated share went from **1 field to 3909 of 5659 (69.1%)**, and
the name blocker went from 4518 fields to 3 — so the reftypes, which the first
measurement demoted, are now the whole remaining gap.

**Corpus order is not cost order**, and the previous version of this list
conflated them. The two are separated below.

1. **`u8` in the C subset, then `Smallstr` `rpascal`.** The attribute join is
   **done** — `Dmmeta.AttrTag`/`AttrData`/`Db.attr?`/`checkAttr` and one
   reader/printer registry — so `bitfld`, `charset`, `lenfld`, `substr` and
   `fconst` each need a payload arm and nothing else. `Smallstr` is modelled,
   checked and round-tripped, and `Templates/Smallstr.lean` states all three
   `strtype` abstractions with `rpascal`'s read-back law **proved** and the
   other two's ambiguity exhibited as checked witnesses
   (`rightpad_ambiguous`, `leftpad_ambiguous`).

   What is left is emission, and it is blocked on one thing: `amc` writes
   `u8 ch[N+1]; u8 n_ch;` and `CSubset.ScalarTy` is `u32 | u64 | bool`.
   `docs/DIVERGENCE.md` §3.8 is the entry and says what the change costs — a
   constructor on `ScalarTy`, `Value` and `Lit`, rows in the eval tables, arms
   in `Wf`, a name and a suffix in the printer, and a case in every proof that
   matches a `Value` or a `Lit` exhaustively. Bulk, not a decision. It
   unblocks five reftypes.

   Not in scope with it: choosing between §3.7's two routes for
   `leftpad`/`rightpad`. Those stay owed.

2. **`Ptrary` (136 fields).** An array of pointers over a base pool. Needs the
   pool to exist but not to grow, so it lands inside the current allocator
   story.
3. **`Lary` (390 fields) and the growable pools** — `Tary` (69), `Tpool` (40),
   `Lpool` (10). Largest by corpus count and **largest by cost**: `Lary` is a
   growable array, so it needs `Stmt.alloc`, the allocator contract and the L0
   heap rework, which is the biggest deferred item in the repo
   (`docs/DIVERGENCE.md` §2.2). Doing it first would spend the whole budget on
   one reftype; doing it after 1–2 means the pool machinery arrives with three
   consumers already waiting.
4. **Xref maintenance**, using the prepare/commit design from
   `Spec/Algebra.lean`. 789 `dmmeta.xref` records, and `docs/CONFORMANCE.md`
   is explicit that a field counted "generated" today gets its accessors and
   *not* its participation in the indexes — so the 69.1% overstates what a
   user gets until this exists.
5. **The tail**: `Global` (60), `RegxSql` (52), `Varlen` (39), `Bheap` (23),
   `Hook` (22), `Cppstack` (21), `Fbuf` (11), then the singletons. `Bheap` and
   `Atree` (3) headed this list two revisions ago and are near the bottom of
   the real distribution.

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

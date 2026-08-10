# AMCC — progress log

## Now

**`Llist.genWellFormed`, then `Thash`'s.** The generator defect is fixed and
the extension lemmas are proved; see "Where the every-schema gap stands" for
the three remaining pieces and the order. Then the attribute join — see
"Where the attribute join stands", whose blocking question is now answered.

## Done

- **P — the layout defect in `Thash`, `Llist` and `Pool`.** All three built two
  structs by hand and emitted only those; they now extend
  `Dmmeta.genStructs d` with `Layout.addFields`, exactly as `genUpptr` already
  emitted the whole lowered table. Both failing schemas from the handoff are
  checked-in regression cases — `nestedDb` (element ctype with a record-typed
  field) and `selfDb` (a ctype indexing itself) — run through `Wf.check` in
  Lean and *compiled* by `scripts/smoke.sh`, headers alone included. `Pool` had
  the same defect and got the same fix. The five original goldens are
  byte-identical, which is the expected result: the sample schemas were always
  the two-struct case.

- **O — mangling, and the remeasurement.** `Dmmeta.mangle` is
  `amc::strptr_PrintCppIdent` transcribed, applied at the generator's boundary
  so the `Db` keeps the schema's qualified names and the ssim round trip is
  untouched. It is deliberately not injective; `Dmmeta.check` gained one
  clause on mangled ctype names and the qualified-name clause from 47ecf60
  covers fields unchanged. **`docs/CONFORMANCE.md` went from 1 generated field
  to 3909 of 5659 (69.1%)**, and `docs/PLAN.md` was reordered on cost rather
  than corpus count — the attribute join that unblocks five reftypes now leads,
  and `Lary` sits behind it because it needs the heap rework.

- **N — `Upptr.genWellFormed`.** Proved, so the banner in
  `scripts/gen/upptr_gen.h` is now true of this template. `Templates/NameWf.lean`
  is the shared half: sublist-descent of the schema's qualified-name
  distinctness, `pairwise_flatMap` for the block structure, and
  `append_ne_rev` — which reverses both strings so the suffix comparison
  becomes a *decidable prefix* comparison (`prefixIncompat`, `by decide` per
  pair) rather than one needing length reasoning. `LawfulBEq Reftype` landed
  in `Dmmeta` on the way: the derive handler registers `BEq` and not the
  lawfulness, and every template selects its fields with `==` while its laws
  are stated with `=`.

- **M — `Reftype.needsRecordArg`.** Second hole of the same shape as the
  `Inlary` one: `Dmmeta.check` accepted an `Upptr` at `u64` and the generated
  accessors failed `Wf.check` with four type errors. Found by starting
  `Upptr.genWellFormed`. Fixed in the checker, with three examples including
  the `Pkey` exemption.

- **L — `Layout.layoutWellFormed`.** Proved: every schema the lowering accepts
  produces structs and globals `Wf.check` accepts. The hard clause is the one
  the single-table `genWellFormed` never faced — struct nesting must be
  acyclic — and it needed the transport of "declared earlier" from the *ctype*
  index the schema checker speaks in to the *struct* index `Wf.checkStructs`
  speaks in, across the filter that drops the scalar ctypes
  (`getElem?_filterMap`, `mem_filterMap_take`). `fieldTy_shape` is the one
  place the shape of a lowered field type is opened. `Db.find?_name` and
  `Db.find?_of_mem_pairwise` landed in `Dmmeta` on the way.

- **K — conformance measured against the real corpus.** `docs/CONFORMANCE.md`,
  from `amc`'s own `data/dmmeta`: 1420 ctypes, 5659 fields. **79.9% of fields
  have a reftype AMCC handles and exactly one is generated** — the rest are
  blocked by namespace-qualified names, which `Dmmeta.isCIdent` rejects.
  `Ssim.Conformance` decides every verdict in Lean using the shipping reader
  and the shipping `supported` list; `scripts/conformance/` slices and counts
  and decides nothing. `docs/PLAN.md`'s "Next, in order" was reordered on the
  strength of it: a name mapping went from absent to first.

- **J — the `Inlary` bound hole, and the shared half of the every-schema gap.**
  `Dmmeta.check` accepted `Inlary max:0`; `Layout.layoutCheck` accepted it too;
  and `CSubset.Wf.check` then **rejected** the generated program with
  `"D.row: bad array size"`. The front end was accepting what the back end
  could not emit — the failure `docs/GOALS.md`'s standing rule is about — and
  it is why `Layout.LayoutWellFormed` could not be proved as stated. Fixed in
  the *checker*, with two negative `rfl` examples pinning the message.
  `Amcc/Templates/LayoutWf.lean` now holds the shared machinery:
  `pairwise_filterMap_map`, `structs_distinct`, `fields_distinct`,
  `facts_of_check`, and the order-preserving-filter transport
  (`filterMap_take_prefix`, `mem_filterMap_take`). `dups_eq_nil_iff` and
  `distinct_eq_nil` moved from `ArrayTableWf` into `CSubset.Wf`, where every
  generator can reach them.

- **I — `Thash.findCorrect`.** Proved, over `CSubset.Chain`. The statement was
  **strengthened** first: the original `FindCorrect` said "null, or a pointer
  to something with the right key", which a function that always returns `NULL`
  satisfies. It now says `Find` returns `firstSat (keyAt m key k) qs` — *the
  first row on the bucket's chain whose key matches* — and `find_hit` /
  `find_miss` read either answer back into the store. New general machinery in
  `Chain.lean` (`Reaches.drop`, `Reaches.next_at`, `firstSat` and its lemmas,
  `keyAt`/`keyAt_iff`, `ptrOf`), and the local-store lemmas moved from `Llist`
  into `CSubset.Calls` where both templates can reach them.

- **H — the ssim front end.** `Amcc/Ssim/Tuple.lean` reads `amc`'s tuple format
  — `txt/ssim.md`'s grammar, `algo::PickSsimQuoteChar`'s quoting rule and
  `algo::_PrintQuotedChar`'s escapes, transcribed — and prints it back;
  `Amcc/Ssim/Schema.lean` maps four record types onto `Dmmeta.Db` and rejects,
  by name, the twelve reftypes no template emits. `Amcc/Ssim/Checks.lean` runs
  the round trip in both directions as `rfl`, plus the exact rejection
  messages. `lake exe amcc --ssim <file>` and `--ssim-of <name>`;
  `scripts/ssim/` holds one schema per ctype-model template, and
  `scripts/smoke.sh` diffs both the round trip *and* the checked-in text
  against what the built-in schema prints to. Two `docs/DIVERGENCE.md`
  entries: §3.5 (what is read) and §3.6 (nothing is proved, and why that
  matters more here than in the printer).

- **G — the header/implementation split.** `Amcc/Codegen/Split.lean` partitions
  a `Program` at the **AST** level, with `split_partition` proving the two
  halves together carry exactly the input's declarations and
  `split_protos_match` proving every body has a prototype and every prototype a
  body. `Print.header`/`Print.impl` render the halves in `amc`'s layout;
  `lake exe amcc all --out <dir>` writes them; `scripts/gen/` holds the
  goldens; `scripts/smoke.sh` builds each template three ways — single file,
  split with `-I`, and a translation unit that includes only the header — all
  under `-Wall -Wextra -Werror`, and diffs the split output against the
  goldens. Two `docs/DIVERGENCE.md` entries: §3.3 (`.c`, not `.cpp`) and §3.4
  (the partition is proved, the rendering is not).

- **F — `Llist.RemoveUnlinks`.** Proved, so both linking laws are closed.
  `exec_removeMiddle` is the branch where `row->prev` names a predecessor:
  `Reaches.splice` closes the chain over the gap, `Backlinked.of_append` /
  `Backlinked.append` re-hang the second half from `pp`, and
  `erase_append_cons_cons` is what `qs.erase q` computes to.
  `exec_removeBody` dispatches between it and `exec_removeHead` on the same
  `Backlinked.split` the invariant already supplied — the row's back-pointer
  *is* the case analysis, which is why the doubly-linked flavour unlinks in
  O(1). `removeUnlinks` runs it through `callFun_normal` as `insertLinks` does.

- **E — the C-name uniqueness obligation.** `Dmmeta.check` now rejects two
  fields whose `<ctype>_<field>` qualified names collide (`a`/`b_c` versus
  `a_b`/`c` — `c ++ "_" ++ f` is not injective in the pair), with a positive
  and a negative `rfl` example. `Upptr.lookups_of_wf` proves that a program
  `CSubset.Wf.check` accepts has pairwise-distinct function names, so
  `CSubset.lookupFun_of_mem` supplies the hypothesis every accessor law
  assumes. Without the checker clause a *legal* schema could emit two
  functions with one name and every law would be vacuous for it, with nothing
  to notice — which is what the obligation was.

- **B — the chain invariant.** `Amcc/CSubset/Chain.lean`. `Reaches` is
  inductive, so finiteness/acyclicity/NULL-termination are consequences of
  inhabitation rather than clauses; `det`, `nodup`, `frame`, `tail`, `splice`,
  `next_of_mem`, `mem_sub` are proved, as are `Backlinked` (+ `frame`,
  `split`), `Flagged` (+ `frame`, `cons`, `erase`), `Counted`, `RowsDisjoint`,
  and the path-disjointness lemmas (`fldPath_disjoint`, `fldPath_ne_disjoint`,
  `overlaps_ext`, `overlaps_symm`). `Thash` will use the same module unchanged.

- **C (most) — `Llist.InsertLinks`, and `Remove`'s head case.** `insertLinks`
  is proved over `ListInv`. For `Remove`: `exec_removeTail` (the last four
  statements) and `exec_removeHead` (the whole body when the row is the head)
  are proved. `RemoveUnlinks` itself awaits the middle-case assembly.

- **A — `Thash.BucketInRange`.** Proved, together with `mask_eq_mod` and
  `accepted_bucket_facts`. `PLAN.md`'s "Next, in order" corrected in the same
  commit: it still listed `Thash` as upcoming after it had shipped, and its
  numbering ran 0,1,2,3,3.

- **D — `Thash`.** `Templates/Thash.lean` emits five functions over a
  fixed-capacity, power-of-two bucket array and passes `Wf.check`. Proved:
  `size_correct` and both idempotence guards. **Not proved**: `FindCorrect`
  (needs the same chain invariant `Llist` needs) and `BucketInRange` (the
  no-trap obligation for the bucket subscript — small and self-contained).
  Three divergences recorded in `docs/DIVERGENCE.md` §3.2: fixed buckets with
  no rehash, a mask where `amc` has a hash, and a `CAP`-bounded chain walk
  because the subset has no `while` and no `break`. Differentially tested by
  `scripts/smoke.sh` on keys that collide.

- **C — `Llist` link/unlink.** `Templates/Llist.lean` emits `amc`'s `zdl`
  flavour — nine functions — and passes `Wf.check`. Proved: `init_correct`,
  the five readers, and both idempotence guards. **Not proved**: the linking
  laws, stated as `InsertLinks` / `RemoveUnlinks`. They need a reachability
  predicate over the store that does not exist yet; the "Still owed" section
  of the module says exactly what, and `docs/PLAN.md` carries it as the next
  proof obligation. Differentially tested by `scripts/smoke.sh`.

- **B — `Upptr` accessors.** `Templates/Upptr.lean`: `Init`/`Get`/`Set`/`Q`
  emitted per `dmmeta.reftype Upptr` field, with `get_set` (read-back),
  `init_correct`, `test_null`/`test_ptr`, and a frame law. Differentially
  tested by `scripts/smoke.sh` (`lake exe amcc upptr`).

- **A — `MilestoneTheorem` closed for the array table.** `InsertRefines`,
  `EraseRefines`, `RepInvPreserved` and all three `NoTrap` clauses are proved,
  in `Amcc/Templates/ArrayTableErase.lean` and
  `Amcc/Templates/ArrayTableInsert.lean`. `lake build` exits 0 with no new
  warnings, no `sorry`/`admit`, `scripts/smoke.sh` passes.

## Next

- `Llist.genWellFormed`, then `Thash.genWellFormed`
- The attribute-join mechanism, then `Smallstr` `rpascal`
- The `Dmmeta.check` ⟹ `Wf.check` link for the non-array templates. `Upptr`,
  `Llist`, `Thash` each have `Wf.check … = []` only as a computational example
  on their sample schema; the array table has it for *every* accepted schema
  (`genWellFormed`). Until that exists for the others, `lookups_of_wf`'s
  hypothesis is discharged per-schema rather than once.

## Where the every-schema gap stands

*Updated: the generator defect is **fixed** and five holes are closed. `Upptr`
is proved. `Llist` and `Thash` `genWellFormed` are the remaining work, and the
handoff below is the shape they follow.*

### Proved and committed

- `Layout.checkStructs_gen`, `Layout.checkGlobals_gen`,
  `Layout.layoutWellFormed` — the lowered table.
- **`Layout.addFields`** + `addFields_names`, `addFields_take`,
  **`Layout.checkStructs_addFields`**, **`Layout.checkGlobals_addFields`** —
  the *extended* table, which is what `Llist`/`Thash`/`Pool` now emit.
  `checkStructs_addFields` takes facts only about the fields a template adds:
  names not clashing with the struct's own, legal sizes, mentioned structs
  emitted, and `layoutDeps = []`. That last is true of every field any
  template adds (pointer, `bool`, `u32`, array of pointers) and is what keeps
  the declared-earlier obligation from needing re-establishment.
- `Templates/NameWf.lean` in full, `Upptr.genWellFormed`, and
  **`Llist.names_pairwise`** — the nine names, all thirty-six pairs.

### What `Llist.genWellFormed` still needs

`Templates/LlistWf.lean` has the statement and the name half. What is left:

1. **The struct half.**
   ```lean
   Wf.checkStructs (Layout.addFields dbN (dbFields nm elemN)
     (Layout.addFields elemN (elemFields nm elemN) (genStructs d))) = []
   ```
   Two nested `checkStructs_addFields` applications over
   `Layout.checkStructs_gen hchk`. The inner one's `hdist` is where the new
   `Dmmeta.check` clause is spent: `clashesGenerated` is exactly the statement
   that `mangle f.name ≠ mangle fld.name ++ "_next"` for every field `f` of
   the element, so a lemma turning that clause into the `Pairwise` the
   obligation wants is the one genuinely new thing to write. The `hres` side
   needs `elemN ∈ (genStructs d).map name`, which `checkStructs_gen`'s
   `hmemName` already builds — **lift it out of that proof into a named lemma
   first**; it is private to the proof body today.
2. **`checkGlobals`** — `checkGlobals_addFields` twice over
   `checkGlobals_gen`. Should be four lines.
3. **`checkFun` × 9.** `initDef`, `firstDef`, `nextDef`, `prevDef`, `inQDef`,
   `emptyQDef`, `sizeDef` are one statement each and follow `UpptrWf`'s
   `checkFun_defsFor` verbatim. `insertDef` (six statements, one `if`) and
   `removeDef` (eight, two `if`s) are the work. All nine need the field
   lookups `NameWf.ctx_field?` supplies — for `next`/`prev`/`inlist` on the
   element and `head`/`count` on the parent — and those come from the
   *extended* struct, so `NameWf.struct_field?` needs an `addFields` variant.
   Write that variant before starting the nine.

`Thash` is the same shape with five functions, one `forN` body and one `call`.
The `call` needs `Wf.Ctx.fun?` to resolve `Find` from `earlier`, which no
template has exercised — `checkFun`'s `earlier` is `p.funs.take i`, and `Find`
is emitted before `InsertMaybe`, so it is in the prefix. Nothing else is new.

### Five findings, all one shape

`Dmmeta.check` accepted schemas whose generated programs `CSubset.Wf.check`
**rejects** — the front end running ahead of the back end. The first two were
the *checker* being weaker than the theorem needs; the next two were the
*generator* being narrower than its statement; the fifth was created by fixing
the third and fourth. **All five are now closed.**

1. **`Inlary max:0`** — bad array size. Fixed: bound in `(0, u32Bound)`.
2. **`Upptr` at a scalar `arg`** — pointer to a machine scalar. Fixed:
   `Reftype.needsRecordArg`.
3. **`Thash`/`Llist`/`Pool` over an element with a record-typed field** —
   referenced a struct not emitted. Fixed: all three extend
   `Dmmeta.genStructs` via `Layout.addFields`.
   Regressions: `Thash.Examples.nestedDb`, `Llist.Examples.nestedDb`.
4. **`Thash` indexing its own ctype** — duplicate struct name. Fixed by the
   same change; two `addFields` at one name compose.
   Regression: `Thash.Examples.selfDb`.
5. **A field named what a template generates** — `task_row.zdl_todo_next`
   against `TaskDb.zdl_todo`. Fixed: `clashesGenerated`. A blanket
   reservation of the nine suffixes was tried first and is **wrong** — it
   rejects this repo's own `child_row.zd_next`, and `c_next`, `line_n`,
   `prev_head` in the corpus. The collision needs the stripped prefix to be a
   *declared field name*.

**Every template's `GenWellFormed` is a differential test between the two
checkers, run at proof time over all schemas.** Four attempts, five holes —
and the fifth was found by the *layout fix* rather than by a proof, because
extending the lowered table is what first put a generated field next to a
declared one in the same struct.

## Where the attribute join stands

**Not started.** `docs/DIVERGENCE.md` §3.7 is the research half, and it
answers the question that was blocking the design:

**`strict` does not forbid the ambiguous values.** Every use of it in
`cpp/amc/smallstr.cpp`'s `CheckSmallstr` guards a *naming-convention* check —
the numeric suffix must match the length, a `numstr`'s ctype name must carry
the prefix its `strtype`/`pad` imply, the base in the name must match
`numstr.base`. The two value-level checks there (`ValidRnumPadQ`, and no
`numstr` right-padded with `'0'`) are **not** guarded by `strict` and protect
numeric parsing, not injectivity. The generated `ch_SetStrptr` silently clips
and zero-fills. So a `rightpad`/`leftpad` smallstr is lossy by design and
without a guard, `abs` has no inverse, and a read-back law needs a side
condition on the value that AMCC must *invent* — which is why only `rpascal`,
whose `abs` is injective under `count ≤ N`, is safe to implement first.

What remains for the join itself:

- `Dmmeta` needs a per-field attribute table keyed like `Inlary` already is
  (`Db.inlary : List Inlary`, `Db.inlaryMax?`). Generalise that shape rather
  than adding a second special case: `bitfld`, `charset`, `lenfld`, `substr`
  and `fconst` all need it.
- `Ssim.Schema` needs the record head, the round trip, and a **named error**
  when a field claims a reftype whose attribute record is missing — the
  `Inlary needs a declared bound` message is the precedent.
- Then `rpascal`: `ch[N]` is the count, `RepInv` is `count ≤ N`, and the
  writers preserve it. State `abs` for all three `strtype`s so the two
  unimplemented ones are visible as owed rather than absent.

## How `Remove` went, in the end

The head case landed first and the middle case is a near-copy of it, with two
substitutions and one extra case:

- A3 writes `pp->next = _next` instead of `g.head = _next`, so every frame side
  condition in the branch is row-versus-row (`I.disj`) where the head case's
  was row-versus-parent (`row_ne_parent`). The head pointer does not move at
  all, and `headOf_append_cons` is what says so about the chain.
- A4 is character-for-character the head case's, except the value written is
  `.ptr pp` rather than `.null`. Factoring the packaging out of the head case
  first is what made that free.
- The `fields` clause needs a fourth case the head case does not have: `r = pp`,
  whose `next` A3 wrote. Its value is the one `Reaches.splice` consumes, so it
  was already in hand as `hppNext5`.

The three snags recorded from the earlier cut-back attempt were all real:

- `Ne.symm` direction. `hqPost`/`hppPost` give `q ≠ r` and `pp ≠ r`, and
  `RowsDisjoint` wants the arguments in the order the rows appear, so the
  symmetry has to be applied at the call and not assumed.
- Steering the `▸`. `hqs ▸ I.chain` rewrites inside `headOf qs` as well as the
  list, so the chain hypothesis is built by rewriting the *goal* backwards
  (`rw [← headOf_append_cons …, ← hqs]`) rather than by transporting the
  hypothesis forwards.
- `Backlinked.append`'s second obligation carries `lastOr (pre ++ [pp]) .null`
  literally; `lastOr_append_singleton` has to be rewritten in the **goal** as
  well as in the split's output, or the value `A4` installed does not match.

One thing that was not anticipated: `cases hpost : post` substitutes into the
goal but not into the hypotheses, so inside a branch `hnew4`/`hl3next` still
mention `post` while the goal mentions `q1 :: post0`. Every membership side
goal is then `by rw [hpost]; simp` rather than `simp`.

## Decisions

- **Mangling happens at the generator's boundary, not in the reader.** The
  `Db` stores the schema's own names — `abt.FArch` — and `Dmmeta.mangle` is
  applied where a schema name becomes a C identifier: `structOf`, `fieldTy`,
  `genGlobals`, `qualName`, and each template's call into `defsFor`. Mangling
  in the reader would have been fewer edits and would have broken the round
  trip, which is the one thing standing in for a proof of the front end.

- **`mangle` is not injective, and the checker catches the collisions.**
  `a.b` and `a_b` both give `a_b`. A clever injective encoding would produce C
  nobody can read and would put the correctness of names inside the mapping;
  instead `Dmmeta.check` gained one clause on mangled ctype names, and the
  `<ctype>_<field>` clause from 47ecf60 covers fields with no change at all —
  which is what it was added for.

- **`attribute [local irreducible] Dmmeta.mangle` in the three proof files.**
  `String.toList` does not whnf on a symbolic string, so unfolding `mangle`
  during elaboration *diverges*: every statement mentioning `mangle c.name`
  timed out, at 200k heartbeats and at 1M. It is `local` because the checker's
  `rfl` examples elsewhere compute `mangle` on literals and must keep doing so.
  The pattern to copy: name every projection through it (`structOf_name`) and
  abstract the name function out of shared lemmas (`structs_distinct`'s `nf`)
  so unification never has to look inside.

- **The conformance census is a separate classifier, not `readDb`.** `readDb`
  aborts on the first unsupported reftype, which is right for a front end and
  useless for a census: one bad field would hide the five thousand behind it.
  `Ssim.Conformance.classify` walks every tuple and records a verdict per
  record. It reuses `supported`, `isCIdent` and `parseFile` rather than
  re-deciding anything, and `verdict_iff_supported` is a `decide` proof that
  the census and the reader agree about what is in scope.

- **The census reports the reftype verdict and the name verdict in separate
  columns.** Collapsing them to one overall verdict hides the number that
  turned out to matter: 4518 fields have a supported reftype and are blocked
  only by the name. With one column the report would have said "1 of 5659
  generated" and left the reader to guess why.

- **`splitOnChar` is tail-recursive now, and `parseFile` accumulates
  reversed.** The obvious versions overflowed the stack and ran quadratically
  on `data/dmmeta` — seven thousand lines, most of a megabyte. A census that
  cannot read the corpus it measures is no census, so the shape of the reader
  is part of the requirement, not an optimisation.

- **`FindCorrect` was too weak to be worth proving, and was strengthened
  before being closed.** As first stated it said `Find` returns `NULL` or a
  pointer to a row with the right key — which `return NULL;` satisfies. It now
  says `Find` returns the *first* row on the bucket's chain whose key matches,
  so the miss case carries information too. Strengthening a statement to close
  it is the opposite of the failure mode the standing rule warns about, and the
  weak version is worth recording because it looked complete.

- **The chain-search test is a `Path → Bool`, not a proposition.** `Value` has
  no `DecidableEq` — the derive handler does not apply to its nested `List`
  recursion, and adding one by hand needs a mutual induction — and the
  generated guard is a Boolean expression anyway. `keyAt` is the Bool test and
  `keyAt_iff` converts, which is also why the guard proof lines up with
  `evalBin .eq` on two `u32`s with no lemma in between.

- **`_p`'s clause in the walk invariant is conditional.** Once `_hit` is set
  the outer `if (_hit == NULL)` fails and the body stops running *entirely*,
  including the advance — so `_p` freezes and does not track `qs.drop j`. The
  invariant states the `_p` clause under `firstSat … = none`, which is exactly
  when the body still runs. Stating it unconditionally is the version that does
  not go through, and it was the first thing that went wrong here.

- **The local-store lemmas moved from `Llist` to `CSubset.Calls`.** `step_local`,
  `readPath_setLocal`, `getLocal_setLocal_self`/`_ne` are about the subset, not
  about lists; `Thash`'s walk needed the same four. `Store.setLocal_toMem`
  joined `Store.setLocal_glb` in `Value.lean` for the same reason — it is the
  whole frame argument for a function that touches only its own temporaries.

- **The front end is `List Char`, not `String`.** `String.splitOn`,
  `String.trim`, `String.toNat?` and `String.startsWith` are well-founded
  recursions and **do not reduce in the kernel** — the same hazard `Dmmeta`'s
  `pow2Exp?` avoided for `Nat.log2`. Every one of them is re-done structurally
  over `List Char`. The reason is not tidiness: it is that the round trip is
  what stands in for a proof of the reader, and a round trip checked by
  `#guard` would be testing the *compiled* reader rather than the one the
  theorems see. `String.toList`, `String.ofList`, `List.foldl` and `toString`
  on a `Nat` all reduce, and are used freely.

- **The lexer is a left fold with an explicit state, not a fuel-driven
  scanner.** Each character advances the state exactly once, so the function is
  structural with no fuel parameter to pick a bound for. The state carries the
  position of the first **unquoted** colon, because that — not the first colon
  of the assembled token — is what separates key from value: `comment:"a:b"`
  has two colons and only one of them splits.

- **`amcc.root`, rather than reusing `dmmeta.nsdb`.** `amc` designates the
  database ctype by the `<ns>.FDb` convention inside a namespace declared by
  `dmmeta.nsdb`. `Dmmeta.Db` has no namespaces, so reusing that head would mean
  reading its `ns:` key as a ctype name — a reinterpretation pretending to be a
  match. Recorded in `docs/DIVERGENCE.md` §3.5.

- **Unknown tuple heads are rejected, not skipped.** A skipping reader would
  accept the whole of `data/dmmeta` and silently generate from the fraction it
  understood, which is exactly the failure the round trip exists to catch and
  the one it *could not* catch, since a skipped record cannot be printed back.

- **Record-level errors carry the line number too.** `parseFile` returns
  located tuples rather than bare ones. The first cut only located *lexical*
  errors, so "no AMCC template emits Bheap" arrived with no indication of which
  of two hundred lines said so.

- **`#pragma once`, not a named include guard.** `amc`'s generated headers use
  `#pragma once` (`include/gen/*_gen.h`, line 25 of every one), and the
  instruction was to match what `amc` does rather than what seems reasonable.
  It is also the mechanism with no name to collide.

- **The prototype/definition markers carry the C name, because that is all the
  AST has.** `amc` writes `// func:abt.FArch.msghdr.CopyOut` in the header and
  `// --- abt.FArch.msghdr.CopyOut` in the `.cpp` — the *provenance*, ctype and
  field and operation. `CSubset.FunDef` carries only the emitted C name, so the
  markers carry that. Threading provenance through the AST would be a real
  change to `Program` for a comment, and it is not free: it would have to be
  maintained by every template and checked by nothing.

- **The split's globals lose `static`.** Single-file output keeps
  `static T g;` — internal linkage, zero-initialised, nothing else in the
  program. A global declared `extern` in a header cannot be `static`, so the
  split emits `extern T g;` and `T g;`. The two modes therefore differ in
  linkage and only in linkage, which is why `smoke.sh` diffs the two modes'
  *answers* against each other and not just against the expectations.

- **The drivers were left declaring their own structs and prototypes rather
  than including the generated header.** Redundant on its face — but it makes
  the driver an *independent* transcription of the interface, so the split
  build checks the header against a second opinion instead of against itself.
  A driver that included the header could not catch a header that declared the
  wrong signature.

- **`Remove` is three lemmas, not one: `exec_removeHead`, `exec_removeMiddle`,
  `exec_removeBody`.** The generated `if (_prev != NULL)` is the branch, and
  `Backlinked.split` is exactly the same case distinction stated over the
  invariant — so the dispatch is one `rcases` and neither branch has to carry
  the other's hypotheses. Trying to prove one lemma covering both is what made
  the earlier attempt unmanageable: the chain rewriting differs
  (`Reaches.tail` versus `Reaches.splice`), the erase rewriting differs, and
  the head case has no `pp` to say anything about.

- **`Backlinked` gained `of_append`/`append` and `lastOr` rather than a
  bespoke splice lemma.** An unlink is "split the chain, shorten the second
  half, put it back", and the head case is the degenerate split at `[]`. One
  pair of lemmas covers both branches and `Thash` will reuse them, where a
  splice lemma specialised to `Llist`'s field names would not.

- **`Dmmeta.check` gained a qualified-name clause rather than each template
  checking its own names.** Every template prefixes its operation names with
  `<ctype>_<field>`, so the collision is a property of the schema, not of any
  one generator; catching it once is what lets each template state its laws
  against "a program in which the name resolves" and have that be reachable.

- **`InsertLinks` and `RemoveUnlinks` were not provable as first stated, and
  are restated over `ListInv`.** The originals were purely local — "after
  `Insert` the head is the row and its flag is set" — with no hypothesis
  ruling out the neighbours aliasing the row. `Remove` reads `row->prev` and
  `row->next` and writes *through* them, so without disjointness the second
  write can clobber the first: the old statements describe code that does not
  exist. Both restatements keep every conclusion the originals had and add the
  abstract effect (the chain becomes `q :: qs`, or `qs.erase q`). Strictly
  more is claimed about the result; strictly more is assumed about the input,
  and what is assumed is what an allocator supplies.

- **`Flagged` is indexed by a universe of live rows, not by all paths.** The
  backward direction is what makes the guards sound, and it cannot be
  maintained over all paths: a write to one row's flag is invisible only where
  it does not overlap, and an arbitrary path may be a prefix of a row.

- **`Reaches` is inductive rather than a fixpoint with an acyclicity clause.**
  A cyclic structure then admits no finite derivation, so no witness list
  exists for it at all — sharper than carrying "no cycle" as an invariant,
  because nothing has to maintain it, and it makes `nodup` a theorem.

- **`BucketInRange` was false as stated and is now correct.** It quantified
  over every `nb` including `0`, where `Nat` subtraction makes the mask `0` and
  `0 < 0` fails. Added `0 < nb`, which `genThash` already enforces. This is a
  correction, not a weakening: the old statement could not have been
  discharged for any schema, so nothing that used to be claimed is now
  claimed less.

- **The power-of-two condition does not keep the subscript in range.** Masking
  clears bits, so `key & (NB-1) < NB` for *any* positive `NB`. What
  power-of-two buys is `mask_eq_mod` — that the mask is the modulus — which is
  the claim `DIVERGENCE` §3.2 makes and which is now checked rather than
  asserted. Stating them as two theorems keeps the two claims from being
  confused, as the module docstring had invited.

- **`genThash`'s power-of-two guard now returns the exponent.** It was
  `Nat.land nb (nb-1) == 0`, from which recovering `nb = 2 ^ e` needs a real
  induction over `Nat.land` that core does not supply. `pow2Exp? pow2Fuel nb`
  is a structural search that hands the witness straight to the proofs. It is
  not `2 ^ Nat.log2 n == n`, because `Nat.log2` is well-founded and does not
  reduce in the kernel — that would have cost every schema check in the file
  its `rfl`.

- **`Path.overlaps` now means something.** It was defined in `Value.lean` with
  a docstring promising "no aliasing analysis — a prefix test" and *never
  used*. `Store.readPath_writePath_disjoint` proves the promise: a write at
  `p` is invisible at every `q` with `p.overlaps q = false`. The pre-existing
  `readPath_writePath_ne` only covered *different roots*, which is useless for
  two rows of the same pool. Getting there needed `LawfulBEq` instances for
  `PathStep` and `Root` — the `deriving` handler does not register them, and
  `List.isPrefixOf` cannot be reasoned about without them.

- **The `Upptr` laws are stated against an arbitrary program in which the name
  resolves**, with `lookupFun_of_mem` turning "the schema declares this field"
  into that hypothesis. Name collisions (`a`/`b_c` and `a_b`/`c` generate the
  same C name) are a whole-schema property and belong to the checker, not to
  this template; making that a hypothesis says so instead of hiding it.

- **`resolve_slot` / `resolve_field` / `resolve_ptrField` / `write_slotField`
  take the storage binding, not `RepInv`.** They only ever used `R.storage`,
  and the writers need to resolve against *intermediate* stores that satisfy
  the binding but for which `RepInv` has not yet been re-established. Taking
  `hglb` is what makes `exec_assignFields` possible at all.

- **`exec_assignFields` is parameterised by `lv : Ident → LVal` plus a
  resolution hypothesis quantified over stores.** One lemma then serves both
  `_at->f` (the update path, pointer from `find`) and `g_<t>[_j].f` (the
  fresh-slot path, loop index). The two lvalue forms resolve for different
  reasons but to the same path, and the writes in between touch only the
  storage global — never the frame the resolution depends on.

- **`setFields` (a left fold of `Env.set`) is the accumulated effect.**
  Everything downstream — the row's key, occupancy and value fields reading
  back as intended — is a statement about `setFields`, proved before any of it
  meets the generator. `Env.set` is domain-invariant, so `RowOk`'s
  "field present" clauses survive any number of writes for free.

- **Two abstraction lemmas, not one.** The update path and the fresh path both
  return `true` and both establish `Abs.insert`, but for different reasons:
  `absOf_update` because the key stayed where it was, `absOf_setRow` because
  it appeared where nothing was. `repInv_setRow`'s `distinct` clause is where
  "the `find` that ran first missed" is spent.

- **`Wf.TypeSound` is confirmed off the critical path.** Every structural
  error the array table could raise is dischargeable from `RepInv` where it
  arises. Recorded in `Amcc.lean` and `docs/PLAN.md`.

## Findings

- **`Thash` reuses the chain problem, it does not add a new one.** A bucket is
  a chain, so the same reachability predicate serves both templates. The one
  genuinely new obligation is the bucket subscript's bound, which is algebra
  about `UInt32.land` and depends on no invariant at all — which is why it is
  stated separately as `BucketInRange` and is the next thing to prove.

- **A linked list has no carrier.** `RepInv` for the array table quantifies
  over indices of a `List Value`. A list's shape is a property of a graph in
  the heap, so its invariant needs a reachability predicate over the store —
  and `Thash` will need the same one, because a bucket *is* a chain. That is
  why the linking laws are stated rather than proved: building the predicate
  once, for both, beats improvising it twice.

## Dead ends

- **`simp only [execAt]` in a `.seq` collapses the goal past `step_local`.**
  Reducing the first statement of a block by unfolding `execAt` leaves a term
  in which `execAt p callee` no longer appears, so the next `step_local` cannot
  unify its `p`/`callee`. Prove the first statement's execution as a named
  `have` and `rw` it instead — that is what both branches of
  `exec_findLoopBody` do.

- **A `show (do match ← … with | …)` breaks if the `match ←` wraps.** The
  continuation line is indented past the `|` arms, which ends the `do` block's
  layout and produces `unexpected token '|'`. Keep the `match ←` on one line,
  however long.

- **`set`, `by_contra`, `List.Forall₂` are unavailable** — no mathlib. `set`
  in particular is easy to reach for and fails with a bare "unknown tactic";
  write the term out or use a `have` for each fact about it.

- **`∃ x (y : T), p` does not parse.** Write `∃ (x : S) (y : T), p`.

- **`simp only [evalExpr]` / `[execAt]` unfold too far** for a hypothesis
  stated one level up (`read_field`, `resolve_ptrField`) to match afterwards.
  Peel exactly one constructor first — `execAt_seq`, `execAt_cond`,
  `execAt_assign`, `execAt_forN`, or a `show` of the `do` block — then rewrite.

- **`cases h : e` substitutes in the goal but not in hypotheses.** The `rw [h]
  at hyp` is still needed, and its absence shows up as a confusing "did not
  find the pattern" against a goal that already looks rewritten.

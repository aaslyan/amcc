# AMCC — progress log

## Now

**`Llist.RemoveUnlinks`** — the two branch assemblies. Everything they need is
proved; see "Where Remove stands" below. Then `Thash.FindCorrect`.

## Done

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

- `Llist.RemoveUnlinks` — the middle-case assembly, then both through
  `callFun_normal` (see "Where Remove stands")
- `Thash.FindCorrect`, over `CSubset.Chain`
- The `Dmmeta.check` ⟹ `Wf.check` link for the non-array templates. `Upptr`,
  `Llist`, `Thash` each have `Wf.check … = []` only as a computational example
  on their sample schema; the array table has it for *every* accepted schema
  (`genWellFormed`). Until that exists for the others, `lookups_of_wf`'s
  hypothesis is discharged per-schema rather than once.

## Where `Remove` stands

**Head case: done.** `Llist.exec_removeHead` is proved — `row->prev` is `NULL`,
so `Backlinked.split` puts `q` first, the generated `if (_prev != NULL)` takes
its else branch and writes `g.head = _next`, the new chain is `Reaches.tail`,
and `erase_cons_self` turns `q :: post` into `qs.erase q`. `exec_removeTail`
finishes. The A4 packaging (`if (_next != NULL) _next->prev = _prev`, split on
whether `post` is empty) is in that proof and is what the middle case should
copy — it is identical there except the value written is `.ptr pp` instead of
`.null`.

**Middle case: not assembled.** It was written once and cut back rather than
committed under a `sorry`. Its shape, and everything it needs, is proved:

- `hqs : qs = pre ++ pp :: q :: post` and `pval = .ptr pp`, both from
  `Backlinked.split`.
- A3 takes its *then* branch and writes `fldPath pp next := headOf post` —
  `step_ptr` with `ptr := tmpPrev`, `q := pp`.
- Chain: `Reaches.splice pre (headOf qs) pp q post`, then rewrite the head
  value with `headOf_append_cons`.
- Back-links: `Backlinked.of_append (pre ++ [pp]) .null (q :: post)` splits the
  old chain; `Backlinked.append` puts it back with `post` re-rooted at `pp`
  (`lastOr_append_singleton` is the bridge). The `post = q1 :: post0` sub-case
  takes `q1.prev` from A4 and the rest from `of_append`'s second component.
- Erase: `erase_append_cons_cons pre pp q post` needs `q ∉ pre` and `q ≠ pp`,
  both from `List.pairwise_append.mp (hqs ▸ hnd)`.

Three things went wrong in the cut-back attempt and are worth knowing:

- `Ne.symm` direction on `hppPost`/`hqPost` — they give `pp ≠ r` and `q ≠ r`,
  and `RowsDisjoint` wants the arguments in the order the rows appear.
- `hsplit`'s `Backlinked.of_append` needs the list in `(pre ++ [pp]) ++ q ::
  post` form; `hqs ▸ I.back` gives `pre ++ pp :: q :: post`, so the `▸` has to
  be steered rather than left to unify.
- The `fields` clause needs a fourth case in the middle branch: `r = pp`, whose
  `next` A3 wrote. The head case has only three.

**Then**: `removeUnlinks` assembles the two branches through `callFun_normal`
exactly as `insertLinks` does.
## Decisions

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

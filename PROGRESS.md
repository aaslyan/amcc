# AMCC — progress log

## Now

**B — `Upptr` accessors.**

## Done

- **A — `MilestoneTheorem` closed for the array table.** `InsertRefines`,
  `EraseRefines`, `RepInvPreserved` and all three `NoTrap` clauses are proved,
  in `Amcc/Templates/ArrayTableErase.lean` and
  `Amcc/Templates/ArrayTableInsert.lean`. `lake build` exits 0 with no new
  warnings, no `sorry`/`admit`, `scripts/smoke.sh` passes.

## Next

- C — `Llist` link/unlink over the pool
- D — `Thash`; record fixed-capacity buckets as a divergence

## Decisions

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

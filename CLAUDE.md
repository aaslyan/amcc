# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

**Read `docs/GOALS.md` first — it is canonical, and if anything here contradicts it, it wins.**

AMCC is a **verified reimplementation of OpenACR's `amc`** (<https://github.com/alexeilebedev/openacr>), written in Lean 4 (Lake package, no external dependencies — no mathlib).

**The goal: replicate OpenACR's `amc` with provable correctness.** amc turns a relational schema into data-structure code; AMCC does the same, and additionally emits — as Lean statements anyone can read, cite and build on — what the generated functions are guaranteed to do. The deliverable is not only C: it is C *plus explicit, machine-checked statements of its behaviour*, so a consumer can depend on the guarantee rather than on testing.

AMCC is a general-purpose data-structure generator. It is not written for, aimed at, or scoped by any particular application.

**The standing rule:** `amc`'s actual capability defines what to build; proof difficulty is an engineering problem to solve inside that target, **never** a reason to shrink it. Completeness of the reftype vocabulary is the goal, not a stretch goal. If the C subset cannot express something `amc` generates, the subset changes.

Use the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`).

## Commands

- `lake build` — builds the library and proof-checks everything. **This is the main verification signal**; there is no separate test runner.
- `lake exe amcc [orders|tag]` — print the generated C for an example schema to stdout.
- `bash scripts/smoke.sh` — the differential smoke test: emits the C, compiles it with `cc -Wall -Wextra -Werror`, replays the `ArrayTableChecks` call sequences against the binary, and diffs the answers against the Lean semantics'. Needs a C compiler; this is the one check `lake build` cannot run.
- `lake env lean Amcc/CSubset/WfChecks.lean` — check a single file in the Lake environment.
- `lake clean` — remove build artifacts when a stale build is suspected.

## The build closure — critical

`Amcc.lean` is the library root and the **build closure**: a module not imported there is silently not proof-checked by `lake build`. When adding any module, add its import to `Amcc.lean`. (The companion repo had an incident where a dropped import made a proof file silently stop being checked.) Note the phase-status section of `Amcc.lean`'s docstring can lag the actual files — trust the imports and the modules themselves.

## Architecture

The project is a pipeline of phases; each phase's modules only depend on earlier phases.

**Phase 0 — the C subset** (`Amcc/CSubset/Syntax.lean`, `Examples.lean`): AST of the only C the generators may emit. The design bet: classic undefined behaviour is made *inexpressible* (no signed ints, no division/shifts, pure expressions, no recursion) rather than modelled. **Three** partial operations remain: out-of-range subscript, null dereference, use-after-free — all proof obligations on generated code, all distinguishable from the structural errors a well-formed program cannot raise. (The original design had only the first, by forbidding dynamic storage outright; that made every table's capacity a compile-time constant, which is why it was changed.) `Examples.tinyTable` is a hand-written instance of the shape Phase 3 generates.

**Phase 1 — semantics** (`Amcc/CSubset/`):
- `Value.lean` — structured stores (not bytes); a pointer is an access path (`Path`) rooted at a **global or a heap block** (`Root`); `Value.null` exists; `Mem` (globals + heap + fresh-id counter) is what persists across calls, and `Store` adds the current frame. Block identities are monotone and never reissued, which is what makes use-after-free detectable. `Value.arrOf` builds a **runtime-sized** array — size lives in the value, not the type.
- `Eval.lean` — `execStmt`, a *total, structurally-decreasing function* (possible because of Phase 0's restrictions). Errors are classified: `oob` is the only one reachable for well-formed programs; `typeErr`/`unbound`/`depth` are made unreachable by the checker.
- `SmallStep.lean` — the normative relation `Step` (stuck = error), plus `execStmt_sound` and `step_det` pinning the function to the relation.
- `Wf.lean` — decidable checker for the well-formedness obligations; returns a *list of violations* (generator-friendly), with `Program.wf` as the Boolean view for theorems.
- `Sanity.lean` — reusable frame lemmas (`assign_local_preserves_glb`, `call_restores_frame`) plus closed `rfl` example theorems.

**Phase 2 — schema DSL** (`Amcc/Schema.lean`): the generator's input language. `Reftype` (from OpenACR's `dmmeta.reftype`) names a field's structural role — currently only `Pkey` and `Val`. The leading-underscore namespace is reserved for generated locals; `Names` centralizes generated C names so the collision check and generator can't drift apart.

**Phase 3 — first template** (`Amcc/Interface.lean`, `Amcc/Templates/ArrayTable.lean`): `MapLaws` is a *bundled* interface (deliberately not a type class) with four laws; `genC` emits a fixed-capacity array table with linear scan and occupancy flags; `absOf` is the abstraction function written independently of `genC` — `ArrayTableChecks.lean`'s `absOf_after_insert`-style equations are the one place the two are forced to agree. `ArrayTableWf.lean` **proves** `GenWellFormed` (`genWellFormed`: every accepted schema generates a `Wf.check`-clean program) — its infrastructure (LawfulBEq instances for the syntax types, `dups`/`Pairwise` characterisation, `find?_keyed` lookup lemmas, `checkStmt_block` distribution) is reusable for the remaining proofs. Proof-engineering caveat learned there: full `simp` fuses `find?`/`flatMap` over `map` before custom rewrites match — state sub-lemmas over a *symbolic* `Wf.Ctx` with projection equations as hypotheses, and decompose with `simp only`.

**Phase 4 — printing** (`Amcc/Codegen/Print.lean`, `PrintChecks.lean`): `Print.program` renders a `Program` as one C translation unit. It is a **trusted, unverified** component, kept audit-simple: every compound expression parenthesised, every literal suffixed, declarators printed by structural recursion. `PrintChecks.lean` pins the printed output byte-for-byte (golden tests); `scripts/smoke.sh` is the empirical link to real C (see Commands). `Main.lean` + the `amcc` exe target are the CLI.

Two Props are *stated but unproved* — treat them as the open obligations, not as available lemmas:
- `Wf.TypeSound` (`Amcc/CSubset/Wf.lean`) — well-formed programs can't raise `typeErr`/`unbound`/`depth`; the bridge Phase 3 consumes.
- `ArrayTable.MilestoneTheorem` (`Amcc/Templates/ArrayTable.lean`) — every well-formed schema's generated table simulates the abstract map.

**Reference point:** the target is `amc`'s generated API and reftype vocabulary (`~/openacr*/data/dmmeta/`). Generated functions should look like amc's, adapted to C — pointer-returning `Find` with `NULL` for absent, fields read through the pointer, amc's operation-name suffixes. Where AMCC differs from amc it should be because a proof demanded it, and the difference should be written down.

## Testing conventions

- Regressions are Lean `example` declarations in `*Checks.lean` modules (`WfChecks.lean`, `ArrayTableChecks.lean`), computational via `:= rfl` whenever possible — `rfl` is kernel reduction, so these are checked equalities, not sampled tests.
- Negative checker cases assert the **exact error list**, so a silently weakened check fails visibly. Each negative example violates exactly one obligation.
- Docstrings on checked examples carry the marker `checked by: \`lake build\``.
- Long `rfl` computations need `set_option maxHeartbeats` raised (see `Sanity.lean`, `ArrayTableChecks.lean`); keep very expensive runs out of `rfl` entirely.
- **Two computational tiers.** Small runs are `rfl` (kernel-checked). Any long generated-program run is `#guard` (compiled evaluation — still fails `lake build` on a wrong answer, but trusts the compiler). The boundary is real and measured: kernel-normalising the full-table scan case grew past 23 GB and OOM'd, while `#guard` runs it in ~0.25 s. Comparisons under `#guard` need `BEq` (`Value` derives it; `Except`'s instance is derived in `ArrayTableChecks.lean`).

## Style

- Two-space indentation in declarations and match arms; namespaces match the directory path.
- PascalCase for inductives/structures (`ScalarTy`, `Program`); lower camelCase for definitions and examples (`execStmt`, `tinyTable`, `pMissingReturn`).
- Prefer small structural Lean definitions over ad hoc string logic; keep module docstrings specific — the existing ones explain *why* each design decision was made, and new modules should follow that pattern.

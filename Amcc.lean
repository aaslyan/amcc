import Amcc.Spec.Algebra
import Amcc.Spec.Pool
import Amcc.Spec.Table
import Amcc.CSubset.Syntax
import Amcc.CSubset.Examples
import Amcc.CSubset.Value
import Amcc.CSubset.Eval
import Amcc.CSubset.Wf
import Amcc.CSubset.WfChecks
import Amcc.CSubset.SmallStep
import Amcc.CSubset.Sanity
import Amcc.Schema
import Amcc.Dmmeta
import Amcc.Interface
import Amcc.Templates.ArrayTable
import Amcc.Templates.ArrayTableWf
import Amcc.Templates.ArrayTableFind
import Amcc.Templates.ArrayTableErase
import Amcc.Templates.ArrayTableInsert
import Amcc.Templates.Layout
import Amcc.Templates.Pool
import Amcc.Templates.ArrayTableChecks
import Amcc.Codegen.Print
import Amcc.Codegen.PrintChecks

/-!
# AMCC — a verified schema-to-C generator

## The algebra
- `Spec.Algebra` — the axiomatic core, independent of everything else: the
  postulated allocator contract, structured memory, the object store, access
  patterns as views, and the relational promise derived from them.
- `Spec.Pool`    — a free-list pool (OpenACR's `Tpool`/`Lary` shape) **proved**
  to satisfy `ObjStoreLaws` over an arbitrary base provider, with `reserve`
  for the two-phase insert, and a counterexample showing a *moving* pool
  cannot satisfy the stability law.
- `Spec.Table`   — the two joined: a concrete table over the pool, carrying a
  `Count` index, **proved** to satisfy `TwoPhaseLaws`. The retrieval and
  invisible-failure promises then follow from the generic theorems with no
  further work, which is what having the interface is for.

Library root, and the **build closure**: a module not imported here is not
proof-checked by `lake build`, so `lake build` succeeding is the whole
verification signal. (A dropped import is the one way a proof file can
silently stop being checked, so this file is the place to look when something
that should fail does not.)

## Phase 0 — the C subset's syntax
- `CSubset.Syntax`   — the AST, and the eleven well-formedness obligations
- `CSubset.Examples` — `trivialCell` and `tinyTable`, hand-written ASTs

## Phase 1 — semantics
- `CSubset.Value`     — values, access paths, stores, the frame lemmas
- `CSubset.Eval`      — the executable big-step semantics (`execStmt`)
- `CSubset.Wf`        — the decidable checker for the obligations
- `CSubset.WfChecks`  — the checker exercised, positively and negatively
- `CSubset.SmallStep` — the normative relation, determinism, and
                        `execStmt_sound` / `exec_iff_steps`
- `CSubset.Sanity`    — the phase's sanity theorems

## Phase 2 — the schema DSL
- `Schema` — the legacy single-table input language, and its checker
- `Dmmeta` — the **ctype model**: `Ctype`, `Field` whose `arg` names another
  ctype, `Db` in declaration order, the full `Reftype` vocabulary with its
  `dmmeta/reftype.ssim` flags, and a checker that resolves every `arg` and
  keeps layout acyclic while letting pointers and indexes refer forwards

## Phase 3 — the array-table template
- `Interface`                  — the abstract map (`MapLaws`) a table implements
- `Templates.ArrayTable`       — `genC`, `absOf`, and the milestone obligations
- `Templates.ArrayTableWf`     — **proved**: `GenWellFormed` — every accepted
                                 schema generates a program `Wf.check` accepts
- `Templates.ArrayTableFind`   — **proved**: `FindCorrect`, `NoTrapFind`, and
                                 the resolve/read/write lemma bank the writers
                                 are built from
- `Templates.ArrayTableErase`  — **proved**: `EraseRefines`, `NoTrapErase`
- `Templates.ArrayTableInsert` — **proved**: `InsertRefines`, `NoTrapInsert`,
                                 `RepInvPreserved`, and with them
                                 **`MilestoneTheorem`** — every well-formed
                                 schema's generated table simulates the
                                 abstract map
- `Templates.ArrayTableChecks` — the generator exercised on concrete schemas

## Phase 4 — printing
- `Templates.Pool`      — the **pool template** over the ctype model: a
                          free-list allocator (`Tpool`'s shape) emitted as C,
                          with `Init`/`Alloc`/`Free`/`N`
- `Codegen.Print`       — the pretty-printer to C text (trusted, unverified)
- `Codegen.PrintChecks` — byte-for-byte golden tests of the printed output

`lake exe amcc` prints the generated C for an example schema;
`scripts/smoke.sh` compiles it and replays the `ArrayTableChecks` call
sequences against the binary — the differential check of printer + compiler
against `execStmt`.

## Still open
`CSubset.Wf.TypeSound`. It turned out **not** to be on the critical path for
Phase 3: every structural error the array table could raise is dischargeable
from `RepInv` where it arises, so `MilestoneTheorem` is proved without it. It
remains owed as the general bridge a template that cannot argue locally would
need.

`Codegen.Print` is unverified — see `docs/DIVERGENCE.md` §3. A closed
`MilestoneTheorem` certifies the generated **AST**; the C text is covered by
goldens and `scripts/smoke.sh` only.
-/

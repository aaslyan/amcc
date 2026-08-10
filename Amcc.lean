import Amcc.Spec.Algebra
import Amcc.Spec.Pool
import Amcc.Spec.Table
import Amcc.CSubset.Syntax
import Amcc.CSubset.Examples
import Amcc.CSubset.Value
import Amcc.CSubset.Eval
import Amcc.CSubset.Calls
import Amcc.CSubset.Chain
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
import Amcc.Templates.Upptr
import Amcc.Templates.Llist
import Amcc.Templates.Thash
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
- `CSubset.Chain`     — chains in the store: `Reaches` (inductive, so
                        acyclicity is a consequence of inhabitation rather
                        than a clause), `Backlinked`, `Flagged`, `Counted`,
                        `RowsDisjoint`, and the path-disjointness lemmas.
                        Used unchanged by `Llist` and `Thash` — a bucket is a
                        chain
- `CSubset.Calls`     — template-independent reasoning about a call: peeling
                        one statement, resolving a name to a definition, and
                        getting in and out of `callFun`
- `CSubset.Wf`        — the decidable checker for the obligations
- `CSubset.WfChecks`  — the checker exercised, positively and negatively
- `CSubset.SmallStep` — the normative relation, determinism, and
                        `execStmt_sound` / `exec_iff_steps`
- `CSubset.Sanity`    — the phase's sanity theorems

## Phase 2 — the schema DSL
- `Schema` — the legacy single-table input language, and its checker
- `Dmmeta` — the **ctype model**, including the qualified-name clause that
             rejects two fields printing to the same C identifier: `Ctype`, `Field` whose `arg` names another
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
- `Templates.Thash`     — the **hash index**: five functions over a
                          fixed-capacity, power-of-two bucket array. The count
                          and both idempotence guards are proved, and so is
                          `bucketInRange` — the bucket subscript cannot trap —
                          together with `mask_eq_mod`, which is what the
                          power-of-two requirement actually buys. `FindCorrect`
                          is stated and owed
- `Templates.Llist`     — the **intrusive doubly-linked list** (`amc`'s `zdl`
                          flavour): nine functions, with the readers, both
                          idempotence guards, **`insertLinks`** and
                          **`removeUnlinks`** all proved over `ListInv` — both
                          linking laws are closed, so the chain the template
                          maintains is now a theorem about the emitted code
                          rather than a claim about it
- `Templates.Upptr`     — the **up-pointer template** (its `lookups_of_wf`
                          shows `Wf.check` acceptance supplies the resolution
                          hypothesis every accessor law assumes): `Init`/`Get`/`Set`/`Q`
                          for a `dmmeta.reftype Upptr` field, with the
                          read-back law (`get_set`) and the frame law proved
                          for every program the names resolve in
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

`Templates.Thash.FindCorrect`. The predicate it needs — `CSubset.Chain` —
exists, and both of `Llist`'s linking laws are now proved over it, so what
remains is the assembly. `Templates.Thash.BucketInRange` is closed.

`Codegen.Print` is unverified — see `docs/DIVERGENCE.md` §3. A closed
`MilestoneTheorem` certifies the generated **AST**; the C text is covered by
goldens and `scripts/smoke.sh` only.
-/

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
import Amcc.Templates.LayoutWf
import Amcc.Templates.NameWf
import Amcc.Templates.Pool
import Amcc.Templates.Tpool
import Amcc.Templates.Upptr
import Amcc.Templates.UpptrWf
import Amcc.Templates.Llist
import Amcc.Templates.LlistWf
import Amcc.Templates.Thash
import Amcc.Templates.ThashWf
import Amcc.Templates.ThashFind
import Amcc.Templates.ThashRefine
import Amcc.Templates.Smallstr
import Amcc.Templates.SmallstrWf
import Amcc.Templates.Bheap
import Amcc.Templates.Atree
import Amcc.Templates.Rbtree
import Amcc.Spec.Rbtree
import Amcc.Templates.Lary
import Amcc.Templates.Cursor
import Amcc.Templates.Xref
import Amcc.Templates.SerDe
import Amcc.Templates.SsimDb
import Amcc.Templates.Msgcurs
import Amcc.Templates.Opt
import Amcc.Templates.ArrayTableChecks
import Amcc.Templates.MiniDb
import Amcc.Ssim.Tuple
import Amcc.Ssim.Schema
import Amcc.Ssim.Conformance
import Amcc.Ssim.Checks
import Amcc.Codegen.Split
import Amcc.Codegen.Print
import Amcc.Codegen.PrintChecks
import Amcc.Codegen.ExportLean

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
- `Dmmeta` — the **ctype model**, including `mangle` — `amc`'s
             `strptr_PrintCppIdent`, which is what lets a namespace-qualified
             schema become C at all — and the qualified-name clause that
             rejects two fields printing to the same C identifier: `Ctype`, `Field` whose `arg` names another
  ctype, `Db` in declaration order, the full `Reftype` vocabulary — all
  **thirty-five** rows of `dmmeta/reftype.ssim`, with their flags — the
  per-field **attribute join** (`AttrTag`, `AttrData`, `Db.attr?`,
  `checkAttr`) that carries `dmmeta.inlary` and `dmmeta.smallstr` and gives
  every table the same named missing-record error, and a checker that resolves
  every `arg` and keeps layout acyclic while letting pointers and indexes
  refer forwards

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
                          power-of-two requirement actually buys
- `Templates.ThashFind` — **proved**: `findCorrect` — `Find` returns the first
                          row on the bucket's chain whose key matches, with
                          `find_hit`/`find_miss` reading either answer back as
                          a statement about the store. The same `Reaches` the
                          list uses, with the bucket head in place of the list
                          head, and the same loop packaging the array table's
                          scan uses
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
- `Ssim.Tuple`          — the **ssim tuple format**: `amc`'s line-oriented
                          `key:value` records, with `algo::PickSsimQuoteChar`'s
                          quoting rule and `algo::_PrintQuotedChar`'s escapes
                          transcribed rather than approximated, and a printer
                          that is their inverse
- `Ssim.Schema`         — tuples into `Dmmeta.Db` and back. Four record types
                          and eight of the thirty-five reftypes: the reader rejects,
                          by name, everything no template can emit, so it
                          cannot run ahead of the generator
- `Ssim.Conformance`    — the **census**: what AMCC would do with every ctype
                          and field of a real `dmmeta` corpus, decided by the
                          shipping reader and the shipping `supported` list so
                          the numbers cannot drift from the generator.
                          `docs/CONFORMANCE.md` is the result and
                          `scripts/conformance/run.sh` regenerates it
- `Ssim.Checks`         — the front end's **round trip**, kernel-checked in
                          both directions, plus the exact rejection messages.
                          Nothing about the reader is proved; the round trip is
                          what stands in (`docs/DIVERGENCE.md` §3.6)
- `Templates.LlistWf`   — **proved**: `Llist.genWellFormed` — every schema
                          `Dmmeta.check` accepts generates a program
                          `Wf.check` accepts, the self-threading case
                          included. Second of the three ctype-model templates
                          to match what the generated headers claim
- `Templates.Smallstr`  — all three `dmmeta.strtype` abstractions, with
                          `rpascal`'s read-back law **proved** and the two
                          padded forms' ambiguity exhibited as checked
                          witnesses. Nothing is emitted: `amc` writes `u8` and
                          the C subset has no eight-bit scalar
                          (`docs/DIVERGENCE.md` §3.8)
- `Templates.ThashWf`   — **proved**: `Thash.genWellFormed` — the same for the
                          hash index, self-indexing included. `InsertMaybe`
                          calls `Find`, the first generated body to make
                          `Wf.Ctx.fun?` resolve a callee out of `funs.take i`;
                          and `accepted_bucket_fits` cashes the generator's
                          own `pow2Exp?` guard, because a `Thash` field is not
                          an `Inlary` and `Dmmeta.check`'s array-bound clause
                          never reaches its bucket count. **Third of three —
                          the header banner is now true for all five
                          templates.** `laws_apply` here and in `LlistWf` /
                          `UpptrWf` discharges every law's resolution
                          hypothesis once from `Dmmeta.check`
- `Templates.LayoutWf`  — **proved**: `layoutWellFormed` — every schema the
                          lowering accepts produces structs and globals
                          `Wf.check` accepts, including that struct nesting is
                          acyclic — plus `addFields` and
                          `checkStructs_addFields`, since `Llist`, `Thash` and
                          `Pool` *extend* that layout rather than replacing it.
                          The shared half of the every-schema gap
- `Templates.NameWf`    — distinctness of generated **function names**, once
                          for all three ctype-model templates: a template's
                          filtered field list is a sublist of `qualNames`, so
                          the schema's `<ctype>_<field>` uniqueness clause
                          descends, and `append_ne_rev` settles the suffixes by
                          reversing them into a decidable prefix comparison
- `Templates.UpptrWf`   — **proved**: `Upptr.genWellFormed` — every schema
                          `Dmmeta.check` accepts generates a program
                          `Wf.check` accepts. The header's banner is now true
                          of this template too
- `Codegen.Split`       — the **header/implementation partition**, at the AST
                          level: `split_partition` proves the two halves
                          together carry exactly the input's declarations, and
                          `split_protos_match` that every body has a prototype
                          and every prototype a body. The printer stays
                          trusted; the partition does not have to be
- `Codegen.Print`       — the pretty-printer to C text (trusted, unverified),
                          in three modes: one self-contained translation unit,
                          or `<name>_gen.h` + `<name>_gen.c`
- `Codegen.PrintChecks` — byte-for-byte golden tests of the printed output

`lake exe amcc` prints the generated C for an example schema, `--out <dir>`
writes the two-file layout, and `--ssim <file>` runs the front end's round trip;
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

`Codegen.Print` and `Ssim` are unverified — see `docs/DIVERGENCE.md` §3.1,
§3.4 and §3.6. A closed `MilestoneTheorem` certifies the generated **AST**;
the C text is covered by goldens and `scripts/smoke.sh`, and the schema text
by the round trip. Those are the three links in the chain that are tested
rather than proved, and the front end is the one that matters most, because a
misread schema is certified code against a specification the user did not
write.
-/

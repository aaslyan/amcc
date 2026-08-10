# AMCC — conformance against the real `dmmeta` corpus

*Measured against `/home/aaslyan/openacr-mine/data/dmmeta`, 1420 ctypes and 5659 fields.
Regenerate with `scripts/conformance/run.sh`; every verdict is produced by
`Ssim.Conformance` in Lean, using the shipping reader, the shipping
`supported` list and the shipping `Dmmeta.isCIdent`. The Python under
`scripts/conformance/` slices and counts and decides nothing.*

---

## The headline

**4519 of 5659 fields (79.9%) have a reftype AMCC
already handles. 1 of them is generated.**

Every one of the other 4518 is blocked by the same thing, and it is not a
reftype: `dmmeta` names are namespace-qualified — `abt.FArch`,
`dmmeta.Ctype` — and `Dmmeta.isCIdent` rejects a dot. AMCC has no namespace
model and no mangling, so the corpus is out of reach for a reason that has
nothing to do with data structures.

That was not the expected answer. The standing assumption in `docs/PLAN.md`
was that the remaining reftypes were what stood between AMCC and real
schemas. They are the *second* obstacle; a name mapping is the first, and it
gates four times as many fields as the largest missing reftype.

---

## Ctypes

| verdict | count | share |
|---|---|---|
| accepted | 39 | 2.7% |
| name is not a C identifier | 1381 | 97.3% |

## Fields, by what AMCC can do with the reftype

| reftype verdict | count | share | meaning |
|---|---|---|---|
| generated | 3912 | 69.1% | a template emits operations |
| lowered | 607 | 10.7% | becomes a struct field; no operations |
| rejected | 1140 | 20.1% | no representation at all |

## Fields, by what actually blocks them

| blocker | count | share of all fields |
|---|---|---|
| nothing — generated | 1 | 0.0% |
| the name only (reftype is supported) | 4518 | 79.8% |
| the reftype | 1140 | 20.1% |

Broken down, the name-only blockers are:

| reason | fields |
|---|---|
| owner name is not a C identifier | 4517 |
| not <ctype>.<field> | 1 |

---

## Top reasons for rejection, by how many real fields each blocks

| rank | reason | fields blocked |
|---|---|---|
| 1 | namespace-qualified name (no C-identifier mapping) | 4518 |
| 2 | reftype `Lary` has no representation | 390 |
| 3 | reftype `Smallstr` has no representation | 140 |
| 4 | reftype `Ptrary` has no representation | 136 |
| 5 | reftype `Bitfld` has no representation | 75 |
| 6 | reftype `Tary` has no representation | 69 |
| 7 | reftype `Global` has no representation | 60 |
| 8 | reftype `RegxSql` has no representation | 52 |
| 9 | reftype `Tpool` has no representation | 40 |
| 10 | reftype `Varlen` has no representation | 39 |
| 11 | reftype `Bheap` has no representation | 23 |
| 12 | reftype `Charset` has no representation | 23 |
| 13 | reftype `Hook` has no representation | 22 |
| 14 | reftype `Cppstack` has no representation | 21 |
| 15 | reftype `Fbuf` has no representation | 11 |
| 16 | reftype `Lpool` has no representation | 10 |
| 17 | reftype `Exec` has no representation | 6 |
| 18 | reftype `Opt` has no representation | 6 |
| 19 | reftype `Alias` has no representation | 4 |
| 20 | reftype `Regx` has no representation | 3 |
| 21 | reftype `Delptr` has no representation | 3 |
| 22 | reftype `Atree` has no representation | 3 |
| 23 | reftype `Malloc` has no representation | 2 |
| 24 | reftype `Sbrk` has no representation | 1 |
| 25 | reftype `ZSListMT` has no representation | 1 |

---

## What the numbers do not capture

The census reads the three `dmmeta` record types AMCC models
(`dmmeta.ctype`, `dmmeta.field`, `dmmeta.inlary`). `data/dmmeta` has
**110 more that AMCC does not model at all**, carrying
10302 records — 59.2% of the corpus, against
40.8% for the four AMCC reads. The largest are:

| record type | records |
|---|---|
| `dmmeta.userfunc` | 1655 |
| `dmmeta.ctypelen` | 1333 |
| `dmmeta.cfmt` | 845 |
| `dmmeta.xref` | 789 |
| `dmmeta.cpptype` | 403 |
| `dmmeta.fconst` | 337 |
| `dmmeta.ssimfile` | 301 |
| `dmmeta.finput` | 300 |
| `dmmeta.chash` | 240 |
| `dmmeta.thash` | 239 |

Three of those matter more than their counts suggest, and none of them is a
field-level verdict this census could produce:

- **`dmmeta.xref` (789 records).** Cross-reference
  maintenance is the centre of the library — `docs/GOALS.md` calls it central,
  not peripheral. AMCC models it (`Amcc/Spec/Algebra.lean`) and emits none. A
  field counted "generated" above gets its accessors and *not* its
  participation in the indexes that must be updated when a record is inserted.
  The percentage above therefore overstates what a user would get.
- **Cursors.** Every access pattern in `amc` has one, and they appear in the
  generated API rather than in `data/dmmeta` as their own head, so they are
  invisible to a record census entirely.
- **The ssim layer itself** — `acr`, query mode, `ssimfile` loading,
  `Print`/`ReadStrptrMaybe`, `CopyIn`/`CopyOut`. AMCC reads ssim as a *front
  end* and generates none of the machinery `amc` generates for handling it.

Two further caveats on the reading of the table:

- A "generated" verdict is about the reftype and the names, not about the
  whole ctype. A ctype whose fields are individually fine can still fail
  `Dmmeta.check` — for the layout-acyclicity rule, for a duplicate qualified
  name — and the census does not run the whole-schema check, because the
  corpus does not get far enough for it to mean anything.
- `Val` dominates the corpus (2936 fields, 51.9% of the
  total), and a `Val` whose `arg` is a ctype AMCC cannot lower —
  `algo.cstring`, `algo_lib.Replscope` — is counted here by its reftype and
  would still fail at lowering. The number is an upper bound.

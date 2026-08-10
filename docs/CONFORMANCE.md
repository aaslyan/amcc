# AMCC — conformance against the real `dmmeta` corpus

*Measured against `/home/aaslyan/openacr-mine/data/dmmeta`, 1420 ctypes and 5659 fields.
Regenerate with `scripts/conformance/run.sh`; every verdict is produced by
`Ssim.Conformance` in Lean, using the shipping reader, the shipping
`supported` list, the shipping `Dmmeta.mangle` and the shipping
`Dmmeta.isCIdent`. The Python under `scripts/conformance/` slices and counts
and decides nothing.*

---

## The headline

**3909 of 5659 fields (69.1%) would be generated**, and
1419 of 1420 ctypes (99.9%) are
nameable.

The previous measurement said **one**. The difference is entirely
`Dmmeta.mangle`: `dmmeta` names are namespace-qualified, a dot is not a C
identifier character, and until the mapping existed 4518 fields with a
supported reftype were blocked by their *names*. That number is now 3.

What remains is what the first measurement predicted would be second: the
reftypes. 1140 fields
(20.1%) have a reftype AMCC has no
representation for, and that is now the *only* thing of any size between the
generator and the corpus.

---

## Ctypes

| verdict | count | share |
|---|---|---|
| accepted | 1419 | 99.9% |
| mangles to a reserved name | 1 | 0.1% |

## Fields, by what AMCC can do with the reftype

| reftype verdict | count | share | meaning |
|---|---|---|---|
| generated | 3912 | 69.1% | a template emits operations |
| lowered | 607 | 10.7% | becomes a struct field; no operations |
| rejected | 1140 | 20.1% | no representation at all |

## Fields, by what actually blocks them

| blocker | count | share of all fields |
|---|---|---|
| nothing — generated | 3909 | 69.1% |
| the name only (reftype is supported) | 3 | 0.1% |
| the reftype | 1140 | 20.1% |

Broken down, the name-only blockers are:

| reason | fields |
|---|---|
| field mangles to a reserved name | 2 |
| not <ctype>.<field> | 1 |

---

## Top reasons for rejection, by how many real fields each blocks

| rank | reason | fields blocked |
|---|---|---|
| 1 | reftype `Lary` has no representation | 390 |
| 2 | reftype `Smallstr` has no representation | 140 |
| 3 | reftype `Ptrary` has no representation | 136 |
| 4 | reftype `Bitfld` has no representation | 75 |
| 5 | reftype `Tary` has no representation | 69 |
| 6 | reftype `Global` has no representation | 60 |
| 7 | reftype `RegxSql` has no representation | 52 |
| 8 | reftype `Tpool` has no representation | 40 |
| 9 | reftype `Varlen` has no representation | 39 |
| 10 | reftype `Bheap` has no representation | 23 |
| 11 | reftype `Charset` has no representation | 23 |
| 12 | reftype `Hook` has no representation | 22 |
| 13 | reftype `Cppstack` has no representation | 21 |
| 14 | reftype `Fbuf` has no representation | 11 |
| 15 | reftype `Lpool` has no representation | 10 |
| 16 | reftype `Exec` has no representation | 6 |
| 17 | reftype `Opt` has no representation | 6 |
| 18 | reftype `Alias` has no representation | 4 |
| 19 | reftype `Regx` has no representation | 3 |
| 20 | reftype `Delptr` has no representation | 3 |
| 21 | reftype `Atree` has no representation | 3 |
| 22 | reftype `Malloc` has no representation | 2 |
| 23 | reftype `Sbrk` has no representation | 1 |
| 24 | reftype `ZSListMT` has no representation | 1 |
| 25 | the name, after mangling | 3 |

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

**The census is per-record and misses the whole-schema clauses.**
`Dmmeta.check` has three checks that need every ctype and field at once — two
mangled names colliding, two qualified names colliding, and a field named what
a template would generate — and `Ssim.Conformance.classify` decides one tuple
at a time. So the generated count above is an **upper bound** on that axis too.
The last of the three is known to bite in the corpus: `c_next` alongside a
field `c`, and `line_n` alongside `line` (5 of those), are exactly the shape
`clashesGenerated` rejects. Under ten fields, but not zero, and the census
does not currently show them.

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

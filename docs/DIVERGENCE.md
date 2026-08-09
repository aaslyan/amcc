# AMCC vs `amc` — where they differ, and why

*Grounded in `~/openacr-mine` (dmmeta @ 2026-06-09). Every claim below cites
the file it was read from.*

`docs/GOALS.md` says AMCC should differ from `amc` **only where a proof
demanded it, and the difference should be written down.** This is that
document.

It is in three parts, and the third matters as much as the first: places where
`amc`'s approach could not be justified formally, places where AMCC is
*weaker* because of a restriction we chose, and places where `amc` simply does
more than we have attempted. A divergence list that only contained the first
would be advocacy, not analysis.

---

## 1. Where a proof obligation forced a different design

### 1.1 `XrefMaybe` is not atomic

**The strongest finding, and it is visible in the generated code**
(`cpp/gen/abt_gen.cpp`):

```c
bool abt::targsrc_XrefMaybe(abt::FTargsrc &row) {
    abt::FTarget* p_target = abt::ind_target_Find(target_Get(row));
    if (UNLIKELY(!p_target)) return false;          // ① parent not found
    c_targsrc_Insert(*p_target, row);               // ② linked into parent
    if (!ind_targsrc_InsertMaybe(row)) return false; // ③ duplicate key
    row.p_target = p_target;                        // ④ up-pointer set
    return true;
}
```

When ③ fails, the row is **already** in the parent's `Ptrary` from ②, and its
up-pointer is **not** set, because ④ never runs. So a failed cross-reference
leaves a row that is half-linked and whose back-pointer is null.

`amc` is explicit that recovery belongs to the caller — `txt/exe/amc/xref.md`
says "In this case, the child record should be deleted." So the invariant *a
record is either in every index or in none* is not maintained by `XrefMaybe`;
it is a contract between the generated function and whoever calls it, carried
in prose.

**AMCC's design instead:** prepare/commit (`Amcc/Spec/Algebra.lean`). Every
structural failure mode is a pure query — parent not found, duplicate key,
parent index full — and out-of-memory becomes one via per-index `reserve`. So
*prepare* decides everything that can fail and *commit* cannot fail. The
failure path never reaches commit, so **there is nothing to undo and no
unwind path to get right**.

This is not a bug in `amc`: it is a deliberate trade, and it costs nothing in
the common case. But it is a correctness obligation that cannot be discharged
from the generated code alone, and that is the difference.

### 1.2 Double-delete is detected at runtime, not prevented

`cpp/amc/tpool.cpp` generates:

```c
void $name_FreeMem($Parent, $Cpptype &row) {
    if (UNLIKELY(row.$name_next != ($Cpptype*)-1)) {
        FatalErrorExit("$ns.tpool_double_delete  pool:$field  comment:'double deletion caught'");
    }
    row.$name_next = $parname.$name_free;   // insert into free list
    $parname.$name_free = &row;
}
```

Two observations.

**Double-free is possible and is handled by aborting.** The guard is real
engineering — it turns silent corruption into a diagnosable crash — but it is
detection, in production, not prevention.

**The sentinel is `($Cpptype*)-1`.** An integer-to-pointer conversion producing
a value that points at no object. In C this is implementation-defined at best;
the standard gives no meaning to such a pointer beyond that it need not be
valid. `amc` only ever compares it, which works on every real target, but it
is not a value a conforming program can construct.

**AMCC's position:** the subset has no integer-to-pointer conversion, so that
sentinel is *inexpressible*. Freeing is total, and double-free is ruled out by
the pool's representation invariant (`Amcc/Spec/Pool.lean`): `free_nodup` says
no slot appears twice on the free list, and it is carried in the heap *type*,
so a pool that violates it is not merely incorrect — it is unrepresentable.

### 1.3 Reftype compatibility is enforced by a hand-written pass

`cpp/amc/checkxref.cpp` is a C++ pass that rejects, for instance, an xref on a
deletable ctype that has no `cascdel`:

```cpp
static void CheckXref_Nocascdel(amc::FXref &xref) {
    if (xref.p_field->reftype != dmmeta_Reftype_reftype_Upptr
        && xref.p_field->reftype != dmmeta_Reftype_reftype_Count
        && CanDeleteQ(*xref.p_field->p_ctype)
        && !xref.c_nocascdel) {
        prerr("amc.need_cascdel" ...);
```

These are genuine obligations — without a `cascdel`, deleting a parent leaves
dangling references. But they are encoded as an ad-hoc pass with a hand-written
reftype exclusion list. Adding a reftype means remembering to update it, and
nothing checks that you did.

**In AMCC these are typing obligations.** The sharpest case is stable
addresses: `Amcc/Spec/Pool.lean`'s `alloc_frame` says allocation does not
disturb live records, and `moving_not_stable` proves a *moving* pool cannot
satisfy it. So a structure requiring stability **cannot be instantiated over
`Tary`** — the proof does not typecheck. `Lary` has 390 uses and `Ptrary` 136,
so this is the most common structural dependency in the schema, and it is the
one `amc` leaves to convention.

### 1.4 Nothing is stated about what the generated code does

`amc` emits the code. It does not emit, and does not have, a statement of what
the code guarantees. This is the premise of AMCC rather than a criticism of
`amc`'s engineering — but it is the largest difference, and everything above
is downstream of it.

---

## 2. Where AMCC is weaker, because of a restriction we chose

### 2.1 ~~Index-linked free list~~ — resolved

This entry recorded a divergence that turned out to be unnecessary, and the
correction is worth keeping because the mistake is instructive.

The emitted pool used `uint32_t` slot indices plus a `_slot` field so that
`Free(E *p)` could recover an element's index. The stated reason was that
`CSubset.Index` has no arithmetic, so `&g.f[_i + 1]` — needed to link element
`i` to element `i+1` — cannot be written.

That reasoning assumed the free list had to be built **forwards**. It does
not. Building it backwards with a running pointer needs no arithmetic:

```c
for (_i = 0; _i < N; ++_i) { g.f[_i]._freenext = _prev; _prev = &g.f[_i]; }
g.f_free = _prev;
```

The order of a free list is not observable, so the reversal costs nothing. The
emitted pool now uses **pointer links with a `NULL` empty-list sentinel,
exactly as `amc` does**, and the `_slot` field is gone.

The lesson: a claimed limitation of the subset should be checked against what
the subset can actually express before it is designed around.

### 2.2 Fixed capacity, still, in the emitted pool

The emitted pool is over an `Inlary` — a bounded inline array. `amc`'s `Tpool`
grows, taking blocks from a base pool
(`blocksize = BumpToPow2(64 * sizeof(T))`, `cpp/amc/tpool.cpp`).

The semantics now has a heap, `NULL`, runtime-sized storage and runtime loop
bounds, so growth is expressible; the statements that would let generated code
allocate (`Stmt.alloc`/`Stmt.free` and the allocator oracle) are not written
yet. This is unfinished work, not a design position.

### 2.3 No multithreaded free

`amc` generates a CAS-based free path when `mtfree` is set
(`cpp/amc/tpool.cpp`). AMCC has no concurrency model at all, and adding one
would be a substantially larger project than everything here.

---

## 3. What `amc` does that AMCC has not attempted

Stated plainly so the comparison is not read as parity.

- **Storage providers**: `Lary` (390 uses), `Ptrary` (136), `Tary` (69),
  `Tpool` (40), `Lpool`, `Blkpool`, `Delptr`, `Malloc`, `Sbrk` — AMCC emits
  one, over `Inlary`.
- **Access patterns**: `Thash`, `Llist` in eight flavours, `Bheap`, `Atree`,
  `Count`, and a cursor for every one of them. AMCC emits none.
- **Cross-references** — the centre of the library. AMCC models them
  (`Amcc/Spec/Algebra.lean`) and emits none.
- **The ssim layer** entirely: `acr`, query mode, `ssimfile` loading,
  `Print`/`ReadStrptrMaybe`, `CopyIn`/`CopyOut`. AMCC's schemas are Lean terms
  by construction.
- **Scale**: the `amc` namespace alone generates ~54,000 lines across 130
  ctypes and 660 fields.

### 3.1 The pretty-printer is unverified

`MilestoneTheorem` (`Amcc/Templates/ArrayTableInsert.lean`) is closed: for
every well-formed schema, the generated table simulates the abstract map. It
certifies the **AST** — the `CSubset.Program` that `genC` builds — under
`CSubset`'s semantics.

`Amcc/Codegen/Print.lean` turns that AST into C text, and **nothing is proved
about it.** It is covered by byte-for-byte goldens (`Codegen/PrintChecks.lean`)
and by `scripts/smoke.sh`, which compiles the printed C with
`cc -Wall -Wextra -Werror` and diffs its answers against the Lean semantics on
the `ArrayTableChecks` call sequences. That is a differential test, not a
proof: it covers the schemas and the call sequences it was given.

So the honest statement of what AMCC currently certifies is *"the generated
AST implements a map"*, plus *"the printer agrees with the semantics on the
cases we ran"*. The gap between those two is the printer.

**What would discharge it.** A formal semantics for the fragment of C the
printer targets, and a theorem that `Print.program p` denotes what
`execStmt p` computes. That is a substantially larger project than everything
above it — it means committing to a C semantics — and the usual middle path is
to shrink the trusted base rather than eliminate it: prove the printer
*injective* and its output *reparseable* into the same AST, which turns "the
printer is correct" into "the C compiler agrees with our reading of C". Per
`docs/GOALS.md`, difficulty is not grounds for carving this out permanently.
It is owed.

---

## The honest summary

Three of `amc`'s design decisions cannot be justified from the generated code
alone: cross-referencing is not atomic and delegates recovery by prose,
double-free is detected rather than prevented and its sentinel is not a
constructible C value, and the compatibility rules between reftypes live in a
hand-written pass rather than in the types. Each is a reasonable engineering
trade for a mature system with a test suite and years of production use. Each
is also exactly the kind of thing a proof obligation does not let you leave
implicit — which is the argument for doing this at all.

Against that: AMCC currently emits a small fraction of what `amc` emits, and
two of its own divergences (index links, fixed-capacity pools) are restrictions
we have not yet lifted rather than positions we would defend.

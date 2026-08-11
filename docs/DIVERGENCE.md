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
- **Access patterns**: `Bheap`, `Atree`, `Count`, and a cursor for every access
  pattern, plus seven of `Llist`'s eight flavours. AMCC emits `Llist`'s `zdl`
  and a fixed-capacity `Thash` — `Llist`'s two linking laws are proved;
  `Thash.FindCorrect` is stated and not yet proved.
- **Cross-references** — the centre of the library. AMCC models them
  (`Amcc/Spec/Algebra.lean`) and emits none.
- **The ssim layer** entirely: `acr`, query mode, `ssimfile` loading,
  `Print`/`ReadStrptrMaybe`, `CopyIn`/`CopyOut`. AMCC's schemas are Lean terms
  by construction.
- **Scale**: the `amc` namespace alone generates ~54,000 lines across 130
  ctypes and 660 fields.

### 2.4 `Llist` membership is a stored flag, not the `(T*)-1` sentinel

`amc`'s `InLlistQ` is `row.$xfname_next != ($Cpptype*)-1` — the same
unconstructible pointer §1.2 records for the pool's double-delete guard. Every
one of `amc`'s eight list flavours needs a not-in-list marker, so this is not
specific to any of them.

The subset has no integer-to-pointer conversion, so AMCC's element gains one
generated `bool` instead. The cost is one byte per element against `amc`'s
zero. The return is that "is this row in the list" is a fact stored in the
program's own value domain, so `Insert`'s and `Remove`'s idempotence guards are
statements about the store — `Templates/Llist.lean`'s `insert_noop` and
`remove_noop` — rather than about implementation-defined behaviour.

AMCC also emits only the `zdl` flavour of the eight (zero-terminated,
doubly-linked, head insertion). Circular is ruled out by the same sentinel
problem; singly-linked is not, but `amc`'s singly-linked `Remove` scans from
the head to find the predecessor, which makes it O(n) and makes the unlink
argument a statement about a scan. The other seven are unattempted work, not a
design position.

### 3.0 `Upptr` is exposed as four functions, not a public member

`cpp/amc/upptr.cpp` is nineteen lines: it declares the member
(`InsVar(R, field.p_ctype, "$Cpptype*", "$name", ...)`) and generates one
function, `Init`, whose body is `$parname.$name = NULL;`. There is no getter —
the member is public C++, and the cross-reference code assigns it inline
(`row.p_target = p_target;`, quoted in §1.1).

AMCC emits the member too (`Dmmeta.fieldTy` lowers `Upptr` to a pointer field,
so `row->p_level` still works), plus `Init`, `Get`, `Set` and `Q`. The extra
three are a divergence in *surface*, and the reason is this project's rather
than `amc`'s: a function is where a proof obligation can be attached.
`Templates/Upptr.lean` proves read-back (`get_set`) and frame — a `Set`
through one row is invisible through any non-overlapping path — and neither
statement can be made about a bare member assignment, because there is no
generated function to make it about.

The cost is four function symbols per up-pointer where `amc` emits one.

### 3.2 `Thash` has a fixed bucket array, a mask for a hash, and a bounded walk

Three separate divergences, all in one template, and worth separating because
only one of them is a design position.

**Fixed capacity: no rehash, no growth.** `amc`'s `Thash` keeps its buckets in
a `Tary` and grows them through `$name_Reserve`, rehashing every element.
AMCC's bucket array is an inline array of a size the schema declares
(`dmmeta.inlary`), so the load factor rises without bound and nothing is ever
rehashed. This is §2.2's gap again — `Stmt.alloc`/`Stmt.free` and the allocator
oracle are not written, so nothing generated can allocate — and it is
**unfinished work, not a position we would defend**.

**The hash is a mask.** The subset has no division and no shifts, so
`key % nbuckets` is inexpressible. `key & (NB-1)` is, and it is the same
function when `NB` is a power of two, which the generator therefore requires
and refuses schemas without. Against `amc` this costs the freedom to pick any
bucket count, and it costs whatever a real hash function would buy on
adversarial keys — AMCC indexes the key directly, so keys that agree modulo
`NB` all collide. That is a genuine weakness for a general-purpose index.

**The chain walk is bounded.** There is no `while` and no `break` in the
subset: the only loop is `forN` with a bound read once, before the first
iteration. A hash chain has no static length, so `Find` and `Remove` run `CAP`
iterations — the declared element capacity, an upper bound on any chain — with
the body guarded so that it does nothing once the chain ends. Functionally that
is `amc`'s walk; operationally it is O(CAP) where `amc` is O(chain). This one
follows from Phase 0's decision that every loop must have a literal bound,
which is what makes `execStmt` total, so it is the cost of the design rather
than an oversight.

What is proved about the template is the count and the two idempotence guards.
`FindCorrect` and `BucketInRange` are stated and owed; see `Amcc.lean`'s "Still
open".

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

### 3.3 The output is split into `.h` and `.c`, not `.h` and `.cpp`

`amc` emits `include/gen/<ns>_gen.h` and `cpp/gen/<ns>_gen.cpp` (plus an
`<ns>_gen.inl.h` for the inline bodies). AMCC now emits the same two-file
layout — the same banner shape, `#pragma once` as the include guard, struct
definitions and the database global's `extern` and one prototype per function
in the header; the header's `#include` first, the global's definition and the
bodies in the implementation — but names the second file `<name>_gen.c`.

**Why.** `docs/GOALS.md` puts AMCC in C rather than C++ by design ("same API
shape, same operation vocabulary, same reftypes — in C rather than C++"), and
the C subset has no member functions, no references and no overloading, so
there is nothing in the emitted text that a C++ compiler would accept and a C
compiler would not. Naming it `.cpp` would misdescribe the contents. There is
no `.inl.h`: `amc` needs one because it marks small accessors `inline` in the
header, and the subset has no `inline` — every function has exactly one
definition, in the implementation file.

**What would discharge it.** Nothing; this one is a consequence of the C target
and is expected to stay. It is recorded because a reader comparing directory
listings should not have to guess whether the missing `.cpp` means a missing
feature.

### 3.4 The header/implementation split is proved; the *rendering* still is not

The partition itself is an AST operation (`Amcc/Codegen/Split.lean`) and
`split_partition` proves the two halves together carry exactly the input's
declarations, with `split_protos_match` proving every body has a prototype and
every prototype a body. That was deliberate: a printer bug produces text that
fails to compile, but a *partition* bug produces two files that each compile
and a symbol that exists in neither — a failure the C toolchain only notices at
link time, and only if something calls it.

What is **not** proved is that `Print.header` and `Print.impl` render those
declarations faithfully — that the prototype the header carries has the same
signature as the body the implementation carries, as *text*. That is the same
gap as §3.1 and has the same discharge; until then, `scripts/smoke.sh` compiles
the two files together, and separately compiles a translation unit that
includes only the header, so a header that does not stand alone fails visibly.

**What would discharge it.** §3.1's theorem, applied twice: if
`Print.funDef fd` and `Print.funProto fd` both denote `fd`, then a prototype
that disagrees with its body is unreachable. A cheaper partial measure, worth
having on its own, is to prove `Print.funSig` is the shared prefix of both —
the printer is already written that way, so it is a statement about the code as
it stands rather than a redesign.

### 3.5 The front end reads four record types, not two hundred

`Amcc/Ssim/` reads `amc`'s ssim tuple format — the grammar of `txt/ssim.md`,
`algo::PickSsimQuoteChar`'s quoting rule and `algo::_PrintQuotedChar`'s escapes,
transcribed rather than approximated. What it reads *into* is much smaller than
what `amc` reads:

- **Four record types**: `dmmeta.ctype`, `dmmeta.field`, `dmmeta.inlary` and
  `amcc.root`. `data/dmmeta` alone has over a hundred ssimfiles, and `amc`
  consumes most of them. Every other tuple head is **rejected**, not skipped.
- **Eight of the thirty-five reftypes** — the ones a template or the storage
  lowering can act on. The other twenty-seven are rejected by name, with a message
  that distinguishes "no such reftype" from "AMCC cannot emit that yet". This
  is `docs/GOALS.md`'s standing rule applied to the front end: the reader must
  never run ahead of the generator, because a schema that parses and cannot be
  emitted is worse than one that does not parse.
- **`amcc.root` is ours.** `amc` designates the database ctype by the
  `<ns>.FDb` convention inside a namespace declared by `dmmeta.nsdb`. AMCC's
  `Dmmeta.Db` has no namespaces — a schema is a flat list of ctypes with one
  named as the root — so reusing `dmmeta.nsdb` would mean reading its `ns:`
  key as a ctype name. A head under our own namespace says what is happening
  instead of pretending to a compatibility that is not there.

**What would discharge it.** Reading more of `data/dmmeta` is not the
discharge; emitting more of what it describes is, and the reader should follow
one reftype at a time behind the templates. `supported` in
`Amcc/Ssim/Schema.lean` is the single list to extend, and it is deliberately
in one place so the gap stays countable.

### 3.6 The reader is unverified, and the round trip is what stands in

`Amcc/Ssim/` has no theorem about it. That matters more than the printer's
unverified status (§3.1), and in the opposite direction: a **back-end** bug
produces C that fails to compile or fails the differential test, but a
**front-end** bug produces a schema the user did not write, which
`Dmmeta.check` then accepts, every theorem proves about, and every smoke test
passes. The result is certified code against the wrong specification, with
nothing anywhere to notice.

What stands in for a proof is the round trip, run in both directions and
kernel-checked:

- `Db → text → Db` (`Amcc/Ssim/Checks.lean`, `rfl`) for every schema the
  templates are proved about, so a schema written as ssim and the same schema
  written as a Lean term are the same input to every theorem here;
- `text → Db → text` on hand-written text, in Lean and again over
  `scripts/ssim/*.ssim` in `scripts/smoke.sh`, which also diffs the
  checked-in text against what the built-in schema prints to — without that
  second diff the round trip would only say the reader and the printer agree
  with each other.

A reader that drops an attribute, mis-splits a quoted value or coerces a name
cannot survive those, because the printer has no way to invent back what the
reader threw away. It is not a proof: it says the pair is invertible on the
inputs given, not that either half means what `amc` means.

**What would discharge it.** A grammar for the tuple format and a theorem that
`printFile ∘ parseFile` is the identity on strings the grammar accepts, with
`parseFile ∘ printFile` the identity on tuples — the round trip promoted from
examples to a statement quantified over inputs. That is a self-contained
project and much smaller than §3.1's, because it needs no C semantics: both
sides are AMCC's own.

### 3.7 `Smallstr`: what `strict` enforces, and why only `rpascal` is safe to prove

`dmmeta.strtype` has three values and `data/dmmeta/smallstr.ssim` uses all
three — `rightpad` 83, `leftpad` 37, `rpascal` 20. AMCC will implement
`rpascal` first, and this entry is why.

**The three abstractions.** For a field of declared length `N` over a byte
array `ch`, the value the C sees is:

- **`rpascal`** — the count is **out of band**. `cpp/amc/smallstr.cpp` emits
  `u8 ch[N+1];` *and a separate* `u8 n_ch;`, and `ch_N` reads `n_ch`
  directly. So `abs(ch, n) = ch[0 … n]`, and the representation invariant is
  `n ≤ N`. (An earlier revision of this entry put the count in `ch[N]`, which
  is the classic Pascal-string layout but not the one `amc` generates; the
  correction is `Templates/Smallstr.lean`'s `RpascalInv`.) **Injective**: two
  representations agreeing on the count and on that many bytes are the same
  value, and every value of length ≤ N has exactly one canonical
  representation. `Templates.Smallstr.absRpascal_encode` is the read-back law,
  proved, with no side condition; `encodeRpascal_injective` is the same fact
  the other way. That invariant is a `RepInv` clause every write must
  preserve, which is the same shape as `CSubset.Chain`'s `Counted` and reuses
  the same machinery.
- **`rightpad`** — `abs(ch) = ch` with trailing `pad` bytes removed.
  `amc`'s generated `ch_N` is literally
  ```c
  ret = 10; while (ret>0 && parent.ch[ret-1]==u8(0)) ret--;
  ```
  (`include/gen/algo_gen.inl.h`, `algo::ch_N(const algo::RnullStr10&)`).
- **`leftpad`** — the mirror image, `pad` bytes removed from the front.

**Neither padded form is injective**, and that is the blocker. `"ab"` and
`"ab "` have the same representation under `rightpad` with `pad = ' '`, so
`abs` has no inverse and a read-back law — *`Get` after `Set` returns what was
set* — is **false** as stated. There is no way to write the law honestly
without knowing what rules out the ambiguous values.

**What `strict` actually does — and it is not that.** Read from
`cpp/amc/smallstr.cpp`, `CheckSmallstr`. Every use of `smallstr.strict` guards
a **naming-convention** check:

1. the numeric suffix in the ctype name must equal the declared length
   (`amc.badsuffix`);
2. for a `numstr`, the ctype name must start with the prefix the
   `strtype`/`pad` pair implies — `RspaceStr`, `LspaceStr`, `LnumStr`,
   `LnullStr`, `RnullStr` (`amc.numstr_badprefix`);
3. for a `numstr`, the base encoded in the ctype name must match
   `numstr.base` (`amc.badbase`).

**`strict` says nothing about values.** It constrains identifiers so a reader
can tell what a type is from its name. The two value-level checks in that
function are *not* guarded by `strict` at all:

- `ValidRnumPadQ` — a `rightpad` pad character may not be confusable with a
  digit (`amc.invalidpad`);
- a `numstr` may not be `rightpad` with pad `'0'` (`amc.rightpad_insanity`).

Both protect *numeric parsing*, not injectivity. And the generated writer does
not help either: `ch_SetStrptr` for a `rightpad` type copies `min(len, N)`
bytes and zero-fills the rest, with the comment "If RHS is too large, it is
silently clipped" — it neither rejects nor detects a value ending in the pad
byte.

**Conclusion.** In `amc`, a `rightpad`/`leftpad` smallstr **is** a lossy
representation, by design and without a guard. The honest statement of a
read-back law for those two therefore needs a side condition on the value —
"does not end in `pad`" for `rightpad`, "does not begin with it" for
`leftpad` — and that condition is AMCC's to state, because `amc` does not
state it anywhere. That is a design decision, not a transcription, so it is
deferred rather than guessed.

**What would discharge it.** Either the side-conditioned law, with the
generated `Set` rejecting or normalising ambiguous values and the divergence
from `amc`'s silent clipping recorded here; or a proof that the values
actually stored in the corpus never end in the pad, which would make the side
condition vacuous in practice and is checkable with the conformance harness.
The first is honest and diverges; the second is weaker and does not. The
choice is a later round's; nothing here picks between them.

**The witnesses are checked, not asserted.** `Templates/Smallstr.lean` states
all three abstractions, and the two that are owed carry a concrete pair:
`rightpad_ambiguous` exhibits `"a "` and `"a"` at capacity 2 with the same
bytes, and `leftpad_ambiguous` exhibits `"01"` and `"1"` at capacity 2 with
`amc`'s own `pad:"'0'"`. `absRightpad_encode_fails` and
`absLeftpad_encode_fails` are the read-back law failing on them. So the claim
"neither padded form is injective" is a proved fact in the build rather than a
paragraph, and `hasReadBack` is the single Boolean a future arm has to answer.

### 3.8 `Smallstr` is modelled but not emitted: the C subset has no `u8`

`amc` emits `u8 ch[N];` (padded) or `u8 ch[N+1]; u8 n_ch;` (`rpascal`).
`CSubset.ScalarTy` is `u32 | u64 | bool`. There is no eight-bit scalar, so
`Dmmeta.fieldTy` has no lowering for a `Smallstr` field and `Ssim.supported`
does not list the reftype: a schema that declares one is rejected by name,
with the message the other unimplemented reftypes get.

Everything *around* the field is in place — the `dmmeta.smallstr` record is
read, joined onto the field by `Dmmeta.Db.attr?`, checked (including `amc`'s
own 255 ceiling on an `rpascal` length), printed back byte-for-byte, and the
three abstractions are stated with `rpascal`'s read-back law proved.

This is **not** a design question. `docs/GOALS.md`'s standing rule is that the
subset changes when it cannot express what `amc` generates, and `u8` is needed
by five reftypes (`Smallstr`, `Bitfld`, `Charset`, and the two string-adjacent
ones), so it changes. What it costs: a constructor on `ScalarTy`, `Value`,
`Lit`; rows in `evalUn`/`evalBin`/the cast table; arms in `Wf.litTy`,
`isWord`, `binTy`; a type name and a literal suffix in the printer; and a case
in every proof that matches a `Value` or a `Lit` exhaustively. Nothing in it is
hard and none of it is a decision — it is bulk, and it is owed.

**Until it lands, `docs/CONFORMANCE.md`'s `Smallstr` row stays "rejected".**
Counting it as modelled would be exactly the kind of overstatement the census
exists to prevent.

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
we have not yet lifted rather than positions we would defend. Its front end
reads five of `amc`'s record types and eight of its thirty-five reftypes, and
neither the front end nor the printer is proved — §3.1, §3.4 and §3.6 are the
three unverified links in a chain whose middle is machine-checked.

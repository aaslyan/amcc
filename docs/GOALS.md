# AMCC — what this project is

*Canonical. If anything in this repository contradicts this file, this file wins.*

## The goal

**AMCC is a verified reimplementation of OpenACR's `amc`**
(<https://github.com/alexeilebedev/openacr>).

It consumes the same kind of relational schema `amc` consumes and generates the
same kind of data-structure code `amc` generates — same API shape, same
operation vocabulary, same reftypes — in C rather than C++.

What it adds over `amc`: for every generated function, an **explicit statement
in Lean of what that function is guaranteed to do**, machine-checked, and
written so that a third party can read it, cite it, and build on it without
trusting AMCC or reading its proofs.

The deliverable is two things of equal weight: **the C, and the statements
about the C.**

## What that entails

**Completeness is the goal, not a stretch goal.** The whole reftype vocabulary
is in scope — allocators (`Malloc`, `Sbrk`, `Tpool`, `Lpool`, `Blkpool`,
`Lary`, `Tary`, `Inlary`, `Delptr`), structures (`Thash`, `Llist` in its
flavours, `Bheap`, `Atree`, `Ptrary`, `Upptr`, `Count`), cross-references,
cursors, and the field-level machinery. Generic programming means the consumer
picks; we do not pick for them.

**API parity with `amc`, adapted to C.** Pointer-returning `Find` with `NULL`
for absent, fields read through the pointer, `amc`'s operation names and
prefixes, real structs. Where C cannot do what C++ does — namespaces,
references — adapt minimally. Where AMCC differs from `amc`, it must be
because a proof demanded it, and the difference gets written down.

**All the operations, including the hard ones.** Cross-reference maintenance
(`XrefMaybe`) is central, not peripheral: inserting a record updates every
index, and that has to be guaranteed, transactionally.

**Allocation is a proved layer.** `malloc`/`sbrk` are postulated at the leaf —
not our concern. Every pool built on top of them is proved correct relative to
that assumption.

**No restriction may make a real data structure inexpressible.** If the C
subset cannot express something `amc` generates, the subset changes. It is our
artifact; it does not get to constrain the target.

## What is explicitly not the goal

- Not an application. No domain frames the interfaces, the examples, or the
  motivation for any design decision.
- Not a demonstration, and not a research toy.
- Not a subset of `amc` chosen because it is convenient to prove.

## The standing rule

**`amc`'s actual capability defines what to build. Proof difficulty is an
engineering problem to solve inside that target, never a reason to shrink it.**

This rule exists because it was broken repeatedly: fixed capacity promoted to
the foundation, proposals to cover a handful of reftypes, proposals to emit a
pool over a static arena rather than do the heap work, proposals to defer
insertion-ordered structures because a formalisation did not cover them. Each
was proof convenience driving the product definition.

When something is hard to prove, the answer is a better proof architecture.
The object-store layer is the worked example: it front-loaded one substantial
proof and in exchange turned every structure proof from aliasing reasoning
over a heap into mathematics over a finite map.

## Definition of done

A user writes a schema in `amc`'s reftype vocabulary. `amcc` emits C that
compiles, together with a Lean module stating what each generated function
guarantees. `lake build` proof-checks those statements against the generator
for **every accepted schema** — not per instance.

The trust boundary is small, explicit, and documented: the Lean kernel, the
pretty-printer, the C compiler, and the leaf allocator.

## Reference

The specification of *what* to build is `amc` itself —
<https://github.com/alexeilebedev/openacr>, with `~/openacr-mine` as the local
reference checkout: `data/dmmeta/` for the schema vocabulary, `cpp/gen/` for the generated
API, `cpp/amc/` for the generator, `txt/exe/amc/` for the documentation. The
proofs are what AMCC adds.

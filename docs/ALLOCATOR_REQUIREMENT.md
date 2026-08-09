# AMCC Allocator Requirement

Working requirement, 2026-08-09.

AMCC must not bake fixed capacity into the core model. Fixed-size pools may be
one backend, but they are not the semantic foundation of the project.

## Core requirement

AMCC verifies generated data-structure code against an abstract allocator
contract.

The generator may rely on allocation, reallocation, or pool operations only
through an explicit allocator interface whose obligations are stated in Lean.
Generated table/list/hash correctness is conditional on that allocator
satisfying its contract.

In other words:

> Given an allocator that returns valid allocated memory when it succeeds, the
> generated code preserves representation invariants and implements the
> abstract data-structure operation. If allocation fails, the generated code
> reports failure and preserves the old abstract state.

## Allocation failure

Allocation failure is part of the public semantics, not an exceptional
implementation accident.

Any generated operation that may need more storage must have a failure path.
The failure path must satisfy:

- it reports allocation failure or returns `false`;
- it preserves the representation invariant;
- it leaves the abstract table/list/index state unchanged;
- it does not leak partially linked rows, indexes, or relation edges.

The success path must satisfy:

- newly allocated storage is valid according to the allocator contract;
- all existing logical contents are preserved unless the requested operation
  intentionally changes them;
- the generated operation refines the unbounded abstract model.

## Allocator contract boundary

The first version of AMCC does not need to prove `malloc`, `realloc`, arenas,
or OS allocation correct. It only needs a precise contract for allocator
providers.

Possible allocator providers include:

- a trusted `malloc`/`realloc` wrapper;
- a caller-provided arena;
- a growable buffer allocator;
- a fixed-size `Tpool`;
- a test allocator with deterministic failure injection.

This list is intentionally not limited to `Tpool`. In OpenACR/amc,
`Tpool` is one member of a larger pool family, and AMCC should preserve that
design freedom.

## OpenACR pool vocabulary

OpenACR's `amc` treats pools as named fields with reftypes, and lets one pool
obtain memory from another through `dmmeta.basepool`. AMCC should mirror this
at the specification level: generated data structures depend on an allocator
contract, while concrete pool providers implement that contract.

Relevant OpenACR pool providers include:

- `Malloc`: pass-through allocation using `malloc`/`free`;
- `Sbrk`: base allocator using `sbrk`, with optional zeroing and huge-page
  accounting;
- `Tpool`: fixed-size element allocator with a singly linked free list; obtains
  new blocks from its base pool and keeps freed elements for reuse;
- `Lpool`: size-class allocator built from multiple `Tpool`-style free lists;
  requests are rounded to a size class;
- `Blkpool`: block allocator for mostly-FIFO lifetimes; individual frees
  decrement a block refcount, and whole blocks are reused when the refcount
  reaches zero;
- `Tary`: growable contiguous array, similar to a vector; growth may move
  memory, so persistent cross-references into elements are not valid;
- `Lary`: growable leveled array with stable element addresses; allocates new
  levels instead of moving old elements;
- `Inlary`: bounded inline array inside the parent object; when `min < max`,
  allocation is possible up to the inline maximum, and only the last element is
  removable;
- `Delptr`: lazily allocated private value owned by its parent and freed with
  the parent;
- `Val`: in-place value storage, useful as the degenerate non-allocating
  provider.

These providers have different semantic properties. AMCC should model those
properties explicitly rather than hiding them behind one generic "allocate"
operation.

At minimum, allocator contracts should distinguish:

- fixed-size element allocation versus variable-size byte allocation;
- stable-address allocation versus moving reallocation;
- append-only/last-removable arrays versus arbitrary delete/reuse pools;
- owned child storage versus global/shared storage;
- fallible `Maybe`-style allocation versus fatal allocation;
- zero-initialized memory versus uninitialized memory;
- whether freeing returns memory to the provider, to a free list, or only marks
  a block reusable after a larger lifetime condition.

`dmmeta.basepool` should become an explicit composition mechanism in AMCC's
model. A `Tpool` may be backed by `Malloc`, `Sbrk`, `Lpool`, an arena, or a
trusted external provider. The proof obligation for generated relational code
should depend on the composed allocator contract, not on the concrete provider
chosen.

Each provider may be trusted, tested, or later proved independently. The
correctness of generated relational code depends only on the allocator contract,
not on a specific allocation strategy.

## Sketch of the Lean shape

The exact definitions may change, but the proof architecture should look like
this:

```lean
structure AllocatorLaws where
  valid_alloc :
    alloc st n = .ok (st', block) ->
      ValidBlock st' block n

  alloc_fresh :
    alloc st n = .ok (st', block) ->
      FreshBlock st block

  alloc_preserves_existing :
    alloc st n = .ok (st', block) ->
      ExistingBlocksPreserved st st'

  alloc_fail_preserves :
    alloc st n = .error e ->
      AllocStatePreserved st
```

Generated operation specs should then be conditional on `AllocatorLaws`:

```lean
InsertRefines :
  AllocatorLaws ->
  call insert old args = .ok (new, result) ->
    match result with
    | .success =>
        absOf new = Abs.insert (absOf old) key values
    | .allocFailed =>
        absOf new = absOf old
```

## Consequences for the roadmap

The existing fixed-capacity array table remains useful as a minimal backend and
as proof scaffolding, but it must not define the long-term architecture.

The Phase 5 plan should be revised so that:

- `Tpool` is treated as one allocator backend, not the centerpiece;
- `Lary`, `Tary`, `Lpool`, `Blkpool`, `Malloc`, `Sbrk`, `Inlary`, `Delptr`,
  and `Val` are considered allocator/storage providers with explicit contracts;
- `basepool` composition is part of the schema/model, so pool providers can be
  chained without changing generated relational logic;
- schema-level `capacity` is removed from the core semantic model;
- generated tables carry allocator-owned storage or a table handle;
- operations that can grow expose fallible results;
- relational invariants are proved assuming allocator validity;
- allocator implementations can be supplied, trusted, tested, or proved later.

## Project statement

AMCC is a verified schema-to-C generator for relational data structures
parameterized over memory management. It proves the generated relational code
correct for any allocator satisfying an explicit contract. Allocation may fail;
when it does, generated operations preserve invariants and leave the abstract
state unchanged.

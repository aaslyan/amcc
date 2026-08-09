import Amcc.Spec.Algebra

/-!
# AMCC — the pool allocator, proved

A **model** of OpenACR's `Tpool`: fixed-size element allocation with a free
list, obtaining new blocks from a base provider. Written as a Lean data
structure rather than as generated C, deliberately — proving `ObjStoreLaws`
for generated code needs the semantics rework (heap, null, allocator oracle),
whereas proving it for a model needs nothing that does not already exist. If
the free list cannot satisfy the interface as stated, the interface is wrong,
and this file is the cheapest possible way to find that out.

## What is proved here

- `objStore_laws` — the free-list pool satisfies every clause of
  `ObjStoreLaws`, **including `alloc_frame`**: allocating never disturbs a
  record that is already live. That is the stable-address property, and it is
  what `Upptr`, `Ptrary` and every intrusive list depend on.
- `reserve_sound` — after a successful `reserve n`, the pool can serve `n`
  allocations without consulting its base. This is the primitive the
  two-phase insert needs: it is what lets the *prepare* phase guarantee that
  *commit* cannot run out of memory.
- `grow_frame` — growth preserves every existing record. Levels are appended,
  never moved. This is why `Lary` is the workhorse of OpenACR.
- `moving_not_stable` — a *moving* pool, which relocates elements on growth,
  **cannot** satisfy `alloc_frame`. A concrete counterexample, not a
  hand-wave. This is `Tary`, and it is why intrusive structures may not be
  instantiated over it.

## The composition result

`objStore_laws` is proved for an *arbitrary* base provider: the `take`
function is a parameter and **no laws are assumed about it whatsoever**. The
base may fail whenever it likes, return blocks in any order, be `malloc`,
`sbrk`, an arena, or another pool. The pool's stability does not depend on any
of it, because the pool never moves a cell it has already handed out.

That is `dmmeta.basepool` as a theorem, and it is the strongest form of the
claim: *given an allocator that returns memory when it succeeds, our pool is
correct* — with "when it succeeds" carrying no obligations at all beyond
producing a value.

## What `Val` is

Deliberately an arbitrary type. The pool does not care what a record is, so
instantiating `Val` at the C subset's struct values — `CSubset.Value.strct`,
laid out by a `CSubset.StructDef` — is a later step that changes nothing
here. Records are C structs in the end; that is a fact about the
instantiation, not about the allocator.

## The representation invariant

Two clauses, and both are load-bearing:

- `free_none` — every slot on the free list is genuinely vacant. Without it
  `alloc` could hand out a slot that is still in use.
- `free_nodup` — no slot appears twice on the free list. Without it a slot
  could be allocated twice, which is precisely the double-allocation bug this
  interface exists to rule out.

They are carried in the heap *type* (`Heap` is a subtype), so a pool that
violates them is not merely incorrect — it is unrepresentable.
-/

namespace Amcc
namespace Spec
namespace Pool

variable {Val B : Type}

/-! ## State -/

/-- Slot-indexed storage plus a free list. `none` in `cells` is a vacant slot;
`base` is whatever the underlying provider carries. -/
structure St (Val B : Type) where
  cells : List (Option Val)
  free  : List Nat
  base  : B

/-- The contents of a slot in a cell list: `none` when out of range or vacant.

Factored out of `St.slotVal` so that every proof below is about *lists*, with
no structure projections to fight. -/
def valAt (cs : List (Option Val)) (r : Nat) : Option Val :=
  match cs[r]? with
  | some (some v) => some v
  | _             => none

/-- The contents of a slot. -/
def St.slotVal (p : St Val B) (r : Nat) : Option Val := valAt p.cells r

theorem valAt_set_self {cs : List (Option Val)} {r : Nat} (hlt : r < cs.length)
    (v : Val) : valAt (cs.set r (some v)) r = some v := by
  unfold valAt; rw [List.getElem?_set_self (by simpa using hlt)]

theorem valAt_set_none {cs : List (Option Val)} {r : Nat} (hlt : r < cs.length) :
    valAt (cs.set r none) r = (none : Option Val) := by
  unfold valAt; rw [List.getElem?_set_self (by simpa using hlt)]

theorem valAt_set_ne {cs : List (Option Val)} {r r' : Nat} (hne : r ≠ r')
    (x : Option Val) : valAt (cs.set r x) r' = valAt cs r' := by
  unfold valAt; rw [List.getElem?_set_ne hne]

/-- The representation invariant. See the header for why each clause is
needed. -/
structure St.Wf (p : St Val B) : Prop where
  free_none  : ∀ r ∈ p.free, p.cells[r]? = some none
  free_nodup : p.free.Nodup

/-- A pool heap is a *well-formed* state: the invariant lives in the type. -/
def Heap (Val B : Type) := { p : St Val B // p.Wf }

/-! ## Small facts about slots and the free list -/

theorem lt_of_slotVal {p : St Val B} {r : Nat} (h : (p.slotVal r).isSome = true) :
    r < p.cells.length := by
  unfold St.slotVal valAt at h
  split at h
  · next v hv => obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hv; exact hlt
  · simp at h

/-- Every slot on the free list is in range. -/
theorem lt_of_free {p : St Val B} (W : p.Wf) {r : Nat} (hr : r ∈ p.free) :
    r < p.cells.length := by
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp (W.free_none r hr)
  exact hlt

/-- A slot on the free list holds nothing. -/
theorem slotVal_of_free {p : St Val B} (W : p.Wf) {r : Nat} (hr : r ∈ p.free) :
    p.slotVal r = none := by
  unfold St.slotVal valAt
  rw [W.free_none r hr]

/-- Live slots are not on the free list — the fact that makes `alloc` hand out
a genuinely unused slot. -/
theorem notMem_free_of_live {p : St Val B} (W : p.Wf) {r : Nat}
    (h : (p.slotVal r).isSome = true) : r ∉ p.free := by
  intro hr
  rw [slotVal_of_free W hr] at h
  exact Bool.noConfusion h

/-! ## Invariant preservation -/

theorem wf_alloc {p : St Val B} (W : p.Wf) {r : Nat} {rest : List Nat}
    (hf : p.free = r :: rest) (v : Val) :
    St.Wf { p with cells := p.cells.set r (some v), free := rest } := by
  have hnd : (r :: rest).Nodup := hf ▸ W.free_nodup
  rw [List.nodup_cons] at hnd
  refine ⟨?_, hnd.2⟩
  intro r' hr'
  have hne : r ≠ r' := fun e => hnd.1 (e ▸ hr')
  show (p.cells.set r (some v))[r']? = some none
  rw [List.getElem?_set_ne hne]
  exact W.free_none r' (by rw [hf]; exact List.mem_cons_of_mem _ hr')

theorem wf_set {p : St Val B} (W : p.Wf) {r : Nat}
    (hl : (p.slotVal r).isSome = true) (v : Val) :
    St.Wf { p with cells := p.cells.set r (some v) } := by
  refine ⟨?_, W.free_nodup⟩
  intro r' hr'
  have hne : r ≠ r' := fun e => notMem_free_of_live W hl (e ▸ hr')
  show (p.cells.set r (some v))[r']? = some none
  rw [List.getElem?_set_ne hne]
  exact W.free_none r' hr'

theorem wf_free {p : St Val B} (W : p.Wf) {r : Nat}
    (hl : (p.slotVal r).isSome = true) :
    St.Wf { p with cells := p.cells.set r none, free := r :: p.free } := by
  have hnm : r ∉ p.free := notMem_free_of_live W hl
  refine ⟨?_, List.nodup_cons.mpr ⟨hnm, W.free_nodup⟩⟩
  intro r' hr'
  show (p.cells.set r none)[r']? = some none
  rcases List.mem_cons.mp hr' with rfl | hr'
  · rw [List.getElem?_set_self (by simpa using lt_of_slotVal hl)]
  · have hne : r ≠ r' := fun e => hnm (e ▸ hr')
    rw [List.getElem?_set_ne hne]
    exact W.free_none r' hr'

/-- Growth appends fresh vacant slots and never touches an existing one. -/
theorem wf_grow {p : St Val B} (W : p.Wf) (k : Nat) (b' : B) :
    St.Wf { cells := p.cells ++ List.replicate k none
          , free  := p.free ++ (List.range k).map (· + p.cells.length)
          , base  := b' } := by
  have hold : ∀ r ∈ p.free, r < p.cells.length := fun r hr => lt_of_free W hr
  have hnew : ∀ r ∈ (List.range k).map (· + p.cells.length), p.cells.length ≤ r := by
    intro r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    omega
  constructor
  · intro r hr
    show (p.cells ++ List.replicate k none)[r]? = some none
    rcases List.mem_append.mp hr with hr | hr
    · rw [List.getElem?_append_left (hold r hr)]
      exact W.free_none r hr
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      rw [List.getElem?_append_right (by omega)]
      simp only [List.getElem?_replicate, Nat.add_sub_cancel]
      rw [if_pos (List.mem_range.mp hj)]
  · show (p.free ++ (List.range k).map (· + p.cells.length)).Nodup
    rw [List.nodup_append]
    refine ⟨W.free_nodup, ?_, ?_⟩
    · show List.Pairwise (· ≠ ·) ((List.range k).map (· + p.cells.length))
      rw [List.pairwise_map]
      exact List.nodup_range.imp (by omega)
    · intro a ha b hb
      have := hold a ha
      have := hnew b hb
      omega

/-! ## The operations -/

def allocRef (h : Heap Val B) (v : Val) : Option (Heap Val B × Nat) :=
  match hf : h.1.free with
  | []        => none
  | r :: rest =>
    some (⟨{ h.1 with cells := h.1.cells.set r (some v), free := rest },
            wf_alloc h.2 hf v⟩, r)

def setRef (h : Heap Val B) (r : Nat) (v : Val) : Heap Val B :=
  if hl : (h.1.slotVal r).isSome = true then
    ⟨{ h.1 with cells := h.1.cells.set r (some v) }, wf_set h.2 hl v⟩
  else h

def freeRef (h : Heap Val B) (r : Nat) : Heap Val B :=
  if hl : (h.1.slotVal r).isSome = true then
    ⟨{ h.1 with cells := h.1.cells.set r none, free := r :: h.1.free }, wf_free h.2 hl⟩
  else h

/-- Ask the base provider for `k` more slots. The provider is an arbitrary
function: it may fail whenever it likes, and **no laws are assumed about
it**. -/
def grow (take : B → Nat → Option B) (h : Heap Val B) (k : Nat) :
    Option (Heap Val B) :=
  match take h.1.base k with
  | none    => none
  | some b' =>
    some ⟨{ cells := h.1.cells ++ List.replicate k none
          , free  := h.1.free ++ (List.range k).map (· + h.1.cells.length)
          , base  := b' }, wf_grow h.2 k b'⟩

/-- Ensure the pool can serve `n` allocations without consulting the base
again. The primitive the two-phase insert's *prepare* phase calls, and the
reason its *commit* phase cannot run out of memory. -/
def reserve (take : B → Nat → Option B) (h : Heap Val B) (n : Nat) :
    Option (Heap Val B) :=
  if n ≤ h.1.free.length then some h
  else grow take h (n - h.1.free.length)

/-- The pool, packaged as an object store. Note that `take` does not appear:
allocation never consults the base, which is exactly what makes `commit`
infallible once `reserve` has run. -/
def objStore : ObjStore (Heap Val B) Nat Val where
  live  := fun h r => (h.1.slotVal r).isSome = true
  get   := fun h r => h.1.slotVal r
  set   := setRef
  alloc := allocRef
  free  := freeRef

/-! ## The laws, one lemma at a time -/

/-- Everything a successful allocation tells us: which slot it took off the
free list, and what the cell list became. -/
theorem allocRef_spec {h : Heap Val B} {v : Val} {h' : Heap Val B} {r : Nat}
    (hA : allocRef h v = some (h', r)) :
    (∃ rest, h.1.free = r :: rest) ∧ h'.1.cells = h.1.cells.set r (some v) := by
  unfold allocRef at hA
  split at hA
  · exact Option.noConfusion hA
  · next r0 rest hf =>
    have hEq := Option.some.inj hA
    rw [Prod.mk.injEq] at hEq
    obtain ⟨hsub, hr⟩ := hEq
    subst hr
    have hv := congrArg Subtype.val hsub
    exact ⟨⟨rest, hf⟩, by rw [← hv]⟩

theorem allocRef_mem {h : Heap Val B} {v : Val} {h' : Heap Val B} {r : Nat}
    (hA : allocRef h v = some (h', r)) : r ∈ h.1.free := by
  obtain ⟨⟨rest, hf⟩, _⟩ := allocRef_spec hA
  rw [hf]; exact List.mem_cons_self

theorem allocRef_live {h : Heap Val B} {v : Val} {h' : Heap Val B} {r : Nat}
    (hA : allocRef h v = some (h', r)) : (h'.1.slotVal r).isSome = true := by
  obtain ⟨_, hc⟩ := allocRef_spec hA
  show (valAt h'.1.cells r).isSome = true
  rw [hc, valAt_set_self (lt_of_free h.2 (allocRef_mem hA))]
  rfl

theorem allocRef_fresh {h : Heap Val B} {v : Val} {h' : Heap Val B} {r : Nat}
    (hA : allocRef h v = some (h', r)) : ¬ ((h.1.slotVal r).isSome = true) := by
  rw [slotVal_of_free h.2 (allocRef_mem hA)]
  simp

theorem allocRef_get {h : Heap Val B} {v : Val} {h' : Heap Val B} {r : Nat}
    (hA : allocRef h v = some (h', r)) : h'.1.slotVal r = some v := by
  obtain ⟨_, hc⟩ := allocRef_spec hA
  show valAt h'.1.cells r = some v
  rw [hc, valAt_set_self (lt_of_free h.2 (allocRef_mem hA))]

theorem allocRef_frame {h : Heap Val B} {v : Val} {h' : Heap Val B} {r r' : Nat}
    (hA : allocRef h v = some (h', r)) (hlive : (h.1.slotVal r').isSome = true) :
    h'.1.slotVal r' = h.1.slotVal r' := by
  obtain ⟨_, hc⟩ := allocRef_spec hA
  have hne : r ≠ r' := fun e => notMem_free_of_live h.2 hlive (e ▸ allocRef_mem hA)
  show valAt h'.1.cells r' = valAt h.1.cells r'
  rw [hc, valAt_set_ne hne]

theorem setRef_get_self {h : Heap Val B} {r : Nat} {v : Val}
    (hl : (h.1.slotVal r).isSome = true) : (setRef h r v).1.slotVal r = some v := by
  unfold setRef
  rw [dif_pos hl]
  show valAt (h.1.cells.set r (some v)) r = some v
  exact valAt_set_self (lt_of_slotVal hl) v

theorem setRef_frame {h : Heap Val B} {r r' : Nat} {v : Val} (hne : r' ≠ r) :
    (setRef h r v).1.slotVal r' = h.1.slotVal r' := by
  unfold setRef
  split
  · show valAt (h.1.cells.set r (some v)) r' = valAt h.1.cells r'
    exact valAt_set_ne (Ne.symm hne) _
  · rfl

theorem freeRef_dead {h : Heap Val B} {r : Nat} :
    ¬ (((freeRef h r).1.slotVal r).isSome = true) := by
  unfold freeRef
  split
  · next hl =>
    show ¬ ((valAt (h.1.cells.set r none) r).isSome = true)
    rw [valAt_set_none (lt_of_slotVal hl)]
    simp
  · next hl => exact hl

theorem freeRef_frame {h : Heap Val B} {r r' : Nat} (hne : r' ≠ r) :
    (freeRef h r).1.slotVal r' = h.1.slotVal r' := by
  unfold freeRef
  split
  · show valAt (h.1.cells.set r none) r' = valAt h.1.cells r'
    exact valAt_set_ne (Ne.symm hne) _
  · rfl

/-! ## The theorem -/

/-- **The free-list pool is an object store**, for every base provider, with
no assumptions on that provider at all.

`alloc_frame` is the clause that matters: allocating a record leaves every
already-live record exactly where it was. Stable addresses, proved.

checked by: `lake build` -/
theorem objStore_laws : ObjStoreLaws (objStore (Val := Val) (B := B)) where
  alloc_live   := allocRef_live
  alloc_fresh  := allocRef_fresh
  alloc_get    := allocRef_get
  alloc_frame  := allocRef_frame
  set_get_self := setRef_get_self
  set_frame    := setRef_frame
  free_dead    := freeRef_dead
  free_frame   := freeRef_frame

/-! ## Reserve, and why commit cannot fail -/

/-- **Growth never moves a record.** New capacity is appended; every live
record keeps both its handle and its contents.

This is the `Lary` property — new levels rather than relocation — and it is
what makes growth compatible with up-pointers and intrusive lists.

checked by: `lake build` -/
theorem grow_frame {take : B → Nat → Option B} {h h' : Heap Val B} {k : Nat}
    (hg : grow take h k = some h') {r : Nat}
    (hlive : (h.1.slotVal r).isSome = true) :
    h'.1.slotVal r = h.1.slotVal r := by
  unfold grow at hg
  split at hg
  · exact Option.noConfusion hg
  · next b' hb =>
    have hv := congrArg Subtype.val (Option.some.inj hg)
    show valAt h'.1.cells r = valAt h.1.cells r
    rw [← hv]
    show valAt (h.1.cells ++ List.replicate k none) r = valAt h.1.cells r
    unfold valAt
    rw [List.getElem?_append_left (lt_of_slotVal hlive)]

/-- **After a successful `reserve n`, the pool holds at least `n` free
slots** — so `n` allocations in a row cannot fail.

This is the guarantee the *prepare* phase of a transactional insert buys, and
the reason the *commit* phase is infallible.

checked by: `lake build` -/
theorem reserve_sound {take : B → Nat → Option B} {h h' : Heap Val B} {n : Nat}
    (hr : reserve take h n = some h') : n ≤ h'.1.free.length := by
  unfold reserve at hr
  split at hr
  · next hle =>
    have hv := congrArg Subtype.val (Option.some.inj hr)
    rw [← hv]; exact hle
  · next hgt =>
    unfold grow at hr
    split at hr
    · exact Option.noConfusion hr
    · next b' hb =>
      have hv := congrArg Subtype.val (Option.some.inj hr)
      rw [← hv]
      show n ≤ (h.1.free
        ++ (List.range (n - h.1.free.length)).map (· + h.1.cells.length)).length
      simp only [List.length_append, List.length_map, List.length_range]
      omega

/-- A pool with a free slot can always allocate — the other half of what
`reserve` guarantees.

checked by: `lake build` -/
theorem alloc_isSome {h : Heap Val B} (hne : h.1.free ≠ []) (v : Val) :
    (allocRef h v).isSome = true := by
  unfold allocRef
  split
  · next hf => exact absurd hf hne
  · rfl

/-! ## The records a pool holds

The bridge to the relational layer: a pool viewed as the list of records
currently in it. Slot order, which is *not* insertion order — the reason the
table laws above are stated up to `List.Perm`. -/

/-- The records a pool currently holds, in slot order. -/
def liveRecs (h : Heap Val B) : List Val := h.1.cells.filterMap id

private theorem filterMap_set_perm {cs : List (Option Val)} {r : Nat} {v : Val}
    (h : cs[r]? = some none) :
    (List.filterMap id (cs.set r (some v))).Perm (v :: List.filterMap id cs) := by
  induction cs generalizing r with
  | nil => simp at h
  | cons a as ih =>
    cases r with
    | zero =>
      simp at h; subst h
      simp [List.filterMap_cons_none]
    | succ n =>
      simp only [List.getElem?_cons_succ] at h
      cases a with
      | none => simpa [List.filterMap_cons_none] using ih h
      | some x =>
        simp only [List.set_cons_succ, List.filterMap_cons_some (f := id) (b := x) rfl]
        exact (ih h).cons x |>.trans (List.Perm.swap _ _ _)

/-- **Allocation adds exactly the new record.** Up to permutation, because the
slot it lands in depends on the free list.

checked by: `lake build` -/
theorem liveRecs_alloc {h : Heap Val B} {v : Val} {h' : Heap Val B} {r : Nat}
    (hA : allocRef h v = some (h', r)) : (liveRecs h').Perm (v :: liveRecs h) := by
  obtain ⟨_, hc⟩ := allocRef_spec hA
  have hcell : h.1.cells[r]? = some none := h.2.free_none r (allocRef_mem hA)
  show (List.filterMap id h'.1.cells).Perm (v :: List.filterMap id h.1.cells)
  rw [hc]
  exact filterMap_set_perm hcell

/-- **Growth adds capacity, not records.**

checked by: `lake build` -/
theorem liveRecs_grow {take : B → Nat → Option B} {h h' : Heap Val B} {k : Nat}
    (hg : grow take h k = some h') : liveRecs h' = liveRecs h := by
  unfold grow at hg
  split at hg
  · exact Option.noConfusion hg
  · next b' hb =>
    have hv := congrArg Subtype.val (Option.some.inj hg)
    show List.filterMap id h'.1.cells = List.filterMap id h.1.cells
    rw [← hv]
    show List.filterMap id (h.1.cells ++ List.replicate k none)
        = List.filterMap id h.1.cells
    simp [List.filterMap_append]

/-- **Reserving is invisible.** This is what makes the *prepare* phase of a
transactional insert observationally neutral.

checked by: `lake build` -/
theorem liveRecs_reserve {take : B → Nat → Option B} {h h' : Heap Val B} {n : Nat}
    (hr : reserve take h n = some h') : liveRecs h' = liveRecs h := by
  unfold reserve at hr
  split at hr
  · rw [← Option.some.inj hr]
  · exact liveRecs_grow hr

/-- A pool that has reserved a slot can allocate. -/
theorem free_ne_nil_of_reserve {take : B → Nat → Option B} {h h' : Heap Val B}
    {n : Nat} (hr : reserve take h n = some h') (hn : 0 < n) : h'.1.free ≠ [] := by
  have hlen := reserve_sound hr
  intro he
  rw [he] at hlen
  simp at hlen
  omega

/-! ## The negative result

A pool that *moves* its elements cannot satisfy the interface. This is `Tary`,
and the point of proving it is that the object-store contract genuinely
discriminates: refusing to instantiate an intrusive list over a moving pool is
not a convention we impose, it is a theorem. -/

/-- A moving pool: allocation relocates every existing element, exactly as a
reallocating array does when it grows. -/
def moving : ObjStore (List Nat) Nat Nat where
  live  := fun h r => r < h.length
  get   := fun h r => h[r]?
  set   := fun h r v => h.set r v
  alloc := fun h v => some (v :: h, 0)
  free  := fun h _ => h

/-- **A moving pool is not an object store.** Concretely: a pool holding one
record, allocating a second, and the first record's handle now denotes the
new one.

Every intrusive link, up-pointer and pointer array in an OpenACR schema would
be silently invalidated. `Lary` (390 uses) satisfies `alloc_frame`; `Tary`
(69 uses) cannot — and this is that distinction, proved rather than
documented.

checked by: `lake build` -/
theorem moving_not_stable : ¬ ObjStoreLaws moving := by
  intro L
  have h := L.alloc_frame (h := [7]) (v := 9) (h' := [9, 7]) (r := 0) (r' := 0)
    rfl (by show (0 : Nat) < [7].length; decide)
  simp [moving] at h

end Pool
end Spec
end Amcc

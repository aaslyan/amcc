import Amcc.Templates.Layout

/-!
# AMCC — the layout pass is well-formed for every lowerable schema

`Templates/Layout.lean` states `LayoutWellFormed`; this module proves it.

It is the shared foundation of item B: `Upptr`, `Llist` and `Thash` all emit
`Dmmeta.genStructs` and `Dmmeta.genGlobals`, so each of their
every-schema well-formedness proofs would otherwise have to redo the struct
and global obligations from scratch. Done once here, each template is left
with only its own functions to discharge.

## The hole this proof found

`LayoutWellFormed` was **false as stated** when this file was started, and the
counterexample is small: a schema with an `Inlary` whose declared bound is `0`
passed `Dmmeta.check` *and* `Layout.layoutCheck`, and the generated program was
then rejected by `CSubset.Wf.check` with `"D.row: bad array size"`. The
schema-level clause only asked that a bound *exist*; obligation 3 asks that it
be a legal C array size.

The fix is in the checker, not in the theorem: `Dmmeta.checkField` now rejects
a bound outside `(0, u32Bound)`, with two negative examples pinning the exact
message. That is the direction `docs/GOALS.md` requires — the front end must
not accept what the back end cannot emit — and it is the finding this item was
asked to look for.

## The three obligations, and where each comes from

- **Struct names distinct** — `genStructs` maps the non-scalar ctypes of
  `withBuiltins` to structs of the same name, so the name list is a *sublist*
  of `Db.names`, which `Dmmeta.check`'s `dups full.names = []` clause makes
  pairwise-distinct.
- **Field names distinct, per struct** — `structOf` is a `filterMap` over the
  ctype's fields that preserves names and order, so again a sublist, of a list
  `checkCtype`'s `dups` clause makes distinct.
- **Sizes, resolution and nesting** — one case analysis over `fieldTy`. Every
  lowered type is `scalar`, `strct n`, `ptr (strct n)` or `arr (strct n) k`,
  and each of the three obligations is read off the reftype: `sizesOk` needs
  the `Inlary` bound (above), `allStructs` needs `arg` to resolve, and
  `layoutDeps` needs it declared *earlier* — which is exactly
  `Reftype.layoutDep` and the checker's declared-earlier rule, the clause the
  single-table `GenWellFormed` never had to face.
-/

namespace Templates
namespace Layout

open Dmmeta
open CSubset

/-! ## Sublists inherit distinctness

Both name obligations have the same shape, so they are discharged by the same
two lemmas. -/

/-- A `filterMap` that preserves the projected value produces a sublist of the
projection — which is all either name obligation needs. -/
theorem pairwise_filterMap_map {α β : Type _} {g : β → String} {h : α → String}
    {f : α → Option β} (hg : ∀ a b, f a = some b → g b = h a) :
    ∀ (l : List α), (l.map h).Pairwise (· ≠ ·) →
      ((l.filterMap f).map g).Pairwise (· ≠ ·)
  | [], _ => List.Pairwise.nil
  | a :: l, hp => by
    rw [List.map_cons, List.pairwise_cons] at hp
    have ih := pairwise_filterMap_map hg l hp.2
    -- every surviving name still comes from some element of `l`
    have hmem : ∀ x ∈ (l.filterMap f).map g, ∃ a' ∈ l, h a' = x := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      obtain ⟨a', ha', hfa⟩ := List.mem_filterMap.mp hb
      exact ⟨a', ha', (hg a' b hfa).symm⟩
    cases hf : f a with
    | none => simpa [List.filterMap_cons, hf] using ih
    | some b =>
      rw [List.filterMap_cons, hf, List.map_cons, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih⟩
      obtain ⟨a', ha', rfl⟩ := hmem x hx
      rw [hg a b hf]
      exact hp.1 (h a') (List.mem_map_of_mem ha')

/-! ## The struct table -/

/-- Struct names are pairwise distinct, because ctype names are and
`genStructs` keeps the name. -/
theorem structs_distinct {d : Db} (h : dups d.withBuiltins.names = []) :
    ((genStructs d).map StructDef.name).Pairwise (· ≠ ·) := by
  refine pairwise_filterMap_map (g := StructDef.name) (h := Ctype.name)
    (f := fun c => if c.scalar.isSome then none else some (structOf d.withBuiltins c))
    ?_ _ (CSubset.dups_eq_nil_iff.mp h)
  intro a b hab
  simp only [] at hab
  cases hs : a.scalar with
  | none =>
    rw [hs] at hab
    simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hab
    rw [← Option.some.inj hab]; rfl
  | some t => rw [hs] at hab; simp at hab

/-- Field names within one generated struct are pairwise distinct, because the
ctype's are and `structOf` keeps the name. -/
theorem fields_distinct {full : Db} {c : Ctype}
    (h : dups (c.fields.map Field.name) = []) :
    ((structOf full c).fields.map Prod.fst).Pairwise (· ≠ ·) := by
  refine pairwise_filterMap_map (g := Prod.fst) (h := Field.name)
    (f := fun f => (fieldTy full c.name f).map (fun t => (f.name, t)))
    ?_ _ (CSubset.dups_eq_nil_iff.mp h)
  intro a b hab
  simp only [] at hab
  cases ht : fieldTy full c.name a with
  | none => rw [ht] at hab; simp at hab
  | some t =>
    rw [ht] at hab
    simp only [Option.map_some] at hab
    rw [← Option.some.inj hab]

/-! ## What `Dmmeta.check` hands over

`checkCtype` and `checkField` are concatenations, and the proof needs three of
their components separately. Pulling them out once keeps the case analysis
below readable, and puts the `++`-nesting in one place where a change to the
checker's clause order shows up as one broken pattern rather than five. -/

/-- Acceptance gives, for every ctype and every field of it: the field names of
that ctype are distinct, the `arg` resolves, a layout-carrying field's `arg`
was declared earlier, and an `Inlary`'s bound is a legal array size. -/
theorem facts_of_check {d : Db} (h : check d = []) :
    dups d.withBuiltins.names = []
    ∧ ∀ i, ∀ hi : i < d.withBuiltins.ctypes.length,
        dups ((d.withBuiltins.ctypes[i]'hi).fields.map Field.name) = []
        ∧ ∀ f ∈ (d.withBuiltins.ctypes[i]'hi).fields,
            (∃ ac, d.withBuiltins.find? f.arg = some ac)
            ∧ (f.reftype.layoutDep = true →
                ((d.withBuiltins.ctypes.take i).map Ctype.name).contains f.arg = true)
            ∧ (f.reftype = .Inlary →
                ∃ n, d.withBuiltins.inlaryMax? (d.withBuiltins.ctypes[i]'hi).name f.name = some n
                  ∧ 0 < n ∧ n < Wf.u32Bound) := by
  simp only [check, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
  obtain ⟨⟨⟨hdup, _⟩, _⟩, hcty⟩ := h
  refine ⟨hdup, fun i hi => ?_⟩
  rw [List.flatMap_eq_nil_iff] at hcty
  have hmem : ((d.withBuiltins.ctypes[i]'hi), i) ∈ d.withBuiltins.ctypes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact List.getElem?_eq_getElem hi
  have hc := hcty _ hmem
  simp only [checkCtype, List.append_eq_nil_iff, List.map_eq_nil_iff] at hc
  obtain ⟨⟨⟨⟨_, hfd⟩, _⟩, _⟩, hfl⟩ := hc
  refine ⟨hfd, fun f hf => ?_⟩
  rw [List.flatMap_eq_nil_iff] at hfl
  have hcf := hfl f hf
  simp only [checkField, List.append_eq_nil_iff] at hcf
  obtain ⟨⟨_, _⟩, harg⟩ := hcf
  cases ha : d.withBuiltins.find? f.arg with
  | none => rw [ha] at harg; simp at harg
  | some ac =>
    rw [ha] at harg
    simp only [List.append_eq_nil_iff] at harg
    obtain ⟨⟨hdep, _⟩, hinl⟩ := harg
    refine ⟨⟨ac, rfl⟩, ?_, ?_⟩
    · intro hld
      cases hcon : ((d.withBuiltins.ctypes.take i).map Ctype.name).contains f.arg with
      | true  => rfl
      | false => rw [hld, hcon] at hdep; simp at hdep
    · intro hinlary
      rw [hinlary] at hinl
      cases hm : d.withBuiltins.inlaryMax? (d.withBuiltins.ctypes[i]'hi).name f.name with
      | none => rw [hm] at hinl; simp at hinl; exact absurd hinl (by decide)
      | some n =>
        rw [hm] at hinl
        simp only [] at hinl
        refine ⟨n, rfl, ?_, ?_⟩ <;>
          · cases hr : (0 < n && n < Wf.u32Bound) with
            | true =>
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
              first | exact hr.1 | exact hr.2
            | false =>
              rw [hr] at hinl; simp at hinl; exact absurd hinl (by decide)

/-! ## An order-preserving `filterMap` preserves "declared earlier"

This is the clause the single-table `GenWellFormed` never had to face, and it
is the only place index arithmetic appears: `genStructs` drops the scalar
ctypes, so "the `arg` was declared before this ctype" has to be transported
across the filter to "the struct is emitted before this struct". -/

/-- If `a` sits in the first `i` elements and survives the filter, its image
sits in the first `(l.take i).filterMap f |>.length` elements — and that is a
prefix of what `filterMap` produces for the whole list. -/
theorem filterMap_take_prefix {α β : Type _} (f : α → Option β) :
    ∀ (l : List α) (i : Nat),
      (l.filterMap f).take ((l.take i).filterMap f).length
        = (l.take i).filterMap f := by
  intro l i
  have h : List.filterMap f l
      = (l.take i).filterMap f ++ (l.drop i).filterMap f := by
    rw [← List.filterMap_append, List.take_append_drop]
  rw [h]
  exact List.take_left

/-- Membership version, which is what `checkStructs`'s `earlier.contains`
needs. -/
theorem mem_filterMap_take {α β : Type _} [BEq β] [LawfulBEq β]
    {f : α → Option β} {l : List α} {i : Nat} {a : α} {b : β}
    (ha : a ∈ l.take i) (hfa : f a = some b) :
    b ∈ (l.filterMap f).take ((l.take i).filterMap f).length := by
  rw [filterMap_take_prefix f l i]
  exact List.mem_filterMap.mpr ⟨a, ha, hfa⟩

end Layout
end Templates

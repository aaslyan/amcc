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

-- `String.toList` on a *symbolic* string does not whnf, so unfolding `mangle`
-- during elaboration diverges: every statement here that mentions
-- `mangle c.name` timed out until this line was added. It is `local` rather
-- than global because the checker's `rfl` examples elsewhere do compute
-- `mangle` on literals, and must keep doing so.
attribute [local irreducible] Dmmeta.mangle

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

/-! ## The struct table

`mangle` is a fold over characters with a keyword lookup, so leaving it to
`rfl` and unification makes the elaborator whnf it on symbolic names. Every
projection through it is therefore a named `rfl` lemma, applied rather than
recomputed. -/

/-- The generated struct's name is the mangled ctype name. -/
theorem structOf_name (full : Db) (c : Ctype) :
    (structOf full c).name = mangle c.name := rfl

/-- Struct names are pairwise distinct, because ctype names are and
`genStructs` keeps the name. -/
theorem structs_distinct {d : Db} {nf : Ctype → String}
    (hnf : ∀ c, (structOf d.withBuiltins c).name = nf c)
    (h : dups (d.withBuiltins.ctypes.map nf) = []) :
    ((genStructs d).map StructDef.name).Pairwise (· ≠ ·) := by
  refine pairwise_filterMap_map (g := StructDef.name) (h := nf)
    (f := fun c => if c.scalar.isSome then none else some (structOf d.withBuiltins c))
    ?_ _ (CSubset.dups_eq_nil_iff.mp h)
  intro a b hab
  simp only [] at hab
  cases hs : a.scalar with
  | none =>
    rw [hs] at hab
    simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hab
    rw [← Option.some.inj hab]; exact hnf a
  | some t => rw [hs] at hab; simp at hab

/-- Field names within one generated struct are pairwise distinct, because the
ctype's are and `structOf` keeps the name. -/
theorem fields_distinct {full : Db} {c : Ctype} {nf : Field → String}
    (hnf : ∀ f t, fieldTy full c.name f = some t →
      ((mangle f.name, t) : String × Ty).1 = nf f)
    (h : (c.fields.map nf).Pairwise (· ≠ ·)) :
    ((structOf full c).fields.map Prod.fst).Pairwise (· ≠ ·) := by
  refine pairwise_filterMap_map (g := Prod.fst) (h := nf)
    (f := fun f => (fieldTy full c.name f).map (fun t => (mangle f.name, t)))
    ?_ c.fields h
  intro a b hab
  simp only [] at hab
  cases ht : fieldTy full c.name a with
  | none => rw [ht] at hab; simp at hab
  | some t =>
    rw [ht] at hab
    simp only [Option.map_some] at hab
    rw [← Option.some.inj hab]
    exact hnf a t ht

/-- `Pairwise` on a `flatMap` restricts to each block. -/
theorem pairwise_of_flatMap {α β : Type _} {R : β → β → Prop} {f : α → List β} :
    ∀ (l : List α), (l.flatMap f).Pairwise R → ∀ a ∈ l, (f a).Pairwise R
  | [], _, _, hm => absurd hm (by simp)
  | a :: l, hp, b, hb => by
    rw [List.flatMap_cons, List.pairwise_append] at hp
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hp.1
    · exact pairwise_of_flatMap l hp.2.1 b hb'

/-- **Within one ctype, the mangled field names are distinct.** Not from the
raw-name clause — two raw names can mangle together — but from the *qualified*
name clause, by cancelling the shared `<ctype>_` prefix. This is the clause
from 47ecf60 doing exactly the job mangling needed it for. -/
theorem mangled_fields_pairwise {d : Db}
    (hq : dups (qualNames d.withBuiltins) = [])
    {j : Nat} (hj : j < d.withBuiltins.ctypes.length) :
    (((d.withBuiltins.ctypes[j]'hj).fields.map
      (fun f => mangle f.name)).Pairwise (· ≠ ·)) := by
  have hqp : ((d.withBuiltins.ctypes.flatMap
      (fun c => c.fields.map (fun f => qualName c.name f.name))).Pairwise (· ≠ ·)) :=
    CSubset.dups_eq_nil_iff.mp hq
  have hblock := pairwise_of_flatMap (R := (· ≠ ·))
    d.withBuiltins.ctypes hqp (d.withBuiltins.ctypes[j]'hj) (List.getElem_mem hj)
  rw [List.pairwise_map] at hblock ⊢
  refine hblock.imp ?_
  intro a b hab hm
  exact hab (congrArg (fun t => mangle (d.withBuiltins.ctypes[j]'hj).name ++ "_" ++ t) hm)

/-! ## What `Dmmeta.check` hands over

`checkCtype` and `checkField` are concatenations, and the proof needs three of
their components separately. Pulling them out once keeps the case analysis
below readable, and puts the `++`-nesting in one place where a change to the
checker's clause order shows up as one broken pattern rather than five. -/

/-- Acceptance gives, for every ctype and every field of it: the field names of
that ctype are distinct, the `arg` resolves, a layout-carrying field's `arg`
was declared earlier, and an `Inlary`'s bound is a legal array size. -/
theorem facts_of_check {d : Db} (h : check d = []) :
    (dups d.withBuiltins.names = []
      ∧ dups (d.withBuiltins.ctypes.map (fun c => mangle c.name)) = []
      ∧ dups (qualNames d.withBuiltins) = [])
    ∧ (∀ r, d.root = some r →
        ∃ c, d.withBuiltins.find? r = some c ∧ c.scalar = none)
    ∧ ∀ i, ∀ hi : i < d.withBuiltins.ctypes.length,
        dups ((d.withBuiltins.ctypes[i]'hi).fields.map Field.name) = []
        ∧ ((d.withBuiltins.ctypes[i]'hi).scalar.isSome = true →
            (d.withBuiltins.ctypes[i]'hi).fields = [])
        ∧ ∀ f ∈ (d.withBuiltins.ctypes[i]'hi).fields,
            (∃ ac, d.withBuiltins.find? f.arg = some ac)
            ∧ (f.reftype.layoutDep = true →
                ((d.withBuiltins.ctypes.take i).map Ctype.name).contains f.arg = true)
            ∧ (f.reftype = .Inlary →
                ∃ n, d.withBuiltins.inlaryMax? (d.withBuiltins.ctypes[i]'hi).name f.name = some n
                  ∧ 0 < n ∧ n < Wf.u32Bound)
            ∧ (f.reftype.needsRecordArg = true →
                ∃ ac, d.withBuiltins.find? f.arg = some ac ∧ ac.scalar = none) := by
  simp only [check, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨hdup, hmdup⟩, hqdup⟩, hroot⟩, hcty⟩, _⟩ := h
  refine ⟨⟨hdup, hmdup, hqdup⟩, ?_, fun i hi => ?_⟩
  · intro r hr
    rw [hr] at hroot
    simp only [] at hroot
    cases hf : d.withBuiltins.find? r with
    | none => rw [hf] at hroot; simp at hroot
    | some c =>
      rw [hf] at hroot
      simp only [] at hroot
      refine ⟨c, rfl, ?_⟩
      cases hs : c.scalar with
      | none   => rfl
      | some t => rw [hs] at hroot; simp at hroot
  rw [List.flatMap_eq_nil_iff] at hcty
  have hmem : ((d.withBuiltins.ctypes[i]'hi), i) ∈ d.withBuiltins.ctypes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact List.getElem?_eq_getElem hi
  have hc := hcty _ hmem
  simp only [checkCtype, List.append_eq_nil_iff, List.map_eq_nil_iff] at hc
  obtain ⟨⟨⟨⟨_, hfd⟩, _⟩, hsf⟩, hfl⟩ := hc
  refine ⟨hfd, ?_, fun f hf => ?_⟩
  · intro hsc
    cases hfs : (d.withBuiltins.ctypes[i]'hi).fields with
    | nil => rfl
    | cons a l =>
      rw [hsc, hfs] at hsf
      simp at hsf
  rw [List.flatMap_eq_nil_iff] at hfl
  have hcf := hfl f hf
  simp only [checkField, List.append_eq_nil_iff] at hcf
  obtain ⟨⟨_, _⟩, harg⟩ := hcf
  cases ha : d.withBuiltins.find? f.arg with
  | none => rw [ha] at harg; simp at harg
  | some ac =>
    rw [ha] at harg
    simp only [List.append_eq_nil_iff] at harg
    obtain ⟨⟨⟨hdep, _⟩, hneed⟩, hinl⟩ := harg
    refine ⟨⟨ac, rfl⟩, ?_, ?_, ?_⟩
    · intro hld
      cases hcon : ((d.withBuiltins.ctypes.take i).map Ctype.name).contains f.arg with
      | true  => rfl
      | false => rw [hld, hcon] at hdep; simp at hdep
    · intro hinlary
      rw [hinlary] at hinl
      cases hm : d.withBuiltins.inlaryMax? (d.withBuiltins.ctypes[i]'hi).name f.name with
      | none => rw [hm] at hinl; simp at hinl
      | some n =>
        rw [hm] at hinl
        simp only [] at hinl
        refine ⟨n, rfl, ?_, ?_⟩ <;>
          · cases hr : (0 < n && n < Wf.u32Bound) with
            | true =>
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
              first | exact hr.1 | exact hr.2
            | false =>
              rw [hr] at hinl; simp at hinl
    · -- a pointer or an index resolves to a record
      intro hnr
      refine ⟨ac, rfl, ?_⟩
      cases hsc : ac.scalar with
      | none   => rfl
      | some t =>
        rw [hnr, hsc] at hneed
        simp only [Option.isSome_some, Bool.and_true, if_true] at hneed
        exact absurd hneed (by simp)

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

/-- **Where a filtered element ends up.** The bridge between the *ctype* index
`Dmmeta.check` speaks in and the *struct* index `Wf.checkStructs` speaks in.

By induction on `l` with `i` generalised, splitting on `f a`. Do not try to do
this over `List.zipIdx` directly — `List.mem_zipIdx_iff_getElem?` turns the
membership into this statement first, which is also how `facts_of_check` gets
at the ctype index. -/
theorem getElem?_filterMap {α β : Type _} (f : α → Option β) :
    ∀ (l : List α) (i : Nat) (b : β), (l.filterMap f)[i]? = some b →
      ∃ (j : Nat) (hj : j < l.length),
        f (l[j]'hj) = some b ∧ ((l.take j).filterMap f).length = i
  | [], i, b, h => by simp at h
  | a :: l, i, b, h => by
    cases hfa : f a with
    | none =>
      rw [List.filterMap_cons, hfa] at h
      obtain ⟨j, hj, h1, h2⟩ := getElem?_filterMap f l i b h
      exact ⟨j + 1, by simpa using hj, h1, by simpa [List.filterMap_cons, hfa] using h2⟩
    | some b0 =>
      rw [List.filterMap_cons, hfa] at h
      cases i with
      | zero =>
        refine ⟨0, by simp, ?_, by simp⟩
        show f a = some b
        rw [hfa]
        simpa using h
      | succ i =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨j, hj, h1, h2⟩ := getElem?_filterMap f l i b h
        refine ⟨j + 1, by simpa using hj, h1, ?_⟩
        simp [hfa, h2]

/-! ## What a lowered field type can be

One case analysis over the six reftypes with a lowering, crossed with "is the
`arg` a scalar". It is the only place the shape of `fieldTy` is opened, and
everything the struct obligations need is read off it here. -/

/-- Every generated field type is a scalar, a struct, a pointer to one, or a
bounded array of one — and in the last three cases the struct is the field's
`arg`, which resolves to a *record* ctype. `layoutDeps` is non-empty only when
the reftype embeds rather than points, which is exactly `Reftype.layoutDep`. -/
theorem fieldTy_shape {full : Db} {owner : String} {f : Field} {t : Ty}
    (ht : fieldTy full owner f = some t) :
    (∀ n ∈ Wf.Ty.allStructs t,
        n = mangle f.arg ∧ ∃ ac, full.find? f.arg = some ac ∧ ac.scalar = none)
    ∧ (∀ n ∈ Wf.Ty.layoutDeps t, n = mangle f.arg ∧ f.reftype.layoutDep = true)
    ∧ (f.reftype ≠ .Inlary → Wf.Ty.sizesOk t = true)
    ∧ (∀ k, full.inlaryMax? owner f.name = some k → 0 < k → k < Wf.u32Bound →
        Wf.Ty.sizesOk t = true) := by
  simp only [fieldTy] at ht
  obtain ⟨ac, hac, ht⟩ := Option.bind_eq_some_iff.mp ht
  -- `base` is the argument's own type: a machine scalar, or the record struct
  have hbase : ∀ (u : Ty),
      (match ac.scalar with
        | some st => Ty.scalar st | none => Ty.strct (mangle ac.name)) = u →
      (∀ n ∈ Wf.Ty.allStructs u, n = mangle f.arg ∧ ac.scalar = none)
        ∧ Wf.Ty.layoutDeps u = Wf.Ty.allStructs u
        ∧ Wf.Ty.sizesOk u = true := by
    intro u hu
    have hname : mangle ac.name = mangle f.arg :=
      congrArg mangle (Db.find?_name hac)
    cases hs : ac.scalar with
    | some st => rw [hs] at hu; subst hu; exact ⟨by simp [Wf.Ty.allStructs], rfl, rfl⟩
    | none =>
      rw [hs] at hu; subst hu
      refine ⟨?_, rfl, rfl⟩
      intro n hn
      simp only [Wf.Ty.allStructs, List.mem_singleton] at hn
      exact ⟨hn.trans hname, rfl⟩
  cases hr : f.reftype with
  | Val =>
    rw [hr] at ht; simp only [Option.some.injEq] at ht
    obtain ⟨h1, h2, h3⟩ := hbase t ht
    exact ⟨fun n hn => ⟨(h1 n hn).1, ac, hac, (h1 n hn).2⟩,
      fun n hn => ⟨(h1 n (h2 ▸ hn)).1, rfl⟩, fun _ => h3,
      fun _ _ _ _ => h3⟩
  | Base =>
    rw [hr] at ht; simp only [Option.some.injEq] at ht
    obtain ⟨h1, h2, h3⟩ := hbase t ht
    exact ⟨fun n hn => ⟨(h1 n hn).1, ac, hac, (h1 n hn).2⟩,
      fun n hn => ⟨(h1 n (h2 ▸ hn)).1, rfl⟩, fun _ => h3,
      fun _ _ _ _ => h3⟩
  | Pkey =>
    rw [hr] at ht
    cases hs : ac.scalar with
    | some st =>
      rw [hs] at ht; simp only [Option.isSome_some, if_true, Option.some.injEq] at ht
      subst ht
      exact ⟨by simp [Wf.Ty.allStructs], by simp [Wf.Ty.layoutDeps], fun _ => rfl,
        fun _ _ _ _ => rfl⟩
    | none =>
      rw [hs] at ht
      simp only [Option.isSome_none, Bool.false_eq_true, if_false,
        Option.some.injEq] at ht
      subst ht
      have hname : mangle ac.name = mangle f.arg :=
      congrArg mangle (Db.find?_name hac)
      refine ⟨?_, by simp [Wf.Ty.layoutDeps], fun _ => rfl, fun _ _ _ _ => rfl⟩
      intro n hn
      simp only [Wf.Ty.allStructs, List.mem_singleton] at hn
      exact ⟨hn.trans hname, ac, hac, hs⟩
  | Upptr | Ptr =>
    all_goals (
      rw [hr] at ht; simp only [Option.some.injEq] at ht
      subst ht
      obtain ⟨h1, _, h3⟩ := hbase _ rfl
      refine ⟨?_, by simp [Wf.Ty.layoutDeps], fun _ => ?_, fun _ _ _ _ => ?_⟩
      · intro n hn
        simp only [Wf.Ty.allStructs] at hn
        exact ⟨(h1 n hn).1, ac, hac, (h1 n hn).2⟩
      · simpa [Wf.Ty.sizesOk] using h3
      · simpa [Wf.Ty.sizesOk] using h3)
  | Inlary =>
    rw [hr] at ht
    simp only [Option.map_eq_some_iff] at ht
    obtain ⟨k, hk, ht⟩ := ht
    subst ht
    obtain ⟨h1, h2, h3⟩ := hbase _ rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n hn
      simp only [Wf.Ty.allStructs] at hn
      exact ⟨(h1 n hn).1, ac, hac, (h1 n hn).2⟩
    · intro n hn
      simp only [Wf.Ty.layoutDeps] at hn
      rw [← h2] at h1
      exact ⟨(h1 n hn).1, rfl⟩
    · intro hne; exact absurd rfl hne
    · intro k' hk' hpos hlt
      rw [hk] at hk'
      cases hk'
      simp only [Wf.Ty.sizesOk, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hpos, hlt⟩, h3⟩
  | Lary | Tary | Tpool | Lpool | Blkpool | Malloc | Sbrk | Delptr | Thash
  | Llist | Bheap | Atree | Ptrary | Count =>
    all_goals (rw [hr] at ht; simp at ht)

/-- A layout dependency is a mentioned struct — the inclusion the nesting
obligation needs in order to reuse `allStructs`'s resolution fact. -/
theorem layoutDeps_sub_allStructs : ∀ (t : Ty) (n : String),
    n ∈ Wf.Ty.layoutDeps t → n ∈ Wf.Ty.allStructs t
  | .scalar _, _, h => h
  | .strct _,  _, h => h
  | .arr t' _, n, h => layoutDeps_sub_allStructs t' n h
  | .ptr _,    _, h => by simp [Wf.Ty.layoutDeps] at h

/-! ## Assembling `LayoutWellFormed`

The three obligations, one after the other, against the concatenation
`Wf.check` is. -/

/-- `genStructs` is a `filterMap` over the ctypes; naming the function once
keeps the two views of it (here and in `structs_distinct`) from drifting. -/
def structOf? (full : Db) (c : Ctype) : Option StructDef :=
  if c.scalar.isSome then none else some (structOf full c)

theorem genStructs_eq (d : Db) :
    genStructs d = d.withBuiltins.ctypes.filterMap (structOf? d.withBuiltins) := rfl

/-- Every struct AMCC emits is some ctype's, and its name is that ctype's. -/
theorem structOf?_name {full : Db} {c : Ctype} {sd : StructDef}
    (h : structOf? full c = some sd) :
    sd.name = mangle c.name ∧ sd = structOf full c := by
  simp only [structOf?] at h
  cases hs : c.scalar with
  | some t => rw [hs] at h; simp at h
  | none =>
    rw [hs] at h
    simp only [Option.isSome_none, Bool.false_eq_true, if_false,
      Option.some.injEq] at h
    exact ⟨by rw [← h]; exact structOf_name _ _, h.symm⟩

/-- **The struct table a schema lowers to is well-formed.** Named separately
from `layoutWellFormed` because the three ctype-model templates emit exactly
this struct table alongside their own functions, and each needs this half on
its own.

checked by: `lake build` -/
theorem checkStructs_gen {d : Db} (hchk : check d = []) :
    Wf.checkStructs (genStructs d) = [] := by
  obtain ⟨⟨hdup, hmdup, hqdup⟩, _, hcty⟩ := facts_of_check hchk
  have hmemName : ∀ (c : Ctype), c ∈ d.withBuiltins.ctypes → c.scalar = none →
      ((genStructs d).map StructDef.name).contains (mangle c.name) = true := by
    intro c hc hs
    refine List.elem_eq_true_of_mem (List.mem_map.mpr
      ⟨structOf d.withBuiltins c, ?_, structOf_name _ _⟩)
    exact List.mem_filterMap.mpr ⟨c, hc, by simp [hs]⟩
  simp only [Wf.checkStructs, List.append_eq_nil_iff]
  refine ⟨CSubset.distinct_eq_nil
    (structs_distinct (nf := fun c => mangle c.name) (fun _ => rfl) hmdup), ?_⟩
  rw [List.flatMap_eq_nil_iff]
  rintro ⟨sd, i⟩ hsdi
  -- which ctype produced this struct, and where it sat
  rw [List.mem_zipIdx_iff_getElem?] at hsdi
  obtain ⟨j, hj, hsj, hlen⟩ :=
    getElem?_filterMap (structOf? d.withBuiltins) d.withBuiltins.ctypes i sd
      (by rw [← genStructs_eq]; exact hsdi)
  obtain ⟨hsdname, hsdeq⟩ := structOf?_name hsj
  obtain ⟨hfd, _, hff⟩ := hcty j hj
  simp only [List.append_eq_nil_iff]
  refine ⟨CSubset.distinct_eq_nil (hsdeq ▸ fields_distinct
    (nf := fun f => mangle f.name) (fun _ _ _ => rfl)
    (mangled_fields_pairwise hqdup hj)), ?_⟩
  rw [List.flatMap_eq_nil_iff]
  rintro ⟨fn, ft⟩ hfv
  -- the field this slot came from, and its lowering
  rw [hsdeq] at hfv
  simp only [structOf, List.mem_filterMap] at hfv
  obtain ⟨f, hfmem, hfeq⟩ := hfv
  obtain ⟨t, hty, hpair⟩ := Option.map_eq_some_iff.mp hfeq
  injection hpair with hfn hft
  subst hft
  obtain ⟨hall, hdep, hsz, hszI⟩ := fieldTy_shape hty
  obtain ⟨hargres, hargearly, hinl, _⟩ := hff f hfmem
  simp only [List.append_eq_nil_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- obligation 3: the size is legal
    by_cases hI : f.reftype = .Inlary
    · obtain ⟨k, hk, hpos, hlt⟩ := hinl hI
      rw [if_pos (hszI k hk hpos hlt)]
    · rw [if_pos (hsz hI)]
  · -- obligation 2a: every struct the type mentions is emitted
    rw [List.flatMap_eq_nil_iff]
    intro n hn
    obtain ⟨hnarg, ac, hac, hacs⟩ := hall n hn
    have hmem : ac ∈ d.withBuiltins.ctypes :=
      List.mem_of_find?_eq_some (by simpa [Db.find?] using hac)
    rw [if_pos (by rw [hnarg, ← Db.find?_name hac]; exact hmemName ac hmem hacs)]
  · -- obligation 2b: a layout dependency was emitted *earlier*
    rw [List.flatMap_eq_nil_iff]
    intro n hn
    obtain ⟨hnarg, hld⟩ := hdep n hn
    obtain ⟨ac, hacmem, hacname⟩ :=
      List.mem_map.mp (List.mem_of_elem_eq_true (hargearly hld))
    obtain ⟨_, ac', hac', hacs'⟩ := hall n (layoutDeps_sub_allStructs _ n hn)
    -- the ctype the checker found and the one `find?` resolves are the same,
    -- because ctype names are distinct
    have hsame : ac = ac' := by
      have hmem : ac ∈ d.withBuiltins.ctypes := List.mem_of_mem_take hacmem
      have hfind : d.withBuiltins.find? ac.name = some ac :=
        Db.find?_of_mem_pairwise _ (CSubset.dups_eq_nil_iff.mp hdup) ac hmem
      rw [hacname] at hfind
      exact Option.some.inj (hfind.symm.trans hac')
    refine if_pos ?_
    refine List.elem_eq_true_of_mem (List.mem_map.mpr
      ⟨structOf d.withBuiltins ac, ?_, ?_⟩)
    · rw [← hlen, genStructs_eq]
      refine mem_filterMap_take (i := j) hacmem ?_
      simp [structOf?, hsame ▸ hacs']
    · rw [structOf_name, hnarg, ← hacname]

/-- **The database global a schema lowers to is well-formed.** The other half
the templates need on its own.

checked by: `lake build` -/
theorem checkGlobals_gen {d : Db} (hchk : check d = []) :
    Wf.checkGlobals (genStructs d) (genGlobals d) = [] := by
  obtain ⟨_, hroot, _⟩ := facts_of_check hchk
  simp only [Wf.checkGlobals, genGlobals, List.append_eq_nil_iff]
  cases hr : d.root with
  | none => exact ⟨rfl, rfl⟩
  | some r =>
    obtain ⟨c, hc, hcs⟩ := hroot r hr
    refine ⟨CSubset.distinct_eq_nil (by simp), ?_⟩
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_eq_nil_iff]
    refine ⟨rfl, ?_⟩
    simp only [Wf.Ty.allStructs, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    have hmem : c ∈ d.withBuiltins.ctypes :=
      List.mem_of_find?_eq_some (by simpa [Db.find?] using hc)
    have hname : mangle c.name = mangle r := congrArg mangle (Db.find?_name hc)
    refine if_pos ?_
    refine List.elem_eq_true_of_mem (List.mem_map.mpr
      ⟨structOf d.withBuiltins c, ?_, ?_⟩)
    · exact List.mem_filterMap.mpr ⟨c, hmem, by simp [hcs]⟩
    · rw [structOf_name]; exact hname

/-- **The layout pass is well-formed for every accepted schema.**

`layoutWf` is `layoutCheck`, which is `Dmmeta.check` plus the no-empty-struct
clause; only the first half is used here, so the theorem is really about
`Dmmeta.check` and the empty-struct clause is what keeps the *output* legal C
rather than what keeps it well-formed in the subset's sense.

checked by: `lake build` -/
theorem layoutWellFormed : LayoutWellFormed := by
  intro d hwf
  have hchk : check d = [] := by
    have h : layoutCheck d = [] := List.isEmpty_iff.mp hwf
    simp only [layoutCheck, List.append_eq_nil_iff] at h
    exact h.1
  simp only [Wf.check, genLayout, List.append_eq_nil_iff]
  exact ⟨⟨⟨checkStructs_gen hchk, checkGlobals_gen hchk⟩, rfl⟩, rfl⟩

end Layout
end Templates

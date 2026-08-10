import Amcc.Templates.LayoutWf
import Amcc.CSubset.Calls

/-!
# AMCC — distinctness of generated function names

Obligation 1 asks that a translation unit's function names be pairwise
distinct. For the array table that was four names built from one schema, and
`ArrayTableWf` discharged it by hand. For the ctype-model templates the name
list is a **`flatMap` over fields**, one block of four (or five, or nine)
names per field, and the distinctness has to come from the schema's own
`<ctype>_<field>` uniqueness clause.

This module is that argument, once, for all three templates. It is here rather
than in whichever template needed it first because the shape is identical in
each: same `flatMap`, same qualified prefix, different literal suffixes.

## The two ways two generated names could collide

**Same field, different operation.** `q ++ "_Init"` versus `q ++ "_Get"`.
Cancelling the shared prefix leaves the suffixes, and `CSubset.append_ne`
already did this for the array table.

**Different fields.** `q ++ s` versus `q' ++ s'` with `q ≠ q'`. If `s = s'`
this is right-cancellation. If `s ≠ s'` it is *not* enough that the suffixes
differ — `q ++ "_Q"` and `q' ++ "_Get"` could in principle coincide with
`q' = q ++ "_Ge"`… except that they cannot, because reading both strings
**backwards** they disagree within the first two characters.

That is the trick `append_ne_rev` packages: reversing turns a suffix
comparison, which needs length reasoning, into a *prefix* comparison, which
`simp` decides by peeling `List.cons`. Each of the six suffix pairs a template
needs is then one `by simp`.

## Why the qualified names are distinct in the first place

`Dmmeta.check` has the clause: `c ++ "_" ++ f` is not injective in the pair —
ctype `a` with field `b_c` and ctype `a_b` with field `c` both qualify to
`a_b_c` — so the schema checker rejects the collision. That clause landed in
47ecf60 precisely so the accessor laws would not be vacuous; here it is what
makes the *whole program* well-formed rather than one function resolvable.

The templates each generate over a *filtered* subset of the fields, so what
descends is not the whole `qualNames` list but a **sublist** of it, and
`List.Pairwise.sublist` does the rest.
-/

-- `String.toList` on a *symbolic* string does not whnf, so unfolding `mangle`
-- during elaboration diverges: every statement here that mentions
-- `mangle c.name` timed out until this line was added. It is `local` rather
-- than global because the checker's `rfl` examples elsewhere do compute
-- `mangle` on literals, and must keep doing so.
attribute [local irreducible] Dmmeta.mangle

namespace Templates
namespace NameWf

open Dmmeta
open CSubset

/-! ## Sublists

`Layout.pairwise_filterMap_map` proved the `Pairwise` consequence directly.
The `Sublist` form below is strictly more useful — it composes through the
outer `flatMap`, which the `Pairwise` form cannot. -/

/-- An order-preserving `filterMap` whose image keeps the projected value
yields a **sublist** of the projection. -/
theorem filterMap_map_sublist {α β γ : Type _} {p : α → Option β} {g : β → γ}
    {h : α → γ} (hg : ∀ a b, p a = some b → g b = h a) :
    ∀ (l : List α), ((l.filterMap p).map g).Sublist (l.map h)
  | [] => List.Sublist.slnil
  | a :: l => by
    rw [List.map_cons]
    cases hp : p a with
    | none =>
      rw [List.filterMap_cons, hp]
      exact (filterMap_map_sublist hg l).cons _
    | some b =>
      rw [List.filterMap_cons, hp, List.map_cons, hg a b hp]
      exact (filterMap_map_sublist hg l).cons₂ _

/-- Sublists compose through a `flatMap`. -/
theorem flatMap_sublist {α β : Type _} {f g : α → List β}
    (h : ∀ a, (f a).Sublist (g a)) :
    ∀ (l : List α), (l.flatMap f).Sublist (l.flatMap g)
  | [] => List.Sublist.slnil
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h a).append (flatMap_sublist h l)

/-! ## `Pairwise` through a `flatMap`

The two obligations a block-structured name list has: each block is internally
distinct, and any two *different* blocks are disjointly distinct. -/

theorem pairwise_flatMap {α β : Type _} {R : β → β → Prop} {f : α → List β} :
    ∀ (l : List α),
      (∀ a ∈ l, (f a).Pairwise R) →
      l.Pairwise (fun a b => ∀ x ∈ f a, ∀ y ∈ f b, R x y) →
      (l.flatMap f).Pairwise R
  | [], _, _ => List.Pairwise.nil
  | a :: l, hin, hcr => by
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨hin a (by simp), ?_, ?_⟩
    · exact pairwise_flatMap l (fun b hb => hin b (List.mem_cons_of_mem _ hb))
        (List.pairwise_cons.mp hcr).2
    · intro x hx y hy
      obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.mp hy
      exact (List.pairwise_cons.mp hcr).1 b hb x hx y hyb

/-! ## Suffixed names

Two lemmas, and between them they settle every pair a template can produce. -/

/-- Different qualified prefixes, **same** suffix. -/
theorem append_ne_of_prefix_ne {q q' s : String} (h : q ≠ q') :
    q ++ s ≠ q' ++ s := by
  intro e
  refine h (String.ext ?_)
  have hd := congrArg String.toList e
  simp only [String.toList_append] at hd
  exact List.append_cancel_right hd

/-- Two character lists disagree before either runs out — so neither is a
prefix of the other, however they are extended. Decidable, which is the point:
every instance is `by decide` on two string literals. -/
def prefixIncompat : List Char → List Char → Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then prefixIncompat as bs else true

theorem append_ne_of_incompat : ∀ (a b : List Char),
    prefixIncompat a b = true → ∀ (l l' : List Char), a ++ l ≠ b ++ l'
  | [], _, h, _, _ => by simp [prefixIncompat] at h
  | _ :: _, [], h, _, _ => by simp [prefixIncompat] at h
  | a :: as, b :: bs, h, l, l' => by
    simp only [prefixIncompat] at h
    by_cases hab : a = b
    · simp only [hab, beq_self_eq_true, if_true] at h
      simp only [List.cons_append, ne_eq, List.cons.injEq, not_and]
      intro _
      exact append_ne_of_incompat as bs h l l'
    · simp only [List.cons_append, ne_eq, List.cons.injEq, not_and]
      intro heq
      exact absurd heq hab

/-- **Different suffixes, whatever the prefixes.** The hypothesis is stated on
the *reversed* character lists, because that turns "is one suffix a suffix of
the other" — which needs length reasoning — into "do they disagree within the
first few characters", which is decidable on literals.

Every instance is `NameWf.append_ne_rev (by decide)`. -/
theorem append_ne_rev {q q' s s' : String}
    (h : prefixIncompat s.toList.reverse s'.toList.reverse = true) :
    q ++ s ≠ q' ++ s' := by
  intro e
  have hd := congrArg (fun t : String => t.toList.reverse) e
  simp only [String.toList_append, List.reverse_append] at hd
  exact append_ne_of_incompat _ _ h _ _ hd

/-! ## The qualified names a schema declares

`Dmmeta.check` runs against `withBuiltins`, and the templates generate from
`d` itself. The two agree, because a builtin ctype has no fields. -/

theorem qualNames_withBuiltins (d : Db) : qualNames d.withBuiltins = qualNames d := by
  simp only [qualNames, Db.withBuiltins, List.flatMap_append]
  simp [builtins]

/-- **The schema's qualified names are pairwise distinct.** The form every
template's distinctness proof starts from. -/
theorem quals_pairwise {d : Db} (hchk : check d = []) :
    (qualNames d).Pairwise (· ≠ ·) := by
  simp only [check, List.append_eq_nil_iff, List.map_eq_nil_iff] at hchk
  obtain ⟨⟨⟨⟨⟨_, _⟩, hq⟩, _⟩, _⟩, _⟩ := hchk
  rw [← qualNames_withBuiltins d]
  exact CSubset.dups_eq_nil_iff.mp hq

/-! ## Fields a template generates over

Each of the three templates selects its fields the same way — a `flatMap` over
the ctypes, a `filterMap` on the reftype — so the sublist argument is written
once here and instantiated with the reftype. -/

/-- The fields of one reftype, paired with their owning ctype: the shape
`Upptr.upFields`, `Llist.listFields` and `Thash.hashFields` all have. -/
def fieldsOf (d : Db) (r : Reftype) : List (Dmmeta.Ident × Field) :=
  d.ctypes.flatMap (fun c =>
    c.fields.filterMap (fun f => if f.reftype == r then some (c.name, f) else none))

/-- **Their qualified names are a sublist of the schema's**, so distinctness
descends. -/
theorem fieldsOf_quals_sublist (d : Db) (r : Reftype) :
    (((fieldsOf d r).map (fun cf => qualName cf.1 cf.2.name)).Sublist
      (qualNames d)) := by
  simp only [fieldsOf, qualNames, List.map_flatMap]
  refine flatMap_sublist (fun c => ?_) d.ctypes
  refine filterMap_map_sublist
    (g := fun cf : Dmmeta.Ident × Field => qualName cf.1 cf.2.name)
    (h := fun f : Field => qualName c.name f.name) ?_ c.fields
  intro a b hab
  simp only [] at hab
  cases hr : a.reftype == r with
  | true  =>
    rw [hr] at hab
    simp only [if_true, Option.some.injEq] at hab
    rw [← hab]
  | false => rw [hr] at hab; simp at hab

/-- ...and therefore pairwise distinct.

checked by: `lake build` -/
theorem fieldsOf_quals_pairwise {d : Db} (hchk : check d = []) (r : Reftype) :
    (((fieldsOf d r).map (fun cf => qualName cf.1 cf.2.name)).Pairwise (· ≠ ·)) :=
  (quals_pairwise hchk).sublist (fieldsOf_quals_sublist d r)

/-- The cross-block condition, in the form `pairwise_flatMap` wants: two
entries at different positions of the field list have different qualified
names. -/
theorem fieldsOf_pairwise_qual {d : Db} (hchk : check d = []) (r : Reftype) :
    (fieldsOf d r).Pairwise
      (fun a b : Dmmeta.Ident × Field =>
        qualName a.1 a.2.name ≠ qualName b.1 b.2.name) := by
  have h := fieldsOf_quals_pairwise hchk r
  rwa [List.pairwise_map] at h

/-! ## Looking a generated struct field up

`checkStmt` on `row->f` needs `Ctx.field?` to resolve, which is two `find?`s:
the struct by ctype name, then the field by name. Both are "the first match in
a distinct-keyed list", which is `CSubset.find?_of_mem_pairwise`; what has to
be supplied is membership and the distinctness, and both come from the layout
proof. Shared, because all three templates dereference a row. -/

/-- The generated struct for a record ctype resolves by name. -/
theorem structs_find? {d : Db} (hchk : check d = []) {c : Ctype}
    (hc : c ∈ d.withBuiltins.ctypes) (hs : c.scalar = none) :
    (genStructs d).find? (fun sd => sd.name == mangle c.name)
      = some (structOf d.withBuiltins c) := by
  obtain ⟨⟨_, hmdup, _⟩, _, _⟩ := Layout.facts_of_check hchk
  have h := CSubset.find?_of_mem_pairwise (f := StructDef.name) (genStructs d)
    (structOf d.withBuiltins c)
    (List.mem_filterMap.mpr ⟨c, hc, by simp [hs]⟩)
    (Layout.structs_distinct (nf := fun c => mangle c.name) (fun _ => rfl) hmdup)
  rw [Layout.structOf_name] at h
  exact h

/-- ...and a lowered field resolves within it. -/
theorem struct_field? {full : Db} {c : Ctype} {f : Field} {t : Ty}
    (hfd : (c.fields.map (fun f => mangle f.name)).Pairwise (· ≠ ·))
    (hf : f ∈ c.fields) (hty : fieldTy full c.name f = some t) :
    (structOf full c).fields.find? (fun fv => fv.1 == mangle f.name)
      = some (mangle f.name, t) := by
  have h := CSubset.find?_of_mem_pairwise (f := Prod.fst)
    (structOf full c).fields (mangle f.name, t)
    (List.mem_filterMap.mpr ⟨f, hf, by rw [hty]; rfl⟩)
    (Layout.fields_distinct (nf := fun f => mangle f.name) (fun _ _ _ => rfl) hfd)
  exact h

/-- The two composed, in the form `Wf.Ctx.field?` wants. -/
theorem ctx_field? {d : Db} (hchk : check d = []) {c : Ctype} {f : Field} {t : Ty}
    (hc : c ∈ d.withBuiltins.ctypes) (hs : c.scalar = none) (hf : f ∈ c.fields)
    (hty : fieldTy d.withBuiltins c.name f = some t)
    {ctx : Wf.Ctx} (hstructs : ctx.structs = genStructs d) :
    ctx.field? (mangle c.name) (mangle f.name) = some t := by
  obtain ⟨⟨_, _, hqdup⟩, _, _⟩ := Layout.facts_of_check hchk
  obtain ⟨i, hi, hci⟩ : ∃ i, ∃ hi : i < d.withBuiltins.ctypes.length,
      (d.withBuiltins.ctypes[i]'hi) = c := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp hc
    exact ⟨i, hi.1, hi.2⟩
  have hfd : (c.fields.map (fun f => mangle f.name)).Pairwise (· ≠ ·) := by
    rw [← hci]; exact Layout.mangled_fields_pairwise hqdup hi
  simp only [Wf.Ctx.field?, Wf.Ctx.struct?, hstructs, structs_find? hchk hc hs]
  show (do
    let fv ← List.find? (fun fv => fv.1 == mangle f.name)
      (structOf d.withBuiltins c).fields
    some fv.2) = some t
  rw [struct_field? hfd hf hty]
  rfl

/-- An `Upptr` at a record `arg` lowers to a pointer to that record's struct —
the exact type the four accessors assign and return. -/
theorem fieldTy_upptr {full : Db} {owner : Dmmeta.Ident} {f : Field} {ac : Ctype}
    (hr : f.reftype = .Upptr) (hac : full.find? f.arg = some ac)
    (hs : ac.scalar = none) :
    fieldTy full owner f = some (.ptr (.strct (mangle f.arg))) := by
  have hname : mangle ac.name = mangle f.arg := congrArg mangle (Db.find?_name hac)
  simp only [fieldTy, hac, hr]
  show (some ((match ac.scalar with
    | some st => Ty.scalar st
    | none    => Ty.strct (mangle ac.name)).ptr) : Option Ty)
      = some (Ty.strct (mangle f.arg)).ptr
  rw [hs, hname]

end NameWf
end Templates

import Amcc.Templates.NameWf
import Amcc.Templates.Llist

/-!
# AMCC — the intrusive list is well-formed for every accepted schema

`Templates/Llist.lean` had `Wf.check … = []` only as a computation on its
sample schema. This closes the gap, and with `UpptrWf` it is the second of the
three ctype-model templates to match what `scripts/gen/*_gen.h` already claims.

## How this differs from `UpptrWf`

Two ways, one easier and one harder.

**Easier: one block, not a `flatMap`.** `genLlist` emits the list for the
*first* `Llist` field of the root, so the name obligation is nine names with
one shared prefix. `CSubset.append_ne` settles all thirty-six pairs; none of
`NameWf`'s cross-block machinery is needed.

**Harder: the struct table is extended.** `genUpptr` emits `genStructs d`
unchanged; this emits `addFields … (addFields … (genStructs d))`, so
`Layout.checkStructs_gen` is only half the struct obligation and
`Layout.checkStructs_addFields` is the other half. What has to be supplied is
that the three link fields do not clash with the element's own — which is
exactly the `clashesGenerated` clause `Dmmeta.check` gained.
-/

set_option maxHeartbeats 1000000

attribute [local irreducible] Dmmeta.mangle

namespace Templates
namespace Llist

open Dmmeta
open CSubset

/-- **Every accepted schema that generates a list generates an accepted
program.** `genLlist` declines when the schema has no `Llist` field, which is
`Layout.layoutCheck`'s business rather than this theorem's. -/
def GenWellFormed : Prop :=
  ∀ (d : Dmmeta.Db) (p : Program), Dmmeta.check d = [] → genLlist d = some p →
    CSubset.Wf.check p = []

/-! ## The nine names

One shared prefix and nine literal suffixes. Every pair cancels the prefix, so
`CSubset.append_ne` does all of it — the reversed-prefix argument `UpptrWf`
needed is for names with *different* prefixes, which cannot arise here. -/

theorem defsFor_names (nm : Names) (elem : CSubset.Ident) :
    (defsFor nm elem).map FunDef.name
      = [nm.init, nm.insert, nm.remove, nm.first, nm.nextFn, nm.prevFn,
         nm.inQ, nm.emptyQ, nm.size] := rfl

/-- **The nine generated names are pairwise distinct.**

checked by: `lake build` -/
theorem names_pairwise (dbC fld : CSubset.Ident) :
    (((defsFor (names dbC fld) "e").map FunDef.name).Pairwise (· ≠ ·)) := by
  rw [defsFor_names]
  simp only [names]
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_,
    List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_,
    List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_,
    List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, by simp⟩⟩⟩⟩⟩⟩⟩⟩ <;>
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact CSubset.append_ne (s := dbC ++ "_" ++ fld) (by decide)

/-! ## The struct table

`genLlist` emits `addFields dbN … (addFields elemN … (genStructs d))`, so the
obligation is `Layout.checkStructs_gen` with two `checkStructs_addFields`
applications on top. Each supplies four facts about the fields *it* adds; the
only interesting one is the first, and it is `Layout.field_ne_generated`. -/

/-- The names the three link fields carry. -/
theorem elemFields_names (nm : Names) (elem : CSubset.Ident) :
    (elemFields nm elem).map Prod.fst = [nm.next, nm.prev, nm.inlist] := rfl

theorem dbFields_names (nm : Names) (elem : CSubset.Ident) :
    (dbFields nm elem).map Prod.fst = [nm.head, nm.count] := rfl

/-- Every added field is a pointer, a `bool` or a `u32`: legal sizes, no
layout dependency, and the only struct mentioned is the element's.

checked by: `lake build` -/
theorem elemFields_ok (nm : Names) (elem : CSubset.Ident) :
    (∀ fv ∈ elemFields nm elem, Wf.Ty.sizesOk fv.2 = true)
    ∧ (∀ fv ∈ elemFields nm elem, Wf.Ty.layoutDeps fv.2 = [])
    ∧ (∀ fv ∈ elemFields nm elem, ∀ m ∈ Wf.Ty.allStructs fv.2, m = elem) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro fv hfv
    simp only [elemFields, List.mem_cons, List.not_mem_nil, or_false] at hfv
    rcases hfv with rfl | rfl | rfl <;>
      first
        | rfl
        | (intro m hm; simp only [Wf.Ty.allStructs, List.mem_singleton] at hm; exact hm)
        | (intro m hm; simp [Wf.Ty.allStructs] at hm)

theorem dbFields_ok (nm : Names) (elem : CSubset.Ident) :
    (∀ fv ∈ dbFields nm elem, Wf.Ty.sizesOk fv.2 = true)
    ∧ (∀ fv ∈ dbFields nm elem, Wf.Ty.layoutDeps fv.2 = [])
    ∧ (∀ fv ∈ dbFields nm elem, ∀ m ∈ Wf.Ty.allStructs fv.2, m = elem) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro fv hfv
    simp only [dbFields, List.mem_cons, List.not_mem_nil, or_false] at hfv
    rcases hfv with rfl | rfl <;>
      first
        | rfl
        | (intro m hm; simp only [Wf.Ty.allStructs, List.mem_singleton] at hm; exact hm)
        | (intro m hm; simp [Wf.Ty.allStructs] at hm)

/-- **The added link names do not collide with the element's own fields.**
The one place `Dmmeta.check`'s `clashesGenerated` clause is spent, via
`Layout.field_ne_generated`: each link is `<field>_<suffix>` for a declared
field, so no declared field can carry that name.

checked by: `lake build` -/
theorem hdist_elem {d : Db} (hchk : check d = []) {dbC : Ctype} {fld : Field}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hfld : fld ∈ dbC.fields)
    (elemN : CSubset.Ident) :
    ∀ sd ∈ genStructs d, sd.name = elemN →
      ((sd.fields.map Prod.fst)
        ++ (elemFields (names (mangle dbC.name) (mangle fld.name)) elemN).map
             Prod.fst).Pairwise (· ≠ ·) := by
  obtain ⟨⟨_, _, hqdup⟩, _, _⟩ := Layout.facts_of_check hchk
  intro sd hsd _
  obtain ⟨c, hc, _, rfl⟩ := Layout.struct_of_mem hsd
  have hgm : mangle fld.name ∈ fieldCNames d.withBuiltins :=
    Layout.mem_fieldCNames hdb hfld
  rw [elemFields_names]
  refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
  · exact Layout.fields_distinct (nf := fun f => mangle f.name) (fun _ _ _ => rfl)
      (Layout.mangled_fields_pairwise_mem hqdup hc)
  · -- the three links differ from each other: same prefix, different suffixes
    simp only [names]
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, by simp⟩⟩ <;>
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;>
        exact CSubset.append_ne (s := mangle fld.name) (by decide)
  · -- ...and from every field the element already has
    intro m hm b hb
    simp only [names, List.mem_cons, List.not_mem_nil, or_false] at hb
    have hmm := Layout.mem_fieldCNames_of_struct hsd hm
    rcases hb with rfl | rfl | rfl <;>
      exact Layout.field_ne_generated hchk hmm hgm (by decide)

/-- **The same for the parent's head and count**, over the *already extended*
table — so in the self-list case the struct already carries the three links
and the head and count must differ from those too. All five share the field's
qualified prefix, so that part is `append_ne`; the element's own fields are
`field_ne_generated` again, with `_head` and `_n` among the reserved
suffixes.

checked by: `lake build` -/
theorem hdist_db {d : Db} (hchk : check d = []) {dbC : Ctype} {fld : Field}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hfld : fld ∈ dbC.fields)
    (elemN : CSubset.Ident) :
    ∀ sd ∈ Layout.addFields elemN
        (elemFields (names (mangle dbC.name) (mangle fld.name)) elemN)
        (genStructs d),
      sd.name = mangle dbC.name →
      ((sd.fields.map Prod.fst)
        ++ (dbFields (names (mangle dbC.name) (mangle fld.name)) elemN).map
             Prod.fst).Pairwise (· ≠ ·) := by
  obtain ⟨⟨_, _, hqdup⟩, _, _⟩ := Layout.facts_of_check hchk
  intro sd hsd _
  obtain ⟨sd0, hsd0, rfl⟩ := Layout.mem_addFields hsd
  have hgm : mangle fld.name ∈ fieldCNames d.withBuiltins :=
    Layout.mem_fieldCNames hdb hfld
  obtain ⟨c, hc, _, rfl⟩ := Layout.struct_of_mem hsd0
  -- the head and count differ from each other, and from every declared field
  have hown : ∀ m ∈ (structOf d.withBuiltins c).fields.map Prod.fst,
      ∀ b ∈ (dbFields (names (mangle dbC.name) (mangle fld.name)) elemN).map Prod.fst,
      m ≠ b := by
    intro m hm b hb
    simp only [dbFields_names, names, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    have hmm := Layout.mem_fieldCNames_of_struct hsd0 hm
    rcases hb with rfl | rfl <;>
      exact Layout.field_ne_generated hchk hmm hgm (by decide)
  have hpair2 : ((dbFields (names (mangle dbC.name) (mangle fld.name)) elemN).map
      Prod.fst).Pairwise (· ≠ ·) := by
    simp only [dbFields_names, names]
    refine List.pairwise_cons.mpr ⟨?_, by simp⟩
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    exact CSubset.append_ne (s := mangle fld.name) (by decide)
  have hown0 : ((structOf d.withBuiltins c).fields.map Prod.fst).Pairwise (· ≠ ·) :=
    Layout.fields_distinct (nf := fun f => mangle f.name) (fun _ _ _ => rfl)
      (Layout.mangled_fields_pairwise_mem hqdup hc)
  -- the three links, and how they sit against the element's own fields
  have hlinks : ((elemFields (names (mangle dbC.name) (mangle fld.name)) elemN).map
      Prod.fst).Pairwise (· ≠ ·) := by
    simp only [elemFields_names, names]
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, by simp⟩⟩ <;>
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;>
        exact CSubset.append_ne (s := mangle fld.name) (by decide)
  have hcrossL : ∀ m ∈ (structOf d.withBuiltins c).fields.map Prod.fst,
      ∀ b ∈ (elemFields (names (mangle dbC.name) (mangle fld.name)) elemN).map Prod.fst,
      m ≠ b := by
    intro m hm b hb
    simp only [elemFields_names, names, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    have hmm := Layout.mem_fieldCNames_of_struct hsd0 hm
    rcases hb with rfl | rfl | rfl <;>
      exact Layout.field_ne_generated hchk hmm hgm (by decide)
  have hLvD : ∀ m ∈ (elemFields (names (mangle dbC.name) (mangle fld.name)) elemN).map
        Prod.fst,
      ∀ b ∈ (dbFields (names (mangle dbC.name) (mangle fld.name)) elemN).map Prod.fst,
      m ≠ b := by
    intro m hm b hb
    simp only [elemFields_names, names, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    simp only [dbFields_names, names, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hm with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;>
      exact CSubset.append_ne (s := mangle fld.name) (by decide)
  by_cases hn : (structOf d.withBuiltins c).name = elemN
  · -- the self-list case: the struct already carries the three links
    rw [if_pos (beq_iff_eq.mpr hn)]
    simp only [List.map_append]
    refine List.pairwise_append.mpr
      ⟨List.pairwise_append.mpr ⟨hown0, hlinks, hcrossL⟩, hpair2, ?_⟩
    intro m hm b hb
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · exact hown m hm b hb
    · exact hLvD m hm b hb
  · rw [if_neg (fun h => hn (eq_of_beq h))]
    exact List.pairwise_append.mpr ⟨hown0, hpair2, hown⟩

end Llist
end Templates

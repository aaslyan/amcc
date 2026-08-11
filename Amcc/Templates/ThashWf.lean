import Amcc.Templates.NameWf
import Amcc.Templates.Thash

/-!
# AMCC — the hash index is well-formed for every accepted schema

`LlistWf` is the model; this is the same argument with five functions instead
of nine and two added fields per struct instead of three. The self-threading
case is **not** hypothetical here either — `Examples.selfDb` indexes its own
ctype, so the field-lookup bundle carries both branches from the start rather
than acquiring the second one after a failed assembly.

Two things are new relative to `Llist`, both in `checkFun`:

- `findDef` and `removeDef` have `forN` bodies, so obligation 8 (the loop
  variable is a `u32` local the body does not assign) has to be discharged;
- `insertDef` **calls** `Find`, so `Wf.Ctx.fun?` has to resolve it out of the
  `earlier` list. `checkFun`'s `earlier` is `p.funs.take i` and `Find` is
  emitted first, so it is in the prefix — but no template had exercised that
  path before.

The bucket count's legality comes from the *generator's* guard rather than
from `Dmmeta.check`: a `Thash` field is not an `Inlary`, so the schema
checker's array-bound clause does not apply to it, and `accepted_bucket_facts`
is what supplies `0 < nb` from `pow2Exp?`.
-/

set_option maxHeartbeats 1000000

attribute [local irreducible] Dmmeta.mangle

namespace Templates
namespace Thash

open Dmmeta
open CSubset

/-- **Every accepted schema that generates a hash index generates an accepted
program.** -/
def GenWellFormed : Prop :=
  ∀ (d : Dmmeta.Db) (p : Program), Dmmeta.check d = [] → genThash d = some p →
    CSubset.Wf.check p = []

/-! ## The five names -/

theorem defsFor_names (nm : Names) (elem key : CSubset.Ident) (mask cap nb : Nat) :
    (defsFor nm elem key mask cap nb).map FunDef.name
      = [nm.init, nm.find, nm.insert, nm.remove, nm.size] := rfl

/-- **The five generated names are pairwise distinct.** One shared prefix and
five literal suffixes, so `CSubset.append_ne` settles all ten pairs.

checked by: `lake build` -/
theorem names_pairwise (dbC fld : CSubset.Ident) (elem key : CSubset.Ident)
    (mask cap nb : Nat) :
    (((defsFor (names dbC fld) elem key mask cap nb).map
      FunDef.name).Pairwise (· ≠ ·)) := by
  rw [defsFor_names]
  simp only [names]
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_,
    List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, by simp⟩⟩⟩⟩ <;>
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;>
      exact CSubset.append_ne (s := dbC ++ "_" ++ fld) (by decide)

/-! ## The added fields -/

theorem elemFields_names (nm : Names) (elem : CSubset.Ident) :
    (elemFields nm elem).map Prod.fst = [nm.next, nm.inhash] := rfl

theorem dbFields_names (nm : Names) (elem : CSubset.Ident) (nb : Nat) :
    (dbFields nm elem nb).map Prod.fst = [nm.buckets, nm.count] := rfl

/-- The element's two links are a pointer and a `bool`. -/
theorem elemFields_ok (nm : Names) (elem : CSubset.Ident) :
    (∀ fv ∈ elemFields nm elem, Wf.Ty.sizesOk fv.2 = true)
    ∧ (∀ fv ∈ elemFields nm elem, Wf.Ty.layoutDeps fv.2 = [])
    ∧ (∀ fv ∈ elemFields nm elem, ∀ m ∈ Wf.Ty.allStructs fv.2, m = elem) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro fv hfv
    simp only [elemFields, List.mem_cons, List.not_mem_nil, or_false] at hfv
    rcases hfv with rfl | rfl <;>
      first
        | rfl
        | (intro m hm; simp only [Wf.Ty.allStructs, List.mem_singleton] at hm; exact hm)
        | (intro m hm; simp [Wf.Ty.allStructs] at hm)

/-- The parent's bucket array and count. The array's legality is the one place
the generator's own power-of-two guard is spent rather than a schema clause —
a `Thash` field is not an `Inlary`, so `Dmmeta.check`'s array-bound rule does
not reach it. -/
theorem dbFields_ok (nm : Names) (elem : CSubset.Ident) {nb : Nat}
    (hpos : 0 < nb) (hlt : nb < Wf.u32Bound) :
    (∀ fv ∈ dbFields nm elem nb, Wf.Ty.sizesOk fv.2 = true)
    ∧ (∀ fv ∈ dbFields nm elem nb, Wf.Ty.layoutDeps fv.2 = [])
    ∧ (∀ fv ∈ dbFields nm elem nb, ∀ m ∈ Wf.Ty.allStructs fv.2, m = elem) := by
  have harr : Wf.Ty.sizesOk (Ty.arr (.ptr (.strct elem)) nb) = true := by
    simp only [Wf.Ty.sizesOk, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hpos, hlt⟩, trivial⟩
  refine ⟨?_, ?_, ?_⟩
  · intro fv hfv
    simp only [dbFields, List.mem_cons, List.not_mem_nil, or_false] at hfv
    rcases hfv with rfl | rfl
    · exact harr
    · rfl
  · intro fv hfv
    simp only [dbFields, List.mem_cons, List.not_mem_nil, or_false] at hfv
    rcases hfv with rfl | rfl <;> rfl
  · intro fv hfv
    simp only [dbFields, List.mem_cons, List.not_mem_nil, or_false] at hfv
    rcases hfv with rfl | rfl
    · intro m hm
      simp only [Wf.Ty.allStructs, List.mem_singleton] at hm
      exact hm
    · intro m hm
      simp [Wf.Ty.allStructs] at hm

/-! ## The extended struct table -/

/-- The doubly-extended table `genThash` emits. -/
def tableOf (d : Db) (dbN elemN : CSubset.Ident) (nm : Names) (nb : Nat) :
    List StructDef :=
  Layout.addFields dbN (dbFields nm elemN nb)
    (Layout.addFields elemN (elemFields nm elemN) (genStructs d))

/-- **The added link names do not collide with the element's own fields.**
`Layout.field_ne_generated` spends `Dmmeta.check`'s `clashesGenerated` clause;
`_next` and `_inhash` are both reserved suffixes. -/
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
  · simp only [names]
    refine List.pairwise_cons.mpr ⟨?_, by simp⟩
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    exact CSubset.append_ne (s := mangle fld.name) (by decide)
  · intro m hm b hb
    simp only [names, List.mem_cons, List.not_mem_nil, or_false] at hb
    have hmm := Layout.mem_fieldCNames_of_struct hsd hm
    rcases hb with rfl | rfl <;>
      exact Layout.field_ne_generated hchk hmm hgm (by decide)

/-- The same for the parent's bucket array and count, over the *already
extended* table — so in the self-indexing case the struct already carries the
two links. -/
theorem hdist_db {d : Db} (hchk : check d = []) {dbC : Ctype} {fld : Field}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hfld : fld ∈ dbC.fields)
    (elemN : CSubset.Ident) (nb : Nat) :
    ∀ sd ∈ Layout.addFields elemN
        (elemFields (names (mangle dbC.name) (mangle fld.name)) elemN)
        (genStructs d),
      sd.name = mangle dbC.name →
      ((sd.fields.map Prod.fst)
        ++ (dbFields (names (mangle dbC.name) (mangle fld.name)) elemN nb).map
             Prod.fst).Pairwise (· ≠ ·) := by
  obtain ⟨⟨_, _, hqdup⟩, _, _⟩ := Layout.facts_of_check hchk
  intro sd hsd _
  obtain ⟨sd0, hsd0, rfl⟩ := Layout.mem_addFields hsd
  have hgm : mangle fld.name ∈ fieldCNames d.withBuiltins :=
    Layout.mem_fieldCNames hdb hfld
  obtain ⟨c, hc, _, rfl⟩ := Layout.struct_of_mem hsd0
  have hown : ∀ m ∈ (structOf d.withBuiltins c).fields.map Prod.fst,
      ∀ b ∈ (dbFields (names (mangle dbC.name) (mangle fld.name)) elemN nb).map
        Prod.fst, m ≠ b := by
    intro m hm b hb
    simp only [dbFields_names, names, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    have hmm := Layout.mem_fieldCNames_of_struct hsd0 hm
    rcases hb with rfl | rfl <;>
      exact Layout.field_ne_generated hchk hmm hgm (by decide)
  have hpair2 : ((dbFields (names (mangle dbC.name) (mangle fld.name)) elemN nb).map
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
  have hlinks : ((elemFields (names (mangle dbC.name) (mangle fld.name)) elemN).map
      Prod.fst).Pairwise (· ≠ ·) := by
    simp only [elemFields_names, names]
    refine List.pairwise_cons.mpr ⟨?_, by simp⟩
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    exact CSubset.append_ne (s := mangle fld.name) (by decide)
  have hcrossL : ∀ m ∈ (structOf d.withBuiltins c).fields.map Prod.fst,
      ∀ b ∈ (elemFields (names (mangle dbC.name) (mangle fld.name)) elemN).map
        Prod.fst, m ≠ b := by
    intro m hm b hb
    simp only [elemFields_names, names, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    have hmm := Layout.mem_fieldCNames_of_struct hsd0 hm
    rcases hb with rfl | rfl <;>
      exact Layout.field_ne_generated hchk hmm hgm (by decide)
  have hLvD : ∀ m ∈ (elemFields (names (mangle dbC.name) (mangle fld.name)) elemN).map
        Prod.fst,
      ∀ b ∈ (dbFields (names (mangle dbC.name) (mangle fld.name)) elemN nb).map
        Prod.fst, m ≠ b := by
    intro m hm b hb
    simp only [elemFields_names, names, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    simp only [dbFields_names, names, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hm with rfl | rfl <;> rcases hb with rfl | rfl <;>
      exact CSubset.append_ne (s := mangle fld.name) (by decide)
  by_cases hn : (structOf d.withBuiltins c).name = elemN
  · rw [if_pos (beq_iff_eq.mpr hn)]
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

/-- **The emitted struct table is well-formed.**

checked by: `lake build` -/
theorem checkStructs_gen_thash {d : Db} (hchk : check d = [])
    {dbC elemC : Ctype} {fld : Field} {nb : Nat}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hfld : fld ∈ dbC.fields)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none)
    (hpos : 0 < nb) (hlt : nb < Wf.u32Bound) :
    Wf.checkStructs
      (tableOf d (mangle dbC.name) (mangle elemC.name)
        (names (mangle dbC.name) (mangle fld.name)) nb) = [] := by
  have hmem := Layout.mem_genStructs_name helem hes
  obtain ⟨se, sl, sa⟩ := elemFields_ok (names (mangle dbC.name) (mangle fld.name))
    (mangle elemC.name)
  obtain ⟨de, dl, da⟩ := dbFields_ok (names (mangle dbC.name) (mangle fld.name))
    (mangle elemC.name) hpos hlt
  refine Layout.checkStructs_addFields
    (Layout.checkStructs_addFields (Layout.checkStructs_gen hchk)
      (hdist_elem hchk hdb hfld _) se ?_ sl)
    (hdist_db hchk hdb hfld _ nb) de ?_ dl
  · intro fv hfv m hm
    rw [sa fv hfv m hm]
    exact hmem
  · intro fv hfv m hm
    rw [Layout.addFields_names, da fv hfv m hm]
    exact hmem

/-- **And the global.**

checked by: `lake build` -/
theorem checkGlobals_gen_thash {d : Db} (hchk : check d = [])
    (n₁ n₂ : CSubset.Ident) (e₁ e₂ : List (CSubset.Ident × Ty)) :
    Wf.checkGlobals
      (Layout.addFields n₂ e₂ (Layout.addFields n₁ e₁ (genStructs d)))
      (genGlobals d) = [] :=
  Layout.checkGlobals_addFields (Layout.checkGlobals_addFields
    (Layout.checkGlobals_gen hchk))

end Thash
end Templates

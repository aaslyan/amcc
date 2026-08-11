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

/-! ## The four field lookups

`next` and `inhash` on the element, `buckets` and `n` on the parent. Both
branches from the start: `Examples.selfDb` indexes its own ctype. -/

/-- **The four lookups when the two ctypes differ.** -/
theorem field_lookups {d : Db} (hchk : check d = []) {dbC elemC : Ctype}
    {fld : Field} {nb : Nat}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hdbs : dbC.scalar = none)
    (hfld : fld ∈ dbC.fields)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none)
    (hne : mangle dbC.name ≠ mangle elemC.name)
    (globals : List GlobalDef) (funs : List FunDef)
    (locals : List (CSubset.Ident × ValTy)) :
    let nm := names (mangle dbC.name) (mangle fld.name)
    let elemN := mangle elemC.name
    let dbN := mangle dbC.name
    let ctx : Wf.Ctx := ⟨tableOf d dbN elemN nm nb, globals, funs, locals⟩
    ctx.field? elemN nm.next = some (.ptr (.strct elemN))
    ∧ ctx.field? elemN nm.inhash = some (.scalar .bool)
    ∧ ctx.field? dbN nm.buckets = some (.arr (.ptr (.strct elemN)) nb)
    ∧ ctx.field? dbN nm.count = some (.scalar .u32) := by
  intro nm elemN dbN ctx
  have hne' : dbN ≠ elemN := hne
  have hen : (structOf d.withBuiltins elemC).name = elemN := Layout.structOf_name _ _
  have hdn : (structOf d.withBuiltins dbC).name = dbN := Layout.structOf_name _ _
  obtain ⟨⟨_, hmdup, _⟩, _, _⟩ := Layout.facts_of_check hchk
  have hsd : ((genStructs d).map StructDef.name).Pairwise (· ≠ ·) :=
    Layout.structs_distinct (nf := fun c => mangle c.name) (fun _ => rfl) hmdup
  have hbase : (genStructs d).find? (fun sd => sd.name == elemN)
      = some (structOf d.withBuiltins elemC) := by
    have h := CSubset.find?_of_mem_pairwise (f := StructDef.name) (genStructs d)
      (structOf d.withBuiltins elemC)
      (List.mem_filterMap.mpr ⟨elemC, helem, by simp [hes]⟩) hsd
    rwa [hen] at h
  have hdbase : (genStructs d).find? (fun sd => sd.name == dbN)
      = some (structOf d.withBuiltins dbC) := by
    have h := CSubset.find?_of_mem_pairwise (f := StructDef.name) (genStructs d)
      (structOf d.withBuiltins dbC)
      (List.mem_filterMap.mpr ⟨dbC, hdb, by simp [hdbs]⟩) hsd
    rwa [hdn] at h
  have hinnerE : (Layout.addFields elemN (elemFields nm elemN) (genStructs d)).find?
      (fun sd => sd.name == elemN)
      = some { structOf d.withBuiltins elemC with
               fields := (structOf d.withBuiltins elemC).fields
                         ++ elemFields nm elemN } := by
    rw [Layout.find?_addFields _ hbase, if_pos (beq_iff_eq.mpr hen)]
  have hinnerD : (Layout.addFields elemN (elemFields nm elemN) (genStructs d)).find?
      (fun sd => sd.name == dbN) = some (structOf d.withBuiltins dbC) := by
    rw [Layout.find?_addFields _ hdbase,
      if_neg (fun e => hne' (hdn ▸ eq_of_beq e))]
  have helemS : (tableOf d dbN elemN nm nb).find? (fun sd => sd.name == elemN)
      = some { structOf d.withBuiltins elemC with
               fields := (structOf d.withBuiltins elemC).fields
                         ++ elemFields nm elemN } := by
    simp only [tableOf]
    rw [Layout.find?_addFields _ hinnerE,
      if_neg (fun e => hne' (hen ▸ (eq_of_beq e).symm))]
  have hdbS : (tableOf d dbN elemN nm nb).find? (fun sd => sd.name == dbN)
      = some { structOf d.withBuiltins dbC with
               fields := (structOf d.withBuiltins dbC).fields
                         ++ dbFields nm elemN nb } := by
    simp only [tableOf]
    rw [Layout.find?_addFields _ hinnerD, if_pos (beq_iff_eq.mpr hdn)]
  have hpe : (((structOf d.withBuiltins elemC).fields
      ++ elemFields nm elemN).map Prod.fst).Pairwise (· ≠ ·) := by
    simpa using hdist_elem hchk hdb hfld elemN (structOf d.withBuiltins elemC)
      (List.mem_filterMap.mpr ⟨elemC, helem, by simp [hes]⟩) hen
  have hpd : (((structOf d.withBuiltins dbC).fields
      ++ dbFields nm elemN nb).map Prod.fst).Pairwise (· ≠ ·) := by
    simpa using hdist_db hchk hdb hfld elemN nb (structOf d.withBuiltins dbC)
      (by
        refine List.mem_map.mpr ⟨structOf d.withBuiltins dbC, ?_, ?_⟩
        · exact List.mem_filterMap.mpr ⟨dbC, hdb, by simp [hdbs]⟩
        · rw [if_neg (fun e => hne' (hdn ▸ eq_of_beq e))])
      hdn
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Wf.Ctx.field?, Wf.Ctx.struct?, ctx, helemS, hdbS]
  · show (do
      let fv ← ((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.next)
      some fv.2) = _
    rw [NameWf.find?_field (p := (nm.next, Ty.ptr (.strct elemN)))
      (by simp [elemFields]) hpe]
    rfl
  · show (do
      let fv ← ((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.inhash)
      some fv.2) = _
    rw [NameWf.find?_field (p := (nm.inhash, Ty.scalar .bool))
      (by simp [elemFields]) hpe]
    rfl
  · show (do
      let fv ← ((structOf d.withBuiltins dbC).fields ++ dbFields nm elemN nb).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.buckets)
      some fv.2) = _
    rw [NameWf.find?_field (p := (nm.buckets, Ty.arr (.ptr (.strct elemN)) nb))
      (by simp [dbFields]) hpd]
    rfl
  · show (do
      let fv ← ((structOf d.withBuiltins dbC).fields ++ dbFields nm elemN nb).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.count)
      some fv.2) = _
    rw [NameWf.find?_field (p := (nm.count, Ty.scalar .u32))
      (by simp [dbFields]) hpd]
    rfl

/-- **The four lookups when the ctype indexes itself.** `Examples.selfDb`. -/
theorem field_lookups_self {d : Db} (hchk : check d = []) {dbC elemC : Ctype}
    {fld : Field} {nb : Nat}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hfld : fld ∈ dbC.fields)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none)
    (hself : mangle dbC.name = mangle elemC.name)
    (globals : List GlobalDef) (funs : List FunDef)
    (locals : List (CSubset.Ident × ValTy)) :
    let nm := names (mangle dbC.name) (mangle fld.name)
    let elemN := mangle elemC.name
    let dbN := mangle dbC.name
    let ctx : Wf.Ctx := ⟨tableOf d dbN elemN nm nb, globals, funs, locals⟩
    ctx.field? elemN nm.next = some (.ptr (.strct elemN))
    ∧ ctx.field? elemN nm.inhash = some (.scalar .bool)
    ∧ ctx.field? dbN nm.buckets = some (.arr (.ptr (.strct elemN)) nb)
    ∧ ctx.field? dbN nm.count = some (.scalar .u32) := by
  intro nm elemN dbN ctx
  have hen : (structOf d.withBuiltins elemC).name = elemN := Layout.structOf_name _ _
  have hne' : dbN = elemN := hself
  obtain ⟨⟨_, hmdup, _⟩, _, _⟩ := Layout.facts_of_check hchk
  have hsd : ((genStructs d).map StructDef.name).Pairwise (· ≠ ·) :=
    Layout.structs_distinct (nf := fun c => mangle c.name) (fun _ => rfl) hmdup
  have hmemE : structOf d.withBuiltins elemC ∈ genStructs d :=
    List.mem_filterMap.mpr ⟨elemC, helem, by simp [hes]⟩
  have hbase : (genStructs d).find? (fun sd => sd.name == elemN)
      = some (structOf d.withBuiltins elemC) := by
    have h := CSubset.find?_of_mem_pairwise (f := StructDef.name) (genStructs d)
      (structOf d.withBuiltins elemC) hmemE hsd
    rwa [hen] at h
  have hinnerE : (Layout.addFields elemN (elemFields nm elemN) (genStructs d)).find?
      (fun sd => sd.name == elemN)
      = some { structOf d.withBuiltins elemC with
               fields := (structOf d.withBuiltins elemC).fields
                         ++ elemFields nm elemN } := by
    rw [Layout.find?_addFields _ hbase, if_pos (beq_iff_eq.mpr hen)]
  have hboth := Layout.find?_addFields (n := dbN) (extra := dbFields nm elemN nb)
    _ hinnerE
  rw [if_pos (beq_iff_eq.mpr (hen.trans hne'.symm))] at hboth
  have hbothD : (Layout.addFields dbN (dbFields nm elemN nb)
      (Layout.addFields elemN (elemFields nm elemN) (genStructs d))).find?
        (fun sd => sd.name == dbN)
      = (Layout.addFields dbN (dbFields nm elemN nb)
      (Layout.addFields elemN (elemFields nm elemN) (genStructs d))).find?
        (fun sd => sd.name == elemN) := by rw [hne']
  have hpw : ((((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN)
      ++ dbFields nm elemN nb).map Prod.fst).Pairwise (· ≠ ·) := by
    simpa using hdist_db hchk hdb hfld elemN nb
      ({ structOf d.withBuiltins elemC with
         fields := (structOf d.withBuiltins elemC).fields ++ elemFields nm elemN })
      (List.mem_map.mpr ⟨structOf d.withBuiltins elemC, hmemE,
        by rw [if_pos (beq_iff_eq.mpr hen)]⟩)
      (hen.trans hne'.symm)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Wf.Ctx.field?, Wf.Ctx.struct?, ctx, tableOf, hbothD, hboth]
  · show (do
      let fv ← (((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN) ++ dbFields nm elemN nb).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.next)
      some fv.2) = _
    rw [NameWf.find?_field (p := (nm.next, Ty.ptr (.strct elemN)))
      (by simp [elemFields]) hpw]
    rfl
  · show (do
      let fv ← (((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN) ++ dbFields nm elemN nb).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.inhash)
      some fv.2) = _
    rw [NameWf.find?_field (p := (nm.inhash, Ty.scalar .bool))
      (by simp [elemFields]) hpw]
    rfl
  · show (do
      let fv ← (((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN) ++ dbFields nm elemN nb).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.buckets)
      some fv.2) = _
    rw [NameWf.find?_field (p := (nm.buckets, Ty.arr (.ptr (.strct elemN)) nb))
      (by simp [dbFields]) hpw]
    rfl
  · show (do
      let fv ← (((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN) ++ dbFields nm elemN nb).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.count)
      some fv.2) = _
    rw [NameWf.find?_field (p := (nm.count, Ty.scalar .u32))
      (by simp [dbFields]) hpw]
    rfl

/-- **The four lookups, either way.** -/
theorem field_lookups_any {d : Db} (hchk : check d = []) {dbC elemC : Ctype}
    {fld : Field} {nb : Nat}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hdbs : dbC.scalar = none)
    (hfld : fld ∈ dbC.fields)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none)
    (globals : List GlobalDef) (funs : List FunDef)
    (locals : List (CSubset.Ident × ValTy)) :
    let nm := names (mangle dbC.name) (mangle fld.name)
    let elemN := mangle elemC.name
    let dbN := mangle dbC.name
    let ctx : Wf.Ctx := ⟨tableOf d dbN elemN nm nb, globals, funs, locals⟩
    ctx.field? elemN nm.next = some (.ptr (.strct elemN))
    ∧ ctx.field? elemN nm.inhash = some (.scalar .bool)
    ∧ ctx.field? dbN nm.buckets = some (.arr (.ptr (.strct elemN)) nb)
    ∧ ctx.field? dbN nm.count = some (.scalar .u32) := by
  by_cases hne : mangle dbC.name = mangle elemC.name
  · exact field_lookups_self hchk hdb hfld helem hes hne globals funs locals
  · exact field_lookups hchk hdb hdbs hfld helem hes hne globals funs locals

/-- The database global resolves. -/
theorem global_lookup {d : Db} {dbC : Ctype} (hroot : d.root = some dbC.name)
    (structs : List StructDef) (funs : List FunDef)
    (locals : List (CSubset.Ident × ValTy)) :
    (Wf.Ctx.mk structs (genGlobals d) funs locals).global?
        ("g_" ++ mangle dbC.name)
      = some { name := "g_" ++ mangle dbC.name,
               ty := .strct (mangle dbC.name) } := by
  simp [Wf.Ctx.global?, genGlobals, hroot]

/-! ## The five bodies

`Init` and `Remove` have `forN` loops over the bucket array and the chain;
`Find` has one too and returns; `InsertMaybe` calls `Find`. The lookups are
bundled once and each body is a `simp only` / `simp` pair over it, as in
`LlistWf`. -/

/-- The bundle, in the `∀`-over-frames form `simp` can instantiate. -/
theorem checkFun_thash {d : Db} (hchk : check d = []) {dbC elemC : Ctype}
    {fld : Field} {nb : Nat}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hdbs : dbC.scalar = none)
    (hfld : fld ∈ dbC.fields) (hroot : d.root = some dbC.name)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none)
    (hnb : nb < Wf.u32Bound) {earlier : List FunDef} :
    let nm := names (mangle dbC.name) (mangle fld.name)
    let elemN := mangle elemC.name
    let dbN := mangle dbC.name
    ∀ fd ∈ [initDef nm elemN nb, sizeDef nm],
      Wf.checkFun (tableOf d dbN elemN nm nb) (genGlobals d) earlier fd = [] := by
  intro nm elemN dbN fd hfd
  obtain ⟨hnext, hinh, hbuck, hcnt⟩ :=
    field_lookups_any (nb := nb) hchk hdb hdbs hfld helem hes
      (genGlobals d) earlier []
  have hg : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) earlier locals).global?
          nm.dbGlobal = some { name := nm.dbGlobal, ty := .strct dbN } :=
    fun locals => global_lookup hroot _ _ locals
  have hfB : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) earlier locals).field?
        dbN nm.buckets = some (.arr (.ptr (.strct elemN)) nb) := fun _ => hbuck
  have hfC : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) earlier locals).field?
        dbN nm.count = some (.scalar .u32) := fun _ => hcnt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfd
  rcases hfd with rfl | rfl
  · simp only [Wf.checkFun, initDef, dbFld, bucket, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, ValTy.toTy, Stmt.block, LocalDef.zeroed]
    simp [hg, hfB, hfC, Wf.isValTy, Wf.distinct, Wf.dups, tmpI, Wf.indexOk,
      Wf.Ctx.local?, Wf.litTy, Wf.Stmt.assigns, hnb, Wf.inferExpr,
      Wf.addrChecks]
  · simp only [Wf.checkFun, sizeDef, dbFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, ValTy.toTy]
    simp [hg, hfC, Wf.isValTy, Wf.distinct, Wf.dups, Wf.Stmt.alwaysReturns]

/-- **`Find` and `Remove`.** Both walk the chain with a `forN` bounded by the
capacity and read `_p-><key>`, so beyond the four field equations they need
the *key* field to resolve on the element struct — which is a lowered field,
not an added one, so `NameWf.struct_field?` supplies it rather than
`find?_field`.

checked by: `lake build` -/
theorem checkFun_walk {d : Db} (hchk : check d = []) {dbC elemC : Ctype}
    {fld key : Field} {nb cap mask : Nat}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hdbs : dbC.scalar = none)
    (hfld : fld ∈ dbC.fields) (hroot : d.root = some dbC.name)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none)
    (hkey : key ∈ elemC.fields)
    (hkty : fieldTy d.withBuiltins elemC.name key = some (.scalar .u32))
    (hcap : cap < Wf.u32Bound) {earlier : List FunDef} :
    let nm := names (mangle dbC.name) (mangle fld.name)
    let elemN := mangle elemC.name
    let dbN := mangle dbC.name
    ∀ fd ∈ [findDef nm elemN (mangle key.name) mask cap,
            removeDef nm elemN (mangle key.name) mask cap],
      Wf.checkFun (tableOf d dbN elemN nm nb) (genGlobals d) earlier fd = [] := by
  intro nm elemN dbN fd hfd
  obtain ⟨hnext, hinh, hbuck, hcnt⟩ :=
    field_lookups_any (nb := nb) hchk hdb hdbs hfld helem hes
      (genGlobals d) earlier []
  obtain ⟨⟨_, _, hqdup⟩, _, _⟩ := Layout.facts_of_check hchk
  -- the key is a *lowered* field of the element struct
  have hkf : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) earlier locals).field?
        elemN (mangle key.name) = some (.scalar .u32) := by
    intro locals
    have hbase : (genStructs d).find? (fun sd => sd.name == elemN)
        = some (structOf d.withBuiltins elemC) := by
      have h := CSubset.find?_of_mem_pairwise (f := StructDef.name) (genStructs d)
        (structOf d.withBuiltins elemC)
        (List.mem_filterMap.mpr ⟨elemC, helem, by simp [hes]⟩)
        (Layout.structs_distinct (nf := fun c => mangle c.name) (fun _ => rfl)
          (Layout.facts_of_check hchk).1.2.1)
      rwa [Layout.structOf_name] at h
    have hlow : (structOf d.withBuiltins elemC).fields.find?
        (fun fv => fv.1 == mangle key.name)
        = some (mangle key.name, Ty.scalar .u32) :=
      NameWf.struct_field? (Layout.mangled_fields_pairwise_mem hqdup helem)
        hkey hkty
    -- whichever branch the table is in, the element struct's own fields are a
    -- *prefix* of its final field list, and the key is among them — so
    -- `List.find?_append` settles it without splitting on the two topologies
    obtain ⟨rest, hres⟩ : ∃ rest,
        (tableOf d dbN elemN nm nb).find? (fun sd => sd.name == elemN)
          = some { structOf d.withBuiltins elemC with
                   fields := (structOf d.withBuiltins elemC).fields ++ rest } := by
      have hen : (structOf d.withBuiltins elemC).name = elemN :=
        Layout.structOf_name _ _
      have hinner : (Layout.addFields elemN (elemFields nm elemN)
          (genStructs d)).find? (fun sd => sd.name == elemN)
          = some { structOf d.withBuiltins elemC with
                   fields := (structOf d.withBuiltins elemC).fields
                             ++ elemFields nm elemN } := by
        rw [Layout.find?_addFields _ hbase, if_pos (beq_iff_eq.mpr hen)]
      by_cases hne : dbN = elemN
      · refine ⟨elemFields nm elemN ++ dbFields nm elemN nb, ?_⟩
        simp only [tableOf, ← List.append_assoc]
        rw [Layout.find?_addFields _ hinner,
          if_pos (beq_iff_eq.mpr (hen.trans hne.symm))]
      · refine ⟨elemFields nm elemN, ?_⟩
        simp only [tableOf]
        rw [Layout.find?_addFields _ hinner,
          if_neg (fun e => hne (hen ▸ (eq_of_beq e).symm))]
    simp only [Wf.Ctx.field?, Wf.Ctx.struct?, tableOf] at hres ⊢
    rw [hres]
    show (do
      let fv ← ((structOf d.withBuiltins elemC).fields ++ rest).find? (fun fv : CSubset.Ident × Ty => fv.1 == mangle key.name)
      some fv.2) = _
    rw [List.find?_append, hlow]
    rfl
  have hg : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) earlier locals).global?
          nm.dbGlobal = some { name := nm.dbGlobal, ty := .strct dbN } :=
    fun locals => global_lookup hroot _ _ locals
  have hfN : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) earlier locals).field?
        elemN nm.next = some (.ptr (.strct elemN)) := fun _ => hnext
  have hfI : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) earlier locals).field?
        elemN nm.inhash = some (.scalar .bool) := fun _ => hinh
  have hfB : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) earlier locals).field?
        dbN nm.buckets = some (.arr (.ptr (.strct elemN)) nb) := fun _ => hbuck
  have hfC : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) earlier locals).field?
        dbN nm.count = some (.scalar .u32) := fun _ => hcnt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfd
  rcases hfd with rfl | rfl
  · simp only [Wf.checkFun, findDef, findLoopBody, dbFld, ptrFld, bucket,
      ptrLocal, Wf.checkStmt, Wf.addrChecks, Wf.inferExpr, Wf.inferLVal,
      ValTy.toTy, Stmt.block, Stmt.when, LocalDef.zeroed]
    simp [hg, hfN, hfB, hkf, Wf.isValTy, Wf.distinct, Wf.dups,
      parKey, tmpB, tmpP, tmpHit, tmpI, Wf.indexOk, Wf.Ctx.local?, Wf.litTy,
      Wf.binTy, Wf.isPtrTy, Wf.isWord, Wf.Stmt.assigns, Wf.Stmt.alwaysReturns,
      hcap, Wf.inferExpr, Wf.addrChecks, ValTy.toTy]
  · simp only [Wf.checkFun, removeDef, dbFld, ptrFld, bucket, ptrLocal,
      Wf.checkStmt, Wf.addrChecks, Wf.inferExpr, Wf.inferLVal, ValTy.toTy,
      Stmt.block, Stmt.when, LocalDef.zeroed]
    simp [hg, hfN, hfI, hfB, hfC, hkf, Wf.isValTy, Wf.distinct, Wf.dups,
      parRow, tmpB, tmpP, tmpPrev, tmpI, Wf.indexOk, Wf.Ctx.local?, Wf.litTy,
      Wf.binTy, Wf.isPtrTy, Wf.isWord, Wf.Stmt.assigns, hcap, Wf.inferExpr,
      Wf.addrChecks, ValTy.toTy]

/-- **`InsertMaybe`.** The one body that *calls* another generated function:
`_p = D_f_Find(row->k)`. Obligation 4 asks that the callee be declared
earlier, so `Wf.Ctx.fun?` has to resolve `Find` out of the `earlier` list —
`checkFun`'s `earlier` is `p.funs.take i`, and `defsFor` emits `Find` second,
so at `InsertMaybe`'s index the prefix contains it. No template had exercised
this path before.

checked by: `lake build` -/
theorem checkFun_insert {d : Db} (hchk : check d = []) {dbC elemC : Ctype}
    {fld key : Field} {nb cap mask : Nat}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hdbs : dbC.scalar = none)
    (hfld : fld ∈ dbC.fields) (hroot : d.root = some dbC.name)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none)
    (hkey : key ∈ elemC.fields)
    (hkty : fieldTy d.withBuiltins elemC.name key = some (.scalar .u32)) :
    let nm := names (mangle dbC.name) (mangle fld.name)
    let elemN := mangle elemC.name
    let dbN := mangle dbC.name
    Wf.checkFun (tableOf d dbN elemN nm nb) (genGlobals d)
      [initDef nm elemN nb, findDef nm elemN (mangle key.name) mask cap]
      (insertDef nm elemN (mangle key.name) mask) = [] := by
  intro nm elemN dbN
  obtain ⟨⟨_, _, hqdup⟩, _, _⟩ := Layout.facts_of_check hchk
  -- `field?`/`global?` ignore the function list, so these are stated over an
  -- arbitrary `funs`: the closing `simp` unfolds `findDef` inside the context,
  -- and a lookup pinned to the folded list would stop matching at that point.
  have hkf : ∀ (funs : List FunDef) (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) funs
        locals).field? elemN (mangle key.name) = some (.scalar .u32) := by
    intro funs locals
    have hbase : (genStructs d).find? (fun sd => sd.name == elemN)
        = some (structOf d.withBuiltins elemC) := by
      have h := CSubset.find?_of_mem_pairwise (f := StructDef.name) (genStructs d)
        (structOf d.withBuiltins elemC)
        (List.mem_filterMap.mpr ⟨elemC, helem, by simp [hes]⟩)
        (Layout.structs_distinct (nf := fun c => mangle c.name) (fun _ => rfl)
          (Layout.facts_of_check hchk).1.2.1)
      rwa [Layout.structOf_name] at h
    have hlow : (structOf d.withBuiltins elemC).fields.find?
        (fun fv => fv.1 == mangle key.name)
        = some (mangle key.name, Ty.scalar .u32) :=
      NameWf.struct_field? (Layout.mangled_fields_pairwise_mem hqdup helem)
        hkey hkty
    obtain ⟨rest, hres⟩ : ∃ rest,
        (tableOf d dbN elemN nm nb).find? (fun sd => sd.name == elemN)
          = some { structOf d.withBuiltins elemC with
                   fields := (structOf d.withBuiltins elemC).fields ++ rest } := by
      have hen : (structOf d.withBuiltins elemC).name = elemN :=
        Layout.structOf_name _ _
      have hinner : (Layout.addFields elemN (elemFields nm elemN)
          (genStructs d)).find? (fun sd => sd.name == elemN)
          = some { structOf d.withBuiltins elemC with
                   fields := (structOf d.withBuiltins elemC).fields
                             ++ elemFields nm elemN } := by
        rw [Layout.find?_addFields _ hbase, if_pos (beq_iff_eq.mpr hen)]
      by_cases hne : dbN = elemN
      · refine ⟨elemFields nm elemN ++ dbFields nm elemN nb, ?_⟩
        simp only [tableOf, ← List.append_assoc]
        rw [Layout.find?_addFields _ hinner,
          if_pos (beq_iff_eq.mpr (hen.trans hne.symm))]
      · refine ⟨elemFields nm elemN, ?_⟩
        simp only [tableOf]
        rw [Layout.find?_addFields _ hinner,
          if_neg (fun e => hne (hen ▸ (eq_of_beq e).symm))]
    simp only [Wf.Ctx.field?, Wf.Ctx.struct?, tableOf] at hres ⊢
    rw [hres]
    show (do
      let fv ← ((structOf d.withBuiltins elemC).fields ++ rest).find? (fun fv : CSubset.Ident × Ty => fv.1 == mangle key.name)
      some fv.2) = _
    rw [List.find?_append, hlow]
    rfl
  have hg : ∀ (funs : List FunDef) (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) funs
        locals).global? nm.dbGlobal
        = some { name := nm.dbGlobal, ty := .strct dbN } :=
    fun funs locals => global_lookup hroot _ _ locals
  have hfN : ∀ (funs : List FunDef) (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) funs
        locals).field? elemN nm.next = some (.ptr (.strct elemN)) :=
    fun funs locals => (field_lookups_any (nb := nb) hchk hdb hdbs hfld helem hes
      (genGlobals d) funs locals).1
  have hfI : ∀ (funs : List FunDef) (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) funs
        locals).field? elemN nm.inhash = some (.scalar .bool) :=
    fun funs locals => (field_lookups_any (nb := nb) hchk hdb hdbs hfld helem hes
      (genGlobals d) funs locals).2.1
  have hfB : ∀ (funs : List FunDef) (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) funs
        locals).field? dbN nm.buckets = some (.arr (.ptr (.strct elemN)) nb) :=
    fun funs locals => (field_lookups_any (nb := nb) hchk hdb hdbs hfld helem hes
      (genGlobals d) funs locals).2.2.1
  have hfC : ∀ (funs : List FunDef) (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d) funs
        locals).field? dbN nm.count = some (.scalar .u32) :=
    fun funs locals => (field_lookups_any (nb := nb) hchk hdb hdbs hfld helem hes
      (genGlobals d) funs locals).2.2.2
  -- obligation 4: `Find` is in the prefix, and `Init` does not shadow it
  have hfun : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm nb) (genGlobals d)
        [initDef nm elemN nb, findDef nm elemN (mangle key.name) mask cap]
        locals).fun? nm.find
        = some (findDef nm elemN (mangle key.name) mask cap) := by
    intro locals
    have hne : ((initDef nm elemN nb).name == nm.find) = false :=
      beq_eq_false_iff_ne.mpr (by
        show nm.init ≠ nm.find
        simp only [nm, names]
        exact CSubset.append_ne
          (s := mangle dbC.name ++ "_" ++ mangle fld.name) (by decide))
    have heq : ((findDef nm elemN (mangle key.name) mask cap).name == nm.find)
        = true := by simp [findDef]
    simp only [Wf.Ctx.fun?, List.find?, hne, heq]
  simp only [Wf.checkFun, insertDef, dbFld, ptrFld, bucket, ptrLocal,
    Wf.checkStmt, Wf.addrChecks, Wf.inferExpr, Wf.inferLVal, ValTy.toTy,
    Stmt.block, Stmt.when, LocalDef.zeroed]
  -- `findDef` stays folded here: unfolding it first would stop `hfun` and the
  -- field lookups from matching the context syntactically.
  simp [hg, hfN, hfI, hfB, hfC, hkf, hfun, Wf.isValTy, Wf.distinct, Wf.dups,
    parRow, tmpB, tmpP, Wf.Ctx.local?, Wf.litTy, Wf.binTy, Wf.isPtrTy,
    Wf.isWord, Wf.unTy, Wf.Stmt.alwaysReturns, Wf.inferExpr, Wf.addrChecks,
    ValTy.toTy]
  simp [findDef, parKey, tmpB, tmpP, tmpHit, tmpI, hkf, Wf.Ctx.local?,
    Wf.inferExpr, Wf.inferLVal, Wf.indexOk, Wf.isValTy]

/-! ## What the generator's own guard buys

A `Thash` field is **not** an `Inlary`, so `Dmmeta.check`'s array-bound clause
never reaches its bucket count: nothing in the schema checker says the count is
positive or fits a `u32`. `genThash` guards it itself, with `pow2Exp?`, and
this is where that guard is cashed in. -/

/-- **An accepted bucket count is positive and fits a `u32`.** `pow2Exp?` only
succeeds at `nb = 2 ^ e` with `e ≤ 31`, which bounds `nb` by `2 ^ 31`. The
companion `Thash.accepted_bucket_facts` draws the *masking* consequences out of
the same guard; this one draws the two the well-formedness checker asks for.

checked by: `lake build` -/
theorem accepted_bucket_fits {nb : Nat} (h : (pow2Exp? pow2Fuel nb).isSome) :
    0 < nb ∧ nb < Wf.u32Bound := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
  have hn : nb = 2 ^ e := pow2_of_exp? _ _ _ he
  have hle : e ≤ pow2Fuel := exp?_le _ _ _ he
  subst hn
  refine ⟨Nat.two_pow_pos e, ?_⟩
  calc 2 ^ e ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hle
    _ < Wf.u32Bound := by decide

/-! ## The assembly -/

/-- **Every accepted schema that generates a hash index generates an accepted
program.**

The unwinding is `Llist.genWellFormed`'s, with two extra kinds of step:
`genThash` also picks the element's `Pkey` field and `guard`s both its type and
the bucket count. `guard` is `if p then pure () else failure`, so each one is
discharged by `by_cases` on its condition and reducing the `else` branch to
`none = some _`.

checked by: `lake build` -/
theorem genWellFormed : GenWellFormed := by
  intro d p hchk hgen
  simp only [genThash, bind, Option.bind_eq_some_iff] at hgen
  obtain ⟨dbName, hr, dbC, hdbf, fld, hfldf, elemC, helemf, key, hkeyf,
    _u₁, hgk, nb, hnbf, _u₂, hgp, cap, hcapf, hgen⟩ := hgen
  -- the two guards
  have hkarg : key.arg = "u32" := by
    by_cases hb : (key.arg == "u32") = true
    · exact eq_of_beq hb
    · simp [guard, hb] at hgk
  have hp2 : (pow2Exp? pow2Fuel nb).isSome = true := by
    by_cases hb : (pow2Exp? pow2Fuel nb).isSome = true
    · exact hb
    · simp [guard, hb] at hgp
  obtain ⟨hpos, hlt⟩ := accepted_bucket_fits hp2
  -- the capacity is the bucket count; both come from the same lookup
  have hcn : cap = nb := Option.some.inj (hcapf.symm.trans hnbf)
  rw [hcn] at hgen
  -- the facts every lemma above takes
  have hdb : dbC ∈ d.withBuiltins.ctypes :=
    List.mem_of_find?_eq_some (by simpa [Db.find?] using hdbf)
  have helem : elemC ∈ d.withBuiltins.ctypes :=
    List.mem_of_find?_eq_some (by simpa [Db.find?] using helemf)
  have hfld : fld ∈ dbC.fields := List.mem_of_find?_eq_some hfldf
  have hkey : key ∈ elemC.fields :=
    List.mem_of_find?_eq_some (by simpa [keyField?] using hkeyf)
  have hdbn : dbC.name = dbName := Db.find?_name hdbf
  have hrootC : d.root = some dbC.name := by rw [hdbn]; exact hr
  obtain ⟨_, hrt, hcty⟩ := Layout.facts_of_check hchk
  obtain ⟨rc, hrc, hrcs⟩ := hrt dbC.name hrootC
  have hdbs : dbC.scalar = none := by
    have heq : rc = dbC :=
      Option.some.inj (hrc.symm.trans (by rw [hdbn]; exact hdbf))
    rw [← heq]; exact hrcs
  have hfr : fld.reftype = Reftype.Thash := by
    have h := List.find?_some hfldf
    simpa using h
  have hes : elemC.scalar = none := by
    obtain ⟨i, hi, hci⟩ : ∃ i, ∃ hi : i < d.withBuiltins.ctypes.length,
        (d.withBuiltins.ctypes[i]'hi) = dbC := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp hdb
      exact ⟨i, hi.1, hi.2⟩
    obtain ⟨_, _, hff⟩ := hcty i hi
    rw [hci] at hff
    obtain ⟨_, _, _, hrec⟩ := hff fld hfld
    obtain ⟨ac, hac, hacs⟩ := hrec (by rw [hfr]; rfl)
    have heq : ac = elemC := Option.some.inj (hac.symm.trans helemf)
    rw [← heq]; exact hacs
  -- the key is a `Pkey` at `u32`, so it lowers to a `u32` field
  have hkrt : key.reftype = Reftype.Pkey := by
    have h := List.find?_some (by simpa [keyField?] using hkeyf)
    simpa using h
  have hkty : fieldTy d.withBuiltins elemC.name key = some (.scalar .u32) := by
    have hu32 : d.withBuiltins.find? "u32"
        = some { name := "u32", scalar := some .u32 } := by
      simp [Db.find?, Db.withBuiltins, builtins]
    simp [fieldTy, hkarg, hu32, hkrt]
  -- and the four obligations
  rw [← Option.some.inj hgen]
  simp only [Wf.check, List.append_eq_nil_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact checkStructs_gen_thash hchk hdb hfld helem hes hpos hlt
  · exact checkGlobals_gen_thash hchk _ _ _ _
  · exact CSubset.distinct_eq_nil (names_pairwise _ _ _ _ _ _ _)
  · rw [List.flatMap_eq_nil_iff]
    rintro ⟨fd, i⟩ hfdi
    rw [List.mem_zipIdx_iff_getElem?] at hfdi
    -- `InsertMaybe` needs its *own* index: the prefix at that point is exactly
    -- `[Init, Find]`, which is what makes its call resolve. So the five cases
    -- are taken by position rather than by membership.
    rcases i with _ | _ | _ | _ | _ | i
    · have h : initDef (names (mangle dbC.name) (mangle fld.name))
          (mangle elemC.name) nb = fd := by simpa [defsFor] using hfdi
      subst h
      exact checkFun_thash (nb := nb) hchk hdb hdbs hfld hrootC helem hes hlt
        _ (by simp)
    · have h : findDef (names (mangle dbC.name) (mangle fld.name))
          (mangle elemC.name) (mangle key.name) (nb - 1) nb = fd := by
        simpa [defsFor] using hfdi
      subst h
      exact checkFun_walk (mask := nb - 1) (cap := nb) hchk hdb hdbs hfld
        hrootC helem hes hkey hkty hlt _ (by simp)
    · have h : insertDef (names (mangle dbC.name) (mangle fld.name))
          (mangle elemC.name) (mangle key.name) (nb - 1) = fd := by
        simpa [defsFor] using hfdi
      subst h
      exact checkFun_insert hchk hdb hdbs hfld hrootC helem hes hkey hkty
    · have h : removeDef (names (mangle dbC.name) (mangle fld.name))
          (mangle elemC.name) (mangle key.name) (nb - 1) nb = fd := by
        simpa [defsFor] using hfdi
      subst h
      exact checkFun_walk (mask := nb - 1) (cap := nb) hchk hdb hdbs hfld
        hrootC helem hes hkey hkty hlt _ (by simp)
    · have h : sizeDef (names (mangle dbC.name) (mangle fld.name)) = fd := by
        simpa [defsFor] using hfdi
      subst h
      exact checkFun_thash (nb := nb) hchk hdb hdbs hfld hrootC helem hes hlt
        _ (by simp)
    · simp [defsFor] at hfdi

/-! ## The schema-level entry point

As in `LlistWf`: schema acceptance is the only hypothesis a consumer needs, and
all five resolutions come out together instead of being recomputed per schema.
`ThashFind`'s laws additionally need the bucket facts, so those come out here
too — `pow2Exp?` is the generator's guard, not the schema checker's, and this
is the one place both are available at once. -/

/-- **Schema acceptance is enough to apply every law.**

checked by: `lake build` -/
theorem laws_apply {d : Db} {p : Program} (hchk : check d = [])
    (hgen : genThash d = some p) :
    ∃ (nm : Names) (elem key : CSubset.Ident) (nb : Nat),
      p.funs = defsFor nm elem key (nb - 1) nb nb
      ∧ 0 < nb
      ∧ nb < Wf.u32Bound
      ∧ (∀ k : UInt32, (k &&& UInt32.ofNat (nb - 1)).toNat = k.toNat % nb
          ∧ (k &&& UInt32.ofNat (nb - 1)).toNat < nb)
      ∧ (∃ n, p.funs.length = n + 1)
      ∧ lookupFun p nm.init   = .ok (initDef nm elem nb)
      ∧ lookupFun p nm.find   = .ok (findDef nm elem key (nb - 1) nb)
      ∧ lookupFun p nm.insert = .ok (insertDef nm elem key (nb - 1))
      ∧ lookupFun p nm.remove = .ok (removeDef nm elem key (nb - 1) nb)
      ∧ lookupFun p nm.size   = .ok (sizeDef nm) := by
  have hwf : Wf.check p = [] := genWellFormed d p hchk hgen
  simp only [genThash, bind, Option.bind_eq_some_iff] at hgen
  obtain ⟨_, _, dbC, _, fld, _, elemC, _, key, _,
    _u₁, _, nb, hnbf, _u₂, hgp, cap, hcapf, hgen⟩ := hgen
  have hp2 : (pow2Exp? pow2Fuel nb).isSome = true := by
    by_cases hb : (pow2Exp? pow2Fuel nb).isSome = true
    · exact hb
    · simp [guard, hb] at hgp
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hp2
  obtain ⟨hpos, hlt⟩ := accepted_bucket_fits hp2
  have hcn : cap = nb := Option.some.inj (hcapf.symm.trans hnbf)
  rw [hcn] at hgen
  refine ⟨names (mangle dbC.name) (mangle fld.name), mangle elemC.name,
    mangle key.name, nb, ?_⟩
  have hfuns : p.funs = defsFor (names (mangle dbC.name) (mangle fld.name))
      (mangle elemC.name) (mangle key.name) (nb - 1) nb nb := by
    rw [← Option.some.inj hgen]
  have hres : ∀ fd ∈ defsFor (names (mangle dbC.name) (mangle fld.name))
      (mangle elemC.name) (mangle key.name) (nb - 1) nb nb,
      lookupFun p fd.name = .ok fd :=
    fun _ hmem => CSubset.lookupFun_of_wf hwf (by rw [hfuns]; exact hmem)
  refine ⟨hfuns, hpos, hlt, (accepted_bucket_facts he).2,
    CSubset.funs_length_pos
      (fd := initDef (names (mangle dbC.name) (mangle fld.name))
        (mangle elemC.name) nb)
      (by rw [hfuns]; simp [defsFor]), ?_⟩
  refine ⟨
    hres (initDef (names (mangle dbC.name) (mangle fld.name))
      (mangle elemC.name) nb) ?_,
    hres (findDef (names (mangle dbC.name) (mangle fld.name))
      (mangle elemC.name) (mangle key.name) (nb - 1) nb) ?_,
    hres (insertDef (names (mangle dbC.name) (mangle fld.name))
      (mangle elemC.name) (mangle key.name) (nb - 1)) ?_,
    hres (removeDef (names (mangle dbC.name) (mangle fld.name))
      (mangle elemC.name) (mangle key.name) (nb - 1) nb) ?_,
    hres (sizeDef (names (mangle dbC.name) (mangle fld.name))) ?_⟩ <;>
    simp [defsFor]

end Thash
end Templates

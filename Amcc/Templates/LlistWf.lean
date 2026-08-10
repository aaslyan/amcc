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

/-! ## The struct and global halves, assembled -/

/-- **The emitted struct table is well-formed.** Two
`Layout.checkStructs_addFields` applications over `Layout.checkStructs_gen`.

checked by: `lake build` -/
theorem checkStructs_gen_llist {d : Db} (hchk : check d = [])
    {dbC elemC : Ctype} {fld : Field}
    (hdb : dbC ∈ d.withBuiltins.ctypes) (hfld : fld ∈ dbC.fields)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none) :
    Wf.checkStructs
      (Layout.addFields (mangle dbC.name)
        (dbFields (names (mangle dbC.name) (mangle fld.name)) (mangle elemC.name))
        (Layout.addFields (mangle elemC.name)
          (elemFields (names (mangle dbC.name) (mangle fld.name))
            (mangle elemC.name))
          (genStructs d))) = [] := by
  have hmem := Layout.mem_genStructs_name helem hes
  obtain ⟨se, sl, sa⟩ := elemFields_ok (names (mangle dbC.name) (mangle fld.name))
    (mangle elemC.name)
  obtain ⟨de, dl, da⟩ := dbFields_ok (names (mangle dbC.name) (mangle fld.name))
    (mangle elemC.name)
  refine Layout.checkStructs_addFields
    (Layout.checkStructs_addFields (Layout.checkStructs_gen hchk)
      (hdist_elem hchk hdb hfld _) se ?_ sl)
    (hdist_db hchk hdb hfld _) de ?_ dl
  · intro fv hfv m hm
    rw [sa fv hfv m hm]
    exact hmem
  · intro fv hfv m hm
    rw [Layout.addFields_names, da fv hfv m hm]
    exact hmem

/-- **And the global.** `checkGlobals` reads only struct names, and extending
preserves them.

checked by: `lake build` -/
theorem checkGlobals_gen_llist {d : Db} (hchk : check d = [])
    (n₁ n₂ : CSubset.Ident) (e₁ e₂ : List (CSubset.Ident × Ty)) :
    Wf.checkGlobals
      (Layout.addFields n₂ e₂ (Layout.addFields n₁ e₁ (genStructs d)))
      (genGlobals d) = [] :=
  Layout.checkGlobals_addFields (Layout.checkGlobals_addFields
    (Layout.checkGlobals_gen hchk))

/-! ## The five field lookups

Every one of the nine bodies touches only the fields the template *added* and
the database global — never the element's lowered fields — so the whole
`checkFun` obligation depends on the schema through these five equations. They
are proved once against a **symbolic** `Wf.Ctx`, and each body consumes the
bundle and nothing else varies.

Two things about the shape, both of which cost an attempt. `Layout.find?_addFields`
peels the **outer** extension, so the inner one has to be resolved first; and
after `Wf.Ctx.field?` unfolds, the outer `Option` bind over `some {…}` will not
reduce by `simp` — the peeled form has to be written out with `show`. -/

/-- The doubly-extended table `genLlist` emits. -/
def tableOf (d : Db) (dbN elemN : CSubset.Ident) (nm : Names) : List StructDef :=
  Layout.addFields dbN (dbFields nm elemN)
    (Layout.addFields elemN (elemFields nm elemN) (genStructs d))

/-- **The element's three links and the parent's head and count resolve.**

checked by: `lake build` -/
theorem field_lookups {d : Db} (hchk : check d = []) {dbC elemC : Ctype}
    {fld : Field} (hdb : dbC ∈ d.withBuiltins.ctypes) (hdbs : dbC.scalar = none)
    (hfld : fld ∈ dbC.fields)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none)
    (hne : mangle dbC.name ≠ mangle elemC.name)
    (globals : List GlobalDef) (funs : List FunDef)
    (locals : List (CSubset.Ident × ValTy)) :
    let nm := names (mangle dbC.name) (mangle fld.name)
    let elemN := mangle elemC.name
    let dbN := mangle dbC.name
    let ctx : Wf.Ctx := ⟨tableOf d dbN elemN nm, globals, funs, locals⟩
    ctx.field? elemN nm.next = some (.ptr (.strct elemN))
    ∧ ctx.field? elemN nm.prev = some (.ptr (.strct elemN))
    ∧ ctx.field? elemN nm.inlist = some (.scalar .bool)
    ∧ ctx.field? dbN nm.head = some (.ptr (.strct elemN))
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
  -- inner extension: the element gains its links, the parent is untouched
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
  -- outer extension: the parent gains head and count, the element is untouched
  have helemS : (tableOf d dbN elemN nm).find? (fun sd => sd.name == elemN)
      = some { structOf d.withBuiltins elemC with
               fields := (structOf d.withBuiltins elemC).fields
                         ++ elemFields nm elemN } := by
    simp only [tableOf]
    rw [Layout.find?_addFields _ hinnerE,
      if_neg (fun e => hne' (hen ▸ (eq_of_beq e).symm))]
  have hdbS : (tableOf d dbN elemN nm).find? (fun sd => sd.name == dbN)
      = some { structOf d.withBuiltins dbC with
               fields := (structOf d.withBuiltins dbC).fields
                         ++ dbFields nm elemN } := by
    simp only [tableOf]
    rw [Layout.find?_addFields _ hinnerD, if_pos (beq_iff_eq.mpr hdn)]
  -- the two `hdist` lemmas, in the `Pairwise` form `find?_field` wants
  have hpe : (((structOf d.withBuiltins elemC).fields
      ++ elemFields nm elemN).map Prod.fst).Pairwise (· ≠ ·) := by
    simpa using hdist_elem hchk hdb hfld elemN (structOf d.withBuiltins elemC)
      (List.mem_filterMap.mpr ⟨elemC, helem, by simp [hes]⟩) hen
  have hpd : (((structOf d.withBuiltins dbC).fields
      ++ dbFields nm elemN).map Prod.fst).Pairwise (· ≠ ·) := by
    simpa using hdist_db hchk hdb hfld elemN (structOf d.withBuiltins dbC)
      (by
        refine List.mem_map.mpr ⟨structOf d.withBuiltins dbC, ?_, ?_⟩
        · exact List.mem_filterMap.mpr ⟨dbC, hdb, by simp [hdbs]⟩
        · rw [if_neg (fun e => hne' (hdn ▸ eq_of_beq e))])
      hdn
  -- and the five field lookups within the extended structs
  have hnext : ((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN).find?
      (fun fv : CSubset.Ident × Ty => fv.1 == nm.next) = some (nm.next, Ty.ptr (.strct elemN)) :=
    NameWf.find?_field (p := (nm.next, Ty.ptr (.strct elemN)))
      (by simp [elemFields]) hpe
  have hprev : ((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN).find?
      (fun fv : CSubset.Ident × Ty => fv.1 == nm.prev) = some (nm.prev, Ty.ptr (.strct elemN)) :=
    NameWf.find?_field (p := (nm.prev, Ty.ptr (.strct elemN)))
      (by simp [elemFields]) hpe
  have hinl : ((structOf d.withBuiltins elemC).fields ++ elemFields nm elemN).find?
      (fun fv : CSubset.Ident × Ty => fv.1 == nm.inlist) = some (nm.inlist, Ty.scalar .bool) :=
    NameWf.find?_field (p := (nm.inlist, Ty.scalar .bool))
      (by simp [elemFields]) hpe
  have hhead : ((structOf d.withBuiltins dbC).fields ++ dbFields nm elemN).find?
      (fun fv : CSubset.Ident × Ty => fv.1 == nm.head) = some (nm.head, Ty.ptr (.strct elemN)) :=
    NameWf.find?_field (p := (nm.head, Ty.ptr (.strct elemN)))
      (by simp [dbFields]) hpd
  have hcnt : ((structOf d.withBuiltins dbC).fields ++ dbFields nm elemN).find?
      (fun fv : CSubset.Ident × Ty => fv.1 == nm.count) = some (nm.count, Ty.scalar .u32) :=
    NameWf.find?_field (p := (nm.count, Ty.scalar .u32))
      (by simp [dbFields]) hpd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Wf.Ctx.field?, Wf.Ctx.struct?, ctx, helemS, hdbS]
  · show (do
      let fv ← ((structOf d.withBuiltins elemC).fields
        ++ elemFields nm elemN).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.next)
      some fv.2) = _
    rw [hnext]
    rfl
  · show (do
      let fv ← ((structOf d.withBuiltins elemC).fields
        ++ elemFields nm elemN).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.prev)
      some fv.2) = _
    rw [hprev]
    rfl
  · show (do
      let fv ← ((structOf d.withBuiltins elemC).fields
        ++ elemFields nm elemN).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.inlist)
      some fv.2) = _
    rw [hinl]
    rfl
  · show (do
      let fv ← ((structOf d.withBuiltins dbC).fields
        ++ dbFields nm elemN).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.head)
      some fv.2) = _
    rw [hhead]
    rfl
  · show (do
      let fv ← ((structOf d.withBuiltins dbC).fields
        ++ dbFields nm elemN).find? (fun fv : CSubset.Ident × Ty => fv.1 == nm.count)
      some fv.2) = _
    rw [hcnt]
    rfl

/-- The database global resolves. `genLlist` names it `g_<db>`, which is what
`Dmmeta.genGlobals` emits for the root. -/
theorem global_lookup {d : Db} {dbC : Ctype} (hroot : d.root = some dbC.name)
    (structs : List StructDef) (funs : List FunDef)
    (locals : List (CSubset.Ident × ValTy)) :
    (Wf.Ctx.mk structs (genGlobals d) funs locals).global?
        ("g_" ++ mangle dbC.name)
      = some { name := "g_" ++ mangle dbC.name,
               ty := .strct (mangle dbC.name) } := by
  simp [Wf.Ctx.global?, genGlobals, hroot]

/-! ## The seven one-statement bodies

`Init`, `First`, `Next`, `Prev`, `InLlistQ`, `EmptyQ` and `N` are a statement
each over one of the five added fields, so they follow `UpptrWf`'s
`checkFun_defsFor` verbatim once the bundle is in hand. `Insert` and `Remove`
are the work and are separate. -/

theorem checkFun_simple {d : Db} (hchk : check d = []) {dbC elemC : Ctype}
    {fld : Field} (hdb : dbC ∈ d.withBuiltins.ctypes) (hdbs : dbC.scalar = none)
    (hfld : fld ∈ dbC.fields) (hroot : d.root = some dbC.name)
    (helem : elemC ∈ d.withBuiltins.ctypes) (hes : elemC.scalar = none)
    (hne : mangle dbC.name ≠ mangle elemC.name) {earlier : List FunDef} :
    let nm := names (mangle dbC.name) (mangle fld.name)
    let elemN := mangle elemC.name
    let dbN := mangle dbC.name
    ∀ fd ∈ [initDef nm elemN, firstDef nm elemN, nextDef nm elemN,
            prevDef nm elemN, inQDef nm elemN, emptyQDef nm elemN, sizeDef nm],
      Wf.checkFun (tableOf d dbN elemN nm) (genGlobals d) earlier fd = [] := by
  intro nm elemN dbN fd hfd
  obtain ⟨hnext, hprev, hinl, hhead, hcnt⟩ :=
    field_lookups hchk hdb hdbs hfld helem hes hne (genGlobals d) earlier []
  -- `Ctx.field?` and `Ctx.global?` do not read `locals`, so each equation
  -- holds for every frame; stated with the `∀` so `simp` can instantiate it
  have hg : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm) (genGlobals d) earlier locals).global?
          nm.dbGlobal = some { name := nm.dbGlobal, ty := .strct dbN } :=
    fun locals => global_lookup hroot _ _ locals
  have hfN : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm) (genGlobals d) earlier locals).field?
        elemN nm.next = some (.ptr (.strct elemN)) := fun _ => hnext
  have hfP : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm) (genGlobals d) earlier locals).field?
        elemN nm.prev = some (.ptr (.strct elemN)) := fun _ => hprev
  have hfI : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm) (genGlobals d) earlier locals).field?
        elemN nm.inlist = some (.scalar .bool) := fun _ => hinl
  have hfH : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm) (genGlobals d) earlier locals).field?
        dbN nm.head = some (.ptr (.strct elemN)) := fun _ => hhead
  have hfC : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (tableOf d dbN elemN nm) (genGlobals d) earlier locals).field?
        dbN nm.count = some (.scalar .u32) := fun _ => hcnt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfd
  rcases hfd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Wf.checkFun, initDef, dbFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy, Stmt.block]
    simp [hg, hfH, hfC, Wf.isValTy, Wf.distinct, Wf.dups,
      Wf.litTy]
  · simp only [Wf.checkFun, firstDef, dbFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hg, hfH, Wf.isValTy, Wf.distinct, Wf.dups,
      Wf.Stmt.alwaysReturns]
  · simp only [Wf.checkFun, nextDef, ptrFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hfN, Wf.isValTy, Wf.distinct, Wf.dups, parRow,
      Wf.Stmt.alwaysReturns]
  · simp only [Wf.checkFun, prevDef, ptrFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hfP, Wf.isValTy, Wf.distinct, Wf.dups, parRow,
      Wf.Stmt.alwaysReturns]
  · simp only [Wf.checkFun, inQDef, ptrFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hfI, Wf.isValTy, Wf.distinct, Wf.dups, parRow,
      Wf.Stmt.alwaysReturns]
  · simp only [Wf.checkFun, emptyQDef, dbFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hg, hfH, Wf.isValTy, Wf.distinct, Wf.dups, Wf.binTy,
      Wf.isPtrTy, Wf.Stmt.alwaysReturns]
  · simp only [Wf.checkFun, sizeDef, dbFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hg, hfC, Wf.isValTy, Wf.distinct, Wf.dups,
      Wf.Stmt.alwaysReturns]

end Llist
end Templates

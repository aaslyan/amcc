import Amcc.Templates.NameWf
import Amcc.Templates.Upptr

/-!
# AMCC — the up-pointer template is well-formed for every accepted schema

`Templates/Upptr.lean` had `Wf.check … = []` only as a computation on one
sample schema. This closes the gap: **every** schema `Dmmeta.check` accepts
generates a program `CSubset.Wf.check` accepts.

That matters beyond tidiness. `scripts/gen/upptr_gen.h` tells a reader that
what each function is guaranteed to do is machine-checked *for every accepted
schema*, and until this theorem existed that sentence was true of the array
table and overstated for this one. The banner is right; the proofs were behind
it.

## The shape

Three parts, and only the third is specific to up-pointers:

- the struct table and the global, from `Layout.checkStructs_gen` and
  `Layout.checkGlobals_gen`;
- function-name distinctness, from `NameWf` — a `flatMap` of four-name blocks
  over the `Upptr` fields, with the qualified prefixes distinct by
  `Dmmeta.check` and the four suffixes pairwise non-overlapping;
- `checkFun` for each of the four bodies. Each is one statement over a
  dereferenced row, so the only real obligation is that `row->f` types to
  `parent *` — which is `NameWf.ctx_field?` composed with
  `NameWf.fieldTy_upptr`, and which is exactly what the `needsRecordArg`
  clause added to `Dmmeta.check` makes true.
-/

set_option maxHeartbeats 1000000

-- `String.toList` on a *symbolic* string does not whnf, so unfolding `mangle`
-- during elaboration diverges: every statement here that mentions
-- `mangle c.name` timed out until this line was added. It is `local` rather
-- than global because the checker's `rfl` examples elsewhere do compute
-- `mangle` on literals, and must keep doing so.
attribute [local irreducible] Dmmeta.mangle

namespace Templates
namespace Upptr

open Dmmeta
open CSubset

/-- **Every accepted schema generates an accepted program.** -/
def GenWellFormed : Prop :=
  ∀ d : Dmmeta.Db, Dmmeta.check d = [] → CSubset.Wf.check (genUpptr d) = []

/-! ## The field list

`upFields` is `NameWf.fieldsOf` at `Upptr`, definitionally, which is what lets
the shared sublist argument apply verbatim. -/

theorem upFields_eq (d : Db) : upFields d = NameWf.fieldsOf d .Upptr := rfl

/-! ## The four names of one field

They share a qualified prefix and differ in a literal suffix. -/

theorem defsFor_names (c f a : String) :
    (defsFor c f a).map FunDef.name
      = [ c ++ "_" ++ f ++ "_Init", c ++ "_" ++ f ++ "_Get"
        , c ++ "_" ++ f ++ "_Set", c ++ "_" ++ f ++ "_Q" ] := rfl

/-- `qualName` is the mangled prefix every generated symbol is built from. One
delta step, named so nothing has to whnf `mangle` on a symbolic name. -/
theorem qualName_eq (c f : Dmmeta.Ident) :
    qualName c f = Dmmeta.mangle c ++ "_" ++ Dmmeta.mangle f := rfl

/-- The names one field contributes, in terms of its qualified name. -/
theorem block_names (cf : Dmmeta.Ident × Field) :
    (defsFor (Dmmeta.mangle cf.1) (Dmmeta.mangle cf.2.name)
        (Dmmeta.mangle cf.2.arg)).map FunDef.name
      = [ qualName cf.1 cf.2.name ++ "_Init", qualName cf.1 cf.2.name ++ "_Get"
        , qualName cf.1 cf.2.name ++ "_Set", qualName cf.1 cf.2.name ++ "_Q" ] := by
  rw [defsFor_names, qualName_eq]

/-- **Within one field, the four names are distinct** — the suffixes are, and
the prefix cancels. -/
theorem block_pairwise (q : Dmmeta.Ident) :
    ([q ++ "_Init", q ++ "_Get", q ++ "_Set", q ++ "_Q"]).Pairwise (· ≠ ·) := by
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_,
    List.pairwise_cons.mpr ⟨?_, by simp⟩⟩⟩ <;>
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;>
      exact CSubset.append_ne (s := q) (by decide)

/-- **Across two fields with different qualified names, all sixteen pairs are
distinct.** Four of them share a suffix and cancel; the other twelve are the
reversed-prefix argument, one `simp` each. -/
theorem cross_pairwise {q q' : Dmmeta.Ident} (h : q ≠ q') :
    ∀ x ∈ [q ++ "_Init", q ++ "_Get", q ++ "_Set", q ++ "_Q"],
      ∀ y ∈ [q' ++ "_Init", q' ++ "_Get", q' ++ "_Set", q' ++ "_Q"], x ≠ y := by
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | exact NameWf.append_ne_of_prefix_ne h
      | exact NameWf.append_ne_rev (by decide)

/-- **The generated function names are pairwise distinct.**

checked by: `lake build` -/
theorem names_distinct {d : Db} (hchk : check d = []) :
    ((genUpptr d).funs.map FunDef.name).Pairwise (· ≠ ·) := by
  have hq := NameWf.fieldsOf_pairwise_qual hchk .Upptr
  rw [← upFields_eq] at hq
  simp only [genUpptr, List.map_flatMap]
  refine NameWf.pairwise_flatMap (upFields d) (fun cf _ => ?_) ?_
  · rw [block_names]; exact block_pairwise _
  · refine hq.imp ?_
    intro a b hab
    rw [block_names, block_names]
    exact cross_pairwise hab

/-! ## The four bodies

Every accessor dereferences `row` and touches `row->f`, so all four reduce to
the same fact: the generated struct for the child ctype has field `f` at type
`parent *`. -/

/-- The field type the four bodies assume, from the schema's acceptance. The
`needsRecordArg` clause is what makes this reachable: without it `f.arg` could
be `u64` and the emitted `NULL` would have the wrong pointee. -/
theorem up_field_ty {d : Db} (hchk : check d = []) {c : Ctype} {f : Field}
    (hc : c ∈ d.withBuiltins.ctypes) (hs : c.scalar = none) (hf : f ∈ c.fields)
    (hr : f.reftype = .Upptr) {ctx : Wf.Ctx} (hstructs : ctx.structs = genStructs d) :
    ctx.field? (Dmmeta.mangle c.name) (Dmmeta.mangle f.name)
      = some (.ptr (.strct (Dmmeta.mangle f.arg))) := by
  obtain ⟨_, _, hcty⟩ := Layout.facts_of_check hchk
  obtain ⟨i, hi, hci⟩ : ∃ i, ∃ hi : i < d.withBuiltins.ctypes.length,
      (d.withBuiltins.ctypes[i]'hi) = c := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp hc
    exact ⟨i, hi.1, hi.2⟩
  obtain ⟨_, _, hff⟩ := hcty i hi
  rw [hci] at hff
  obtain ⟨_, _, _, hrec⟩ := hff f hf
  -- the `arg` is a record: the `needsRecordArg` clause of `Dmmeta.check`
  obtain ⟨ac, hac, hacs⟩ := hrec (by rw [hr]; rfl)
  exact NameWf.ctx_field? hchk hc hs hf
    (NameWf.fieldTy_upptr hr hac hacs) hstructs

/-- **Each of the four bodies checks clean.** They differ only in which
statement they are, and every one of them reduces to `up_field_ty` plus closed
arithmetic on the operator typings, so the four are proved together against a
*symbolic* `Wf.Ctx` — the `ArrayTableWf` shape, and for its reason: a concrete
`Ctx` would make `simp` fuse the `find?`s before the field lookup could
match. -/
theorem checkFun_defsFor {d : Db} (hchk : check d = []) {c : Ctype} {f : Field}
    (hc : c ∈ d.withBuiltins.ctypes) (hs : c.scalar = none) (hf : f ∈ c.fields)
    (hr : f.reftype = .Upptr) {earlier : List FunDef} :
    ∀ fd ∈ defsFor (Dmmeta.mangle c.name) (Dmmeta.mangle f.name)
        (Dmmeta.mangle f.arg),
      Wf.checkFun (genStructs d) (genGlobals d) earlier fd = [] := by
  intro fd hfd
  -- the one fact all four need, in the context each is checked against
  have hfield : ∀ (locals : List (CSubset.Ident × ValTy)),
      (Wf.Ctx.mk (genStructs d) (genGlobals d) earlier locals).field?
        (Dmmeta.mangle c.name) (Dmmeta.mangle f.name)
          = some (.ptr (.strct (Dmmeta.mangle f.arg))) :=
    fun locals => up_field_ty hchk hc hs hf hr rfl
  simp only [defsFor, List.mem_cons, List.not_mem_nil, or_false] at hfd
  rcases hfd with rfl | rfl | rfl | rfl
  · -- Init: `row->f = NULL`
    simp only [Wf.checkFun, initDef, names, upFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hfield, Wf.isValTy, Wf.distinct, Wf.dups, parRow]
  · -- Get: `return row->f`
    simp only [Wf.checkFun, getDef, names, upFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hfield, Wf.isValTy, Wf.distinct, Wf.dups, parRow, Wf.Stmt.alwaysReturns]
  · -- Set: `row->f = p`
    simp only [Wf.checkFun, setDef, names, upFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hfield, Wf.isValTy, Wf.distinct, Wf.dups, parRow, parP, ValTy.toTy]
  · -- Q: `return row->f != NULL`
    simp only [Wf.checkFun, testDef, names, upFld, Wf.checkStmt, Wf.addrChecks,
      Wf.inferExpr, Wf.inferLVal, Wf.Ctx.local?, ValTy.toTy]
    simp [hfield, Wf.isValTy, Wf.distinct, Wf.dups, parRow, Wf.binTy, Wf.isPtrTy,
      Wf.Stmt.alwaysReturns]

/-- **Every accepted schema generates an accepted program.**

checked by: `lake build` -/
theorem genWellFormed : GenWellFormed := by
  intro d hchk
  simp only [Wf.check, genUpptr, List.append_eq_nil_iff]
  refine ⟨⟨⟨Layout.checkStructs_gen hchk, Layout.checkGlobals_gen hchk⟩,
    CSubset.distinct_eq_nil (names_distinct hchk)⟩, ?_⟩
  rw [List.flatMap_eq_nil_iff]
  rintro ⟨fd, i⟩ hfdi
  -- which field emitted this function
  rw [List.mem_zipIdx_iff_getElem?] at hfdi
  have hmem : fd ∈ (genUpptr d).funs := by
    simp only [genUpptr]
    exact List.mem_of_getElem? hfdi
  simp only [genUpptr, List.mem_flatMap] at hmem
  obtain ⟨cf, hcf, hfd⟩ := hmem
  simp only [upFields, List.mem_flatMap, List.mem_filterMap] at hcf
  obtain ⟨c, hc, f, hf, hcfeq⟩ := hcf
  have hrr : f.reftype = .Upptr := by
    cases hb : f.reftype == Reftype.Upptr with
    | true  => exact eq_of_beq hb
    | false =>
      rw [hb] at hcfeq
      simp only [Bool.false_eq_true, if_false] at hcfeq
      exact absurd hcfeq (by simp)
  have hpair : cf = (c.name, f) := by
    rw [hrr] at hcfeq
    simp only [beq_self_eq_true, if_true, Option.some.injEq] at hcfeq
    exact hcfeq.symm

  subst hpair
  -- and it is a record ctype of the builtin-extended db
  have hcb : c ∈ d.withBuiltins.ctypes :=
    List.mem_append_right _ hc
  have hcs : c.scalar = none := by
    cases hsc : c.scalar with
    | none => rfl
    | some t =>
      exfalso
      obtain ⟨_, _, hcty⟩ := Layout.facts_of_check hchk
      -- a scalar ctype has no fields, so `f ∈ c.fields` is impossible
      obtain ⟨i', hi', hci'⟩ : ∃ i', ∃ hi' : i' < d.withBuiltins.ctypes.length,
          (d.withBuiltins.ctypes[i']'hi') = c := by
        obtain ⟨i', hi'⟩ := List.mem_iff_getElem.mp hcb
        exact ⟨i', hi'.1, hi'.2⟩
      obtain ⟨_, hnf, _⟩ := hcty i' hi'
      rw [hci'] at hnf
      rw [hnf (by rw [hsc]; rfl)] at hf
      exact absurd hf (by simp)
  exact checkFun_defsFor hchk hcb hcs hf hrr fd hfd

end Upptr
end Templates

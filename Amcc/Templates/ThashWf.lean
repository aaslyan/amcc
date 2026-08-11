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

end Thash
end Templates

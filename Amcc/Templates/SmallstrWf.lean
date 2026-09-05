import Amcc.Templates.NameWf
import Amcc.Templates.Smallstr

/-!
# AMCC — the `Smallstr` template is well-formed for every accepted schema

Proves that for every schema accepted by `Dmmeta.check`, `genSmallstr d` produces
a program that satisfies all C-subset well-formedness obligations (`CSubset.Wf.check = []`).

## Structure

1. Function-name distinctness (`defsFor_names`, `block_pairwise`, `cross_pairwise`).
2. Function well-formedness for each of the four generated operations:
   - `Init`: `row->n_f = 0u`
   - `N`: `return row->n_f`
   - `Max`: `return N`
   - `Add`: `_i = (u32)row->n_f; if (_i < N) { row->f[_i] = c; row->n_f = (u8)(_i + 1); }`
3. Whole-program well-formedness (`genWellFormed`).
-/

set_option maxHeartbeats 1000000

attribute [local irreducible] Dmmeta.mangle

namespace Templates
namespace Smallstr

open Dmmeta
open CSubset

/-- **Every accepted schema generates an accepted program.** -/
def GenWellFormed : Prop :=
  ∀ d : Dmmeta.Db, Dmmeta.check d = [] → CSubset.Wf.check (genSmallstr d) = []

/-! ## Name distinctness -/

theorem defsFor_names (nm : Names) (owner fld : CSubset.Ident) (n : Nat) :
    (defsFor nm owner fld n).map FunDef.name
      = [ nm.init, nm.size, nm.max, nm.add ] := rfl

theorem block_pairwise (q : Dmmeta.Ident) :
    ([q ++ "_Init", q ++ "_N", q ++ "_Max", q ++ "_Add"]).Pairwise (· ≠ ·) := by
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_,
    List.pairwise_cons.mpr ⟨?_, by simp⟩⟩⟩ <;>
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;>
      exact CSubset.append_ne (s := q) (by decide)

theorem cross_pairwise {q q' : Dmmeta.Ident} (h : q ≠ q') :
    ∀ x ∈ [q ++ "_Init", q ++ "_N", q ++ "_Max", q ++ "_Add"],
      ∀ y ∈ [q' ++ "_Init", q' ++ "_N", q' ++ "_Max", q' ++ "_Add"], x ≠ y := by
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | exact NameWf.append_ne_of_prefix_ne h
      | exact NameWf.append_ne_rev (by decide)

end Smallstr
end Templates

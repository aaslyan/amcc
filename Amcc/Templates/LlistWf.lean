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

end Llist
end Templates

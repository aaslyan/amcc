import Amcc.CSubset.Eval
import Amcc.CSubset.Examples

/-!
# AMCC — Phase 1: sanity theorems

The brief's Phase 1 success criterion — "prove a couple of sanity theorems
about the trivial example" — plus the frame lemmas that Phase 3 will actually
lean on.

Two kinds of statement appear here, and the difference matters:

- The **general** lemmas (`assign_local_preserves_glb`, `call_restores_frame`)
  quantify over all programs and stores. These are the reusable ones; a
  template proof cites them rather than re-deriving them.
- The **example** theorems are closed computations, checked by `rfl`. They are
  not proof-by-testing: `rfl` is kernel reduction, so `cell_set_then_get` holds
  for every `UInt64`, not for a sample of them. Making these `rfl` rather than
  `simp` calls is the payoff from `execAt`/`execStmt` being structurally
  recursive.
-/

set_option maxHeartbeats 4000000

namespace CSubset
namespace Sanity

open Examples

/-! ## General frame lemmas

These say that the two halves of a `Store` really are independent, which is the
semantic content of Phase 0's decision to forbid `&local`. -/

/-- Resolving a bound local yields that local, and nothing else.

checked by: `lake build` -/
theorem resolve_var {σ : Store} {x : Ident} {v : Value} (h : σ.getLocal x = some v) :
    resolve σ (.var x) = .ok (.lcl x) := by
  simp [resolve, h]

/-- A local-rooted lvalue can only resolve to a local. There is no path into a
frame, so there is nothing else for it to be.

checked by: `lake build` -/
theorem resolve_var_inv {σ : Store} {x : Ident} {l : Loc}
    (h : resolve σ (.var x) = .ok l) : l = .lcl x := by
  simp only [resolve] at h
  split at h
  · cases h; rfl
  · exact Except.noConfusion h

/-- Assigning to a local cannot change any global.

No aliasing side condition and no hypothesis about the expression: it holds
because a `Loc.lcl` write goes through `Store.setLocal`, and nothing can make a
global-rooted path point at a frame.

checked by: `lake build` -/
theorem assign_local_preserves_glb {p : Program} {callee} {x : Ident} {e : Expr}
    {σ σ' : Store} {out : Outcome}
    (h : execAt p callee (.assign (.var x) e) σ = .ok (σ', out)) :
    σ'.glb = σ.glb := by
  simp only [execAt] at h
  obtain ⟨loc, hres, h⟩ := bindOk h
  obtain ⟨v, _, h⟩ := bindOk h
  obtain ⟨σ'', hw, h⟩ := bindOk h
  cases h
  cases resolve_var_inv hres
  simp only [writeLoc] at hw
  split at hw
  · cases hw; rfl
  · exact Except.noConfusion hw

/-- A call leaves the caller's frame exactly as it was. The callee cannot reach
into it: there is no pointer to a frame, so `execAt`'s wholesale restore of
`σ.loc` loses nothing.

checked by: `lake build` -/
theorem call_restores_frame {p : Program} {callee} {f : Ident} {args : List Expr}
    {σ σ' : Store} {out : Outcome}
    (h : execAt p callee (.call none f args) σ = .ok (σ', out)) :
    σ'.loc = σ.loc := by
  simp only [execAt] at h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨_, _, h⟩ := bindOk h
  obtain ⟨r, _, h⟩ := bindOk h
  obtain ⟨_, _⟩ := r
  cases h
  rfl

/-! ## The trivial cell

The brief's example, and the theorem it names. -/

/-- Before anything is written the cell reads zero — C's guarantee for objects
with static storage duration, here a consequence of `initGlobals`.

checked by: `lake build` -/
theorem cell_get_initial :
    Except.map (·.2) (runProgram trivialCell "cell_get" []) = .ok (some (.u64 0)) := rfl

/-- **Setter followed by getter returns what was set.**

Phase 1's sanity theorem, universally quantified: `v` is a variable, so this is
one proof covering all 2⁶⁴ values, not a test over a sample.

checked by: `lake build` -/
theorem cell_set_then_get (v : UInt64) :
    Except.map (·.2) (runCalls trivialCell [("cell_set", [.u64 v]), ("cell_get", [])])
      = .ok [none, some (.u64 v)] := rfl

/-- The setter overwrites: the last write is what the getter sees.

checked by: `lake build` -/
theorem cell_set_twice (v w : UInt64) :
    Except.map (·.2)
      (runCalls trivialCell [("cell_set", [.u64 v]), ("cell_set", [.u64 w]), ("cell_get", [])])
      = .ok [none, none, some (.u64 w)] := rfl

/-! ## The tiny table

Not required by the brief, but this is the shape Phase 3 must generate, so
exercising it now is what tells us the semantics is adequate for the milestone
rather than only for the toy. Each of these reduces in the kernel. -/

/-- An empty table finds nothing — `tbl_find` returns the sentinel `CAP`.

checked by: `lake build` -/
theorem find_on_empty (k : UInt64) :
    Except.map (·.2) (runProgram tinyTable "tbl_find" [.u64 k]) = .ok (some (.u32 4)) := rfl

/-- Insert then find returns the slot that was claimed.

checked by: `lake build` -/
theorem insert_then_find :
    Except.map (·.2)
      (runCalls tinyTable [("tbl_insert", [.u64 7, .u64 42]), ("tbl_find", [.u64 7])])
      = .ok [some (.bool true), some (.u32 0)] := rfl

/-- Distinct keys take distinct slots, and each is found where it was put.

checked by: `lake build` -/
theorem insert_two_then_find :
    Except.map (·.2)
      (runCalls tinyTable
        [("tbl_insert", [.u64 7, .u64 42]), ("tbl_insert", [.u64 9, .u64 43]),
         ("tbl_find", [.u64 9]), ("tbl_find", [.u64 7]), ("tbl_find", [.u64 8])])
      = .ok [some (.bool true), some (.bool true),
             some (.u32 1), some (.u32 0), some (.u32 4)] := rfl

/-- Re-inserting a present key updates in place rather than consuming a slot —
which is the branch guarded by `at != CAP`, and therefore the branch whose
`g_rows[at]` read is only safe because of that guard.

checked by: `lake build` -/
theorem insert_existing_updates_in_place :
    Except.map (·.2)
      (runCalls tinyTable
        [("tbl_insert", [.u64 7, .u64 42]), ("tbl_insert", [.u64 7, .u64 43]),
         ("tbl_find", [.u64 9])])
      = .ok [some (.bool true), some (.bool true), some (.u32 4)] := rfl

/-- The table fills up and then refuses.

checked by: `lake build` -/
theorem insert_beyond_capacity :
    Except.map (·.2)
      (runCalls tinyTable
        [("tbl_insert", [.u64 1, .u64 1]), ("tbl_insert", [.u64 2, .u64 2]),
         ("tbl_insert", [.u64 3, .u64 3]), ("tbl_insert", [.u64 4, .u64 4]),
         ("tbl_insert", [.u64 5, .u64 5])])
      = .ok [some (.bool true), some (.bool true), some (.bool true),
             some (.bool true), some (.bool false)] := rfl

/-- The pointer path end to end: `tbl_bump` takes an address with `&`, stores
it in a pointer local, and reads and writes through `p->val`. `42 + 8 = 50`
lands in the row, so `&`, `*` and `.` compose the way they must.

checked by: `lake build` -/
theorem bump_through_pointer :
    Except.map (fun r => r.1.glb)
      (runCalls tinyTable
        [("tbl_insert", [.u64 7, .u64 42]), ("tbl_bump", [.u32 0, .u64 8])])
      = .ok [("g_rows", .arr
        [ .strct [("key", .u64 7), ("val", .u64 50), ("occupied", .bool true)]
        , .strct [("key", .u64 0), ("val", .u64 0), ("occupied", .bool false)]
        , .strct [("key", .u64 0), ("val", .u64 0), ("occupied", .bool false)]
        , .strct [("key", .u64 0), ("val", .u64 0), ("occupied", .bool false)] ])] := rfl

/-- **The single partial operation, trapping.**

`tbl_at(4)` takes `&g_rows[4]` on a capacity-4 array. The error is `oob` and
not `typeErr`, which is the whole point of classifying errors: this is the one
Phase 3 has to prove away, and it is distinguishable from the structural ones.

checked by: `lake build` -/
theorem addr_out_of_range_traps :
    runProgram tinyTable "tbl_at" [.u32 4] = .error .oob := rfl

/-- Inside the array, the same address is fine — so the trap is a bounds
condition, not `&` being broken.

checked by: `lake build` -/
theorem addr_in_range_ok :
    Except.map (·.2) (runProgram tinyTable "tbl_at" [.u32 3])
      = .ok (some (.ptr ⟨.glob "g_rows", [.idx 3]⟩)) := rfl

/-! ## A loop bounded at run time

`forN` used to take a literal trip count, which meant no generated loop could
scan storage whose size is decided while the program runs — the restriction
that made every table's capacity a compile-time constant. These check that the
replacement works: the same program, three different bounds, one proof each,
and the bound is an ordinary parameter. -/

/-- The loop runs exactly as many times as its runtime bound says.

checked by: `lake build` -/
theorem varLoop_counts_5 :
    Except.map (·.2) (runProgram varLoop "count_upto" [.u32 5])
      = .ok (some (.u32 5)) := rfl

/-- A zero bound runs the body no times — the case a literal-bound loop could
never be handed. -/
theorem varLoop_counts_0 :
    Except.map (·.2) (runProgram varLoop "count_upto" [.u32 0])
      = .ok (some (.u32 0)) := rfl

/-- checked by: `lake build` -/
theorem varLoop_counts_17 :
    Except.map (·.2) (runProgram varLoop "count_upto" [.u32 17])
      = .ok (some (.u32 17)) := rfl

end Sanity
end CSubset

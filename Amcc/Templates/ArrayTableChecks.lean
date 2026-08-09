import Amcc.Templates.ArrayTable

/-!
# AMCC — Phase 3: the array table, exercised

What is checked here, and what it is worth.

**Proved generically (all schemas):** `absOf_eq_empty` — a table with no
occupied slot abstracts to the empty map.

**Checked by computation (the two example schemas):** that `genC` emits code the
C subset accepts, and that running that code behaves like a map. Most are
`rfl`, so they are kernel-checked equalities rather than tests — but they are
about *these* schemas, not all of them, and that distinction is the whole point
of the project. They are evidence the generator is right, not proof.

One check — the full-table and slot-reuse path — is `#guard` rather than
`rfl`. Kernel-normalising that run was measured at over 23 GB of memory before
an out-of-memory panic (the failing insert makes both scans run dry over a full
store, the interpreter's worst case), while compiled evaluation finishes it in
a quarter of a second. `#guard` still runs during `lake build`, so the
verification signal is unchanged; the trust base for that one check is the
compiler rather than the kernel — an acceptable trade for what is explicitly
evidence, not proof.

The cross-check that earns the most is `absOf_after_insert`: `absOf` is written
independently of `genC`, so if the abstraction function disagreed with the
layout the generator actually emits — a wrong field name, the occupancy flag in
the wrong place, the value tuple in the wrong order — that theorem would fail.
It is the one place the two halves of Phase 3 are forced to agree.

**Not proved:** `MilestoneTheorem`. See the assessment at the bottom of this
file.
-/

set_option maxHeartbeats 8000000

namespace Templates
namespace ArrayTableChecks

open CSubset Templates.ArrayTable

-- For the `#guard` check below. `Value` derives `BEq` in `Value.lean`; core
-- provides no `BEq` for `Except`, so it is derived here, in its one consumer.
deriving instance BEq for Except

/-! ## The generator emits well-formed C -/

/-- The generated program satisfies every one of the C subset's eleven
obligations.

checked by: `lake build` -/
example : Wf.check (genC Schema.Examples.orders) = [] := rfl

/-- Including for a schema with no value fields at all, which is the case a
generator is most likely to get wrong.

checked by: `lake build` -/
example : Wf.check (genC Schema.Examples.keysOnly) = [] := rfl

/-- checked by: `lake build` -/
example : (genC Schema.Examples.orders).funs.map FunDef.name
    = ["order_find", "order_insert", "order_erase", "order_get_price", "order_get_qty"] := rfl

/-- The degenerate schema generates no getters. -/
example : (genC Schema.Examples.keysOnly).funs.map FunDef.name
    = ["tag_find", "tag_insert", "tag_erase"] := rfl

/-! ## The generated code behaves like a map -/

private def run (calls : List (Ident × List Value)) :
    Except Err (Mem × List (Option Value)) :=
  runCalls (genC Schema.Examples.orders) calls

/-- Insert, look up, read fields, erase, confirm gone. Every step's answer, in
one equation.

checked by: `lake build` -/
example :
    Except.map (·.2) (run
      [ ("order_insert",    [.u64 7, .u64 100, .u64 5])
      , ("order_find",      [.u64 7])
      , ("order_get_price", [.u64 7])
      , ("order_get_qty",   [.u64 7])
      , ("order_find",      [.u64 8])
      , ("order_erase",     [.u64 7])
      , ("order_find",      [.u64 7])
      , ("order_get_price", [.u64 7]) ])
    = .ok [ some (.bool true)      -- inserted
          , some (.u32 0)          -- found in slot 0
          , some (.u64 100)
          , some (.u64 5)
          , some (.u32 4)          -- absent key gives the CAP sentinel
          , some (.bool true)      -- erased
          , some (.u32 4)          -- now absent
          , some (.u64 0) ]        -- getter's zero for an absent key
    := rfl

/-- Re-inserting a present key updates rather than consuming a second slot —
the `_at != CAP` branch. The second key still lands in slot 1.

checked by: `lake build` -/
example :
    Except.map (·.2) (run
      [ ("order_insert",    [.u64 7, .u64 100, .u64 5])
      , ("order_insert",    [.u64 7, .u64 200, .u64 6])
      , ("order_insert",    [.u64 9, .u64 300, .u64 7])
      , ("order_get_price", [.u64 7])
      , ("order_find",      [.u64 9]) ])
    = .ok [some (.bool true), some (.bool true), some (.bool true),
           some (.u64 200), some (.u32 1)] := rfl

/-! The full-table and slot-reuse path: fill all four slots, watch the fifth
insert fail with nothing changed, erase, and watch the next insert reclaim the
freed slot. This is the interpreter's worst case — the failing insert runs both
scans to exhaustion over a full store — which is why it is `#guard` (compiled
evaluation) and not `rfl` (kernel normalisation): see the module docstring.

checked by: `lake build` (compiled, not kernel-checked) -/
#guard
    (Except.map (·.2) (run
      [ ("order_insert", [.u64 1, .u64 10, .u64 1])
      , ("order_insert", [.u64 2, .u64 20, .u64 2])
      , ("order_insert", [.u64 3, .u64 30, .u64 3])
      , ("order_insert", [.u64 4, .u64 40, .u64 4])
      , ("order_insert", [.u64 5, .u64 50, .u64 5])   -- table full: reports false
      , ("order_erase",  [.u64 2])
      , ("order_insert", [.u64 5, .u64 50, .u64 5])   -- reclaims slot 1
      , ("order_find",   [.u64 5]) ])
    == .ok [ some (.bool true), some (.bool true), some (.bool true), some (.bool true)
           , some (.bool false)     -- full table refuses, changing nothing
           , some (.bool true)      -- erased
           , some (.bool true)      -- re-insert lands in the freed slot
           , some (.u32 1) ])       -- found where slot reuse put it

/-- Erasing an absent key reports failure. -/
example : Except.map (·.2) (run [("order_erase", [.u64 7])])
    = .ok [some (.bool false)] := rfl

/-! ## The abstraction function agrees with the generator

`absOf` was written from the schema, `genC` emits the storage. Nothing forces
them to agree except these equations. -/

/-- After inserting two rows, `absOf` reports exactly them, with the value
fields in schema order and the key field excluded.

checked by: `lake build` -/
example :
    Except.map (fun r => (absOf Schema.Examples.orders r.1.glb (.u64 7),
                          absOf Schema.Examples.orders r.1.glb (.u64 9),
                          absOf Schema.Examples.orders r.1.glb (.u64 8)))
      (run [ ("order_insert", [.u64 7, .u64 100, .u64 5])
           , ("order_insert", [.u64 9, .u64 300, .u64 7]) ])
    = .ok (some [.u64 100, .u64 5], some [.u64 300, .u64 7], none) := rfl

/-- Erasing removes the key from the abstraction even though the payload is
still in the slot — the occupancy flag is what `absOf` reads first.

checked by: `lake build` -/
example :
    Except.map (fun r => absOf Schema.Examples.orders r.1.glb (.u64 7))
      (run [ ("order_insert", [.u64 7, .u64 100, .u64 5])
           , ("order_erase",  [.u64 7]) ])
    = .ok none := rfl

/-- The zero-initialised table abstracts to the empty map. The concrete
instance of the generic `absOf_eq_empty` below.

checked by: `lake build` -/
example : Except.map (fun r => absOf Schema.Examples.orders r.1.glb (.u64 7)) (run [])
    = .ok none := rfl

end ArrayTableChecks
end Templates

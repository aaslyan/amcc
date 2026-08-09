import Amcc.Templates.ArrayTable

/-!
# AMCC — `find`, proved against the semantics

The first refinement proof in the project: reasoning about `execStmt` on a
*generated* body, under `RepInv`, to establish what the function computes.

Everything proved so far about generated code has been **structural** —
`GenWellFormed` says the checker accepts it, `Wf.check` says the shapes fit.
Nothing has said what any generated function *does*. This file is where that
starts, and `find` is the right place to start it: `insert`, `erase` and the
abstraction all call `find`, so no other clause of `Simulates` is reachable
without it.

## Why this order

The plan deferred this behind `TypeSound` and the semantics rework. That was
the wrong call, for a reason worth recording: the technique — loop-invariant
reasoning over `forLoop`, with the error cases discharged from `RepInv` — is
what transfers to every later template. Deferring it left the project's
central claim untested while everything else was built on the assumption that
it would work.

`TypeSound` is deliberately **not** used. It is a general
progress-and-preservation argument over `Step`; for one template the shapes are
pinned by `RepInv` directly, so the structural errors are discharged where they
arise rather than by a theorem that does not exist yet.

## The obligations, bottom up

1. `resolve_slot` — the loop's `g_<t>[_i]` resolves to the path it should.
2. `resolve_field` / `read_field` — a field of that slot reads back what the
   invariant says is there.
3. the guard evaluates to the occupancy-and-key test.
4. `forLoop` induction: scanning `[i, i+rem)` returns the first match.
5. `FindCorrect`.

This file currently establishes (1) and (2). What is *not* yet proved is
recorded honestly at the bottom rather than stated as if it were.
-/

namespace Templates
namespace ArrayTable

open CSubset

variable {s : Schema} {σ : Store}

/-! ## Reading the loop variable

`evalIndex` goes through `UInt32.toNat`, so every slot lemma needs the
round-trip. It holds because `Schema.check` bounds the capacity by `2³²`, which
is exactly why that clause is in the checker. -/

/-- The loop variable, read back as the `Nat` it stands for. -/
theorem evalIndex_var {i : Nat} {x : Ident}
    (hloc : σ.getLocal x = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i) :
    evalIndex σ (.var x) = .ok i := by
  simp only [evalIndex, hloc, hround]

/-! ## Resolving a slot

The first genuine step: `g_<t>[_i]` denotes slot `i` of the storage array.
Every clause of `RepInv` that matters shows up here — `storage` gives the
array, and the length clause is what turns `i < capacity` into an in-range
subscript, which is the whole no-trap argument for this template. -/

/-- **The slot resolves, and does not trap.**

The `oob` case is discharged by `RepInv.length`: the array really is
`capacity` long, so a loop bounded by the capacity cannot leave it.

checked by: `lake build` -/
theorem resolve_slot {i : Nat} (R : RepInv s σ.glb)
    (hlt : i < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpI = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i) :
    resolve σ (slot s tmpI)
      = .ok (.glb ⟨.glob (Schema.names s).storage, [.idx i]⟩) := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  simp only [slot, resolve, evalIndex, hloc, hround, Store.readPath,
    Store.rootVal, hglb, Value.getPath, bind, Except.bind]
  rw [if_pos hlt]
  simp

/-- Reading through a resolved slot gives the row the invariant names. -/
theorem readLoc_slot {i : Nat} {row : Value} (R : RepInv s σ.glb)
    (hrow : (rowsOf s σ.glb)[i]? = some row) :
    readLoc σ (.glb ⟨.glob (Schema.names s).storage, [.idx i]⟩) = .ok row := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  simp only [readLoc, Store.readPath, Store.rootVal, hglb, Value.getPath,
    Value.getStep, hrow]

/-! ## Resolving a field of a slot

`g_<t>[_i].f`. This is where `RepInv.rows` earns its place: without it the
field lookup could fail and the read would be a `typeErr` rather than a value.
Discharging that here, from the invariant, is what makes `TypeSound`
unnecessary for this template. -/

/-- **A field of a slot resolves**, provided the row really has that field —
which for the generated struct's fields is `RowOk`. -/
theorem resolve_field {i : Nat} {row : Value} {f : Ident} {v : Value}
    (R : RepInv s σ.glb)
    (hlt : i < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpI = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i)
    (hrow : (rowsOf s σ.glb)[i]? = some row)
    (hfld : row.getStep (.fld f) = some v) :
    resolve σ (field s tmpI f)
      = .ok (.glb ⟨.glob (Schema.names s).storage, [.idx i, .fld f]⟩) := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  have hstep : (Value.arr (rowsOf s σ.glb)).getStep (.idx i) = some row := by
    simp only [Value.getStep, hrow]
  have hpath : (Value.arr (rowsOf s σ.glb)).getPath [.idx i, .fld f] = some v := by
    show (match (Value.arr (rowsOf s σ.glb)).getStep (.idx i) with
          | some v' => Value.getPath v' [.fld f]
          | none => none) = some v
    rw [hstep]
    show (match row.getStep (.fld f) with
          | some v' => Value.getPath v' []
          | none => none) = some v
    rw [hfld]
    rfl
  simp only [field, resolve, resolve_slot R hlt hloc hround, bind, Except.bind,
    Store.readPath, Store.rootVal, hglb, List.cons_append, List.nil_append]
  rw [hpath]

/-- **And reading it gives the field's value.**

checked by: `lake build` -/
theorem read_field {i : Nat} {row : Value} {f : Ident} {v : Value}
    (R : RepInv s σ.glb)
    (hlt : i < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpI = some (.u32 (UInt32.ofNat i)))
    (hround : (UInt32.ofNat i).toNat = i)
    (hrow : (rowsOf s σ.glb)[i]? = some row)
    (hfld : row.getStep (.fld f) = some v) :
    evalExpr σ (.rd (field s tmpI f)) = .ok v := by
  have hglb : σ.glb.get? (Schema.names s).storage
      = some (.arr (rowsOf s σ.glb)) := R.storage
  have hstep : (Value.arr (rowsOf s σ.glb)).getStep (.idx i) = some row := by
    simp only [Value.getStep, hrow]
  have hpath : (Value.arr (rowsOf s σ.glb)).getPath [.idx i, .fld f] = some v := by
    show (match (Value.arr (rowsOf s σ.glb)).getStep (.idx i) with
          | some v' => Value.getPath v' [.fld f]
          | none => none) = some v
    rw [hstep]
    show (match row.getStep (.fld f) with
          | some v' => Value.getPath v' []
          | none => none) = some v
    rw [hfld]
    rfl
  simp only [evalExpr, resolve_field R hlt hloc hround hrow hfld, bind,
    Except.bind, readLoc, Store.readPath, Store.rootVal, hglb,
    List.cons_append, List.nil_append]
  rw [hpath]

/-! ## What `RepInv` gives about a row

Turning the invariant's existential clauses into the equations the guard needs. -/

/-- The occupancy flag of a live row is a `bool`, and it is the one `absOf`
reads. -/
theorem occupied_of_rowOk {row : Value} (h : RowOk s row) :
    row.getStep (.fld (Schema.names s).occupied)
      = some (.bool (rowOccupied s row)) := by
  obtain ⟨b, hb⟩ := h.occupied
  cases row with
  | strct fs =>
    simp only [Value.getStep]
    simp only at hb
    rw [hb]
    congr 1
    simp only [rowOccupied, hb]
  | u32 _ => simp at hb
  | u64 _ => simp at hb
  | bool _ => simp at hb
  | null => simp at hb
  | ptr _ => simp at hb
  | arr _ => simp at hb

/-! ## Still owed

What this file does **not** prove, stated plainly so the gap is not mistaken
for progress:

- the guard `g[_i].occupied && g[_i].pk == k` as a single equation;
- the `forLoop` induction — that scanning `[i, i+rem)` returns the first
  matching slot and otherwise falls through;
- `FindCorrect` itself, which also needs restating: `find` now returns a row
  **pointer** or `NULL`, so the clause phrased in terms of a `u32` slot index
  and the `CAP` sentinel in `ArrayTable.lean` is stale and describes the old
  API.

The pieces above are the ones every later step consumes, and they went through
without needing `TypeSound` — which is the question this file was opened to
answer. -/

end ArrayTable
end Templates

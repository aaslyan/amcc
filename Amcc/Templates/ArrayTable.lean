import Amcc.Schema
import Amcc.Interface
import Amcc.CSubset.Wf
import Amcc.CSubset.Eval

/-!
# AMCC — Phase 3: the fixed-size array table

The first template: a `capacity`-slot array with a unique primary key, linear
scan, and an occupancy flag per slot. Deliberately the simplest thing that is
still a real data structure — the point of this phase is to get one template
through the whole pipeline, not to get a fast one.

## What is generated

For a schema `s` with primary key `pk` and value fields `v₁ … vₘ`:

```c
typedef struct { <pk> ; <v₁> ; … ; bool occupied; } <t>_row;
static <t>_row g_<t>[CAP];

<t>_row* <t>_Find(<pkty> pk);            /* the row, or NULL when absent */
bool     <t>_InsertMaybe(<pkty> pk, …);  /* update in place, else claim a slot */
bool     <t>_Remove(<pkty> pk);
```

This is `amc`'s API shape, adapted to C: `Find` hands back a pointer to the
row and the caller reads fields off it (`r->price`), exactly as
`ind_targsrc_Find` hands back an `FTargsrc*`.

The earlier design returned a `uint32_t` slot index with `CAP` as the "absent"
sentinel, plus one generated getter per field. That was forced by the subset
having no null pointer, and it was worse in two ways that matter: a getter
could not distinguish an absent key from a stored zero, and reading an
`n`-field row cost `n` full lookups. `NULL` exists now, so neither compromise
is needed.

- **`Find` returns `NULL` when absent.** Unambiguous, and it is what a C
  caller expects.
- **Every access through the returned pointer sits behind `_at != NULL`.**
  That guard is the no-trap argument, now stated against null rather than
  against a sentinel index.

## Temporaries

`_i`, `_at`, `_j`. The leading underscore is reserved by `Schema.check`, so a
schema can never introduce a field that collides with one. Parameters are named
after the fields themselves, which is why the schema's own distinctness rule is
enough to keep them apart.
-/

namespace Templates
namespace ArrayTable

open CSubset

/-! ## Generated code -/

/-- Loop variable of `find`'s scan. -/
def tmpI : Ident := "_i"
/-- Slot index returned by `find`, in every function that calls it. -/
def tmpAt : Ident := "_at"
/-- Loop variable of `insert`'s free-slot scan. -/
def tmpJ : Ident := "_j"

def capLit (s : Schema) : Expr := .lit (.u32 (UInt32.ofNat s.capacity))

/-- The generated row struct, as a type. -/
def rowTy (s : Schema) : Ty := .strct (Schema.names s).row

/-- `g_<t>[i]` -/
def slot (s : Schema) (i : Ident) : LVal :=
  .idx (.glob (Schema.names s).storage) (.var i)

/-- `p->f` — a field reached through the row pointer the API hands out. -/
def ptrField (p : Ident) (f : Ident) : LVal := .fld (.deref p) f

/-- `NULL`, at row-pointer type. -/
def nullRow (s : Schema) : Expr := .null (rowTy s)

/-- The row-pointer local the callers of `Find` keep their result in. -/
def atLocal (s : Schema) : LocalDef :=
  { name := tmpAt, ty := .ptr (rowTy s), init := nullRow s }

/-- `g_<t>[i].f` -/
def field (s : Schema) (i : Ident) (f : Ident) : LVal := .fld (slot s i) f

def zeroLit : ScalarTy → Lit
  | .u8   => .u8 0
  | .u32  => .u32 0
  | .u64  => .u64 0
  | .bool => .bool false

/-- The row struct: the schema's fields, then the occupancy flag. -/
def rowStructDef (s : Schema) : StructDef where
  name   := (Schema.names s).row
  fields := s.fields.map (fun f => (f.name, Ty.scalar f.ty))
            ++ [((Schema.names s).occupied, Ty.scalar .bool)]

def storageDef (s : Schema) : GlobalDef where
  name := (Schema.names s).storage
  ty   := .arr (.strct (Schema.names s).row) s.capacity

/-- The scan's condition: this slot is occupied and holds the key we want.
Named so the proof can be stated about the code that is actually emitted. -/
def findGuard (s : Schema) (pk : Schema.Field) : Expr :=
  .bin .land
    (.rd (field s tmpI (Schema.names s).occupied))
    (.bin .eq (.rd (field s tmpI pk.name)) (.rd (.var pk.name)))

/-- One iteration of the scan. -/
def findLoopBody (s : Schema) (pk : Schema.Field) : Stmt :=
  .when (findGuard s pk) (.ret (some (.addr (slot s tmpI))))

/-- ```c
<t>_row* <t>_Find(<pkty> pk) {
  uint32_t _i = 0;
  for (_i = 0; _i < CAP; ++_i)
    if (g[_i].occupied && g[_i].pk == pk) return &g[_i];
  return NULL;
}
``` -/
def findDef (s : Schema) (pk : Schema.Field) : FunDef where
  name   := (Schema.names s).find
  params := [(pk.name, .scalar pk.ty)]
  ret    := some (.ptr (rowTy s))
  locals := [LocalDef.zeroed tmpI .u32]
  body   := .block
    [ .forN tmpI (.lit s.capacity) (findLoopBody s pk)
    , .ret (some (nullRow s)) ]

/-- ```c
bool <t>_insert(<pkty> pk, <vty> v₁, …) {   /* key first */
  uint32_t _at = 0, _j = 0;
  _at = <t>_find(pk);
  if (_at != CAP) { g[_at].v₁ = v₁; …; return true; }
  for (_j = 0; _j < CAP; ++_j)
    if (!g[_j].occupied) { g[_j].occupied = true; g[_j].pk = pk; …; return true; }
  return false;
}
```
The present-key branch rewrites only the value fields: the key is already
equal, so writing it would be a no-op, and not writing it is one fewer thing
for the simulation proof to account for. -/
def insertDef (s : Schema) (pk : Schema.Field) : FunDef where
  name   := (Schema.names s).insert
  params := (pk :: Schema.valFields s).map (fun f => (f.name, ValTy.scalar f.ty))
  ret    := some (.scalar .bool)
  locals := [atLocal s, LocalDef.zeroed tmpJ .u32]
  body   := .block
    [ .call (some tmpAt) (Schema.names s).find [.rd (.var pk.name)]
    , .when (.bin .ne (.rd (.var tmpAt)) (nullRow s)) <|
        .block ((Schema.valFields s).map
                  (fun f => .assign (ptrField tmpAt f.name) (.rd (.var f.name)))
                ++ [.ret (some (.lit (.bool true)))])
    , .forN tmpJ (.lit s.capacity) <|
        .when (.un .lnot (.rd (field s tmpJ (Schema.names s).occupied))) <|
          .block ([.assign (field s tmpJ (Schema.names s).occupied) (.lit (.bool true))]
                  ++ s.fields.map
                       (fun f => .assign (field s tmpJ f.name) (.rd (.var f.name)))
                  ++ [.ret (some (.lit (.bool true)))])
    , .ret (some (.lit (.bool false))) ]

/-- ```c
bool <t>_erase(<pkty> pk) {
  uint32_t _at = 0;
  _at = <t>_find(pk);
  if (_at != CAP) { g[_at].occupied = false; return true; }
  return false;
}
```
Erasure clears the flag and leaves the payload alone — a slot is absent because
it is unoccupied, never because its contents were scrubbed. `absOf` reads the
flag first, so the stale payload is unobservable. -/
def eraseDef (s : Schema) (pk : Schema.Field) : FunDef where
  name   := (Schema.names s).erase
  params := [(pk.name, .scalar pk.ty)]
  ret    := some (.scalar .bool)
  locals := [atLocal s]
  body   := .block
    [ .call (some tmpAt) (Schema.names s).find [.rd (.var pk.name)]
    , .when (.bin .ne (.rd (.var tmpAt)) (nullRow s)) <|
        .block [ .assign (ptrField tmpAt (Schema.names s).occupied) (.lit (.bool false))
               , .ret (some (.lit (.bool true))) ]
    , .ret (some (.lit (.bool false))) ]

/-- **The generator.**

Total, as the brief specifies. A schema without exactly one primary key has no
array table to generate, so it maps to the empty program — which is vacuously
well-formed, and which `Schema.check` rejects long before anyone runs it.

`find` is emitted first because everything else calls it, and the C subset
requires callees to precede callers. -/
def genC (s : Schema) : Program :=
  match Schema.pkey? s with
  | none => { structs := [], globals := [], funs := [] }
  | some pk =>
    { structs := [rowStructDef s]
    , globals := [storageDef s]
    , funs    := [findDef s pk, insertDef s pk, eraseDef s pk] }

/-! ## The abstraction function

`absOf` reads a concrete store as an `Interface.AbsTable`. It is deliberately
*total*: a store that does not satisfy `RepInv` still gets an answer, just a
meaningless one. That keeps it usable in theorem statements without dragging a
well-formedness proof through every occurrence — the invariant appears as a
hypothesis where it is needed instead. -/

/-- The table's slots, or `[]` if the store is not shaped like a table. -/
def rowsOf (s : Schema) (glb : Env) : List Value :=
  match glb.get? (Schema.names s).storage with
  | some (.arr vs) => vs
  | _              => []

def rowOccupied (s : Schema) (r : Value) : Bool :=
  match r with
  | .strct fs =>
    match Env.get? fs (Schema.names s).occupied with
    | some (.bool b) => b
    | _              => false
  | _ => false

def rowKey? (s : Schema) (r : Value) : Option Interface.Key := do
  let pk ← Schema.pkey? s
  match r with
  | .strct fs => do
    let v ← Env.get? fs pk.name
    Interface.Key.ofValue? v
  | _ => none

def rowVals? (s : Schema) (r : Value) : Option (List Value) :=
  match r with
  | .strct fs => (Schema.valFields s).mapM (fun f => Env.get? fs f.name)
  | _ => none

/-- **The abstraction function.** An occupied slot whose key matches contributes
its value fields; everything else is invisible.

`find?` takes the *first* match. Under `RepInv` there is at most one, so the
choice is immaterial — but making it total here means `absOf` needs no
precondition.

It reads the globals alone, not a whole `Store`: the table has static storage
duration, so a frame can hold nothing of it. That is Phase 0's no-pointer-to-a-
local decision showing up as a smaller abstraction function. -/
def absOf (s : Schema) (glb : Env) : Interface.AbsTable := fun k =>
  match (rowsOf s glb).find?
      (fun r => rowOccupied s r && decide (rowKey? s r = some k)) with
  | some r => rowVals? s r
  | none   => none

/-! ## The representation invariant -/

/-- A slot has the shape the generated struct declares: an occupancy flag that
is a `bool`, a key that is a scalar, and readable value fields.

This is what makes the generated code's reads and comparisons succeed —
`evalBin .eq` needs both operands to be the same scalar constructor, and `land`
needs a `bool`. -/
structure RowOk (s : Schema) (r : Value) : Prop where
  occupied : ∃ b : Bool, (match r with
                          | .strct fs => Env.get? fs (Schema.names s).occupied
                          | _ => none) = some (.bool b)
  key      : (rowKey? s r).isSome
  /-- **The stored key is at the primary key's declared type.**

  Not decoration, and not derivable from `key`. The generated scan compares
  the row's key against the argument with `==`, and `evalBin .eq` is defined
  only on matching scalar constructors — so a store holding a `u32` key in a
  `u64`-keyed table would make the comparison raise `typeErr` rather than
  report a miss. Without this clause the invariant admits stores on which the
  generated code gets stuck, which is exactly what the invariant exists to
  rule out. Found by trying to prove the scan. -/
  keyTy    : ∀ pk k, Schema.pkey? s = some pk → rowKey? s r = some k →
               k.ty = pk.ty
  vals     : (rowVals? s r).isSome

/-- **The representation invariant.**

Three clauses, and each one is load-bearing for a different obligation:

- `storage`/`length` — the array is exactly `capacity` long. This is what turns
  `find`'s `_at ≤ CAP` postcondition plus the `_at != CAP` guard into an
  in-range subscript, and so it is the whole no-trap argument.
- `rows` — every slot is well shaped, so the scan's reads and comparisons
  cannot produce a type error.
- `distinct` — no two occupied slots share a key, which is what makes the
  primary key *primary*: without it `absOf` would depend on scan order and the
  map laws would be false. -/
structure RepInv (s : Schema) (glb : Env) : Prop where
  storage  : glb.get? (Schema.names s).storage = some (.arr (rowsOf s glb))
  length   : (rowsOf s glb).length = s.capacity
  rows     : ∀ r ∈ rowsOf s glb, RowOk s r
  distinct : ∀ (i j : Nat) (ri rj : Value),
               (rowsOf s glb)[i]? = some ri → (rowsOf s glb)[j]? = some rj →
               rowOccupied s ri → rowOccupied s rj →
               rowKey? s ri = rowKey? s rj → i = j

/-! ## Proved: the empty table

The one generic result in this file so far. It needs no schema hypothesis and
no rep invariant: if nothing is occupied, nothing is in the map, whatever the
schema. -/

/-- `find?` returns an element that satisfies the predicate and is in the list.
Proved here rather than cited because core's `List.find?_some` does not unify
against a two-argument boolean conjunction without help. -/
theorem find?_pred {α : Type _} {p : α → Bool} :
    ∀ {l : List α} {a : α}, l.find? p = some a → p a = true ∧ a ∈ l
  | [], _, h => by simp [List.find?] at h
  | x :: xs, a, h => by
    simp only [List.find?] at h
    split at h
    · next hp => cases h; exact ⟨hp, by simp⟩
    · next =>
      obtain ⟨h1, h2⟩ := find?_pred h
      exact ⟨h1, by simp [h2]⟩

/-- A table with no occupied slot abstracts to the empty map — for every
schema.

checked by: `lake build` -/
theorem absOf_eq_empty (s : Schema) (glb : Env)
    (h : ∀ r ∈ rowsOf s glb, rowOccupied s r = false) :
    absOf s glb = Interface.Abs.empty := by
  funext k
  simp only [absOf, Interface.Abs.empty]
  cases hf : (rowsOf s glb).find?
      (fun r => rowOccupied s r && decide (rowKey? s r = some k)) with
  | none => rfl
  | some r =>
    obtain ⟨hpred, hmem⟩ := find?_pred hf
    rw [h r hmem] at hpred
    simp at hpred

/-! ## What the generated operations are, as Lean functions

One call against a global environment. Everything below is stated in terms of
this, so the obligations read as equations about `absOf` rather than about
`execStmt`. -/

/-- Call a generated function against the memory a table lives in.

Takes a `Mem`, not an `Env`: a table's storage is no longer necessarily
statically declared, so what persists across calls is globals *and* heap. -/
def call (s : Schema) (m : Mem) (f : Ident) (args : List Value) :
    Except Err (Mem × Option Value) :=
  callFun (genC s) m f args

/-- The zero-initialised globals of a generated table. -/
def initEnv (s : Schema) : Option Env := initGlobals (genC s)

/-- The initial memory of a generated table: zeroed globals, empty heap. -/
def initMem (s : Schema) : Option Mem :=
  (initGlobals (genC s)).map (fun glb => { glb := glb, hp := [], next := 0 })

/-! ## The milestone obligations

These are the statements Phase 3 owes. They are given as `Prop`-valued
definitions rather than `theorem`s so that the exact obligation is on record
and checkable by eye — writing them down correctly is a real part of the work,
and the shape of `InsertRefines` in particular took a couple of attempts (the
table-full case has to be said, or the obligation is satisfiable by a
generator that silently drops inserts).

`Simulates` bundles them; `MilestoneTheorem` is the "one proof, every schema"
statement the whole project is arranged around. Which of these are proved is
recorded in `Templates.ArrayTableChecks`. -/

/-- **No traps.** The generated operations never raise `Err.oob`, the C
subset's single partial operation — nor anything else.

Stated as "returns `.ok`" rather than "≠ `.error .oob`" because that is
stronger and just as easy to use: it also rules out the structural errors,
which for generated code should be unreachable by construction. -/
def NoTrapFind (s : Schema) : Prop :=
  ∀ (m : Mem) (pk : Schema.Field) (k : Interface.Key),
    Schema.wf s = true → Schema.pkey? s = some pk → k.ty = pk.ty →
    RepInv s m.glb →
    ∃ r, call s m (Schema.names s).find [k.toValue] = .ok r

def NoTrapInsert (s : Schema) : Prop :=
  ∀ (m : Mem) (pk : Schema.Field) (k : Interface.Key) (vs : List Value),
    Schema.wf s = true → Schema.pkey? s = some pk → k.ty = pk.ty →
    RepInv s m.glb → vs.length = (Schema.valFields s).length →
    ∃ r, call s m (Schema.names s).insert (k.toValue :: vs) = .ok r

def NoTrapErase (s : Schema) : Prop :=
  ∀ (m : Mem) (pk : Schema.Field) (k : Interface.Key),
    Schema.wf s = true → Schema.pkey? s = some pk → k.ty = pk.ty →
    RepInv s m.glb →
    ∃ r, call s m (Schema.names s).erase [k.toValue] = .ok r

/-- Split into one clause per operation so that they can be discharged
independently — `find` is provable now, the writers need more. Each carries
the key-type precondition for the same reason `FindCorrect` does. -/
def NoTrap (s : Schema) : Prop :=
  NoTrapFind s ∧ NoTrapInsert s ∧ NoTrapErase s

/-- **`find` agrees with the abstraction.** It returns a pointer to a slot, or
`NULL`, and it is a pointer exactly when the key is present.

The `_at != NULL` guard in `insert` and `erase` consumes this: a non-null
result is a live slot, which is what makes every subsequent access through it
safe. -/
def FindCorrect (s : Schema) : Prop :=
  ∀ (m : Mem) (pk : Schema.Field) (k : Interface.Key),
    Schema.wf s = true → Schema.pkey? s = some pk →
    -- Without this the statement is *false*: `evalBin .eq` is defined only on
    -- matching scalar constructors, so searching a `u64`-keyed table with a
    -- `bool` key raises `typeErr` rather than reporting a miss.
    k.ty = pk.ty →
    RepInv s m.glb →
    ∃ r : Option Nat,
      call s m (Schema.names s).find [k.toValue]
          = .ok (m, some (match r with
                          | some i => .ptr ⟨.glob (Schema.names s).storage, [.idx i]⟩
                          | none   => .null))
      ∧ (r.isSome ↔ (absOf s m.glb k).isSome)

/-- **`insert` refines `Abs.insert`.**

Two cases, and the second is the one that keeps this honest: when the table is
full *and* the key is absent, the operation reports failure and must have
changed nothing. Without that clause a generator that quietly did nothing would
satisfy the first clause vacuously. -/
def InsertRefines (s : Schema) : Prop :=
  ∀ (m m' : Mem) (pk : Schema.Field) (k : Interface.Key) (vs : List Value)
    (b : Bool),
    Schema.wf s = true → Schema.pkey? s = some pk → k.ty = pk.ty →
    RepInv s m.glb →
    vs.length = (Schema.valFields s).length →
    call s m (Schema.names s).insert (k.toValue :: vs) = .ok (m', some (.bool b)) →
    (b = true  → absOf s m'.glb = Interface.Abs.insert (absOf s m.glb) k vs)
    ∧ (b = false → m' = m ∧ absOf s m.glb k = none)

/-- **`erase` refines `Abs.erase`.**

The `b = false` case needs no separate treatment: erasing an absent key is
`Interface.Abs.erase_of_absent`, so both branches land on the same equation. -/
def EraseRefines (s : Schema) : Prop :=
  ∀ (m m' : Mem) (pk : Schema.Field) (k : Interface.Key) (b : Bool),
    Schema.wf s = true → Schema.pkey? s = some pk → k.ty = pk.ty →
    RepInv s m.glb →
    call s m (Schema.names s).erase [k.toValue] = .ok (m', some (.bool b)) →
    absOf s m'.glb = Interface.Abs.erase (absOf s m.glb) k
    ∧ (b = true ↔ (absOf s m.glb k).isSome)

/-- **The invariant survives.** Without this the other obligations only apply
to the first operation, and the whole thing says nothing about a table in use. -/
def RepInvPreserved (s : Schema) : Prop :=
  ∀ (m m' : Mem) (pk : Schema.Field) (k : Interface.Key) (vs : List Value)
    (r : Option Value),
    Schema.wf s = true → Schema.pkey? s = some pk → k.ty = pk.ty →
    RepInv s m.glb →
    vs.length = (Schema.valFields s).length →
    (call s m (Schema.names s).insert (k.toValue :: vs) = .ok (m', r) → RepInv s m'.glb)
    ∧ (call s m (Schema.names s).erase [k.toValue] = .ok (m', r) → RepInv s m'.glb)

/-- **The generated table is a correct map**, in the sense of
`Interface.MapLaws`, under the abstraction `absOf`. -/
def Simulates (s : Schema) : Prop :=
  NoTrap s ∧ FindCorrect s ∧ InsertRefines s ∧ EraseRefines s ∧ RepInvPreserved s

/-- **The theorem this project exists to prove**: one proof, every schema.

Not "a proof per generated instance" — that is the distinction between AMCC and
a code generator with a test suite, and it is why `Simulates` is quantified
outside rather than inside. -/
def MilestoneTheorem : Prop := ∀ s : Schema, Schema.wf s = true → Simulates s

/-- The generator emits code the C subset accepts, for every well-formed
schema. Independent of `MilestoneTheorem`, and a prerequisite for it: an
ill-formed program has no guaranteed semantics to simulate anything.

**Proved**: `Templates.ArrayTable.genWellFormed` in `ArrayTableWf.lean`. -/
def GenWellFormed : Prop :=
  ∀ s : Schema, Schema.wf s = true → CSubset.Wf.check (genC s) = []

end ArrayTable
end Templates

import Amcc.CSubset.Value

/-!
# AMCC — Phase 3: the abstract map interface

The specification a generated table is proved to implement.

This is the half of the deliverable that is not C. A generated table is only
useful to someone else if what it guarantees is written down in a form they can
read and cite, and `MapLaws` is that form for a keyed table: three operations
and the four equations relating them, stated in Lean and independent of any
implementation.

**Nothing upstream supplies this.** `amc` generates the code and states no laws
about it, so `MapLaws` is AMCC's own abstraction rather than something adopted.
It is deliberately minimal — a starting point, not the finished interface. The
growth path is in `docs/PLAN.md`: traversal laws (because `amc` generates a
`_curs` for every access pattern, and nothing here yet says anything about
iteration order) and a fallible insert (because allocation can fail).

## Shape

`MapLaws M` is a *bundle*: the three operations plus the four equations
relating them. Bundling rather than using a type class is deliberate — a
generated table is not a canonical instance of anything, and a schema produces
a different one each time, so there is nothing for instance resolution to find.
A template's correctness theorem produces a `MapLaws` value, and a consumer
takes one as a parameter.

Four laws, no more: they are what any keyed map must satisfy, and each is
discharged for `AbsTable` below in one line. Anything harder to prove would be
a sign the interface, not the implementation, is wrong. Laws for the access
patterns `amc` also generates — ordered iteration, group-by — are additions to
make, not omissions to excuse; see `docs/PLAN.md`.
-/

namespace Interface

open CSubset

/-- The scalar fragment of `Value` — all a primary key can be.

A separate type rather than a predicate on `Value` because it buys
`DecidableEq` for free: `Value` has two nested recursive occurrences and Lean's
deriving handler cannot see through them, whereas `Key` is flat. Keys need
decidable equality (every law below branches on `k' = k`); stored values do
not. -/
inductive Key where
  | u8   : UInt8 → Key
  | u32  : UInt32 → Key
  | u64  : UInt64 → Key
  | bool : Bool → Key
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The scalar type a key stands at.

`CSubset.evalBin .eq` is defined only on matching scalar constructors, so a
comparison against a key of the wrong type does not evaluate to `false` — it
raises `typeErr`. Anything that compares keys therefore has to know this. -/
def Key.ty : Key → CSubset.ScalarTy
  | .u8 _   => .u8
  | .u32 _  => .u32
  | .u64 _  => .u64
  | .bool _ => .bool

def Key.toValue : Key → Value
  | .u8 a   => .u8 a
  | .u32 a  => .u32 a
  | .u64 a  => .u64 a
  | .bool b => .bool b

/-- `none` on an aggregate or a pointer, which the schema checker prevents a
primary key from being. -/
def Key.ofValue? : Value → Option Key
  | .u8 a   => some (.u8 a)
  | .u32 a  => some (.u32 a)
  | .u64 a  => some (.u64 a)
  | .bool b => some (.bool b)
  | _       => none

/-- checked by: `lake build` -/
theorem Key.ofValue_toValue (k : Key) : Key.ofValue? k.toValue = some k := by
  cases k <;> rfl

/-- checked by: `lake build` -/
theorem Key.toValue_inj {k k' : Key} (h : k.toValue = k'.toValue) : k = k' := by
  cases k <;> cases k' <;> simp_all [Key.toValue]

/-! ## The reference implementation

A partial function. This is the *meaning* a table is proved to have, not a data
structure anyone runs — so it is chosen for how easily the laws fall out, and
they fall out by `simp`. -/

/-- The abstract state of a keyed table: key ↦ the tuple of its value fields. -/
abbrev AbsTable := Key → Option (List Value)

namespace Abs

def empty : AbsTable := fun _ => none

def find (m : AbsTable) (k : Key) : Option (List Value) := m k

def insert (m : AbsTable) (k : Key) (vs : List Value) : AbsTable :=
  fun k' => if k' = k then some vs else m k'

def erase (m : AbsTable) (k : Key) : AbsTable :=
  fun k' => if k' = k then none else m k'

end Abs

/-! ## The laws -/

/-- What it means to be a correct keyed map.

The `find`/`insert`/`erase` fields are the operations; the four that follow are
the whole specification. A template's milestone theorem is a term of this type
built from the generated C's behaviour. -/
structure MapLaws (M : Type) where
  find   : M → Key → Option (List Value)
  insert : M → Key → List Value → M
  erase  : M → Key → M
  /-- What you put in is what you get out. -/
  find_insert_self : ∀ m k vs, find (insert m k vs) k = some vs
  /-- Inserting one key disturbs no other — the frame law. -/
  find_insert_ne   : ∀ m k k' vs, k' ≠ k → find (insert m k vs) k' = find m k'
  /-- What you erase is gone. -/
  find_erase_self  : ∀ m k, find (erase m k) k = none
  /-- Erasing one key disturbs no other. -/
  find_erase_ne    : ∀ m k k', k' ≠ k → find (erase m k) k' = find m k'

/-- The reference instance. Each law is one `simp`, which is the point: if a
law were hard here, it would be the wrong law.

checked by: `lake build` -/
def absLaws : MapLaws AbsTable where
  find   := Abs.find
  insert := Abs.insert
  erase  := Abs.erase
  find_insert_self := by intros; simp [Abs.find, Abs.insert]
  find_insert_ne   := by intro _ _ _ _ h; simp [Abs.find, Abs.insert, h]
  find_erase_self  := by intros; simp [Abs.find, Abs.erase]
  find_erase_ne    := by intro _ _ _ h; simp [Abs.find, Abs.erase, h]

/-- Erasing a key that is absent changes nothing — needed because the generated
`erase` returns `false` and leaves the store alone in that case, and the
simulation theorem has to say what abstract step that corresponds to.

checked by: `lake build` -/
theorem Abs.erase_of_absent {m : AbsTable} {k : Key} (h : m k = none) :
    Abs.erase m k = m := by
  funext k'
  simp only [Abs.erase]
  split
  · next hk => cases hk; exact h.symm
  · rfl

end Interface

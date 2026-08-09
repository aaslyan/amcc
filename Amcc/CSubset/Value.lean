import Amcc.CSubset.Syntax

/-!
# AMCC — Phase 1: values, access paths and stores

The state a C-subset program runs against. Three deliberate choices, each of
which pays for itself in the proofs downstream:

**Storage is structured, not bytes.** A `Value` is a word, a pointer, a struct
of named fields, or a list of elements — never an array of octets. Nothing in
the subset can observe layout (no casts at pointer type, no arithmetic on
pointers, no unions), so byte-level modelling would add padding and alignment
obligations that no theorem could ever use. If a later template genuinely needs
layout reasoning, that is a change to this file and nothing else.

**A pointer is an access path**, `Path` — a global's name plus a list of
resolved steps. This is exactly the "global-rooted" invariant from Phase 0's
obligation 7, made into a data type: a value of type `Path` cannot express a
null pointer, an interior offset, or a reference into a frame. Alias testing
between two paths is a prefix comparison, with no arithmetic in it.

**Frames hold only scalars and pointers.** `Store.loc` maps names to values of
`ValTy`, so a local has no interior structure to index into. Together with the
absence of `&local`, that is what makes a local assignment observably local.

Struct fields are represented with the same `Env` type as a frame, so the two
update lemmas proved once for `Env` serve both.
-/

namespace CSubset

/-! ## Access paths -/

/-- One step of an access path. Array steps carry a *resolved* index: bounds
are checked when the step is built (`Eval.resolve`), not when it is followed,
which is what makes `&a[i]` trap on a bad `i` rather than producing a pointer
that traps later. -/
inductive PathStep where
  | fld : Ident → PathStep
  | idx : Nat → PathStep
  deriving DecidableEq, Repr, Inhabited, BEq

/-- What an access path is rooted at.

Originally this was just a global's name, which made *every* pointer point at
statically declared storage and forced every table to have a capacity fixed at
compile time. That restriction is gone: a path may now root at a **heap
block**, identified by the number it was allocated under.

Block identity is a `Nat`, not an address. Nothing in the language can compute
one, compare it arithmetically, or forge it — the only way to obtain a block
root is from an allocation that succeeded. Freeing removes the block from the
heap, so a stale path stops resolving rather than silently reading whatever
moved in. -/
inductive Root where
  /-- Statically declared storage; outlives every frame. -/
  | glob : Ident → Root
  /-- A heap block, by the identity it was allocated under. -/
  | blk  : Nat → Root
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A rooted access path — the runtime meaning of a pointer.

Still non-dangling *by construction* in the sense that matters: a `Path` names
an object or it names a block that has been freed, and the latter is a
distinguishable error rather than undefined behaviour. -/
structure Path where
  root  : Root
  steps : List PathStep
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Two paths denote overlapping storage exactly when one refines the other.
No arithmetic, no aliasing analysis — a prefix test. -/
def Path.overlaps (p q : Path) : Bool :=
  p.root == q.root && (p.steps.isPrefixOf q.steps || q.steps.isPrefixOf p.steps)

/-! ## Values -/

/-- Runtime values.

`u32`/`u64` are Lean's wrapping machine words, which is precisely C's defined
behaviour for `uint32_t`/`uint64_t`. There is no null pointer constructor —
`ptr` carries a `Path`, and every `Path` denotes an object. -/
inductive Value where
  | u32   : UInt32 → Value
  | u64   : UInt64 → Value
  | bool  : Bool → Value
  /-- The null pointer.

  Added because **allocation can fail**, and a language that models dynamic
  storage has to be able to say so. This is the one place the Phase 0 bet is
  deliberately weakened: dereferencing null is now a reachable error, so
  "exactly one partial operation" becomes three (out-of-range subscript, null
  dereference, use-after-free). All three remain *proof obligations on
  generated code* — the same discipline over a bigger surface, rather than a
  restriction that made real data structures inexpressible. -/
  | null  : Value
  | ptr   : Path → Value
  /-- Fields in declaration order. -/
  | strct : List (Ident × Value) → Value
  /-- Elements in index order. -/
  | arr   : List Value → Value
  deriving Repr, Inhabited, BEq

/-! ## Environments

A finite map keyed by identifier, backed by an association list — used both for
frames and globals, and for the fields of a struct value. Lookup and update
touch the *first* matching binding, so the lemmas below hold with no
distinctness side condition, and therefore before the well-formedness checker
has run. -/

abbrev Env := List (Ident × Value)

def Env.get? : Env → Ident → Option Value
  | [], _ => none
  | (k, v) :: rest, x => if k = x then some v else Env.get? rest x

/-- Update `x` if it is bound; leave the environment alone if it is not. The
domain is therefore invariant under `set`, which is why no frame, global, or
struct value ever gains or loses a name mid-run. -/
def Env.set : Env → Ident → Value → Env
  | [], _, _ => []
  | (k, w) :: rest, x, v => if k = x then (k, v) :: rest else (k, w) :: Env.set rest x v

/-- Reading back a name you just wrote gives what you wrote — provided the name
was there to begin with.

checked by: `lake build` -/
theorem Env.get?_set_self (e : Env) (x : Ident) (v : Value) :
    (e.set x v).get? x = (e.get? x).map (fun _ => v) := by
  induction e with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, w⟩ := hd
    by_cases h : k = x
    · simp [Env.set, Env.get?, h]
    · simp [Env.set, Env.get?, h, ih]

/-- Writing one name does not disturb any other. This is the frame lemma for
locals; the corresponding statement for globals is `Store.readPath_writePath_ne`
below, and it is the reason `Expr.addr` is barred from locals.

checked by: `lake build` -/
theorem Env.get?_set_ne (e : Env) {x y : Ident} (h : y ≠ x) (v : Value) :
    (e.set x v).get? y = e.get? y := by
  induction e with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, w⟩ := hd
    by_cases hk : k = x
    · subst hk
      simp [Env.set, Env.get?, Ne.symm h]
    · simp [Env.set, Env.get?, hk, ih]

/-- `set` never changes which names are bound.

checked by: `lake build` -/
theorem Env.isSome_get?_set (e : Env) (x y : Ident) (v : Value) :
    ((e.set x v).get? y).isSome = (e.get? y).isSome := by
  by_cases h : y = x
  · subst h; simp [Env.get?_set_self]
  · simp [Env.get?_set_ne e h]

/-! ## Reading and writing through a path -/

/-- Follow one step into a value. `none` means the step does not fit the
value's shape — a type error, which a well-formed program cannot produce — or
that an array index is out of range, which is the one genuine partiality. -/
def Value.getStep : Value → PathStep → Option Value
  | .strct fs, .fld f => Env.get? fs f
  | .arr vs,   .idx i => vs[i]?
  | _,         _      => none

/-- Replace what one step points at. Fails on the same conditions as
`getStep`, and in particular never grows an array or adds a field: the shape of
a value is fixed when it is created. -/
def Value.setStep : Value → PathStep → Value → Option Value
  | .strct fs, .fld f, w =>
      if (Env.get? fs f).isSome then some (.strct (Env.set fs f w)) else none
  | .arr vs, .idx i, w =>
      if i < vs.length then some (.arr (vs.set i w)) else none
  | _, _, _ => none

private theorem getElem?_set_self {α : Type _} :
    ∀ (l : List α) (i : Nat) (a : α), i < l.length → (l.set i a)[i]? = some a
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, i + 1, a, h => by
      have : i < xs.length := by simpa using h
      simpa using getElem?_set_self xs i a this

/-- One step of read-after-write.

checked by: `lake build` -/
theorem Value.getStep_setStep {v v' u : Value} {s : PathStep}
    (h : v.setStep s u = some v') : v'.getStep s = some u := by
  cases v <;> cases s <;> simp only [Value.setStep] at h <;>
    try exact Option.noConfusion h
  case strct.fld fs f =>
    by_cases hf : (Env.get? fs f).isSome = true
    · rw [if_pos hf] at h
      cases h
      simp only [Value.getStep, Env.get?_set_self]
      cases hg : Env.get? fs f with
      | none => rw [hg] at hf; simp at hf
      | some _ => simp
    · rw [if_neg hf] at h
      exact Option.noConfusion h
  case arr.idx vs i =>
    by_cases hi : i < vs.length
    · rw [if_pos hi] at h
      cases h
      simpa [Value.getStep] using getElem?_set_self vs i u hi
    · rw [if_neg hi] at h
      exact Option.noConfusion h

def Value.getPath : Value → List PathStep → Option Value
  | v, []      => some v
  | v, s :: ss => match v.getStep s with
                  | some v' => v'.getPath ss
                  | none    => none

def Value.setPath : Value → List PathStep → Value → Option Value
  | _, [],      w => some w
  | v, s :: ss, w =>
      match v.getStep s with
      | none    => none
      | some v' =>
        match v'.setPath ss w with
        | none     => none
        | some v'' => v.setStep s v''

/-- Read-after-write along a whole path.

checked by: `lake build` -/
theorem Value.getPath_setPath {w : Value} :
    ∀ {ss : List PathStep} {v v' : Value}, v.setPath ss w = some v' → v'.getPath ss = some w := by
  intro ss
  induction ss with
  | nil =>
    intro v v' h
    simp only [Value.setPath] at h
    cases h
    rfl
  | cons s ss ih =>
    intro v v' h
    simp only [Value.setPath] at h
    split at h
    · exact Option.noConfusion h
    · next v1 _ =>
      split at h
      · exact Option.noConfusion h
      · next v2 hr =>
        have hstep : v'.getStep s = some v2 := Value.getStep_setStep h
        simp only [Value.getPath, hstep]
        exact ih hr

/-! ## Stores -/

/-! ### The heap

Blocks keyed by identity. The same association-list discipline as `Env`, at
`Nat` keys — deliberately the same shape, so the two update lemmas read
identically and the frame reasoning below is uniform over roots. -/

abbrev Heap := List (Nat × Value)

def Heap.get? : Heap → Nat → Option Value
  | [], _ => none
  | (k, v) :: rest, b => if k = b then some v else Heap.get? rest b

/-- Update a block if it is live; leave the heap alone if it is not — so, as
with `Env.set`, the set of live blocks is invariant under `set`. -/
def Heap.set : Heap → Nat → Value → Heap
  | [], _, _ => []
  | (k, w) :: rest, b, v => if k = b then (k, v) :: rest else (k, w) :: Heap.set rest b v

theorem Heap.get?_set_self (h : Heap) (b : Nat) (v : Value) :
    (h.set b v).get? b = (h.get? b).map (fun _ => v) := by
  induction h with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, w⟩ := hd
    by_cases hk : k = b
    · simp [Heap.set, Heap.get?, hk]
    · simp [Heap.set, Heap.get?, hk, ih]

theorem Heap.get?_set_ne (h : Heap) {b c : Nat} (hne : c ≠ b) (v : Value) :
    (h.set b v).get? c = h.get? c := by
  induction h with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, w⟩ := hd
    by_cases hk : k = b
    · subst hk; simp [Heap.set, Heap.get?, Ne.symm hne]
    · simp [Heap.set, Heap.get?, hk, ih]

/-- The whole runtime state: statically declared globals, the current frame,
and the heap — plus the counter that supplies fresh block identities.

`next` is what makes a fresh block genuinely fresh: it only ever increases, so
an identity is never reissued and a path to a freed block can never be
resurrected by a later allocation. That is the property that turns
use-after-free from undefined behaviour into a detectable error. -/
structure Store where
  glb  : Env
  loc  : Env
  hp   : Heap
  /-- Next unused block identity. Monotone; never reissued. -/
  next : Nat
  deriving Repr, Inhabited

def Store.getLocal (σ : Store) (x : Ident) : Option Value := σ.loc.get? x

def Store.setLocal (σ : Store) (x : Ident) (v : Value) : Store :=
  { σ with loc := σ.loc.set x v }

/-! ### Resolving a root

The one place globals and heap blocks are treated differently. Everything
above this — paths, steps, read-after-write — is uniform over both. -/

def Store.rootVal (σ : Store) : Root → Option Value
  | .glob g => σ.glb.get? g
  | .blk b  => Heap.get? σ.hp b

def Store.setRoot (σ : Store) : Root → Value → Store
  | .glob g, v => { σ with glb := σ.glb.set g v }
  | .blk b,  v => { σ with hp := Heap.set σ.hp b v }

theorem Store.rootVal_setRoot_self (σ : Store) (r : Root) (v : Value) :
    (σ.setRoot r v).rootVal r = (σ.rootVal r).map (fun _ => v) := by
  cases r with
  | glob g => exact Env.get?_set_self σ.glb g v
  | blk b  => exact Heap.get?_set_self σ.hp b v

theorem Store.rootVal_setRoot_ne (σ : Store) {r r' : Root} (hne : r' ≠ r)
    (v : Value) : (σ.setRoot r v).rootVal r' = σ.rootVal r' := by
  cases r with
  | glob g =>
    cases r' with
    | glob g' => exact Env.get?_set_ne σ.glb (fun e => hne (by rw [e])) v
    | blk _   => rfl
  | blk b =>
    cases r' with
    | glob _  => rfl
    | blk b'  => exact Heap.get?_set_ne σ.hp (fun e => hne (by rw [e])) v

theorem Store.setRoot_loc (σ : Store) (r : Root) (v : Value) :
    (σ.setRoot r v).loc = σ.loc := by cases r <;> rfl

def Store.readPath (σ : Store) (p : Path) : Option Value :=
  match σ.rootVal p.root with
  | none   => none
  | some v => v.getPath p.steps

def Store.writePath (σ : Store) (p : Path) (w : Value) : Option Store :=
  match σ.rootVal p.root with
  | none => none
  | some v =>
    match v.setPath p.steps w with
    | none    => none
    | some v' => some (σ.setRoot p.root v')

/-! ### Allocation

The whole point of the heap. `allocBlock` is total — refusing an allocation is
the *caller's* decision, taken by consulting an allocator oracle, not
something the store model decides. That keeps the store a faithful record of
memory and leaves "malloc may return null" where it belongs: in the
semantics of the allocation statement. -/

/-- Allocate a block holding `v`, returning the store and a path to it.
The identity is `σ.next`, which is fresh by construction. -/
def Store.allocBlock (σ : Store) (v : Value) : Store × Path :=
  ({ σ with hp := (σ.next, v) :: σ.hp, next := σ.next + 1 }, ⟨.blk σ.next, []⟩)

/-- Free a block. The identity is *not* returned to the pool of fresh names,
so every path into it stays permanently unresolvable. -/
def Store.freeBlock (σ : Store) (b : Nat) : Store :=
  { σ with hp := σ.hp.filter (fun kv => !(kv.1 == b)) }

/-- A dynamically sized array value: `n` copies of `z`, with `n` a **runtime**
quantity. This is what the fixed-capacity design could not express — the size
lives in the value, not in the type. -/
def Value.arrOf (n : Nat) (z : Value) : Value := .arr (List.replicate n z)

/-! ### Memory that outlives a call

The state that persists across calls. It used to be just `Env` — the globals —
which is precisely why every table's storage had to be statically declared.
Now it carries the heap too, so what a program owns between calls is no longer
fixed when the program is written. -/

structure Mem where
  glb  : Env
  hp   : Heap
  next : Nat
  deriving Repr, Inhabited

def Mem.toStore (m : Mem) (loc : Env) : Store :=
  { glb := m.glb, loc := loc, hp := m.hp, next := m.next }

def Store.toMem (σ : Store) : Mem :=
  { glb := σ.glb, hp := σ.hp, next := σ.next }

@[simp] theorem Mem.toStore_toMem (m : Mem) (loc : Env) :
    (m.toStore loc).toMem = m := rfl

/-- Writing a global leaves the frame untouched. Trivial here — and trivial is
the point: it follows from `Store` having two independent components, which
follows from no pointer being able to name a local.

checked by: `lake build` -/
theorem Store.writePath_loc {σ σ' : Store} {p : Path} {w : Value}
    (h : σ.writePath p w = some σ') : σ'.loc = σ.loc := by
  simp only [Store.writePath] at h
  cases hv : σ.rootVal p.root with
  | none => simp [hv] at h
  | some v =>
    simp only [hv] at h
    cases hs : v.setPath p.steps w with
    | none => simp [hs] at h
    | some v' =>
      simp only [hs] at h
      cases h
      exact Store.setRoot_loc σ p.root v'

/-- Writing a local leaves the globals untouched.

checked by: `lake build` -/
theorem Store.setLocal_glb (σ : Store) (x : Ident) (v : Value) :
    (σ.setLocal x v).glb = σ.glb := rfl

/-- Reading back a path you just wrote gives what you wrote.

checked by: `lake build` -/
theorem Store.readPath_writePath_self {σ σ' : Store} {p : Path} {w : Value}
    (h : σ.writePath p w = some σ') : σ'.readPath p = some w := by
  simp only [Store.writePath] at h
  cases hv : σ.rootVal p.root with
  | none => simp [hv] at h
  | some v =>
    simp only [hv] at h
    cases hs : v.setPath p.steps w with
    | none => simp [hs] at h
    | some v' =>
      simp only [hs] at h
      cases h
      simp only [Store.readPath, Store.rootVal_setRoot_self, hv, Option.map_some]
      exact Value.getPath_setPath hs

/-- Writing under one root leaves every other root alone.

checked by: `lake build` -/
theorem Store.readPath_writePath_ne {σ σ' : Store} {p q : Path} {w : Value}
    (hne : q.root ≠ p.root) (h : σ.writePath p w = some σ') :
    σ'.readPath q = σ.readPath q := by
  simp only [Store.writePath] at h
  cases hv : σ.rootVal p.root with
  | none => simp [hv] at h
  | some v =>
    simp only [hv] at h
    cases hs : v.setPath p.steps w with
    | none => simp [hs] at h
    | some v' =>
      simp only [hs] at h
      cases h
      simp only [Store.readPath, Store.rootVal_setRoot_ne _ hne]

/-! ## Zero initialisation

C zero-initialises objects with static storage duration, so the initial store
is determined by the program's declarations alone. The recursion below is
structural because Phase 0's obligation 2 makes struct nesting
backward-referencing: each struct's zero value is built from the zero values of
the structs *already* in the table. That is the obligation earning its keep —
without it this function would need fuel. -/

/-- The zero value at a storage type, given zero values for the structs
declared so far.

Pointer type zeroes to `NULL`, which is what C guarantees for a pointer with
static storage duration. This used to be `none` — there was no null pointer,
so a pointer had no zero, so a global could not contain one. That restriction
is gone, and with it the reason a list could not be rooted in a global head
pointer. -/
def zeroOfTy (tbl : List (Ident × Value)) : Ty → Option Value
  | .scalar .u32  => some (.u32 0)
  | .scalar .u64  => some (.u64 0)
  | .scalar .bool => some (.bool false)
  | .ptr _        => some .null
  | .strct n      => Env.get? tbl n
  | .arr t n      => (zeroOfTy tbl t).map (fun v => .arr (List.replicate n v))

/-- Zero values for a program's structs, in declaration order. -/
def zeroTable (structs : List StructDef) : Env :=
  structs.foldl
    (fun tbl sd =>
      match sd.fields.mapM (fun fv => (zeroOfTy tbl fv.2).map (fun v => (fv.1, v))) with
      | some fvs => tbl ++ [(sd.name, .strct fvs)]
      | none     => tbl)
    []

/-- The initial global environment. `none` when a global's type has no zero
value — which the well-formedness checker rules out ahead of time. -/
def initGlobals (p : Program) : Option Env :=
  let tbl := zeroTable p.structs
  p.globals.mapM (fun g => (zeroOfTy tbl g.ty).map (fun v => (g.name, v)))

end CSubset

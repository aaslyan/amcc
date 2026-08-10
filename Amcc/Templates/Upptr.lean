import Amcc.Dmmeta
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.Templates.ArrayTableWf

/-!
# AMCC — the `Upptr` template

The second operation template over the ctype model, and the first one whose
whole content is a **pointer field**: `dmmeta.reftype Upptr` is a cached
reference from a child row to its parent row.

## What `amc` does

`cpp/amc/upptr.cpp` is nineteen lines. It declares the member —

```cpp
InsVar(R, field.p_ctype, "$Cpptype*", "$name", "", "reference to parent row");
```

— and generates one function, `Init`, whose entire body is
`$parname.$name = NULL;`. There is no getter: the member is public, and the
cross-reference code assigns it directly (`row.p_target = p_target;` in
`targsrc_XrefMaybe`, quoted in `docs/DIVERGENCE.md` §1.1).

## What AMCC emits, and why it is four functions rather than one

The member is already there — `Dmmeta.fieldTy` lowers `Upptr` to
`.ptr (.strct arg)`, so `Dmmeta.structOf` puts it in the struct and C code can
still write `row->p_parent` directly. Nothing about `amc`'s surface is lost.

What is *added* is that each of the three things C code would otherwise do by
hand becomes a function:

```c
void        C_f_Init(C *row);          /* row->f = NULL;        — amc's Init */
Parent*     C_f_Get(C *row);           /* return row->f;                     */
void        C_f_Set(C *row, Parent *p);/* row->f = p;   — what XrefMaybe does */
bool        C_f_Q(C *row);             /* return row->f != NULL;             */
```

The reason is the project's, not `amc`'s: a function is where a proof
obligation can be attached. `upptr_get_set` below says a `Get` after a `Set`
returns exactly what was set — the read-back law — and `upptr_frame` says a
`Set` through one pointer cannot be observed through a non-overlapping one.
Neither statement can be made about a bare member assignment, because there is
no generated function to make it about. This is a divergence in surface and it
is recorded in `docs/DIVERGENCE.md`.

`Q` is the C form of `cget.cpp`'s `$FieldQ`, which for a pointer field returns
the pointer in boolean context.

## The one precondition

Every one of the four dereferences `row`. In the C subset that is a partial
operation twice over — `nullDeref` if the argument is `NULL`, `useAfterFree` if
its root block is gone — so every theorem below carries `RowAt`, which says the
argument really names a row that has the field. That is the whole obligation,
and it is exactly `amc`'s unstated contract that a caller must not pass a
dangling child row.
-/

namespace Templates
namespace Upptr

open CSubset

/-! ## Generated names -/

/-- The row parameter every accessor takes. -/
def parRow : Ident := "row"
/-- The new value `Set` takes. -/
def parP : Ident := "p"

structure Names where
  init : Ident
  get  : Ident
  set  : Ident
  test : Ident
  deriving Repr, Inhabited, DecidableEq

/-- `amc`'s naming, in C: the ctype, the field, the operation. -/
def names (child fld : Ident) : Names where
  init := child ++ "_" ++ fld ++ "_Init"
  get  := child ++ "_" ++ fld ++ "_Get"
  set  := child ++ "_" ++ fld ++ "_Set"
  test := child ++ "_" ++ fld ++ "_Q"

/-- `row->f` — the up-pointer, as an lvalue. -/
def upFld (fld : Ident) : LVal := .fld (.deref parRow) fld

/-! ## The generated code -/

/-- ```c
void C_f_Init(C *row) { row->f = NULL; }
```
`amc`'s `tfunc_Upptr_Init`, with the parent named explicitly because our
`NULL` carries its pointee type. -/
def initDef (nm : Names) (child fld parent : Ident) : FunDef where
  name   := nm.init
  params := [(parRow, .ptr (.strct child))]
  ret    := none
  locals := []
  body   := .assign (upFld fld) (.null (.strct parent))

/-- ```c
Parent* C_f_Get(C *row) { return row->f; }
``` -/
def getDef (nm : Names) (child fld parent : Ident) : FunDef where
  name   := nm.get
  params := [(parRow, .ptr (.strct child))]
  ret    := some (.ptr (.strct parent))
  locals := []
  body   := .ret (some (.rd (upFld fld)))

/-- ```c
void C_f_Set(C *row, Parent *p) { row->f = p; }
```
The assignment `XrefMaybe` performs inline. -/
def setDef (nm : Names) (child fld parent : Ident) : FunDef where
  name   := nm.set
  params := [(parRow, .ptr (.strct child)), (parP, .ptr (.strct parent))]
  ret    := none
  locals := []
  body   := .assign (upFld fld) (.rd (.var parP))

/-- ```c
bool C_f_Q(C *row) { return row->f != NULL; }
``` -/
def testDef (nm : Names) (child fld parent : Ident) : FunDef where
  name   := nm.test
  params := [(parRow, .ptr (.strct child))]
  ret    := some (.scalar .bool)
  locals := []
  body   := .ret (some (.bin .ne (.rd (upFld fld)) (.null (.strct parent))))

/-- The four accessors for one `Upptr` field. -/
def defsFor (child fld parent : Ident) : List FunDef :=
  let nm := names child fld
  [ initDef nm child fld parent
  , getDef nm child fld parent
  , setDef nm child fld parent
  , testDef nm child fld parent ]

/-! ## Assembling a program -/

/-- Every `Upptr` field in the schema, as `(child ctype, field)`. -/
def upFields (d : Dmmeta.Db) : List (Ident × Dmmeta.Field) :=
  d.ctypes.flatMap (fun c =>
    c.fields.filterMap (fun f =>
      if f.reftype == .Upptr then some (c.name, f) else none))

/-- **The generator.** The layout, plus four accessors per `Upptr` field.

Emitted over `Dmmeta.genLayout` rather than as a standalone program because an
up-pointer has no storage of its own: it is a field of a struct the layout pass
already emits, which is exactly why `amc` gets away with nineteen lines. -/
def genUpptr (d : Dmmeta.Db) : Program :=
  { structs := Dmmeta.genStructs d
  , globals := Dmmeta.genGlobals d
  , funs    := (upFields d).flatMap (fun cf => defsFor cf.1 cf.2.name cf.2.arg) }

/-! ## Reading memory between calls

`readMem` and the lookup and call lemmas used below live in `CSubset.Calls`:
they say nothing about up-pointers, and the `Llist` template needs the same
ones. -/

/-- Where the up-pointer lives, given a pointer to the row. -/
def upPath (q : Path) (fld : Ident) : Path := ⟨q.root, q.steps ++ [.fld fld]⟩

/-! ## Looking a generated function up

The accessors are emitted as one block of four per `Upptr` field, so the only
thing standing between "this definition is in the program" and "this name
resolves to it" is `CSubset.lookupFun_of_mem` plus the two facts below. -/

/-- The four accessors of an `Upptr` field are in the generated program. -/
theorem defsFor_subset {d : Dmmeta.Db} {c : Dmmeta.Ctype} {f : Dmmeta.Field}
    (hc : c ∈ d.ctypes) (hf : f ∈ c.fields) (hr : f.reftype = .Upptr) :
    ∀ fd ∈ defsFor c.name f.name f.arg, fd ∈ (genUpptr d).funs := by
  intro fd hfd
  refine List.mem_flatMap.mpr ⟨(c.name, f), ?_, hfd⟩
  refine List.mem_flatMap.mpr ⟨c, hc, ?_⟩
  exact List.mem_filterMap.mpr ⟨f, hf, by rw [hr]; rfl⟩

/-- **Acceptance discharges the resolution hypothesis.**

Every law below assumes `lookupFun p nm.x = .ok (xDef …)`. That hypothesis is
satisfiable exactly when the generated function names are distinct, and
`CSubset.Wf.check` is where distinctness is decided — obligation 1, the
`distinct "function"` clause. So a program the C subset accepts always
supplies it, via `CSubset.lookupFun_of_mem`.

The schema-level guard that makes acceptance reachable is new in
`Dmmeta.check`: `c ++ "_" ++ f` is **not** injective in the pair — ctype `a`
with field `b_c` and ctype `a_b` with field `c` both qualify to `a_b_c` — so
without it a legal schema could emit two functions with one name, and every
law here would be vacuous for that schema with nothing to notice.

checked by: `lake build` -/
theorem lookups_of_wf {d : Dmmeta.Db}
    (h : CSubset.Wf.check (genUpptr d) = []) :
    ((genUpptr d).funs.map FunDef.name).Pairwise (· ≠ ·) := by
  simp only [CSubset.Wf.check, List.append_eq_nil_iff] at h
  exact CSubset.dups_eq_nil_iff.mp
    (List.map_eq_nil_iff.mp h.1.2)

/-! ## The laws

Each is stated against an arbitrary program in which the name resolves to the
definition — the same shape the array table's body lemmas take, and for the
same reason: what the function does is independent of what else the program
contains. `lookupFun_of_mem` above turns "the schema declares this field" into
that hypothesis.

`RowAt` is the shared precondition: the argument names a row that has the
field. It is what discharges both pointer traps, and it is `amc`'s unwritten
contract made explicit. -/

/-- The argument names a row whose up-pointer field currently holds `v`. -/
def RowAt (m : Mem) (q : Path) (fld : Ident) (v : Value) : Prop :=
  readMem m (upPath q fld) = some v

section Laws

variable {p : Program} {m : Mem} {q : Path} {child fld parent : Ident}

/-- Resolving `row->f` when `row` really names a row that has `f`. Both of the
subset's pointer traps are discharged here: `nullDeref` because the local holds
a `ptr` and not `.null`, `useAfterFree` because the root still resolves — and
the root resolves *because* the field does, which is the whole content of
`RowAt`. -/
theorem resolve_up {σ : Store} {v : Value}
    (hloc : σ.getLocal parRow = some (.ptr q))
    (hread : σ.readPath (upPath q fld) = some v) :
    resolve σ (upFld fld) = .ok (.glb (upPath q fld)) := by
  simp only [upPath] at hread
  obtain ⟨w, hw⟩ : ∃ w, σ.rootVal q.root = some w := by
    cases hr : σ.rootVal q.root with
    | none => simp [Store.readPath, hr] at hread
    | some w => exact ⟨w, rfl⟩
  simp only [upFld, resolve, hloc, hw, bind, Except.bind, upPath, hread]

/-! None of the four accessors calls anything, so any positive depth budget
runs the body; `callFun_normal` / `callFun_ret` in `CSubset.Calls` do the
rest. -/

/-- Writing through `row->f`. The write cannot fail — `writePath_isSome` — for
exactly the reason the read cannot: the field is there. -/
theorem exec_assign_up {callee} {σ : Store} {v w : Value} {e : Expr}
    (hloc : σ.getLocal parRow = some (.ptr q))
    (hread : σ.readPath (upPath q fld) = some v)
    (he : evalExpr σ e = .ok w) :
    ∃ σ', execAt p callee (.assign (upFld fld) e) σ = .ok (σ', .normal)
      ∧ σ.writePath (upPath q fld) w = some σ' := by
  obtain ⟨σ', hw⟩ := Store.writePath_isSome (w := w) hread
  refine ⟨σ', ?_, hw⟩
  simp only [execAt, resolve_up hloc hread, he, writeLoc, hw, bind, Except.bind]

/-! ### `Get` -/

/-- **`Get` returns the up-pointer, and changes nothing.**

checked by: `lake build` -/
theorem get_correct {v : Value}
    (hlook : lookupFun p (names child fld).get
      = .ok (getDef (names child fld) child fld parent))
    (hn : ∃ n, p.funs.length = n + 1) (hrow : RowAt m q fld v) :
    callFun p m (names child fld).get [.ptr q] = .ok (m, some v) := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q)]).getLocal parRow
      = some (.ptr q) := rfl
  have hread : (m.toStore [(parRow, Value.ptr q)]).readPath (upPath q fld)
      = some v := by rw [readMem_toStore]; exact hrow
  have hbody : execAt p (execStmt p n)
      (getDef (names child fld) child fld parent).body
      (m.toStore [(parRow, Value.ptr q)])
      = .ok (m.toStore [(parRow, Value.ptr q)], .ret (some v)) := by
    simp only [getDef, execAt, evalExpr, resolve_up hloc hread, readLoc, hread,
      bind, Except.bind]
  have := callFun_ret (p := p) (m := m) (fd := getDef (names child fld) child fld parent)
    (args := [Value.ptr q]) (frame := [(parRow, Value.ptr q)]) hlook hn rfl hbody
  simpa [getDef] using this

/-! ### `Init` and `Set` -/

/-- **`Init` nulls the up-pointer**, and touches nothing that does not overlap
it.

checked by: `lake build` -/
theorem init_correct {v : Value}
    (hlook : lookupFun p (names child fld).init
      = .ok (initDef (names child fld) child fld parent))
    (hn : ∃ n, p.funs.length = n + 1) (hrow : RowAt m q fld v) :
    ∃ m', callFun p m (names child fld).init [.ptr q] = .ok (m', none)
      ∧ RowAt m' q fld .null
      ∧ ∀ r, (upPath q fld).overlaps r = false → readMem m' r = readMem m r := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q)]).getLocal parRow
      = some (.ptr q) := rfl
  have hread : (m.toStore [(parRow, Value.ptr q)]).readPath (upPath q fld)
      = some v := by rw [readMem_toStore]; exact hrow
  obtain ⟨σ', hbody, hwr⟩ :=
    exec_assign_up (p := p) (callee := execStmt p n) (w := Value.null)
      (e := .null (.strct parent)) hloc hread rfl
  refine ⟨σ'.toMem, ?_, ?_, ?_⟩
  · have := callFun_normal (p := p) (m := m) (fd := initDef (names child fld) child fld parent)
      (args := [Value.ptr q]) (frame := [(parRow, Value.ptr q)]) hlook hn rfl
      (by simpa [initDef] using hbody)
    simpa [initDef] using this
  · show readMem σ'.toMem _ = _
    rw [readMem_toMem]
    exact Store.readPath_writePath_self hwr
  · intro r hr
    rw [readMem_toMem, ← readMem_toStore m [(parRow, Value.ptr q)]]
    exact Store.readPath_writePath_disjoint hwr hr

/-- **Read-back: a `Get` after a `Set` returns exactly what was set**, and the
`Set` is invisible at every path that does not overlap the field.

This is the law the whole template exists for. `amc` cannot state it, because
in `amc` there is no `Set` — the cross-reference code assigns the member
inline.

checked by: `lake build` -/
theorem get_set {v pv : Value}
    (hlookS : lookupFun p (names child fld).set
      = .ok (setDef (names child fld) child fld parent))
    (hlookG : lookupFun p (names child fld).get
      = .ok (getDef (names child fld) child fld parent))
    (hn : ∃ n, p.funs.length = n + 1) (hrow : RowAt m q fld v) :
    ∃ m', callFun p m (names child fld).set [.ptr q, pv] = .ok (m', none)
      ∧ callFun p m' (names child fld).get [.ptr q] = .ok (m', some pv)
      ∧ ∀ r, (upPath q fld).overlaps r = false → readMem m' r = readMem m r := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q), (parP, pv)]).getLocal parRow
      = some (.ptr q) := rfl
  have hlocP : (m.toStore [(parRow, Value.ptr q), (parP, pv)]).getLocal parP
      = some pv := rfl
  have hread : (m.toStore [(parRow, Value.ptr q), (parP, pv)]).readPath
      (upPath q fld) = some v := by rw [readMem_toStore]; exact hrow
  obtain ⟨σ', hbody, hwr⟩ :=
    exec_assign_up (p := p) (callee := execStmt p n) (w := pv)
      hloc hread (read_local' hlocP)
  have hrow' : RowAt σ'.toMem q fld pv := by
    show readMem σ'.toMem _ = _
    rw [readMem_toMem]
    exact Store.readPath_writePath_self hwr
  refine ⟨σ'.toMem, ?_, get_correct hlookG ⟨n, hn⟩ hrow', ?_⟩
  · have := callFun_normal (p := p) (m := m) (fd := setDef (names child fld) child fld parent)
      (args := [Value.ptr q, pv]) (frame := [(parRow, Value.ptr q), (parP, pv)])
      hlookS hn rfl (by simpa [setDef] using hbody)
    simpa [setDef] using this
  · intro r hr
    rw [readMem_toMem, ← readMem_toStore m [(parRow, Value.ptr q), (parP, pv)]]
    exact Store.readPath_writePath_disjoint hwr hr

/-! ### `Q` -/

/-- **`Q` is the null test on what `Get` returns**, in both directions.

Two theorems rather than one because `evalBin .ne` is defined on
pointer-against-`NULL` and on `NULL`-against-`NULL`, and on nothing else — so
"the field holds a pointer or `NULL`" is a real precondition, not decoration.

checked by: `lake build` -/
theorem test_null
    (hlook : lookupFun p (names child fld).test
      = .ok (testDef (names child fld) child fld parent))
    (hn : ∃ n, p.funs.length = n + 1) (hrow : RowAt m q fld .null) :
    callFun p m (names child fld).test [.ptr q] = .ok (m, some (.bool false)) := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q)]).getLocal parRow
      = some (.ptr q) := rfl
  have hread : (m.toStore [(parRow, Value.ptr q)]).readPath (upPath q fld)
      = some .null := by rw [readMem_toStore]; exact hrow
  have hbody : execAt p (execStmt p n)
      (testDef (names child fld) child fld parent).body
      (m.toStore [(parRow, Value.ptr q)])
      = .ok (m.toStore [(parRow, Value.ptr q)], .ret (some (.bool false))) := by
    simp only [testDef, execAt, evalExpr, resolve_up hloc hread, readLoc, hread,
      bind, Except.bind, evalBin]
  have := callFun_ret (p := p) (m := m) (fd := testDef (names child fld) child fld parent)
    (args := [Value.ptr q]) (frame := [(parRow, Value.ptr q)]) hlook hn rfl hbody
  simpa [testDef] using this

/-- checked by: `lake build` -/
theorem test_ptr {r : Path}
    (hlook : lookupFun p (names child fld).test
      = .ok (testDef (names child fld) child fld parent))
    (hn : ∃ n, p.funs.length = n + 1) (hrow : RowAt m q fld (.ptr r)) :
    callFun p m (names child fld).test [.ptr q] = .ok (m, some (.bool true)) := by
  obtain ⟨n, hn⟩ := hn
  have hloc : (m.toStore [(parRow, Value.ptr q)]).getLocal parRow
      = some (.ptr q) := rfl
  have hread : (m.toStore [(parRow, Value.ptr q)]).readPath (upPath q fld)
      = some (.ptr r) := by rw [readMem_toStore]; exact hrow
  have hbody : execAt p (execStmt p n)
      (testDef (names child fld) child fld parent).body
      (m.toStore [(parRow, Value.ptr q)])
      = .ok (m.toStore [(parRow, Value.ptr q)], .ret (some (.bool true))) := by
    simp only [testDef, execAt, evalExpr, resolve_up hloc hread, readLoc, hread,
      bind, Except.bind, evalBin]
  have := callFun_ret (p := p) (m := m) (fd := testDef (names child fld) child fld parent)
    (args := [Value.ptr q]) (frame := [(parRow, Value.ptr q)]) hlook hn rfl hbody
  simpa [testDef] using this

end Laws

/-! ## Checked

The generator exercised on the smallest schema that has an `Upptr` at all: a
parent ctype and a child that points up at it. Computational, as `Pool`'s
checks are — these are about *this* schema; the laws above are about every
program in which the names resolve. -/

namespace Examples

/-- A parent, and a child holding a cached reference to it. No database ctype,
because an up-pointer needs no storage of its own. -/
def upDb : Dmmeta.Db where
  ctypes :=
    [ { name   := "level_row"
      , fields := [{ name := "price", arg := "u64", reftype := .Pkey }] }
    , { name   := "child_row"
      , fields := [ { name := "id",      arg := "u64",       reftype := .Pkey }
                  , { name := "p_level", arg := "level_row", reftype := .Upptr } ] } ]

end Examples

namespace Checks

open Dmmeta

/-- The schema is accepted.

checked by: `lake build` -/
example : Dmmeta.check Examples.upDb = [] := rfl

/-- The generated program satisfies every C-subset obligation — including that
`row->p_level` is rooted at a *local pointer parameter*, which is the form the
array table never used.

checked by: `lake build` -/
example : CSubset.Wf.check (genUpptr Examples.upDb) = [] := rfl

/-- ...and **for every accepted schema**, not just this one:
`Templates.Upptr.genWellFormed` in `UpptrWf.lean`. The instance above is
subsumed by it and kept because it also pins a concrete output. -/
example : True := trivial

/-- Four accessors, in `amc`'s naming.

checked by: `lake build` -/
example : (genUpptr Examples.upDb).funs.map FunDef.name
    = ["child_row_p_level_Init", "child_row_p_level_Get",
       "child_row_p_level_Set", "child_row_p_level_Q"] := rfl

/-- The up-pointer is in the child struct, as a pointer to the parent — which
is what `amc`'s one `InsVar` call does.

checked by: `lake build` -/
example : (genUpptr Examples.upDb).structs.map
    (fun sd => (sd.name, sd.fields.map Prod.fst))
    = [("level_row", ["price"]), ("child_row", ["id", "p_level"])] := rfl

/-- An up-pointer needs no storage of its own, so nothing is added to the
globals.

checked by: `lake build` -/
example : (genUpptr Examples.upDb).globals = [] := rfl

end Checks

end Upptr
end Templates

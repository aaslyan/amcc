import Amcc.CSubset.Value

/-!
# AMCC — Phase 1: the executable (big-step) semantics

`execStmt` is a total, structurally-decreasing Lean function, not a relation.
That is possible only because of Phase 0's restrictions — literal loop bounds
and an acyclic call graph — and it buys two things:

- **Phase 4 gets an oracle for free.** The differential harness compares this
  function's answer against the compiled binary's; there is nothing to
  extract or interpret.
- **Phase 3's simulation proofs become rewriting.** Unfolding `execStmt` on a
  known statement is `simp`, not an induction over step sequences.

`SmallStep.lean` gives the relational semantics the brief asks for as the
normative artifact, and proves this function agrees with it.

## Errors are classified, deliberately

`Err` has four constructors and they are not interchangeable:

- `oob` is the *real* one — an array subscript out of range. Phase 3 owes a
  proof that generated code never raises it, and that proof is the interesting
  part of the milestone.
- `typeErr` and `unbound` are shape and scope failures. A program accepted by
  `Wf.check` cannot raise them; that implication is type soundness, stated in
  `Wf.lean` as the bridge Phase 3 consumes.
- `depth` means the call-depth budget ran out. `Wf.check`'s acyclicity
  requirement makes `p.funs.length` always sufficient, so this too is
  unreachable for accepted programs.

Keeping them apart is what lets "generated code never gets stuck" split into
one interesting obligation and three structural ones.
-/

namespace CSubset

/-- Runtime errors. See the module docstring: only `oob` is reachable for a
well-formed program. -/
inductive Err where
  /-- Array subscript out of range — the single genuine partiality in the
  language, and the one Phase 3 must prove away. -/
  | oob
  /-- A value did not have the shape the operation needed. -/
  | typeErr
  /-- A name was not bound. -/
  | unbound
  /-- The call-depth budget was exhausted. -/
  | depth
  /-- A null pointer was dereferenced. Reachable exactly because allocation
  can fail; a proof obligation on generated code, like `oob`. -/
  | nullDeref
  /-- A path into a freed block was followed. Block identities are never
  reissued, so this is always detected rather than silently reading whatever
  was allocated next. -/
  | useAfterFree
  deriving DecidableEq, Repr, Inhabited

/-- Where an lvalue lands.

A local has no interior — locals are scalars and pointers — so `lcl` carries a
name and no path. Everything with structure is global-rooted, which is the
runtime restatement of Phase 0's aliasing story. -/
inductive Loc where
  | lcl : Ident → Loc
  | glb : Path → Loc
  deriving DecidableEq, Repr, Inhabited

/-- How a statement finished. -/
inductive Outcome where
  | normal
  | ret : Option Value → Outcome
  deriving Repr, Inhabited

/-! ## Resolving lvalues -/

/-- Resolve a subscript to a number. -/
def evalIndex (σ : Store) : Index → Except Err Nat
  | .lit n => .ok n
  | .var x =>
    match σ.getLocal x with
    | some (.u32 i) => .ok i.toNat
    | some _        => .error .typeErr
    | none          => .error .unbound

/-- Resolve an lvalue to the storage it names.

Array bounds are checked **here**, when the step is appended — not later when
the path is followed. That is what makes `&a[i]` with a bad `i` an error at the
point the address is taken, rather than a pointer that fails on use, and it is
why `Path` can carry the invariant "this denotes an object". -/
def resolve (σ : Store) : LVal → Except Err Loc
  | .var x =>
    match σ.getLocal x with
    | some _ => .ok (.lcl x)
    | none   => .error .unbound
  | .glob g =>
    match σ.glb.get? g with
    | some _ => .ok (.glb ⟨.glob g, []⟩)
    | none   => .error .unbound
  | .deref p =>
    match σ.getLocal p with
    | some (.ptr path) =>
      -- A path whose root has gone is a freed block, not a type error.
      match σ.rootVal path.root with
      | some _ => .ok (.glb path)
      | none   => .error .useAfterFree
    | some .null       => .error .nullDeref
    | some _           => .error .typeErr
    | none             => .error .unbound
  | .fld l f => do
    match ← resolve σ l with
    | .lcl _ => .error .typeErr
    | .glb path =>
      let path' : Path := ⟨path.root, path.steps ++ [.fld f]⟩
      match σ.readPath path' with
      | some _ => .ok (.glb path')
      | none   => .error .typeErr
  | .idx l i => do
    let n ← evalIndex σ i
    match ← resolve σ l with
    | .lcl _ => .error .typeErr
    | .glb path =>
      match σ.readPath path with
      | some (.arr vs) =>
        if n < vs.length then .ok (.glb ⟨path.root, path.steps ++ [.idx n]⟩)
        else .error .oob
      | some _ => .error .typeErr
      | none   => .error .typeErr

def readLoc (σ : Store) : Loc → Except Err Value
  | .lcl x =>
    match σ.getLocal x with
    | some v => .ok v
    | none   => .error .unbound
  | .glb p =>
    match σ.readPath p with
    | some v => .ok v
    | none   => .error .typeErr

def writeLoc (σ : Store) : Loc → Value → Except Err Store
  | .lcl x, v =>
    match σ.getLocal x with
    | some _ => .ok (σ.setLocal x v)
    | none   => .error .unbound
  | .glb p, v =>
    match σ.writePath p v with
    | some σ' => .ok σ'
    | none    => .error .typeErr

/-! ## Operators

Every operator below is total on well-typed operands — that is Phase 0's
"no partial operators" bet cashed in. The only `error` results are shape
mismatches, which `Wf.check` rules out. -/

def evalUn : UnOp → Value → Except Err Value
  | .lnot, .bool b => .ok (.bool (!b))
  | .bnot, .u32 a  => .ok (.u32 (~~~a))
  | .bnot, .u64 a  => .ok (.u64 (~~~a))
  | _, _           => .error .typeErr

/-- The non-short-circuiting operators. `land` and `lor` are handled in
`evalExpr`, which is where their C-faithful short-circuiting lives. -/
def evalBin : BinOp → Value → Value → Except Err Value
  | .add,  .u32 a, .u32 b => .ok (.u32 (a + b))
  | .add,  .u64 a, .u64 b => .ok (.u64 (a + b))
  | .sub,  .u32 a, .u32 b => .ok (.u32 (a - b))
  | .sub,  .u64 a, .u64 b => .ok (.u64 (a - b))
  | .mul,  .u32 a, .u32 b => .ok (.u32 (a * b))
  | .mul,  .u64 a, .u64 b => .ok (.u64 (a * b))
  | .band, .u32 a, .u32 b => .ok (.u32 (a &&& b))
  | .band, .u64 a, .u64 b => .ok (.u64 (a &&& b))
  | .bor,  .u32 a, .u32 b => .ok (.u32 (a ||| b))
  | .bor,  .u64 a, .u64 b => .ok (.u64 (a ||| b))
  | .bxor, .u32 a, .u32 b => .ok (.u32 (a ^^^ b))
  | .bxor, .u64 a, .u64 b => .ok (.u64 (a ^^^ b))
  | .eq,   .u32 a, .u32 b => .ok (.bool (a == b))
  | .eq,   .u64 a, .u64 b => .ok (.bool (a == b))
  | .eq,   .bool a, .bool b => .ok (.bool (a == b))
  | .eq,   .ptr a, .ptr b => .ok (.bool (a == b))
  | .ne,   .u32 a, .u32 b => .ok (.bool (a != b))
  | .ne,   .u64 a, .u64 b => .ok (.bool (a != b))
  | .ne,   .bool a, .bool b => .ok (.bool (a != b))
  | .ne,   .ptr a, .ptr b => .ok (.bool (a != b))
  | .lt,   .u32 a, .u32 b => .ok (.bool (a < b))
  | .lt,   .u64 a, .u64 b => .ok (.bool (a < b))
  | .le,   .u32 a, .u32 b => .ok (.bool (a ≤ b))
  | .le,   .u64 a, .u64 b => .ok (.bool (a ≤ b))
  | _, _, _ => .error .typeErr

/-- Explicit conversions. Every case is total: widening is exact, narrowing
truncates as C defines for unsigned, and `bool` round-trips through `0`/`1`. -/
def evalCast : ScalarTy → Value → Except Err Value
  | .u32,  .u32 a  => .ok (.u32 a)
  | .u32,  .u64 a  => .ok (.u32 a.toUInt32)
  | .u32,  .bool b => .ok (.u32 (if b then 1 else 0))
  | .u64,  .u32 a  => .ok (.u64 a.toUInt64)
  | .u64,  .u64 a  => .ok (.u64 a)
  | .u64,  .bool b => .ok (.u64 (if b then 1 else 0))
  | .bool, .u32 a  => .ok (.bool (a != 0))
  | .bool, .u64 a  => .ok (.bool (a != 0))
  | .bool, .bool b => .ok (.bool b)
  | _, _ => .error .typeErr

/-! ## Expressions

Pure and store-independent-of-order: every subexpression reads the same `σ`,
so there is no evaluation-order question to answer. -/

def evalExpr (σ : Store) : Expr → Except Err Value
  | .lit (.u32 a)  => .ok (.u32 a)
  | .lit (.u64 a)  => .ok (.u64 a)
  | .lit (.bool b) => .ok (.bool b)
  | .rd l => do readLoc σ (← resolve σ l)
  | .un o e => do evalUn o (← evalExpr σ e)
  | .bin .land e₁ e₂ => do
    match ← evalExpr σ e₁ with
    | .bool false => .ok (.bool false)
    | .bool true =>
      match ← evalExpr σ e₂ with
      | .bool b => .ok (.bool b)
      | _       => .error .typeErr
    | _ => .error .typeErr
  | .bin .lor e₁ e₂ => do
    match ← evalExpr σ e₁ with
    | .bool true => .ok (.bool true)
    | .bool false =>
      match ← evalExpr σ e₂ with
      | .bool b => .ok (.bool b)
      | _       => .error .typeErr
    | _ => .error .typeErr
  | .bin o e₁ e₂ => do evalBin o (← evalExpr σ e₁) (← evalExpr σ e₂)
  | .cast t e => do evalCast t (← evalExpr σ e)
  | .addr l => do
    match ← resolve σ l with
    | .glb p => .ok (.ptr p)
    | .lcl _ => .error .typeErr

/-! ## Statements -/

def lookupFun (p : Program) (f : Ident) : Except Err FunDef :=
  match p.funs.find? (fun fd => fd.name == f) with
  | some fd => .ok fd
  | none    => .error .unbound

def bindParams : List (Ident × ValTy) → List Value → Except Err Env
  | [], []                => .ok []
  | (x, _) :: ps, v :: vs => do let rest ← bindParams ps vs; .ok ((x, v) :: rest)
  | _, _                  => .error .typeErr

/-- Build a callee's frame: parameters from the arguments, then each local's
initialiser evaluated in order, seeing the parameters and the earlier locals.

This is where Phase 0's decision to give every local an explicit initialiser
shows up. There is no zero-fill and no definite-assignment analysis: a frame is
one left fold, and a pointer local gets a real target because the syntax made
one mandatory. -/
def buildFrame (m : Mem) (fd : FunDef) (vs : List Value) : Except Err Env := do
  let params ← bindParams fd.params vs
  fd.locals.foldlM
    (fun acc ld => do
      let v ← evalExpr (m.toStore acc) ld.init
      .ok (acc ++ [(ld.name, v)]))
    params

/-- One iteration sweep of `forN`, parameterised by how to run the body.

Recurses structurally on the iterations remaining and is not mutual with
anything: the body's executor arrives as a value. On exit the loop variable
holds the trip count, matching C's `for (i = 0; i < n; ++i)`, which leaves
`i = n`. -/
def forLoop (bodyExec : Store → Except Err (Store × Outcome)) (x : Ident) :
    Nat → Nat → Store → Except Err (Store × Outcome)
  | i, 0, σ => .ok (σ.setLocal x (.u32 (UInt32.ofNat i)), .normal)
  | i, rem + 1, σ => do
    let σ₀ := σ.setLocal x (.u32 (UInt32.ofNat i))
    match ← bodyExec σ₀ with
    | (σ₁, .normal) => forLoop bodyExec x (i + 1) rem σ₁
    | (σ₁, .ret v)  => .ok (σ₁, .ret v)

/-- Execute a statement at one call-depth level, given `callee` — how to run a
called function's body one level down.

Abstracting the callee out is what keeps this structurally recursive on the
statement: the only recursive calls are on syntactic subterms, and crossing a
call boundary is `callee`'s job, not this function's. `execStmt` below closes
the loop by recursing structurally on the depth. Both being structural is
what makes the semantics *reduce* — `#eval` and `decide` work on it, which is
what Phase 4's differential harness needs and what makes the tests in
`Sanity.lean` kernel-checked equalities rather than `simp` calls. -/
def execAt (p : Program) (callee : Stmt → Store → Except Err (Store × Outcome)) :
    Stmt → Store → Except Err (Store × Outcome)
  | .skip, σ => .ok (σ, .normal)
  | .assign l e, σ => do
    let loc ← resolve σ l
    let v ← evalExpr σ e
    let σ' ← writeLoc σ loc v
    .ok (σ', .normal)
  | .seq s₁ s₂, σ => do
    match ← execAt p callee s₁ σ with
    | (σ₁, .normal) => execAt p callee s₂ σ₁
    | (σ₁, .ret v)  => .ok (σ₁, .ret v)
  | .cond c s₁ s₂, σ => do
    match ← evalExpr σ c with
    | .bool true  => execAt p callee s₁ σ
    | .bool false => execAt p callee s₂ σ
    | _           => .error .typeErr
  | .forN x b body, σ => do
    -- The bound is read once, here, before the first iteration.
    let n ← evalIndex σ b
    forLoop (execAt p callee body) x 0 n σ
  | .ret none, σ => .ok (σ, .ret none)
  | .ret (some e), σ => do
    let v ← evalExpr σ e
    .ok (σ, .ret (some v))
  | .call dst f args, σ => do
    let fd ← lookupFun p f
    let vs ← args.mapM (evalExpr σ)
    let frame ← buildFrame σ.toMem fd vs
    let (σ₁, out) ← callee fd.body (σ.toMem.toStore frame)
    -- The callee's frame dies here; its globals survive. Restoring the
    -- caller's frame wholesale is sound precisely because no pointer can
    -- name a local, so the callee cannot have written through one.
    let σ₂ : Store := σ₁.toMem.toStore σ.loc
    match dst, out with
    | none,   _             => .ok (σ₂, .normal)
    | some x, .ret (some v) => do
      let σ₃ ← writeLoc σ₂ (.lcl x) v
      .ok (σ₃, .normal)
    | some _, _             => .error .typeErr

/-- Execute a statement with a call-depth budget of `d`.

`Wf.check` guarantees the call graph is acyclic, so `d = p.funs.length` is
always enough — the budget is *derived* from the program, never assumed, and
`Err.depth` is unreachable for accepted programs. -/
def execStmt (p : Program) : Nat → Stmt → Store → Except Err (Store × Outcome)
  | 0     => execAt p (fun _ _ => .error .depth)
  | d + 1 => execAt p (execStmt p d)

/-- Sequencing in `Except`: a successful bind means both halves succeeded.

Used throughout Phase 1 to take apart `execAt`'s do-blocks without `split`
gymnastics. -/
theorem bindOk {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error _ => exact Except.noConfusion h
  | ok a    => exact ⟨a, rfl, h⟩

/-! ## Running a whole program -/

/-- Call a function against a given global environment. The depth budget is
`p.funs.length`, which acyclicity makes sufficient. -/
def callFun (p : Program) (m : Mem) (f : Ident) (args : List Value) :
    Except Err (Mem × Option Value) := do
  let fd ← lookupFun p f
  let frame ← buildFrame m fd args
  let (σ, out) ← execStmt p p.funs.length fd.body (m.toStore frame)
  match out with
  | .normal  => .ok (σ.toMem, none)
  | .ret v   => .ok (σ.toMem, v)

/-- Zero-initialise the globals and call `f`. -/
def runProgram (p : Program) (f : Ident) (args : List Value) :
    Except Err (Mem × Option Value) :=
  match initGlobals p with
  | none     => .error .typeErr
  | some glb => callFun p { glb := glb, hp := [], next := 0 } f args

/-- Thread a sequence of calls through the globals, starting zero-initialised,
collecting each call's result.

This is the shape Phase 4's differential harness drives: the same call
sequence goes to the compiled binary, and the two answers are compared. -/
def runCalls (p : Program) (calls : List (Ident × List Value)) :
    Except Err (Mem × List (Option Value)) :=
  match initGlobals p with
  | none => .error .typeErr
  | some glb =>
    calls.foldlM
      (fun (acc : Mem × List (Option Value)) (c : Ident × List Value) => do
        let (g, r) ← callFun p acc.1 c.1 c.2
        .ok (g, acc.2 ++ [r]))
      ({ glb := glb, hp := [], next := 0 }, [])

end CSubset

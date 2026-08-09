import Amcc.CSubset.Eval

/-!
# AMCC — Phase 1: the well-formedness checker

A decidable implementation of the eleven obligations stated in
`Syntax.lean`'s docstring, plus two that only became visible once the semantics
existed (see "Obligations the semantics added" below).

`check` returns the list of violations rather than a bare `Bool`, because its
consumer is a *generator*: when Phase 3 emits a program that fails, "which
obligation, where" is the difference between a five-minute fix and an
afternoon. `Program.wf` is the Boolean view for stating theorems.

## What this file does and does not claim

It decides a syntactic predicate. It does **not** yet prove

```
theorem type_soundness : p.wf → execStmt … ≠ .error .typeErr ∧ … ≠ .error .unbound
```

which is the bridge Phase 3 wants: with it, `Err.typeErr`, `Err.unbound` and
`Err.depth` all become unreachable and the only remaining obligation on
generated code is freedom from `Err.oob`. That theorem is stated at the bottom
of this file as `TypeSound`, unproved, and is the honest first item of Phase 3's
budget — it is a progress-and-preservation argument over `Step`, not a
restatement of the checker.

Until it exists, the checker earns its keep the direct way: `Examples.tinyTable`
is checked to be well-formed *by computation*, so the program Phase 3 must
learn to generate is known to satisfy every obligation the design claims.

## Obligations the semantics added

Writing `Eval` surfaced two requirements that pure syntax did not:

- **Array sizes must fit in `u32`** (and be non-zero). The generated C compares
  a `uint32_t` loop counter against the bound; a bound at or above `2³²` would
  make that comparison mean something different from the Lean `Nat` one. Same
  for `forN` trip counts.
- **A global's type may not contain a pointer.** Globals are zero-initialised,
  and a non-null pointer has no zero — `zeroOfTy` returns `none`, which would
  make `initGlobals` fail at run time rather than at check time.
-/

namespace CSubset
namespace Wf

/-- One past the largest value a `uint32_t` bound may take. -/
def u32Bound : Nat := 4294967296

/-! ## Types -/

/-- Every struct name a type mentions. -/
def Ty.allStructs : Ty → List Ident
  | .scalar _ => []
  | .strct n  => [n]
  | .arr t _  => Ty.allStructs t
  | .ptr t    => Ty.allStructs t

/-- The struct names whose *layout* a type depends on. A pointer is exempt:
`Row *` needs no knowledge of `Row`'s size, which is why obligation 2 can
permit a pointer to a struct declared later or to the enclosing one. -/
def Ty.layoutDeps : Ty → List Ident
  | .scalar _ => []
  | .strct n  => [n]
  | .arr t _  => Ty.layoutDeps t
  | .ptr _    => []

/-- Obligation 3, with the `u32` bound the semantics added. -/
def Ty.sizesOk : Ty → Bool
  | .scalar _ => true
  | .strct _  => true
  | .ptr t    => Ty.sizesOk t
  | .arr t n  => 0 < n && n < u32Bound && Ty.sizesOk t

def Ty.hasPtr : Ty → Bool
  | .scalar _ => false
  | .strct _  => false
  | .ptr _    => true
  | .arr t _  => Ty.hasPtr t

def isWord : Ty → Bool
  | .scalar .u32 => true
  | .scalar .u64 => true
  | _            => false

def isPtrTy : Ty → Bool
  | .ptr _ => true
  | _      => false

/-- Which types a value may have — the image of `ValTy.toTy`. Reading anything
else into an expression would be a struct or array copy, which Phase 0 excluded. -/
def isValTy : Ty → Bool
  | .scalar _ => true
  | .ptr _    => true
  | _         => false

/-! ## Contexts -/

/-- What is in scope while checking one function body. `funs` holds only the
functions declared *before* this one, which is how obligation 4's acyclicity is
enforced: a callee that is not in this list is simply not found. -/
structure Ctx where
  structs : List StructDef
  globals : List GlobalDef
  funs    : List FunDef
  locals  : List (Ident × ValTy)

def Ctx.struct? (c : Ctx) (n : Ident) : Option StructDef :=
  c.structs.find? (fun sd => sd.name == n)

def Ctx.global? (c : Ctx) (n : Ident) : Option GlobalDef :=
  c.globals.find? (fun g => g.name == n)

def Ctx.fun? (c : Ctx) (n : Ident) : Option FunDef :=
  c.funs.find? (fun f => f.name == n)

def Ctx.local? (c : Ctx) (n : Ident) : Option ValTy :=
  (c.locals.find? (fun lv => lv.1 == n)).map Prod.snd

def Ctx.field? (c : Ctx) (sn : Ident) (f : Ident) : Option Ty := do
  let sd ← c.struct? sn
  let fv ← sd.fields.find? (fun fv => fv.1 == f)
  some fv.2

/-! ## Type inference

`none` means ill-typed. The statement checker turns that into a message. -/

/-- Obligation 6: a subscript is a literal or a `u32` local. -/
def indexOk (c : Ctx) : Index → Bool
  | .lit _ => true
  | .var x => c.local? x == some (.scalar .u32)

/-- Obligations 5 and 6. -/
def inferLVal (c : Ctx) : LVal → Option Ty
  | .var x   => (c.local? x).map ValTy.toTy
  | .glob g  => (c.global? g).map GlobalDef.ty
  | .deref p =>
    match c.local? p with
    | some (.ptr t) => some t
    | _             => none
  | .fld l f =>
    match inferLVal c l with
    | some (.strct n) => c.field? n f
    | _               => none
  | .idx l i =>
    if indexOk c i then
      match inferLVal c l with
      | some (.arr t _) => some t
      | _               => none
    else none

/-- The root of an lvalue, as `LVal.root`, but as the tag obligation 7 tests. -/
def rootIsLocal : LVal → Bool
  | .var _   => true
  | .glob _  => false
  | .deref _ => false
  | .fld l _ => rootIsLocal l
  | .idx l _ => rootIsLocal l

def litTy : Lit → Ty
  | .u32 _  => .scalar .u32
  | .u64 _  => .scalar .u64
  | .bool _ => .scalar .bool

def unTy : UnOp → Ty → Option Ty
  | .lnot, .scalar .bool => some (.scalar .bool)
  | .bnot, t             => if isWord t then some t else none
  | _, _                 => none

/-- Obligation 9, one line per operator group. -/
def binTy : BinOp → Ty → Ty → Option Ty
  | .add, a, b | .sub, a, b | .mul, a, b
  | .band, a, b | .bor, a, b | .bxor, a, b =>
    if isWord a && a == b then some a else none
  | .lt, a, b | .le, a, b =>
    if isWord a && a == b then some (.scalar .bool) else none
  | .eq, a, b | .ne, a, b =>
    if a == b && (isWord a || a == Ty.scalar .bool || isPtrTy a)
    then some (.scalar .bool) else none
  | .land, a, b | .lor, a, b =>
    if a == Ty.scalar .bool && b == Ty.scalar .bool then some (.scalar .bool) else none

def inferExpr (c : Ctx) : Expr → Option Ty
  | .lit l => some (litTy l)
  | .null t => some (.ptr t)
  | .rd l  =>
    match inferLVal c l with
    | some t => if isValTy t then some t else none
    | none   => none
  | .un o e => do unTy o (← inferExpr c e)
  | .bin o e₁ e₂ => do binTy o (← inferExpr c e₁) (← inferExpr c e₂)
  | .cast t e => do
    let s ← inferExpr c e
    if isWord s || s == Ty.scalar .bool then some (.scalar t) else none
  -- Obligation 7 lives here: `&` is rejected on a local-rooted lvalue, which
  -- is what keeps every pointer value global-rooted and therefore non-dangling.
  | .addr l => do
    let t ← inferLVal c l
    if rootIsLocal l then none else some (.ptr t)

/-- Obligation 7, reported separately from type inference.

`inferExpr` already rejects `&local` by returning `none`, but "ill-typed
expression" is a poor thing to tell a code generator about the one rule that
keeps every pointer non-dangling. This pass names it.

Lvalues contain no expressions — `Index` is a literal or a variable — so there
is nothing to recurse into on the `rd` and `addr` branches. -/
def addrChecks : Expr → List String
  | .lit _     => []
  | .null _    => []
  | .rd _      => []
  | .un _ e    => addrChecks e
  | .cast _ e  => addrChecks e
  | .bin _ a b => addrChecks a ++ addrChecks b
  | .addr l    =>
    if rootIsLocal l then
      [s!"& applied to a local-rooted lvalue: obligation 7 forbids taking the address of a frame"]
    else []

/-! ## Statements -/

/-- Names a statement may assign to — used by obligation 8 to check that a loop
body leaves its loop variable alone. -/
def Stmt.assigns : Stmt → List Ident
  | .skip              => []
  | .assign (.var x) _ => [x]
  | .assign _ _        => []
  | .seq a b           => Stmt.assigns a ++ Stmt.assigns b
  | .cond _ a b        => Stmt.assigns a ++ Stmt.assigns b
  | .forN x _ b        => x :: Stmt.assigns b
  | .call (some x) _ _ => [x]
  | .call none _ _     => []
  | .ret _             => []

/-- Obligation 11: does every path through this statement end in a `return`?

A `forN` never counts — its trip count may be zero — which is why the generated
`find` ends with an unconditional `return CAP` after its loop. -/
def Stmt.alwaysReturns : Stmt → Bool
  | .ret _      => true
  | .seq a b    => Stmt.alwaysReturns a || Stmt.alwaysReturns b
  | .cond _ a b => Stmt.alwaysReturns a && Stmt.alwaysReturns b
  | _           => false

/-- Check a statement. `ret` is the enclosing function's return type. -/
def checkStmt (c : Ctx) (ret : Option ValTy) : Stmt → List String
  | .skip => []
  | .assign l e =>
    addrChecks e ++
    match inferLVal c l, inferExpr c e with
    | some tl, some te =>
      if !isValTy tl then [s!"assignment to non-scalar location"]
      else if tl == te then [] else [s!"assignment type mismatch"]
    | none, _ => [s!"ill-typed assignment target"]
    | _, none => [s!"ill-typed assigned expression"]
  | .seq a b => checkStmt c ret a ++ checkStmt c ret b
  | .cond e a b =>
    addrChecks e
      ++ (if inferExpr c e == some (Ty.scalar .bool) then [] else [s!"if condition is not bool"])
      ++ checkStmt c ret a ++ checkStmt c ret b
  | .forN x b body =>
    (if c.local? x == some (.scalar .u32) then [] else [s!"loop variable {x} is not a u32 local"])
      ++ (if indexOk c b then [] else [s!"loop bound is not a literal or a u32 local"])
      ++ (match b with
          | .lit n => if n < u32Bound then [] else [s!"loop bound {n} does not fit in u32"]
          | .var _ => [])
      ++ (if (Stmt.assigns body).contains x then [s!"loop body assigns to loop variable {x}"] else [])
      ++ checkStmt c ret body
  | .ret none =>
    if ret.isNone then [] else [s!"bare return in a value-returning function"]
  | .ret (some e) =>
    addrChecks e ++
    match ret, inferExpr c e with
    | some rt, some te => if rt.toTy == te then [] else [s!"return type mismatch"]
    | none, _          => [s!"value returned from a void function"]
    | _, none          => [s!"ill-typed return expression"]
  | .call dst f args =>
    match c.fun? f with
    -- Obligation 4: not found means not declared earlier, so this also rejects
    -- recursion and any call cycle.
    | none => [s!"call to {f}: not declared before this function"]
    | some fd =>
      let argChecks :=
        args.flatMap addrChecks ++
        if args.length != fd.params.length then [s!"call to {f}: wrong number of arguments"]
        else (List.zip args fd.params).flatMap (fun ap =>
          if inferExpr c ap.1 == some ap.2.2.toTy then [] else [s!"call to {f}: argument type mismatch"])
      let dstChecks :=
        match dst, fd.ret with
        | none,   _        => []
        | some x, some rt  =>
          if c.local? x == some rt then [] else [s!"call to {f}: destination {x} has the wrong type"]
        | some _, none     => [s!"call to {f}: void function used as a value"]
      argChecks ++ dstChecks

/-! ## Declarations -/

def dups (xs : List Ident) : List Ident :=
  xs.filter (fun x => 1 < xs.countP (fun y => y == x)) |>.eraseDups

/-- Obligation 1 for one list of names. Public (not `private`) because the
`GenWellFormed` proof needs to reason about `check`'s components by name. -/
def distinct (what : String) (xs : List Ident) : List String :=
  (dups xs).map (fun x => s!"duplicate {what}: {x}")

/-- Obligations 2 and 3 for the struct table: each struct's layout may only
depend on structs already declared, which is what makes `zeroTable` and
`Value` well-founded. -/
def checkStructs (structs : List StructDef) : List String :=
  distinct "struct" (structs.map StructDef.name)
    ++ (structs.zipIdx.flatMap (fun sdi =>
      let sd := sdi.1
      let earlier := (structs.take sdi.2).map StructDef.name
      let allNames := structs.map StructDef.name
      distinct s!"field of {sd.name}" (sd.fields.map Prod.fst)
        ++ sd.fields.flatMap (fun fv =>
          (if Ty.sizesOk fv.2 then [] else [s!"{sd.name}.{fv.1}: bad array size"])
            ++ (Ty.allStructs fv.2).flatMap (fun n =>
                if allNames.contains n then [] else [s!"{sd.name}.{fv.1}: unknown struct {n}"])
            ++ (Ty.layoutDeps fv.2).flatMap (fun n =>
                if earlier.contains n then []
                else [s!"{sd.name}.{fv.1}: struct {n} is not declared earlier"]))))

def checkGlobals (structs : List StructDef) (globals : List GlobalDef) : List String :=
  distinct "global" (globals.map GlobalDef.name)
    ++ globals.flatMap (fun g =>
      (if Ty.sizesOk g.ty then [] else [s!"global {g.name}: bad array size"])
        -- A global of pointer type is fine now: its zero value is NULL.
        ++ (Ty.allStructs g.ty).flatMap (fun n =>
            if (structs.map StructDef.name).contains n then []
            else [s!"global {g.name}: unknown struct {n}"]))

/-- Obligations 1 and 10 for a function, then its body.

Local initialisers are checked in a context holding the parameters and the
*earlier* locals only — the same left-to-right discipline `buildFrame` uses at
run time, so a checked initialiser cannot read a local that has not been
built yet. -/
def checkFun (structs : List StructDef) (globals : List GlobalDef)
    (earlier : List FunDef) (fd : FunDef) : List String :=
  let names := fd.params.map Prod.fst ++ fd.locals.map LocalDef.name
  let base : Ctx := { structs, globals, funs := earlier, locals := fd.params }
  let initChecks :=
    (fd.locals.zipIdx.flatMap (fun ldi =>
      let ld := ldi.1
      let ctx : Ctx :=
        { base with
          locals := fd.params ++ ((fd.locals.take ldi.2).map (fun l => (l.name, l.ty))) }
      addrChecks ld.init ++
      match inferExpr ctx ld.init with
      | none    => [s!"{fd.name}: initialiser of {ld.name} is ill-typed"]
      | some t  => if ld.ty.toTy == t then [] else [s!"{fd.name}: initialiser of {ld.name} has the wrong type"]))
  let full : Ctx :=
    { base with locals := fd.params ++ fd.locals.map (fun l => (l.name, l.ty)) }
  distinct s!"name in {fd.name}" names
    ++ initChecks
    ++ checkStmt full fd.ret fd.body
    ++ (match fd.ret with
        | none   => []
        | some _ =>
          if Stmt.alwaysReturns fd.body then []
          else [s!"{fd.name}: not every path returns a value"])

/-- The whole checker. An empty result means every obligation holds. -/
def check (p : Program) : List String :=
  checkStructs p.structs
    ++ checkGlobals p.structs p.globals
    ++ distinct "function" (p.funs.map FunDef.name)
    ++ p.funs.zipIdx.flatMap (fun fdi =>
        checkFun p.structs p.globals (p.funs.take fdi.2) fdi.1)

end Wf

/-- The Boolean view, for stating theorems. -/
def Program.wf (p : Program) : Bool := (Wf.check p).isEmpty

/-! ## The bridge Phase 3 needs

Stated, not proved. See this file's header: this is a
progress-and-preservation argument over `Step`, and it is the first item on
Phase 3's budget rather than something the checker gives for free.

With it, three of `Err`'s four constructors become unreachable for accepted
programs and the only obligation left on generated code is freedom from
`Err.oob` — which is the shape the milestone's simulation proof wants. -/
def TypeSound : Prop :=
  ∀ (p : Program) (f : Ident) (args : List Value) (e : Err),
    p.wf = true → runProgram p f args = .error e → e = .oob

end CSubset

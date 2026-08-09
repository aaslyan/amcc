import Amcc.CSubset.Wf
import Amcc.CSubset.Examples

/-!
# AMCC — Phase 1: the checker, exercised

Two positive checks and eight negative ones, all by `rfl`.

The negative controls matter more than they look. A checker that accepts
everything also accepts `Examples.tinyTable`, so the positive results below are
only evidence if the checker is known to reject. Each program here violates
exactly one obligation, and the expected message names it — so if a later
change to `Wf.check` silently stops enforcing a rule, one of these fails.

The two most load-bearing are `pAddrLocal` (obligation 7 — the rule the whole
non-dangling argument rests on) and `pRecursion` (obligation 4 — the rule that
makes every program terminate, and hence makes the semantics definable as a
total function at all).
-/

namespace CSubset
namespace WfChecks

open Examples

/-! ## The examples are well-formed -/

/-- checked by: `lake build` -/
example : Wf.check trivialCell = [] := rfl

/-- The program Phase 3 has to learn to generate satisfies every obligation
the design claims — checked, not asserted.

checked by: `lake build` -/
example : Wf.check tinyTable = [] := rfl

/-- checked by: `lake build` -/
example : trivialCell.wf = true ∧ tinyTable.wf = true := ⟨rfl, rfl⟩

/-! ## Negative controls, one obligation each -/

/-- Obligation 7: `&` on a local. Accepting this would put a pointer to a dead
frame into circulation the moment `f` returns. -/
def pAddrLocal : Program where
  structs := []
  globals := []
  funs := [{ name := "f", params := [("x", .scalar .u64)], ret := some (.ptr (.scalar .u64)),
             locals := [], body := .ret (some (.addr (.var "x"))) }]

/-- checked by: `lake build` -/
example : Wf.check pAddrLocal =
    ["& applied to a local-rooted lvalue: obligation 7 forbids taking the address of a frame",
     "ill-typed return expression"] := rfl

/-- A global of pointer type is **accepted**, and zero-initialises to `NULL`.

This used to be rejected: without a null pointer there was no zero value at
pointer type, so `initGlobals` would have failed at run time. Now that `NULL`
exists the rule is gone — which is what makes a global head pointer, and so an
intrusive list rooted in one, expressible at all. -/
def pPtrGlobal : Program where
  structs := []
  globals := [{ name := "g_p", ty := .ptr (.scalar .u64) }]
  funs := []

/-- checked by: `lake build` -/
example : Wf.check pPtrGlobal = [] := rfl

/-- And it really does zero-initialise to `NULL`.

checked by: `lake build` -/
example : initGlobals pPtrGlobal = some [("g_p", .null)] := rfl

/-- Obligation 4: a call to a function declared later. -/
def pForwardCall : Program where
  structs := []
  globals := []
  funs := [{ name := "a", params := [], ret := none, locals := [], body := .call none "b" [] },
           { name := "b", params := [], ret := none, locals := [], body := .skip }]

/-- checked by: `lake build` -/
example : Wf.check pForwardCall = ["call to b: not declared before this function"] := rfl

/-- Obligation 4 again, in the form that matters: **recursion is
inexpressible**. This is what licenses `execStmt`'s structural recursion on the
depth budget, and with it the claim that every program in the subset
terminates. -/
def pRecursion : Program where
  structs := []
  globals := []
  funs := [{ name := "f", params := [], ret := none, locals := [], body := .call none "f" [] }]

/-- checked by: `lake build` -/
example : Wf.check pRecursion = ["call to f: not declared before this function"] := rfl

/-- Obligation 8: the loop body assigns its own loop variable, which would
break the induction principle the loop is supposed to have. -/
def pLoopVarAssigned : Program where
  structs := []
  globals := []
  funs := [{ name := "f", params := [], ret := none, locals := [LocalDef.zeroed "i" .u32],
             body := .forN "i" (.lit 4) (.assign (.var "i") (.lit (.u32 0))) }]

/-- checked by: `lake build` -/
example : Wf.check pLoopVarAssigned = ["loop body assigns to loop variable i"] := rfl

/-- Obligation 11: a value-returning function with a path that falls off the
end. -/
def pMissingReturn : Program where
  structs := []
  globals := []
  funs := [{ name := "f", params := [], ret := some (.scalar .u32), locals := [], body := .skip }]

/-- checked by: `lake build` -/
example : Wf.check pMissingReturn = ["f: not every path returns a value"] := rfl

/-- Obligation 3: a zero-length array. Besides being ill-formed C, this is what
guarantees `&g[0]` always exists — the initialiser of last resort for a pointer
local. -/
def pZeroArray : Program where
  structs := []
  globals := [{ name := "g", ty := .arr (.scalar .u32) 0 }]
  funs := []

/-- checked by: `lake build` -/
example : Wf.check pZeroArray = ["global g: bad array size"] := rfl

/-- Obligation 9: `u32 + u64`. C would silently promote; the subset does not,
which is why `Expr.cast` exists and has to be written explicitly. -/
def pWidthMix : Program where
  structs := []
  globals := []
  funs := [{ name := "f", params := [("a", .scalar .u32), ("b", .scalar .u64)],
             ret := some (.scalar .u32), locals := [],
             body := .ret (some (.bin .add (.rd (.var "a")) (.rd (.var "b")))) }]

/-- checked by: `lake build` -/
example : Wf.check pWidthMix = ["ill-typed return expression"] := rfl

/-- The same function with the cast written in is accepted — so the rejection
above is about the missing conversion, not about `+` being broken.

checked by: `lake build` -/
example : Wf.check
    { structs := [], globals := []
    , funs := [{ name := "f", params := [("a", .scalar .u32), ("b", .scalar .u64)]
               , ret := some (.scalar .u32), locals := []
               , body := .ret (some (.bin .add (.rd (.var "a"))
                                       (.cast .u32 (.rd (.var "b"))))) }] } = [] := rfl

/-- A loop whose bound is a `u32` parameter passes the checker: `indexOk`
accepts a literal or a `u32` local, and nothing else.

checked by: `lake build` -/
example : Wf.check Examples.varLoop = [] := rfl

end WfChecks
end CSubset

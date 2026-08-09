import Amcc.CSubset.Eval

/-!
# AMCC — reasoning about a call, template-independently

The lemmas every operation template needs before it can say anything about a
generated function, factored out of the first template that needed them
(`Templates/Upptr.lean`) when the second one (`Templates/Llist.lean`) needed
them too.

Three groups.

**Peeling one statement.** `simp only [execAt]` unfolds all the way down, which
loses any hypothesis stated one level up — about `resolve`, or `evalExpr`, or a
sub-statement. `execAt_seq` and friends rewrite exactly one constructor and
stop, which is what lets those hypotheses match. This is the single most
recurrent friction in the proofs above them.

**Resolving a name to a definition.** `lookupFun_of_mem`: a function that is in
the program resolves to itself, provided the generated names do not collide.
Collision is a whole-schema property, so it stays a hypothesis.

**Getting in and out of a call.** `callFun_normal` / `callFun_ret` run a body
whose frame is known, at a depth budget the program's own function count
supplies.

`Amcc/Templates/ArrayTable*.lean` predates this file and carries its own copies
under `Templates.ArrayTable`; they were not moved because they are load-bearing
in proofs that are finished, and churn there buys nothing.
-/

namespace CSubset

/-! ## Peeling one statement -/

theorem execAt_seq' {p : Program} {callee} (a b : Stmt) (σ : Store) :
    execAt p callee (.seq a b) σ = (do
      match ← execAt p callee a σ with
      | (σ₁, .normal) => execAt p callee b σ₁
      | (σ₁, .ret v)  => .ok (σ₁, .ret v)) := rfl

theorem execAt_cond' {p : Program} {callee} (c : Expr) (a b : Stmt) (σ : Store) :
    execAt p callee (.cond c a b) σ = (do
      match ← evalExpr σ c with
      | .bool true  => execAt p callee a σ
      | .bool false => execAt p callee b σ
      | _           => .error .typeErr) := rfl

theorem execAt_assign' {p : Program} {callee} (l : LVal) (e : Expr) (σ : Store) :
    execAt p callee (.assign l e) σ = (do
      let loc ← resolve σ l
      let v ← evalExpr σ e
      let σ' ← writeLoc σ loc v
      .ok (σ', .normal)) := rfl

/-- `Stmt.block` collapses a singleton, so `block (a :: as)` is not
syntactically a `.seq`. It behaves like one, which is what an induction over a
statement list needs. -/
theorem execAt_block_cons' {p : Program} {callee} (a : Stmt) (as : List Stmt)
    (σ : Store) :
    execAt p callee (Stmt.block (a :: as)) σ
      = execAt p callee (.seq a (Stmt.block as)) σ := by
  cases as with
  | cons _ _ => rfl
  | nil =>
    show execAt p callee a σ = _
    rw [execAt_seq']
    cases h : execAt p callee a σ with
    | error _ => rfl
    | ok r =>
      obtain ⟨σ₁, o⟩ := r
      cases o with
      | normal => rfl
      | ret _ => rfl

/-- Reading a local. -/
theorem read_local' {σ : Store} {x : Ident} {v : Value}
    (h : σ.getLocal x = some v) : evalExpr σ (.rd (.var x)) = .ok v := by
  simp only [evalExpr, resolve, h, readLoc, bind, Except.bind]

/-! ## Reading memory between calls

`Store.readPath` consults only the globals and the heap, so what a generated
function observes is a function of the `Mem` alone — which is what persists
across a call. -/

def readMem (m : Mem) (p : Path) : Option Value := (m.toStore []).readPath p

theorem readMem_toStore (m : Mem) (loc : Env) (p : Path) :
    (m.toStore loc).readPath p = readMem m p := by
  simp only [readMem, Store.readPath]
  have h : (m.toStore loc).rootVal = (m.toStore []).rootVal := by
    funext r; cases r <;> rfl
  rw [h]

theorem readMem_toMem (σ : Store) (p : Path) :
    readMem σ.toMem p = σ.readPath p := by
  simp only [readMem, Store.readPath]
  have h : (σ.toMem.toStore []).rootVal = σ.rootVal := by funext r; cases r <;> rfl
  rw [h]

/-! ## Resolving a name to a definition -/

theorem find?_of_mem_pairwise {α : Type _} {f : α → Ident} :
    ∀ (l : List α) (a : α), a ∈ l → (l.map f).Pairwise (· ≠ ·) →
      l.find? (fun x => f x == f a) = some a
  | [], _, hm, _ => absurd hm (by simp)
  | x :: xs, a, hm, hpw => by
    rcases List.mem_cons.mp hm with rfl | hm'
    · rw [List.find?_cons_of_pos (by simp)]
    · have hne : f x ≠ f a :=
        (List.pairwise_cons.mp (by simpa using hpw)).1 (f a) (List.mem_map_of_mem hm')
      rw [List.find?_cons_of_neg (by simp [hne])]
      exact find?_of_mem_pairwise xs a hm'
        (List.Pairwise.of_cons (by simpa using hpw))

/-- A function in a program with pairwise-distinct names resolves to itself.

Name distinctness stays a hypothesis because it is a property of the *whole*
schema, not of any one template: `child ++ "_" ++ fld` is not injective in the
pair, so `a`/`b_c` and `a_b`/`c` generate the same C name. That is the schema
checker's business, and making it a hypothesis says so instead of hiding it. -/
theorem lookupFun_of_mem {p : Program} {fd : FunDef} (hmem : fd ∈ p.funs)
    (hpw : (p.funs.map FunDef.name).Pairwise (· ≠ ·)) :
    lookupFun p fd.name = .ok fd := by
  simp only [lookupFun, find?_of_mem_pairwise p.funs fd hmem hpw]

/-! ## Getting in and out of a call

Split by outcome rather than stated with a `match`, because a `match` on the
outcome in the conclusion makes the rewrite motive dependent. -/

theorem callFun_normal {p : Program} {m : Mem} {fd : FunDef} {args : List Value}
    {frame : Env} {n : Nat} {σ' : Store}
    (hlook : lookupFun p fd.name = .ok fd) (hn : p.funs.length = n + 1)
    (hframe : buildFrame m fd args = .ok frame)
    (hbody : execAt p (execStmt p n) fd.body (m.toStore frame)
      = .ok (σ', .normal)) :
    callFun p m fd.name args = .ok (σ'.toMem, none) := by
  simp only [callFun, hlook, hframe, bind, Except.bind, hn]
  rw [show execStmt p (n + 1) = execAt p (execStmt p n) from rfl, hbody]

theorem callFun_ret {p : Program} {m : Mem} {fd : FunDef} {args : List Value}
    {frame : Env} {n : Nat} {σ' : Store} {res : Option Value}
    (hlook : lookupFun p fd.name = .ok fd) (hn : p.funs.length = n + 1)
    (hframe : buildFrame m fd args = .ok frame)
    (hbody : execAt p (execStmt p n) fd.body (m.toStore frame)
      = .ok (σ', .ret res)) :
    callFun p m fd.name args = .ok (σ'.toMem, res) := by
  simp only [callFun, hlook, hframe, bind, Except.bind, hn]
  rw [show execStmt p (n + 1) = execAt p (execStmt p n) from rfl, hbody]

end CSubset

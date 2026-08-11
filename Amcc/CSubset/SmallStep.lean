import Amcc.CSubset.Eval

/-!
# AMCC — Phase 1: the normative small-step semantics

The relation the brief asks for, and the proof that `Eval.execStmt` agrees
with it.

## Why both

`execStmt` is the artifact everything downstream uses: it computes, so Phase 4
can drive it as an oracle and Phase 3 can unfold it by rewriting. But a
function is a poor *specification* — reading it means reading Lean's `do`
desugaring, and any bug in it is invisible, because the function is its own
definition of correctness.

`Step` is the specification. It is nineteen rules, each readable in isolation,
and it commits to nothing about evaluation strategy. `execStmt_sound` below
then says the function only ever produces behaviour the relation sanctions,
and `step_det` says the relation sanctions nothing else. Together they pin the
function down completely: an error in `execStmt` would have to be an error the
rules also make, and the rules are small enough to audit by eye.

## Getting stuck *is* the error

There is no error configuration in this relation. A configuration with no
successor is stuck, and that is exactly what an `Err` is in the functional
semantics. This makes "generated code never gets stuck" a statement about the
normative artifact rather than about an implementation detail — which is the
form Phase 3's obligation ought to take.

## Expressions stay atomic

`Step` refines statements, not expressions: `evalExpr` appears in side
conditions. That is sound here in a way it would not be for real C, because
Phase 0 made expressions pure and total — there is no interleaving to observe,
no sequence point to place, and no way for one subexpression to affect another.
Refining them further would add rules without adding content.
-/

namespace CSubset

/-! ## Configurations -/

/-- What to do after the current statement finishes. -/
inductive Cont where
  /-- Nothing left; the run is over. -/
  | halt : Cont
  /-- Then run this statement. -/
  | kseq : Stmt → Cont → Cont
  /-- Inside `for (x = i; ...)` with `rem` iterations left over `body`. -/
  | kloop : Ident → Nat → Nat → Stmt → Cont → Cont
  /-- Inside a call: where to put the result, and the caller's frame to
  restore. The frame is *saved in the continuation*, which is the small-step
  counterpart of `execAt` restoring `σ.loc` — and it is sound for the same
  reason, that no pointer can name a local. -/
  | kcall : Option Ident → Env → Cont → Cont

/-- A machine configuration. -/
inductive Config where
  /-- About to execute a statement. -/
  | run : Stmt → Store → Cont → Config
  /-- A statement finished normally; feed the continuation. -/
  | nxt : Store → Cont → Config
  /-- Unwinding a `return`. -/
  | rtn : Option Value → Store → Cont → Config
  /-- Terminal. -/
  | done : Option Value → Store → Config

/-- The configuration a finished statement lands in — the bridge between
`Outcome` (how the function reports completion) and `Config` (how the relation
does). -/
def outCfg : Outcome → Store → Cont → Config
  | .normal, σ, k => .nxt σ k
  | .ret v,  σ, k => .rtn v σ k

/-! ## The relation -/

/-- One step. Nineteen rules; a configuration with no successor is stuck, and
stuck is what an error is. -/
inductive Step (p : Program) : Config → Config → Prop where
  | skip {σ k} :
      Step p (.run .skip σ k) (.nxt σ k)
  | assign {l e σ k loc v σ'} :
      resolve σ l = .ok loc → evalExpr σ e = .ok v → writeLoc σ loc v = .ok σ' →
      Step p (.run (.assign l e) σ k) (.nxt σ' k)
  | seq {s₁ s₂ σ k} :
      Step p (.run (.seq s₁ s₂) σ k) (.run s₁ σ (.kseq s₂ k))
  | condT {c s₁ s₂ σ k} :
      evalExpr σ c = .ok (.bool true) →
      Step p (.run (.cond c s₁ s₂) σ k) (.run s₁ σ k)
  | condF {c s₁ s₂ σ k} :
      evalExpr σ c = .ok (.bool false) →
      Step p (.run (.cond c s₁ s₂) σ k) (.run s₂ σ k)
  | forN {x b n body σ k} :
      -- The bound is resolved once, as the loop is entered.
      evalIndex σ b = .ok n →
      Step p (.run (.forN x b body) σ k) (.nxt σ (.kloop x 0 n body k))
  | retNone {σ k} :
      Step p (.run (.ret none) σ k) (.rtn none σ k)
  | retSome {e σ k v} :
      evalExpr σ e = .ok v →
      Step p (.run (.ret (some e)) σ k) (.rtn (some v) σ k)
  | call {dst f args σ k fd vs frame} :
      lookupFun p f = .ok fd →
      args.mapM (evalExpr σ) = .ok vs →
      buildFrame σ.toMem fd vs = .ok frame →
      Step p (.run (.call dst f args) σ k)
             (.run fd.body (σ.toMem.toStore frame) (.kcall dst σ.loc k))
  -- Normal completion meets the continuation.
  | kseq {σ s k} :
      Step p (.nxt σ (.kseq s k)) (.run s σ k)
  | kloopDone {σ x i body k} :
      Step p (.nxt σ (.kloop x i 0 body k))
             (.nxt (σ.setLocal x (.u32 (UInt32.ofNat i))) k)
  | kloopNext {σ x i rem body k} :
      Step p (.nxt σ (.kloop x i (rem + 1) body k))
             (.run body (σ.setLocal x (.u32 (UInt32.ofNat i)))
                   (.kloop x (i + 1) rem body k))
  | kcallNone {σ lc k} :
      Step p (.nxt σ (.kcall none lc k)) (.nxt (σ.toMem.toStore lc) k)
  | haltNxt {σ} :
      Step p (.nxt σ .halt) (.done none σ)
  -- A `return` unwinds until it meets a call.
  | rtnSeq {v σ s k} :
      Step p (.rtn v σ (.kseq s k)) (.rtn v σ k)
  | rtnLoop {v σ x i rem body k} :
      Step p (.rtn v σ (.kloop x i rem body k)) (.rtn v σ k)
  | rtnCallNone {v σ lc k} :
      Step p (.rtn v σ (.kcall none lc k)) (.nxt (σ.toMem.toStore lc) k)
  | rtnCallSome {v σ x lc k σ'} :
      writeLoc (σ.toMem.toStore lc) (.lcl x) v = .ok σ' →
      Step p (.rtn (some v) σ (.kcall (some x) lc k)) (.nxt σ' k)
  | haltRtn {v σ} :
      Step p (.rtn v σ .halt) (.done v σ)

/-- Reflexive-transitive closure, built head-first so proofs compose forwards. -/
inductive Steps (p : Program) : Config → Config → Prop where
  | refl {c} : Steps p c c
  | head {c₁ c₂ c₃} : Step p c₁ c₂ → Steps p c₂ c₃ → Steps p c₁ c₃

theorem Steps.trans {p : Program} {a b c : Config} :
    Steps p a b → Steps p b c → Steps p a c
  | .refl,      h => h
  | .head s r,  h => .head s (r.trans h)

/-- One step is a run of steps. -/
theorem Steps.single {p : Program} {a b : Config} (s : Step p a b) : Steps p a b :=
  .head s .refl

/-! ## Determinism

The relation admits at most one successor per configuration. This is what
turns `execStmt_sound` into a full characterisation: the function's answer is
not merely *a* behaviour the rules allow, it is *the* behaviour. -/

/-- checked by: `lake build` -/
theorem step_det {p : Program} {c c₁ c₂ : Config}
    (h₁ : Step p c c₁) (h₂ : Step p c c₂) : c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

/-- A configuration with no successor. In this relation that is the whole
notion of "finished or broken": `done` is stuck because the run is over, and
anything else that is stuck is an error. -/
def Stuck (p : Program) (c : Config) : Prop := ∀ c', ¬ Step p c c'

/-- checked by: `lake build` -/
theorem done_stuck {p : Program} {v : Option Value} {σ : Store} :
    Stuck p (.done v σ) := by
  intro _ h; cases h

/-- Determinism lifted to whole runs: a configuration reaches at most one
stuck configuration.

checked by: `lake build` -/
theorem steps_stuck_unique {p : Program} :
    ∀ {c d₁ : Config}, Steps p c d₁ → Stuck p d₁ →
      ∀ {d₂ : Config}, Steps p c d₂ → Stuck p d₂ → d₁ = d₂ := by
  intro c d₁ r₁
  induction r₁ with
  | refl =>
    intro h₁ d₂ r₂ _
    cases r₂ with
    | refl     => rfl
    | head s _ => exact absurd s (h₁ _)
  | head s₁ _ ih =>
    intro h₁ d₂ r₂ h₂
    cases r₂ with
    | refl        => exact absurd s₁ (h₂ _)
    | head s₂ r₂' =>
      cases step_det s₁ s₂
      exact ih h₁ r₂' h₂

/-- Runs to a terminal configuration agree on the answer.

checked by: `lake build` -/
theorem steps_done_unique {p : Program} {c : Config} {v₁ v₂ : Option Value} {σ₁ σ₂ : Store}
    (r₁ : Steps p c (.done v₁ σ₁)) (r₂ : Steps p c (.done v₂ σ₂)) :
    v₁ = v₂ ∧ σ₁ = σ₂ := by
  have h := steps_stuck_unique r₁ done_stuck r₂ done_stuck
  cases h
  exact ⟨rfl, rfl⟩

/-! ## The executable semantics is sound for the relation

`execAt_sound` is the workhorse: it is stated for an arbitrary `callee`
together with the hypothesis that `callee` itself is sound, so that
`execStmt_sound` can discharge it by induction on the depth budget. That
mirrors exactly how `execAt`/`execStmt` are defined, which is why the proof
follows the structure of the definitions rather than fighting them. -/

/-- The loop, in isolation: `forLoop` driving `body` corresponds to the
`kloop` continuation unwinding.

checked by: `lake build` -/
theorem forLoop_sound {p : Program} {bodyExec : Store → Except Err (Store × Outcome)}
    {x : Ident} {body : Stmt}
    (hbody : ∀ σ σ' out k, bodyExec σ = .ok (σ', out) →
      Steps p (.run body σ k) (outCfg out σ' k)) :
    ∀ (rem i : Nat) (σ σ' : Store) (out : Outcome) (k : Cont),
      forLoop bodyExec x i rem σ = .ok (σ', out) →
      Steps p (.nxt σ (.kloop x i rem body k)) (outCfg out σ' k) := by
  intro rem
  induction rem with
  | zero =>
    intro i σ σ' out k h
    simp only [forLoop] at h
    cases h
    exact .single .kloopDone
  | succ rem ih =>
    intro i σ σ' out k h
    simp only [forLoop] at h
    obtain ⟨r, hb, h⟩ := bindOk h
    obtain ⟨σ₁, out₁⟩ := r
    cases out₁ with
    | normal =>
      exact .head .kloopNext
        ((hbody _ _ _ (.kloop x (i + 1) rem body k) hb).trans (ih _ _ _ _ _ h))
    | ret v =>
      cases h
      exact .head .kloopNext
        ((hbody _ _ _ (.kloop x (i + 1) rem body k) hb).trans (.single .rtnLoop))

/-- Every successful `execAt` run is a run of the relation.

checked by: `lake build` -/
theorem execAt_sound {p : Program} {callee : Stmt → Store → Except Err (Store × Outcome)}
    (hcallee : ∀ bd σ σ' out k, callee bd σ = .ok (σ', out) →
      Steps p (.run bd σ k) (outCfg out σ' k)) :
    ∀ (s : Stmt) (σ σ' : Store) (out : Outcome) (k : Cont),
      execAt p callee s σ = .ok (σ', out) →
      Steps p (.run s σ k) (outCfg out σ' k) := by
  intro s
  induction s with
  | skip =>
    intro σ σ' out k h
    simp only [execAt] at h
    cases h
    exact .single .skip
  | assign l e =>
    intro σ σ' out k h
    simp only [execAt] at h
    obtain ⟨loc, hres, h⟩ := bindOk h
    obtain ⟨v, hev, h⟩ := bindOk h
    obtain ⟨σ'', hw, h⟩ := bindOk h
    cases h
    exact .single (.assign hres hev hw)
  | seq s₁ s₂ ih₁ ih₂ =>
    intro σ σ' out k h
    simp only [execAt] at h
    obtain ⟨r, h₁, h⟩ := bindOk h
    obtain ⟨σ₁, out₁⟩ := r
    cases out₁ with
    | normal =>
      exact .head .seq
        ((ih₁ σ σ₁ .normal (.kseq s₂ k) h₁).trans (.head .kseq (ih₂ σ₁ σ' out k h)))
    | ret v =>
      cases h
      exact .head .seq
        ((ih₁ _ _ _ (.kseq s₂ k) h₁).trans (.single .rtnSeq))
  | cond c s₁ s₂ ih₁ ih₂ =>
    intro σ σ' out k h
    simp only [execAt] at h
    obtain ⟨v, hc, h⟩ := bindOk h
    cases v with
    | bool b =>
      cases b with
      | true  => exact .head (.condT hc) (ih₁ σ σ' out k h)
      | false => exact .head (.condF hc) (ih₂ σ σ' out k h)
    | u8 _    => exact Except.noConfusion h
    | u32 _   => exact Except.noConfusion h
    | u64 _   => exact Except.noConfusion h
    | ptr _   => exact Except.noConfusion h
    | null    => exact Except.noConfusion h
    | strct _ => exact Except.noConfusion h
    | arr _   => exact Except.noConfusion h
  | forN x b body ih =>
    intro σ σ' out k h
    simp only [execAt] at h
    obtain ⟨n, hb, h⟩ := bindOk h
    exact .head (.forN hb)
      (forLoop_sound (fun σ σ' out k hb' => ih σ σ' out k hb') n 0 σ σ' out k h)
  | call dst f args =>
    intro σ σ' out k h
    simp only [execAt] at h
    obtain ⟨fd, hf, h⟩ := bindOk h
    obtain ⟨vs, hvs, h⟩ := bindOk h
    obtain ⟨frame, hfr, h⟩ := bindOk h
    obtain ⟨r, hc, h⟩ := bindOk h
    obtain ⟨σ₁, out₁⟩ := r
    have hbody := hcallee fd.body (σ.toMem.toStore frame) σ₁ out₁
                    (.kcall dst σ.loc k) hc
    cases dst with
    | none =>
      cases out₁ with
      | normal =>
        cases h
        exact .head (.call hf hvs hfr) (hbody.trans (.single .kcallNone))
      | ret v =>
        cases h
        exact .head (.call hf hvs hfr) (hbody.trans (.single .rtnCallNone))
    | some x =>
      cases out₁ with
      | normal => exact Except.noConfusion h
      | ret ov =>
        cases ov with
        | none => exact Except.noConfusion h
        | some v =>
          obtain ⟨σ₃, hw, h⟩ := bindOk h
          cases h
          exact .head (.call hf hvs hfr) (hbody.trans (.single (.rtnCallSome hw)))
  | ret oe =>
    intro σ σ' out k h
    cases oe with
    | none =>
      simp only [execAt] at h
      cases h
      exact .single .retNone
    | some e =>
      simp only [execAt] at h
      obtain ⟨v, hev, h⟩ := bindOk h
      cases h
      exact .single (.retSome hev)

/-- **The executable semantics is sound for the normative one.**

Anything `execStmt` computes, the relation sanctions — at any call-depth
budget, including budgets too small to finish, since a budget that runs out
simply produces no `.ok` to talk about.

checked by: `lake build` -/
theorem execStmt_sound {p : Program} :
    ∀ (d : Nat) (s : Stmt) (σ σ' : Store) (out : Outcome) (k : Cont),
      execStmt p d s σ = .ok (σ', out) →
      Steps p (.run s σ k) (outCfg out σ' k) := by
  intro d
  induction d with
  | zero =>
    exact execAt_sound (fun _ _ _ _ _ h => Except.noConfusion h)
  | succ d ih =>
    exact execAt_sound (fun bd σ σ' out k h => ih bd σ σ' out k h)

/-- **The two semantics agree.**

Combining soundness with determinism: when `execStmt` succeeds, the relation
reaches the corresponding terminal configuration, and reaches no other. So the
function is not merely consistent with the specification — it computes the
specification.

checked by: `lake build` -/
theorem exec_iff_steps {p : Program} {d : Nat} {s : Stmt} {σ σ' : Store} {v : Option Value}
    (h : execStmt p d s σ = .ok (σ', .ret v)) :
    Steps p (.run s σ .halt) (.done v σ')
    ∧ ∀ {w σ''}, Steps p (.run s σ .halt) (.done w σ'') → w = v ∧ σ'' = σ' := by
  have hrun : Steps p (.run s σ .halt) (.done v σ') :=
    (execStmt_sound d s σ σ' (.ret v) .halt h).trans (.single .haltRtn)
  exact ⟨hrun, fun hw => steps_done_unique hw hrun⟩

end CSubset

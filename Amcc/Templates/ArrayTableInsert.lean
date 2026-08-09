import Amcc.Templates.ArrayTableErase

/-!
# AMCC — `insert` refines `Abs.insert`

`erase` writes one field of one slot. `insert` writes *many*: the update path
overwrites every value field of the row `find` returned, and the fresh-slot
path sets the occupancy flag and then every schema field of the first free
slot. So the ingredient `erase` did not need, and this file starts with, is a
statement about a **block of field assignments** — `exec_assignFields` — proved
once and used by both paths.

Two design notes on that lemma.

It is stated over a list of `(name, value)` **pairs** rather than over
`Schema.Field`s, because the generated statement list is then literally
`ps.map (fun q => .assign (lv q.1) (.rd (.var q.1)))` and `List.map_map` closes
the gap to what the generator emits, whichever field list it emitted from.

Its lvalue arrives as a function `lv : Ident → LVal` together with a
*resolution* hypothesis quantified over stores. That is what lets one lemma
serve both `_at->f` (a pointer from `find`) and `g_<t>[_j].f` (a loop index):
the two lvalue forms resolve for different reasons, but they resolve to the
same path, and the writes in between change only the storage global — never
the frame the resolution depends on.

The accumulated effect of the writes is `setFields`, a left fold of `Env.set`.
Everything downstream — that the row's key, occupancy and value fields read
back as intended — is a statement about `setFields`, proved here in the small
before any of it meets the generator.
-/

namespace Templates
namespace ArrayTable

open CSubset

variable {s : Schema} {σ : Store}

/-! ## List facts

Three small facts about `List.set` that core states in shapes this proof does
not want (`i < length` side conditions where a `getElem?` fact is what is in
hand). Proved directly rather than adapted. -/

theorem set_self_of_getElem? {α : Type _} :
    ∀ (l : List α) (i : Nat) (a : α), l[i]? = some a → l.set i a = l
  | [], _, _, h => by simp at h
  | x :: xs, 0, a, h => by
    have : x = a := by simpa using h
    simp [List.set, this]
  | x :: xs, i + 1, a, h => by
    simp only [List.set]
    rw [set_self_of_getElem? xs i a (by simpa using h)]

theorem getElem?_set_self' {α : Type _} :
    ∀ (l : List α) (i : Nat) (a b : α), l[i]? = some b → (l.set i a)[i]? = some a
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => rfl
  | x :: xs, i + 1, a, b, h => by
    simp only [List.set]
    simpa using getElem?_set_self' xs i a b (by simpa using h)

theorem getElem?_set_ne' {α : Type _} :
    ∀ (l : List α) (i j : Nat) (a : α), i ≠ j → (l.set i a)[j]? = l[j]?
  | [], _, _, _, _ => by simp
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | x :: xs, i + 1, j + 1, a, h => by
    simp only [List.set]
    simpa using getElem?_set_ne' xs i j a (fun e => h (by omega))

/-- `mapM` in the `Option` monad succeeds with `r` when it succeeds pointwise.
Stated by index rather than by `Forall₂` because the two lists this is used on
— the schema's value fields and the argument values — are related by a length
equation, not by a zip. -/
theorem mapM_eq_some {α β : Type _} {g : α → Option β} :
    ∀ (l : List α) (r : List β), l.length = r.length →
      (∀ t, ∀ (h₁ : t < l.length) (h₂ : t < r.length), g (l[t]'h₁) = some (r[t]'h₂)) →
      l.mapM g = some r := by
  intro l
  induction l with
  | nil => intro r hlen _; cases r with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro r hlen h
    cases r with
    | nil => simp at hlen
    | cons b bs =>
      have h0 := h 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0
      have hrest : ∀ t, ∀ (h₁ : t < as.length) (h₂ : t < bs.length),
          g (as[t]'h₁) = some (bs[t]'h₂) := by
        intro t h₁ h₂
        simpa using h (t + 1) (by simp; omega) (by simp; omega)
      simp [List.mapM_cons, h0, ih bs (by simpa using hlen) hrest]

/-! ## `setFields` — the accumulated effect of a block of writes -/

/-- Write each `(name, value)` pair into the environment, left to right.
Written as a fold of `Env.set` so that it inherits `Env.set`'s domain
invariance: a block of field writes cannot add or remove a field. -/
def setFields (fs : Env) : List (Ident × Value) → Env
  | []           => fs
  | (n, v) :: ps => setFields (Env.set fs n v) ps

theorem get?_set_isSome (fs : Env) (x n : Ident) (v : Value) :
    ((Env.set fs x v).get? n).isSome = (fs.get? n).isSome := by
  by_cases h : n = x
  · subst h; rw [Env.get?_set_self]; cases fs.get? n <;> rfl
  · rw [Env.get?_set_ne _ h]

/-- The domain is invariant, so `RowOk`'s "this field is present" clauses
survive any number of writes. -/
theorem setFields_isSome : ∀ (ps : List (Ident × Value)) (fs : Env) (n : Ident),
    ((setFields fs ps).get? n).isSome = (fs.get? n).isSome
  | [], _, _ => rfl
  | (m, w) :: ps, fs, n => by
    show ((setFields (Env.set fs m w) ps).get? n).isSome = _
    rw [setFields_isSome ps, get?_set_isSome]

/-- A name none of the writes mentions reads back unchanged. -/
theorem setFields_get_ne : ∀ (ps : List (Ident × Value)) (fs : Env) (n : Ident),
    (∀ q ∈ ps, q.1 ≠ n) → (setFields fs ps).get? n = fs.get? n
  | [], _, _, _ => rfl
  | (m, w) :: ps, fs, n, h => by
    show (setFields (Env.set fs m w) ps).get? n = _
    rw [setFields_get_ne ps _ n (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      Env.get?_set_ne _ (Ne.symm (h (m, w) (by simp)))]

/-- A name written exactly once reads back as what was written. `Pairwise` is
what rules out a later write clobbering it — and it is exactly the schema
check's duplicate-field clause, arriving here for the first time. -/
theorem setFields_get_mem :
    ∀ (ps : List (Ident × Value)) (fs : Env) (n : Ident) (v : Value),
      (ps.map Prod.fst).Pairwise (· ≠ ·) → (n, v) ∈ ps →
      (fs.get? n).isSome = true → (setFields fs ps).get? n = some v
  | [], _, _, _, _, hm, _ => absurd hm (by simp)
  | (m, w) :: ps, fs, n, v, hpw, hm, hdom => by
    show (setFields (Env.set fs m w) ps).get? n = _
    rcases List.mem_cons.mp hm with he | hm'
    · have h1 : n = m := congrArg Prod.fst he
      have h2 : v = w := congrArg Prod.snd he
      subst h1; subst h2
      have hnot : ∀ q ∈ ps, q.1 ≠ n :=
        fun q hq => Ne.symm ((List.pairwise_cons.mp hpw).1 q.1 (List.mem_map_of_mem hq))
      rw [setFields_get_ne ps _ n hnot, Env.get?_set_self]
      cases hg : fs.get? n with
      | none => rw [hg] at hdom; exact absurd hdom (by simp)
      | some _ => rfl
    · exact setFields_get_mem ps _ n v
        (List.Pairwise.of_cons (by simpa using hpw)) hm'
        (by rw [get?_set_isSome]; exact hdom)

/-! ## What the writes do to the abstraction of a row -/

theorem rowKey_setFields {fs : Env} {pk : Schema.Field} {ps : List (Ident × Value)}
    (hpk : Schema.pkey? s = some pk) (hne : ∀ q ∈ ps, q.1 ≠ pk.name) :
    rowKey? s (.strct (setFields fs ps)) = rowKey? s (.strct fs) := by
  simp [rowKey?, hpk, setFields_get_ne ps fs pk.name hne]

theorem rowOccupied_setFields {fs : Env} {ps : List (Ident × Value)}
    (hne : ∀ q ∈ ps, q.1 ≠ (Schema.names s).occupied) :
    rowOccupied s (.strct (setFields fs ps)) = rowOccupied s (.strct fs) := by
  simp [rowOccupied, setFields_get_ne ps fs (Schema.names s).occupied hne]

/-! ## Peeling a statement

`simp only [execAt]` unfolds too far to be useful once a hypothesis is stated
about `resolve` or `evalExpr`; these rewrite exactly one constructor and stop,
which is what lets the hypotheses match. -/

theorem execAt_assign {p : Program} {callee} (l : LVal) (e : Expr) (σ : Store) :
    execAt p callee (.assign l e) σ = (do
      let loc ← resolve σ l
      let v ← evalExpr σ e
      let σ' ← writeLoc σ loc v
      .ok (σ', .normal)) := rfl

theorem execAt_forN {p : Program} {callee} (x : Ident) (b : Index) (body : Stmt)
    (σ : Store) :
    execAt p callee (.forN x b body) σ = (do
      let n ← evalIndex σ b
      forLoop (execAt p callee body) x 0 n σ) := rfl

/-- `Stmt.block` collapses a singleton, so `block (a :: as)` is not
syntactically a `.seq`. It behaves like one, which is what the induction on a
statement list needs. -/
theorem execAt_block_cons {p : Program} {callee} (a : Stmt) (as : List Stmt)
    (σ : Store) :
    execAt p callee (Stmt.block (a :: as)) σ
      = execAt p callee (.seq a (Stmt.block as)) σ := by
  cases as with
  | cons _ _ => rfl
  | nil =>
    show execAt p callee a σ = _
    rw [execAt_seq]
    cases h : execAt p callee a σ with
    | error _ => rfl
    | ok r =>
      obtain ⟨σ₁, o⟩ := r
      cases o with
      | normal => rfl
      | ret _ => rfl

/-- A block that runs to `normal` followed by a trailing statement. Used for
the `…; return true` shape both `insert` paths end in. -/
theorem execAt_block_append {p : Program} {callee} :
    ∀ (xs : List Stmt) (y : Stmt) (σ σ' : Store),
      execAt p callee (Stmt.block xs) σ = .ok (σ', .normal) →
      execAt p callee (Stmt.block (xs ++ [y])) σ = execAt p callee y σ'
  | [], y, σ, σ', h => by
    have : σ' = σ := by
      have : (Except.ok (σ, Outcome.normal) : Except Err (Store × Outcome))
          = .ok (σ', .normal) := h
      exact (congrArg Prod.fst (Except.ok.inj this)).symm
    subst this; rfl
  | x :: xs, y, σ, σ', h => by
    rw [List.cons_append, execAt_block_cons, execAt_seq]
    rw [execAt_block_cons, execAt_seq] at h
    cases hx : execAt p callee x σ with
    | error _ => rw [hx] at h; simp [bind, Except.bind] at h
    | ok r =>
      obtain ⟨σ₁, o⟩ := r
      cases o with
      | ret _ => rw [hx] at h; simp [bind, Except.bind] at h
      | normal =>
        rw [hx] at h
        simp only [bind, Except.bind] at h ⊢
        exact execAt_block_append xs y σ₁ σ' h

/-! ## A block of field assignments

The lemma the rest of the file is built on. -/

/-- **Executing `p->f = f;` (or `g[j].f = f;`) once per pair.**

The store afterwards differs from the store before in exactly one slot, whose
value is `setFields` of the pairs — and in nothing else, which is what carries
`RepInv`'s other clauses across.

checked by: `lake build` -/
theorem exec_assignFields {p : Program} {callee} {i : Nat} {lv : Ident → LVal}
    {L : Env}
    (hres : ∀ (τ : Store) (n : Ident) (gs : Env),
        τ.loc = L →
        τ.glb.get? (Schema.names s).storage = some (.arr (rowsOf s τ.glb)) →
        (rowsOf s τ.glb)[i]? = some (.strct gs) →
        (Env.get? gs n).isSome = true →
        resolve τ (lv n)
          = .ok (.glb ⟨.glob (Schema.names s).storage, [.idx i, .fld n]⟩)) :
    ∀ (ps : List (Ident × Value)) (fs : Env) (σ : Store),
      σ.loc = L →
      σ.glb.get? (Schema.names s).storage = some (.arr (rowsOf s σ.glb)) →
      (rowsOf s σ.glb)[i]? = some (.strct fs) →
      (∀ q ∈ ps, (Env.get? fs q.1).isSome = true) →
      (∀ q ∈ ps, σ.getLocal q.1 = some q.2) →
      ∃ σ',
        execAt p callee
            (.block (ps.map (fun q => .assign (lv q.1) (.rd (.var q.1))))) σ
          = .ok (σ', .normal)
        ∧ rowsOf s σ'.glb = (rowsOf s σ.glb).set i (.strct (setFields fs ps))
        ∧ σ'.glb.get? (Schema.names s).storage = some (.arr (rowsOf s σ'.glb))
        ∧ σ'.loc = σ.loc ∧ σ'.hp = σ.hp ∧ σ'.next = σ.next := by
  intro ps
  induction ps with
  | nil =>
    intro fs σ _ hglb hrow _ _
    exact ⟨σ, rfl, (set_self_of_getElem? _ i _ hrow).symm, hglb, rfl, rfl, rfl⟩
  | cons q ps ih =>
    obtain ⟨qn, qv⟩ := q
    intro fs σ hloc hglb hrow hdom hlocs
    have hqdom : (Env.get? fs qn).isSome = true := hdom (qn, qv) (by simp)
    have hres1 := hres σ qn fs hloc hglb hrow hqdom
    have hval : σ.getLocal qn = some qv := hlocs (qn, qv) (by simp)
    obtain ⟨σ₁, hwr, hrows1, hstore1, hloc1, hhp1, hnx1⟩ :=
      write_slotField (s := s) (σ := σ) (i := i) (row := .strct fs) (fs := fs)
        (f := qn) (w := qv) hglb hrow rfl hqdom
    have hstep : execAt p callee (.assign (lv qn) (.rd (.var qn))) σ
        = .ok (σ₁, .normal) := by
      rw [execAt_assign]
      simp only [hres1, read_local hval, hwr, bind, Except.bind]
    have hrow1 : (rowsOf s σ₁.glb)[i]? = some (.strct (Env.set fs qn qv)) := by
      rw [hrows1]; exact getElem?_set_self' _ i _ _ hrow
    have hlocEq : ∀ n, σ₁.getLocal n = σ.getLocal n := by
      intro n; simp only [Store.getLocal, hloc1]
    obtain ⟨σ', hbody, hrows', hstore', hloc', hhp', hnx'⟩ :=
      ih (Env.set fs qn qv) σ₁ (by rw [hloc1, hloc]) hstore1 hrow1
        (fun r hr => by
          rw [get?_set_isSome]; exact hdom r (List.mem_cons_of_mem _ hr))
        (fun r hr => by
          rw [hlocEq]; exact hlocs r (List.mem_cons_of_mem _ hr))
    refine ⟨σ', ?_, ?_, hstore', by rw [hloc', hloc1], by rw [hhp', hhp1],
      by rw [hnx', hnx1]⟩
    · rw [List.map_cons, execAt_block_cons, execAt_seq, hstep]
      simpa [bind, Except.bind] using hbody
    · rw [hrows', hrows1, List.set_set]
      rfl

/-! ## Scanning facts

`firstMatch_lt` says the scan is a *first* match: every earlier slot was
checked and missed. That is what turns "slot `j` matches" into "`List.find?`
stops at slot `j`", which is what `absOf` is defined by. -/

theorem firstMatch_lt {glb : Env} {k : Interface.Key} :
    ∀ (rem i j : Nat), firstMatch s glb k i rem = some j →
      ∀ t, i ≤ t → t < j → slotMatches s glb k t = false := by
  intro rem
  induction rem with
  | zero => intro i j h; exact Option.noConfusion h
  | succ rem ih =>
    intro i j h t hit htj
    cases hm : slotMatches s glb k i with
    | true =>
      simp only [firstMatch, hm, if_true] at h
      cases h; omega
    | false =>
      simp only [firstMatch, hm, Bool.false_eq_true, if_false] at h
      rcases Nat.eq_or_lt_of_le hit with rfl | hlt
      · exact hm
      · exact ih (i + 1) j h t hlt htj

/-- The mirror of `find?_set_of_neg`: when the replacement *does* satisfy the
predicate and nothing before it does, `find?` stops at the replaced slot. -/
theorem find?_set_of_pos {α : Type _} {p : α → Bool} :
    ∀ (l : List α) (i : Nat) (x y : α), l[i]? = some y → p x = true →
      (∀ t, t < i → ∀ z, l[t]? = some z → p z = false) →
      (l.set i x).find? p = some x
  | [], _, _, _, h, _, _ => by simp at h
  | a :: as, 0, x, _, _, hx, _ => by
    show List.find? p (x :: as) = some x
    rw [List.find?_cons_of_pos hx]
  | a :: as, i + 1, x, y, h, hx, hlt => by
    have hna : p a = false := hlt 0 (by omega) a rfl
    show List.find? p (a :: as.set i x) = some x
    rw [List.find?_cons_of_neg (by simp [hna])]
    exact find?_set_of_pos as i x y (by simpa using h) hx
      (fun t ht z hz => hlt (t + 1) (by omega) z (by simpa using hz))

/-! ## The frame `insert` runs against

`insert`'s parameters are the key and every value field, in schema order; its
locals are the row pointer `find` fills in and the free-slot scan's index. The
frame is therefore a zip followed by two fixed entries, and every fact the
proof needs about it is a lookup into that shape. -/

theorem bindParams_zip : ∀ (ps : List (Ident × ValTy)) (vs : List Value),
    ps.length = vs.length → bindParams ps vs = .ok ((ps.map Prod.fst).zip vs)
  | [], [], _ => rfl
  | (x, _) :: ps, v :: vs, h => by
    show (do let rest ← bindParams ps vs; Except.ok ((x, v) :: rest)) = _
    rw [bindParams_zip ps vs (by simpa using h)]
    rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem get?_zip_append : ∀ (ns : List Ident) (ws : List Value) (rest : Env) (t : Nat)
    (h1 : t < ns.length) (h2 : t < ws.length), ns.Pairwise (· ≠ ·) →
    Env.get? (ns.zip ws ++ rest) (ns[t]'h1) = some (ws[t]'h2)
  | [], _, _, _, h1, _, _ => absurd h1 (by simp)
  | _ :: _, [], _, _, _, h2, _ => absurd h2 (by simp)
  | n :: _, w :: _, _, 0, _, _, _ => by
    show Env.get? ((n, w) :: _) n = _
    simp [Env.get?]
  | n :: ns, w :: ws, rest, t + 1, h1, h2, hpw => by
    have hlt : t < ns.length := by simpa using h1
    have hne : n ≠ ns[t] :=
      (List.pairwise_cons.mp hpw).1 _ (List.getElem_mem hlt)
    show Env.get? ((n, w) :: (ns.zip ws ++ rest)) (ns[t]'hlt) = _
    simp only [Env.get?, if_neg hne]
    exact get?_zip_append ns ws rest t hlt (by simpa using h2)
      (List.Pairwise.of_cons hpw)

theorem get?_zip_append_ne :
    ∀ (ns : List Ident) (ws : List Value) (rest : Env) (n : Ident),
      (∀ m ∈ ns, m ≠ n) → Env.get? (ns.zip ws ++ rest) n = Env.get? rest n
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | a :: ns, w :: ws, rest, n, h => by
    show Env.get? ((a, w) :: (ns.zip ws ++ rest)) n = _
    simp only [Env.get?, if_neg (h a (by simp))]
    exact get?_zip_append_ne ns ws rest n (fun m hm => h m (List.mem_cons_of_mem _ hm))

/-- The parameter names of the generated `insert`, in order. -/
def parNames (s : Schema) (pk : Schema.Field) : List Ident :=
  (pk :: Schema.valFields s).map Schema.Field.name

/-- The frame itself. -/
def insFrame (s : Schema) (pk : Schema.Field) (k : Interface.Key)
    (vs : List Value) : Env :=
  (parNames s pk).zip (k.toValue :: vs) ++ [(tmpAt, .null), (tmpJ, .u32 0)]

theorem buildFrame_insert {m : Mem} {pk : Schema.Field} {k : Interface.Key}
    {vs : List Value} (hlen : vs.length = (Schema.valFields s).length) :
    buildFrame m (insertDef s pk) (k.toValue :: vs) = .ok (insFrame s pk k vs) := by
  have hp : ((pk :: Schema.valFields s).map
      (fun f => (f.name, ValTy.scalar f.ty))).length = (k.toValue :: vs).length := by
    simp [hlen]
  show (do
    let params ← bindParams ((pk :: Schema.valFields s).map
      (fun (f : Schema.Field) => (f.name, ValTy.scalar f.ty))) (k.toValue :: vs)
    (insertDef s pk).locals.foldlM
      (fun (acc : Env) (ld : LocalDef) => do
        let v ← evalExpr (m.toStore acc) ld.init
        Except.ok (acc ++ [(ld.name, v)])) params) = _
  rw [bindParams_zip _ _ hp]
  simp only [insertDef, insFrame, parNames, List.map_map, Function.comp_def,
    List.foldlM, atLocal, LocalDef.zeroed, nullRow, evalExpr, bind, Except.bind,
    pure, List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- The value the frame binds a name to. Total, so it can be used in the pair
list without a proof obligation at every occurrence; every use is accompanied
by a lookup lemma that pins it down. -/
def frameVal (s : Schema) (pk : Schema.Field) (k : Interface.Key)
    (vs : List Value) (n : Ident) : Value :=
  ((insFrame s pk k vs).get? n).getD .null

section FrameFacts

variable {pk : Schema.Field} {k : Interface.Key} {vs : List Value}

theorem insFrame_get_pk (hpw : (parNames s pk).Pairwise (· ≠ ·)) :
    (insFrame s pk k vs).get? pk.name = some k.toValue := by
  have := get?_zip_append (parNames s pk) (k.toValue :: vs)
    [(tmpAt, Value.null), (tmpJ, .u32 0)] 0 (by simp [parNames]) (by simp) hpw
  simpa [parNames] using this

theorem insFrame_get_val (hpw : (parNames s pk).Pairwise (· ≠ ·)) (t : Nat)
    (h1 : t < (Schema.valFields s).length) (h2 : t < vs.length) :
    (insFrame s pk k vs).get? (((Schema.valFields s)[t]'h1).name)
      = some (vs[t]'h2) := by
  have := get?_zip_append (parNames s pk) (k.toValue :: vs)
    [(tmpAt, Value.null), (tmpJ, .u32 0)] (t + 1)
    (by simp [parNames]; omega) (by simp; omega) hpw
  simpa [parNames] using this

theorem insFrame_get_reserved {n : Ident}
    (hres : ∀ f ∈ s.fields, Schema.isReservedName f.name = false)
    (hn : Schema.isReservedName n = true) (hfl : s.fields.filter
      (fun f => f.reftype == .Pkey) = [pk]) :
    (insFrame s pk k vs).get? n
      = Env.get? [(tmpAt, Value.null), (tmpJ, .u32 0)] n := by
  refine get?_zip_append_ne _ _ _ n ?_
  intro m hm
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
  have hgmem : g ∈ s.fields := by
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact pk_mem hfl
    · exact (val_mem hg').1
  exact ne_of_reserved (hres g hgmem) hn

theorem insFrame_get_at (hres : ∀ f ∈ s.fields, Schema.isReservedName f.name = false)
    (hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk]) :
    (insFrame s pk k vs).get? tmpAt = some .null := by
  rw [insFrame_get_reserved hres (by decide) hfl]; rfl

theorem insFrame_get_j (hres : ∀ f ∈ s.fields, Schema.isReservedName f.name = false)
    (hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk]) :
    (insFrame s pk k vs).get? tmpJ = some (.u32 0) := by
  rw [insFrame_get_reserved hres (by decide) hfl]; rfl

/-- Every schema field's name is bound in the frame — the key by the first
parameter, a value field by its own. -/
theorem insFrame_isSome (hpw : (parNames s pk).Pairwise (· ≠ ·))
    (hlen : vs.length = (Schema.valFields s).length)
    (hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk])
    {f : Schema.Field} (hf : f ∈ s.fields) :
    ((insFrame s pk k vs).get? f.name).isSome = true := by
  rcases List.mem_cons.mp (mem_pk_cons hfl hf) with rfl | hv
  · rw [insFrame_get_pk hpw]; rfl
  · obtain ⟨t, h1, ht⟩ := List.getElem_of_mem hv
    have h2 : t < vs.length := by omega
    rw [← ht, insFrame_get_val hpw t h1 h2]; rfl

theorem frameVal_pk (hpw : (parNames s pk).Pairwise (· ≠ ·)) :
    frameVal s pk k vs pk.name = k.toValue := by
  simp [frameVal, insFrame_get_pk hpw]

theorem frameVal_val (hpw : (parNames s pk).Pairwise (· ≠ ·)) (t : Nat)
    (h1 : t < (Schema.valFields s).length) (h2 : t < vs.length) :
    frameVal s pk k vs (((Schema.valFields s)[t]'h1).name) = vs[t]'h2 := by
  simp [frameVal, insFrame_get_val hpw t h1 h2]

end FrameFacts

/-! ## Updating a row in place

The state content of `insert`'s update path: overwriting a row's value fields
leaves its key and its occupancy alone, so `RepInv`'s `distinct` clause — the
only global one — transfers slot by slot, and `absOf` changes at exactly one
key.

These are stated about `setFields` rather than about the generator, so nothing
here depends on which field list the emitted block came from. -/

theorem rowVals_setFields_eq {base : Env} {ps : List (Ident × Value)}
    {vs : List Value}
    (hpw : (ps.map Prod.fst).Pairwise (· ≠ ·))
    (hdom : ∀ f ∈ Schema.valFields s, (base.get? f.name).isSome = true)
    (hlen : (Schema.valFields s).length = vs.length)
    (hmem : ∀ t, ∀ (h1 : t < (Schema.valFields s).length) (h2 : t < vs.length),
      ((((Schema.valFields s)[t]'h1).name), vs[t]'h2) ∈ ps) :
    rowVals? s (.strct (setFields base ps)) = some vs :=
  mapM_eq_some _ _ hlen fun t h1 h2 =>
    setFields_get_mem ps base _ _ hpw (hmem t h1 h2) (hdom _ (List.getElem_mem h1))

theorem rowKey_setFields_eq {base : Env} {ps : List (Ident × Value)}
    {pk : Schema.Field} {k : Interface.Key}
    (hpk : Schema.pkey? s = some pk)
    (hpw : (ps.map Prod.fst).Pairwise (· ≠ ·))
    (hdom : (base.get? pk.name).isSome = true)
    (hmem : (pk.name, k.toValue) ∈ ps) :
    rowKey? s (.strct (setFields base ps)) = some k := by
  have hg : Env.get? (setFields base ps) pk.name = some k.toValue :=
    setFields_get_mem ps base pk.name k.toValue hpw hmem hdom
  simp [rowKey?, hpk, hg, Interface.Key.ofValue_toValue]

/-- A row keeps its shape when its value fields are overwritten. -/
theorem rowOk_setFields {fs : Env} {ps : List (Ident × Value)} {pk : Schema.Field}
    (hpk : Schema.pkey? s = some pk)
    (hnepk : ∀ q ∈ ps, q.1 ≠ pk.name)
    (hneocc : ∀ q ∈ ps, q.1 ≠ (Schema.names s).occupied)
    (hvals : (rowVals? s (.strct (setFields fs ps))).isSome = true)
    (h : RowOk s (.strct fs)) : RowOk s (.strct (setFields fs ps)) where
  occupied := by
    obtain ⟨b, hb⟩ := h.occupied
    exact ⟨b, by
      show Env.get? (setFields fs ps) (Schema.names s).occupied = some (.bool b)
      rw [setFields_get_ne ps fs _ hneocc]; exact hb⟩
  key := by rw [rowKey_setFields hpk hnepk]; exact h.key
  keyTy := by
    intro pk' k' hpk' hrk
    rw [rowKey_setFields hpk hnepk] at hrk
    exact h.keyTy pk' k' hpk' hrk
  vals := hvals

/-- Every slot of the updated array corresponds to a slot of the original with
the same key and the same occupancy — the fact `distinct` and `absOf` both
turn on. -/
theorem update_slot {glb glb' : Env} {j : Nat} {fs : Env}
    {ps : List (Ident × Value)} {pk : Schema.Field}
    (hpk : Schema.pkey? s = some pk)
    (hnepk : ∀ q ∈ ps, q.1 ≠ pk.name)
    (hneocc : ∀ q ∈ ps, q.1 ≠ (Schema.names s).occupied)
    (hrow : (rowsOf s glb)[j]? = some (.strct fs))
    (hrows : rowsOf s glb' = (rowsOf s glb).set j (.strct (setFields fs ps)))
    (t : Nat) (r : Value) (h : (rowsOf s glb')[t]? = some r) :
    ∃ r0, (rowsOf s glb)[t]? = some r0
      ∧ rowKey? s r = rowKey? s r0 ∧ rowOccupied s r = rowOccupied s r0 := by
  by_cases htj : t = j
  · subst htj
    rw [hrows, getElem?_set_self' _ t _ _ hrow] at h
    cases h
    exact ⟨.strct fs, hrow, rowKey_setFields hpk hnepk, rowOccupied_setFields hneocc⟩
  · rw [hrows, getElem?_set_ne' _ j t _ (fun e => htj e.symm)] at h
    exact ⟨r, h, rfl, rfl⟩

/-- **The representation invariant survives an in-place update.**

checked by: `lake build` -/
theorem repInv_update {glb glb' : Env} {j : Nat} {fs : Env}
    {ps : List (Ident × Value)} {pk : Schema.Field}
    (R : RepInv s glb) (hpk : Schema.pkey? s = some pk)
    (hnepk : ∀ q ∈ ps, q.1 ≠ pk.name)
    (hneocc : ∀ q ∈ ps, q.1 ≠ (Schema.names s).occupied)
    (hrow : (rowsOf s glb)[j]? = some (.strct fs))
    (hvals : (rowVals? s (.strct (setFields fs ps))).isSome = true)
    (hrows : rowsOf s glb' = (rowsOf s glb).set j (.strct (setFields fs ps)))
    (hstore : glb'.get? (Schema.names s).storage = some (.arr (rowsOf s glb'))) :
    RepInv s glb' where
  storage := hstore
  length := by rw [hrows, List.length_set]; exact R.length
  rows := by
    intro r hr
    obtain ⟨t, ht, htr⟩ := List.getElem_of_mem hr
    have hget : (rowsOf s glb')[t]? = some r := by
      rw [List.getElem?_eq_getElem ht, htr]
    by_cases htj : t = j
    · subst htj
      rw [hrows, getElem?_set_self' _ t _ _ hrow] at hget
      cases hget
      exact rowOk_setFields hpk hnepk hneocc hvals
        (R.rows _ (List.mem_of_getElem? hrow))
    · rw [hrows, getElem?_set_ne' _ j t _ (fun e => htj e.symm)] at hget
      exact R.rows _ (List.mem_of_getElem? hget)
  distinct := by
    intro a b ra rb hga hgb hoa hob hkab
    obtain ⟨ra0, hga0, hka, hoa0⟩ :=
      update_slot hpk hnepk hneocc hrow hrows a ra hga
    obtain ⟨rb0, hgb0, hkb, hob0⟩ :=
      update_slot hpk hnepk hneocc hrow hrows b rb hgb
    exact R.distinct a b ra0 rb0 hga0 hgb0 (hoa0 ▸ hoa) (hob0 ▸ hob)
      (by rw [← hka, ← hkb]; exact hkab)

/-- **An in-place update changes the abstraction at exactly one key.**

checked by: `lake build` -/
theorem absOf_update {glb glb' : Env} {j : Nat} {fs : Env}
    {ps : List (Ident × Value)} {pk : Schema.Field} {k : Interface.Key}
    {vs : List Value}
    (hpk : Schema.pkey? s = some pk)
    (hnepk : ∀ q ∈ ps, q.1 ≠ pk.name)
    (hneocc : ∀ q ∈ ps, q.1 ≠ (Schema.names s).occupied)
    (hrow : (rowsOf s glb)[j]? = some (.strct fs))
    (hocc : rowOccupied s (.strct fs) = true)
    (hkey : rowKey? s (.strct fs) = some k)
    (hfirst : ∀ t, t < j → slotMatches s glb k t = false)
    (hnew : rowVals? s (.strct (setFields fs ps)) = some vs)
    (hrows : rowsOf s glb' = (rowsOf s glb).set j (.strct (setFields fs ps))) :
    absOf s glb' = Interface.Abs.insert (absOf s glb) k vs := by
  have hocc' : rowOccupied s (.strct (setFields fs ps)) = true := by
    rw [rowOccupied_setFields hneocc]; exact hocc
  have hkey' : rowKey? s (.strct (setFields fs ps)) = some k := by
    rw [rowKey_setFields hpk hnepk]; exact hkey
  funext k'
  simp only [Interface.Abs.insert]
  by_cases hkk : k' = k
  · subst hkk
    have hpos : (rowsOf s glb').find?
        (fun r => rowOccupied s r && decide (rowKey? s r = some k'))
          = some (.strct (setFields fs ps)) := by
      rw [hrows]
      refine find?_set_of_pos _ j _ _ hrow (by simp [hocc', hkey']) ?_
      intro t ht z hz
      have := hfirst t ht
      simp only [slotMatches, hz] at this
      exact this
    simp [absOf, hpos, hnew]
  · have hne' : ¬ ((some k : Option Interface.Key) = some k') :=
      fun e => hkk (Option.some.inj e).symm
    have hnegRow : (rowOccupied s (.strct (setFields fs ps))
        && decide (rowKey? s (.strct (setFields fs ps)) = some k')) = false := by
      rw [hkey', decide_eq_false hne', Bool.and_false]
    have heq : (rowsOf s glb').find?
        (fun r => rowOccupied s r && decide (rowKey? s r = some k'))
          = (rowsOf s glb).find?
        (fun r => rowOccupied s r && decide (rowKey? s r = some k')) := by
      rw [hrows]
      refine find?_set_of_neg hnegRow ?_
      intro y hy
      rw [hrow] at hy
      cases hy
      rw [hkey, decide_eq_false hne', Bool.and_false]
    simp only [absOf, heq, if_neg hkk]

/-! ## Filling a free slot

The other half of `insert`. Where the update path had to argue that a row's
key does not move, this one has to argue that a key *appears* — so the
hypothesis that carries it is `hnomatch`: the `find` that ran first missed, so
no occupied slot holds `k`, and slot `j` becomes the only one that does. -/

/-- **The representation invariant survives filling a slot.**

`distinct` is where `hnomatch` is spent: any other occupied slot with the same
key would have been a match for the `find` that already reported a miss.

checked by: `lake build` -/
theorem repInv_setRow {glb glb' : Env} {j : Nat} {nr : Value}
    {k : Interface.Key}
    (R : RepInv s glb)
    (hok : RowOk s nr)
    (hkeyNew : rowKey? s nr = some k)
    (hnomatch : ∀ t, t < (rowsOf s glb).length → slotMatches s glb k t = false)
    (hrows : rowsOf s glb' = (rowsOf s glb).set j nr)
    (hstore : glb'.get? (Schema.names s).storage = some (.arr (rowsOf s glb'))) :
    RepInv s glb' where
  storage := hstore
  length := by rw [hrows, List.length_set]; exact R.length
  rows := by
    intro r hr
    obtain ⟨t, ht, htr⟩ := List.getElem_of_mem hr
    have hget : (rowsOf s glb')[t]? = some r := by
      rw [List.getElem?_eq_getElem ht, htr]
    by_cases htj : t = j
    · subst htj
      rw [hrows] at hget
      cases hjlt : Nat.decLt t (rowsOf s glb).length with
      | isFalse hno =>
        rw [List.getElem?_eq_none (by rw [List.length_set]; omega)] at hget
        exact Option.noConfusion hget
      | isTrue hyes =>
        obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp
          (Option.isSome_of_eq_some (List.getElem?_eq_getElem hyes))
        rw [getElem?_set_self' _ t _ _ hr0] at hget
        cases hget; exact hok
    · rw [hrows, getElem?_set_ne' _ j t _ (fun e => htj e.symm)] at hget
      exact R.rows _ (List.mem_of_getElem? hget)
  distinct := by
    -- A slot other than `j` is the one it was, so if it is occupied and holds
    -- `k` it was a match — which `hnomatch` forbids.
    have hold : ∀ t r, t ≠ j → (rowsOf s glb')[t]? = some r →
        rowOccupied s r = true → rowKey? s r = some k → False := by
      intro t r htj hget hocc hkey
      rw [hrows, getElem?_set_ne' _ j t _ (fun e => htj e.symm)] at hget
      have hlt : t < (rowsOf s glb).length :=
        (List.getElem?_eq_some_iff.mp hget).1
      have := hnomatch t hlt
      simp only [slotMatches, hget, hocc, hkey] at this
      simp at this
    intro a b ra rb hga hgb hoa hob hkab
    by_cases haj : a = j
    · by_cases hbj : b = j
      · rw [haj, hbj]
      · subst haj
        have hra : ra = nr := by
          rw [hrows] at hga
          cases hjlt : Nat.decLt a (rowsOf s glb).length with
          | isFalse hno =>
            rw [List.getElem?_eq_none (by rw [List.length_set]; omega)] at hga
            exact Option.noConfusion hga
          | isTrue hyes =>
            obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp
              (Option.isSome_of_eq_some (List.getElem?_eq_getElem hyes))
            rw [getElem?_set_self' _ a _ _ hr0] at hga
            exact (Option.some.inj hga).symm
        exact absurd (hold b rb hbj hgb hob (by rw [← hkab, hra]; exact hkeyNew))
          (by simp)
    · by_cases hbj : b = j
      · subst hbj
        have hrb : rb = nr := by
          rw [hrows] at hgb
          cases hjlt : Nat.decLt b (rowsOf s glb).length with
          | isFalse hno =>
            rw [List.getElem?_eq_none (by rw [List.length_set]; omega)] at hgb
            exact Option.noConfusion hgb
          | isTrue hyes =>
            obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp
              (Option.isSome_of_eq_some (List.getElem?_eq_getElem hyes))
            rw [getElem?_set_self' _ b _ _ hr0] at hgb
            exact (Option.some.inj hgb).symm
        exact absurd (hold a ra haj hga hoa (by rw [hkab, hrb]; exact hkeyNew))
          (by simp)
      · rw [hrows, getElem?_set_ne' _ j a _ (fun e => haj e.symm)] at hga
        rw [hrows, getElem?_set_ne' _ j b _ (fun e => hbj e.symm)] at hgb
        exact R.distinct a b ra rb hga hgb hoa hob hkab

/-- **Filling a free slot adds exactly one key to the abstraction.**

checked by: `lake build` -/
theorem absOf_setRow {glb glb' : Env} {j : Nat} {nr : Value} {k : Interface.Key}
    {vs : List Value} {r0 : Value}
    (hrow : (rowsOf s glb)[j]? = some r0)
    (hoccOld : rowOccupied s r0 = false)
    (hoccNew : rowOccupied s nr = true)
    (hkeyNew : rowKey? s nr = some k)
    (hvalsNew : rowVals? s nr = some vs)
    (hnomatch : ∀ t, t < (rowsOf s glb).length → slotMatches s glb k t = false)
    (hrows : rowsOf s glb' = (rowsOf s glb).set j nr) :
    absOf s glb' = Interface.Abs.insert (absOf s glb) k vs := by
  funext k'
  simp only [Interface.Abs.insert]
  by_cases hkk : k' = k
  · subst hkk
    have hpos : (rowsOf s glb').find?
        (fun r => rowOccupied s r && decide (rowKey? s r = some k')) = some nr := by
      rw [hrows]
      refine find?_set_of_pos _ j _ _ hrow (by simp [hoccNew, hkeyNew]) ?_
      intro t ht z hz
      have hlt : t < (rowsOf s glb).length := (List.getElem?_eq_some_iff.mp hz).1
      have := hnomatch t hlt
      simp only [slotMatches, hz] at this
      exact this
    simp [absOf, hpos, hvalsNew]
  · have hne' : ¬ ((some k : Option Interface.Key) = some k') :=
      fun e => hkk (Option.some.inj e).symm
    have heq : (rowsOf s glb').find?
        (fun r => rowOccupied s r && decide (rowKey? s r = some k'))
          = (rowsOf s glb).find?
        (fun r => rowOccupied s r && decide (rowKey? s r = some k')) := by
      rw [hrows]
      refine find?_set_of_neg (by rw [hkeyNew, decide_eq_false hne', Bool.and_false]) ?_
      intro y hy
      rw [hrow] at hy
      cases hy
      rw [hoccOld, Bool.false_and]
    simp only [absOf, heq, if_neg hkk]

/-! ## The free-slot scan

`insert`'s second loop, and the first generated loop that *writes*. The scan
lemma therefore cannot be a "leaves the store alone" statement the way
`forLoop_scan` was: it has to hand back what the store became, which is why its
conclusion carries the new row and its properties rather than an equation
between stores. -/

/-- Slot `i` is free — the dual of `slotMatches`, and `false` out of range for
the same reason: the loop never goes there. -/
def slotFree (s : Schema) (glb : Env) (i : Nat) : Bool :=
  match (rowsOf s glb)[i]? with
  | some r => !rowOccupied s r
  | none   => false

/-- The first free slot in `[i, i + rem)`. -/
def firstFree (s : Schema) (glb : Env) : Nat → Nat → Option Nat
  | _, 0       => none
  | i, rem + 1 => if slotFree s glb i then some i else firstFree s glb (i + 1) rem

theorem firstFree_some {glb : Env} :
    ∀ (rem i j : Nat), firstFree s glb i rem = some j → slotFree s glb j = true := by
  intro rem
  induction rem with
  | zero => intro i j h; exact Option.noConfusion h
  | succ rem ih =>
    intro i j h
    cases hm : slotFree s glb i with
    | true => simp only [firstFree, hm, if_true] at h; cases h; exact hm
    | false =>
      simp only [firstFree, hm, Bool.false_eq_true, if_false] at h
      exact ih (i + 1) j h

/-- The body of that loop, exactly as `insertDef` emits it. -/
def freeSlotBody (s : Schema) : Stmt :=
  .when (.un .lnot (.rd (field s tmpJ (Schema.names s).occupied))) <|
    .block ([.assign (field s tmpJ (Schema.names s).occupied) (.lit (.bool true))]
            ++ s.fields.map
                 (fun f => .assign (field s tmpJ f.name) (.rd (.var f.name)))
            ++ [.ret (some (.lit (.bool true)))])

theorem eval_freeGuard {j : Nat} {fs : Env} {b : Bool}
    (hglb : σ.glb.get? (Schema.names s).storage = some (.arr (rowsOf s σ.glb)))
    (hlt : j < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpJ = some (.u32 (UInt32.ofNat j)))
    (hround : (UInt32.ofNat j).toNat = j)
    (hrow : (rowsOf s σ.glb)[j]? = some (.strct fs))
    (hocc : Env.get? fs (Schema.names s).occupied = some (.bool b)) :
    evalExpr σ (.un .lnot (.rd (field s tmpJ (Schema.names s).occupied)))
      = .ok (.bool (!b)) := by
  have hfld : (Value.strct fs).getStep (.fld (Schema.names s).occupied)
      = some (.bool b) := hocc
  show (do let v ← evalExpr σ (.rd (field s tmpJ (Schema.names s).occupied));
           evalUn .lnot v) = _
  rw [read_field hglb hlt hloc hround hrow hfld]
  rfl

/-- `mapM` succeeding means every element succeeded — the direction `RowOk`'s
`vals` clause is consumed in. -/
theorem mapM_isSome_mem {α β : Type _} {g : α → Option β} :
    ∀ (l : List α), (l.mapM g).isSome = true → ∀ a ∈ l, (g a).isSome = true := by
  intro l
  induction l with
  | nil => intro _ a ha; exact absurd ha (by simp)
  | cons x xs ih =>
    intro h a ha
    simp only [List.mapM_cons] at h
    cases hx : g x with
    | none => rw [hx] at h; simp at h
    | some _ =>
      rw [hx] at h
      simp only [bind, Option.bind] at h
      cases hr : xs.mapM g with
      | none => rw [hr] at h; simp at h
      | some _ =>
        rcases List.mem_cons.mp ha with rfl | ha'
        · rw [hx]; rfl
        · exact ih (by rw [hr]; rfl) a ha'

/-- A well-formed row has every schema field. -/
theorem rowOk_field_isSome {fs : Env} {pk : Schema.Field}
    (hpk : Schema.pkey? s = some pk)
    (hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk])
    (h : RowOk s (.strct fs)) :
    ∀ f ∈ s.fields, (Env.get? fs f.name).isSome = true := by
  intro f hf
  rcases List.mem_cons.mp (mem_pk_cons hfl hf) with rfl | hv
  · cases hg : Env.get? fs f.name with
    | none => have hk := h.key; simp [rowKey?, hpk, hg] at hk
    | some _ => rfl
  · exact mapM_isSome_mem _ h.vals _ hv

/-! ## The scan's context

Bundling the schema-side hypotheses keeps the scan's signature readable; every
field is discharged once, from `Schema.check`, where `insert`'s obligations are
assembled. -/

/-- What a well-formed schema and a matching argument list give the scan. -/
structure InsCtx (s : Schema) (pk : Schema.Field) (k : Interface.Key)
    (vs : List Value) : Prop where
  facts   : Facts s
  pkey    : Schema.pkey? s = some pk
  filter  : s.fields.filter (fun f => f.reftype == .Pkey) = [pk]
  kty     : k.ty = pk.ty
  vlen    : (Schema.valFields s).length = vs.length
  pkVal   : frameVal s pk k vs pk.name = k.toValue
  valVal  : ∀ t (h1 : t < (Schema.valFields s).length) (h2 : t < vs.length),
              frameVal s pk k vs (((Schema.valFields s)[t]'h1).name) = vs[t]'h2

theorem InsCtx.pwNames {pk : Schema.Field} {k : Interface.Key} {vs : List Value}
    (C : InsCtx s pk k vs) : (s.fields.map Schema.Field.name).Pairwise (· ≠ ·) :=
  C.facts.pwNames

theorem InsCtx.notOcc {pk : Schema.Field} {k : Interface.Key} {vs : List Value}
    (C : InsCtx s pk k vs) :
    ∀ f ∈ s.fields, f.name ≠ (Schema.names s).occupied := C.facts.notOccupied

theorem InsCtx.reserved {pk : Schema.Field} {k : Interface.Key} {vs : List Value}
    (C : InsCtx s pk k vs) :
    ∀ f ∈ s.fields, Schema.isReservedName f.name = false := C.facts.notReserved

/-- The `(name, value)` pairs the fresh-slot path writes: every schema field,
carrying the value its parameter is bound to. -/
def insPairs (s : Schema) (pk : Schema.Field) (k : Interface.Key)
    (vs : List Value) : List (Ident × Value) :=
  s.fields.map (fun f => (f.name, frameVal s pk k vs f.name))

/-- The row a free slot becomes. -/
def newRowOf (s : Schema) (pk : Schema.Field) (k : Interface.Key)
    (vs : List Value) (fs : Env) : Value :=
  .strct (setFields (Env.set fs (Schema.names s).occupied (.bool true))
    (insPairs s pk k vs))

section Ctx

variable {pk : Schema.Field} {k : Interface.Key} {vs : List Value}

theorem insPairs_fst : (insPairs s pk k vs).map Prod.fst
    = s.fields.map Schema.Field.name := by
  simp [insPairs, List.map_map, Function.comp_def]

theorem insPairs_ne_occ (C : InsCtx s pk k vs) :
    ∀ q ∈ insPairs s pk k vs, q.1 ≠ (Schema.names s).occupied := by
  intro q hq
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
  exact C.notOcc f hf

theorem insPairs_pk (C : InsCtx s pk k vs) :
    (pk.name, k.toValue) ∈ insPairs s pk k vs := by
  have h := List.mem_map_of_mem (f := fun f : Schema.Field =>
    (f.name, frameVal s pk k vs f.name)) (pk_mem C.filter)
  simp only at h
  rwa [C.pkVal] at h

theorem insPairs_val (C : InsCtx s pk k vs) (t : Nat)
    (h1 : t < (Schema.valFields s).length) (h2 : t < vs.length) :
    ((((Schema.valFields s)[t]'h1).name), vs[t]'h2) ∈ insPairs s pk k vs := by
  have h := List.mem_map_of_mem (f := fun f : Schema.Field =>
    (f.name, frameVal s pk k vs f.name))
    (val_mem (List.getElem_mem h1)).1
  simp only at h
  rwa [C.valVal t h1 h2] at h

/-- **The row a free slot becomes is well formed, occupied, keyed by `k` and
holds `vs`.** All four are read off `setFields`; none of them mentions the
generator.

checked by: `lake build` -/
theorem newRow_props (C : InsCtx s pk k vs) {fs : Env} (hok : RowOk s (.strct fs))
    (hoccDom : (Env.get? fs (Schema.names s).occupied).isSome = true) :
    RowOk s (newRowOf s pk k vs fs)
    ∧ rowOccupied s (newRowOf s pk k vs fs) = true
    ∧ rowKey? s (newRowOf s pk k vs fs) = some k
    ∧ rowVals? s (newRowOf s pk k vs fs) = some vs := by
  have hpw : ((insPairs s pk k vs).map Prod.fst).Pairwise (· ≠ ·) := by
    rw [insPairs_fst]; exact C.pwNames
  have hdom : ∀ f ∈ s.fields,
      ((Env.set fs (Schema.names s).occupied (.bool true)).get? f.name).isSome
        = true := by
    intro f hf
    rw [get?_set_isSome]; exact rowOk_field_isSome C.pkey C.filter hok f hf
  have hoccT : rowOccupied s (newRowOf s pk k vs fs) = true := by
    simp only [newRowOf, rowOccupied_setFields (insPairs_ne_occ C)]
    exact rowOccupied_set_occupied hoccDom
  have hkeyT : rowKey? s (newRowOf s pk k vs fs) = some k :=
    rowKey_setFields_eq C.pkey hpw (hdom pk (pk_mem C.filter)) (insPairs_pk C)
  have hvalsT : rowVals? s (newRowOf s pk k vs fs) = some vs :=
    rowVals_setFields_eq hpw (fun f hf => hdom f (val_mem hf).1) C.vlen
      (fun t h1 h2 => insPairs_val C t h1 h2)
  refine ⟨⟨⟨true, ?_⟩, by rw [hkeyT]; rfl, ?_, by rw [hvalsT]; rfl⟩,
    hoccT, hkeyT, hvalsT⟩
  · have := hoccT
    simp only [rowOccupied, newRowOf] at this ⊢
    cases hg : Env.get? (setFields (Env.set fs (Schema.names s).occupied (.bool true))
        (insPairs s pk k vs)) (Schema.names s).occupied with
    | none => rw [hg] at this; exact absurd this (by simp)
    | some w =>
      rw [hg] at this
      cases w <;> simp_all
  · intro pk' k' hpk' hrk
    rw [hkeyT] at hrk
    cases hrk
    have : pk' = pk := by rw [C.pkey] at hpk'; exact (Option.some.inj hpk').symm
    rw [this]; exact C.kty

end Ctx

/-! ## Executing the scan -/

/-- **One iteration of the free-slot scan.**

Split into the two guard outcomes rather than stated with an `if`, because the
hit case has to hand back a store and the miss case has to hand back an
equation — a shape no single conclusion carries comfortably.

checked by: `lake build` -/
theorem exec_freeSlotBody {p : Program} {callee} {pk : Schema.Field}
    {k : Interface.Key} {vs : List Value} {j : Nat}
    (C : InsCtx s pk k vs) (R : RepInv s σ.glb)
    (hlt : j < (rowsOf s σ.glb).length)
    (hloc : σ.getLocal tmpJ = some (.u32 (UInt32.ofNat j)))
    (hround : (UInt32.ofNat j).toNat = j)
    (hframe : ∀ f ∈ s.fields,
      σ.getLocal f.name = some (frameVal s pk k vs f.name)) :
    (slotFree s σ.glb j = false →
        execAt p callee (freeSlotBody s) σ = .ok (σ, .normal))
    ∧ (slotFree s σ.glb j = true → ∃ σ' nr,
        execAt p callee (freeSlotBody s) σ = .ok (σ', .ret (some (.bool true)))
        ∧ rowsOf s σ'.glb = (rowsOf s σ.glb).set j nr
        ∧ σ'.glb.get? (Schema.names s).storage = some (.arr (rowsOf s σ'.glb))
        ∧ σ'.loc = σ.loc ∧ σ'.hp = σ.hp ∧ σ'.next = σ.next
        ∧ RowOk s nr ∧ rowOccupied s nr = true
        ∧ rowKey? s nr = some k ∧ rowVals? s nr = some vs) := by
  have hrow0 : (rowsOf s σ.glb)[j]? = some ((rowsOf s σ.glb)[j]'hlt) :=
    List.getElem?_eq_getElem hlt
  have hok0 : RowOk s ((rowsOf s σ.glb)[j]'hlt) := R.rows _ (List.getElem_mem hlt)
  obtain ⟨fs, b, hstrct, hoccfs, hrocc⟩ := strct_of_rowOk hok0
  have hrow : (rowsOf s σ.glb)[j]? = some (.strct fs) := by rw [hrow0, hstrct]
  have hfree_b : slotFree s σ.glb j = !b := by
    simp only [slotFree, hrow0, hrocc]
  have hok : RowOk s (.strct fs) := hstrct ▸ hok0
  have hoccDom : (Env.get? fs (Schema.names s).occupied).isSome = true := by
    rw [hoccfs]; rfl
  constructor
  · intro hnf
    have hb : b = true := by
      rw [hfree_b] at hnf; cases b <;> simp_all
    subst hb
    rw [freeSlotBody, Stmt.when, execAt_cond,
      eval_freeGuard R.storage hlt hloc hround hrow hoccfs]
    rfl
  · intro hf
    have hb : b = false := by
      rw [hfree_b] at hf; cases b <;> simp_all
    subst hb
    have hfldOcc : (Value.strct fs).getStep (.fld (Schema.names s).occupied)
        = some (.bool false) := hoccfs
    have hres1 := resolve_field R.storage hlt hloc hround hrow hfldOcc
    obtain ⟨σ₁, hwr1, hrows1, hstore1, hloc1, hhp1, hnx1⟩ :=
      write_slotField (s := s) (σ := σ) (i := j) (row := .strct fs) (fs := fs)
        (f := (Schema.names s).occupied) (w := .bool true) R.storage hrow rfl hoccDom
    have hstep1 : execAt p callee
        (.assign (field s tmpJ (Schema.names s).occupied) (.lit (.bool true))) σ
        = .ok (σ₁, .normal) := by
      rw [execAt_assign]
      simp only [hres1, evalExpr, hwr1, bind, Except.bind]
    have hrow1 : (rowsOf s σ₁.glb)[j]?
        = some (.strct (Env.set fs (Schema.names s).occupied (.bool true))) := by
      rw [hrows1]; exact getElem?_set_self' _ j _ _ hrow
    have hresF : ∀ (τ : Store) (n : Ident) (gs : Env), τ.loc = σ.loc →
        τ.glb.get? (Schema.names s).storage = some (.arr (rowsOf s τ.glb)) →
        (rowsOf s τ.glb)[j]? = some (.strct gs) →
        (Env.get? gs n).isSome = true →
        resolve τ (field s tmpJ n)
          = .ok (.glb ⟨.glob (Schema.names s).storage, [.idx j, .fld n]⟩) := by
      intro τ n gs hlocτ hglbτ hrowτ hdomn
      have hltτ : j < (rowsOf s τ.glb).length :=
        (List.getElem?_eq_some_iff.mp hrowτ).1
      have hlocJ : τ.getLocal tmpJ = some (.u32 (UInt32.ofNat j)) := by
        simp only [Store.getLocal, hlocτ]; exact hloc
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hdomn
      exact resolve_field hglbτ hltτ hlocJ hround hrowτ
        (show (Value.strct gs).getStep (.fld n) = some w from hw)
    obtain ⟨σ₂, hbody2, hrows2, hstore2, hloc2, hhp2, hnx2⟩ :=
      exec_assignFields (p := p) (callee := callee) (i := j) (lv := field s tmpJ)
        (L := σ.loc) hresF (insPairs s pk k vs)
        (Env.set fs (Schema.names s).occupied (.bool true)) σ₁
        hloc1 hstore1 hrow1
        (fun q hq => by
          obtain ⟨f, hfm, hqe⟩ := List.mem_map.mp hq
          rw [← hqe]
          simp only
          rw [get?_set_isSome]
          exact rowOk_field_isSome C.pkey C.filter hok f hfm)
        (fun q hq => by
          obtain ⟨f, hfm, hqe⟩ := List.mem_map.mp hq
          rw [← hqe]
          simp only
          rw [show σ₁.getLocal f.name = σ.getLocal f.name from by
            simp only [Store.getLocal, hloc1]]
          exact hframe f hfm)
    obtain ⟨hokN, hoccN, hkeyN, hvalsN⟩ := newRow_props C hok hoccDom
    refine ⟨σ₂, newRowOf s pk k vs fs, ?_, ?_, hstore2, by rw [hloc2, hloc1],
      by rw [hhp2, hhp1], by rw [hnx2, hnx1], hokN, hoccN, hkeyN, hvalsN⟩
    · rw [freeSlotBody, Stmt.when, execAt_cond,
        eval_freeGuard R.storage hlt hloc hround hrow hoccfs]
      have hmapeq : s.fields.map
            (fun f => Stmt.assign (field s tmpJ f.name) (.rd (.var f.name)))
          = (insPairs s pk k vs).map
            (fun q => Stmt.assign (field s tmpJ q.1) (.rd (.var q.1))) := by
        simp [insPairs, List.map_map, Function.comp_def]
      have hblk : execAt p callee (Stmt.block
          ([.assign (field s tmpJ (Schema.names s).occupied) (.lit (.bool true))]
           ++ s.fields.map
                (fun f => .assign (field s tmpJ f.name) (.rd (.var f.name))))) σ
          = .ok (σ₂, .normal) := by
        rw [List.singleton_append, execAt_block_cons, execAt_seq, hstep1]
        simp only [bind, Except.bind]
        rw [hmapeq]
        exact hbody2
      show execAt p callee (Stmt.block (_ ++ [Stmt.ret (some (.lit (.bool true)))])) σ
        = _
      rw [execAt_block_append _ _ σ σ₂ hblk]
      rfl
    · rw [hrows2, hrows1, List.set_set]
      rfl

/-- **The whole free-slot scan.**

Every iteration before the hit leaves the store alone, so the store handed back
is the one the single writing iteration produced — which is why the `none` case
can state store equality and the `some` case a single `List.set`.

checked by: `lake build` -/
theorem forLoop_free {p : Program} {callee} {pk : Schema.Field}
    {k : Interface.Key} {vs : List Value}
    (C : InsCtx s pk k vs)
    (hfres : ∀ f ∈ s.fields, Schema.isReservedName f.name = false) :
    ∀ (rem i : Nat) (σ : Store),
      RepInv s σ.glb →
      (∀ f ∈ s.fields, σ.getLocal f.name = some (frameVal s pk k vs f.name)) →
      (σ.getLocal tmpJ).isSome = true →
      i + rem ≤ (rowsOf s σ.glb).length →
      (∀ t, t < (rowsOf s σ.glb).length → (UInt32.ofNat t).toNat = t) →
      ∃ σ',
        forLoop (execAt p callee (freeSlotBody s)) tmpJ i rem σ
          = .ok (σ', match firstFree s σ.glb i rem with
                     | some _ => .ret (some (.bool true))
                     | none   => .normal)
        ∧ σ'.hp = σ.hp ∧ σ'.next = σ.next
        ∧ (∀ f ∈ s.fields,
            σ'.getLocal f.name = some (frameVal s pk k vs f.name))
        ∧ (match firstFree s σ.glb i rem with
           | some t => ∃ nr, rowsOf s σ'.glb = (rowsOf s σ.glb).set t nr
                        ∧ σ'.glb.get? (Schema.names s).storage
                            = some (.arr (rowsOf s σ'.glb))
                        ∧ RowOk s nr ∧ rowOccupied s nr = true
                        ∧ rowKey? s nr = some k ∧ rowVals? s nr = some vs
                        ∧ t < (rowsOf s σ.glb).length
           | none   => σ'.glb = σ.glb) := by
  have hfj : ∀ f ∈ s.fields, f.name ≠ tmpJ :=
    fun f hf => ne_of_reserved (hfres f hf) (by decide)
  intro rem
  induction rem with
  | zero =>
    intro i σ _ hframe _ _ _
    refine ⟨σ.setLocal tmpJ (.u32 (UInt32.ofNat i)), rfl, rfl, rfl, ?_, rfl⟩
    intro f hf
    simp only [Store.setLocal, Store.getLocal, Env.get?_set_ne _ (hfj f hf)]
    exact hframe f hf
  | succ rem ih =>
    intro i σ R hframe hjs hbnd hrnd
    have hlt : i < (rowsOf s σ.glb).length := by omega
    have hglb0 : (σ.setLocal tmpJ (Value.u32 (UInt32.ofNat i))).glb = σ.glb := rfl
    have hj0 : (σ.setLocal tmpJ (Value.u32 (UInt32.ofNat i))).getLocal tmpJ
        = some (.u32 (UInt32.ofNat i)) := by
      simp only [Store.setLocal, Store.getLocal, Env.get?_set_self]
      simp only [Store.getLocal] at hjs
      cases hg : σ.loc.get? tmpJ with
      | none => rw [hg] at hjs; exact absurd hjs (by simp)
      | some _ => rfl
    have hframe0 : ∀ f ∈ s.fields,
        (σ.setLocal tmpJ (Value.u32 (UInt32.ofNat i))).getLocal f.name
          = some (frameVal s pk k vs f.name) := by
      intro f hf
      simp only [Store.setLocal, Store.getLocal, Env.get?_set_ne _ (hfj f hf)]
      exact hframe f hf
    obtain ⟨hmiss, hhit⟩ :=
      exec_freeSlotBody (p := p) (callee := callee)
        (σ := σ.setLocal tmpJ (Value.u32 (UInt32.ofNat i))) (j := i) C
        (by rw [hglb0]; exact R) (by rw [hglb0]; exact hlt) hj0 (hrnd i hlt) hframe0
    cases hfree : slotFree s σ.glb i with
    | true =>
      obtain ⟨σ', nr, hex, hrows, hstore, hloc', hhp', hnx', hok, hocc, hkey,
        hvals⟩ := hhit (by rw [hglb0]; exact hfree)
      rw [hglb0] at hrows
      refine ⟨σ', ?_, by rw [hhp']; rfl, by rw [hnx']; rfl, ?_, ?_⟩
      · show (do
          match ← execAt p callee (freeSlotBody s)
              (σ.setLocal tmpJ (Value.u32 (UInt32.ofNat i))) with
          | (σ₁, .normal) =>
            forLoop (execAt p callee (freeSlotBody s)) tmpJ (i + 1) rem σ₁
          | (σ₁, .ret v)  => Except.ok (σ₁, .ret v)) = _
        rw [hex]
        simp only [firstFree, hfree, if_true, bind, Except.bind]
      · intro f hf
        rw [show σ'.getLocal f.name
              = (σ.setLocal tmpJ (Value.u32 (UInt32.ofNat i))).getLocal f.name from by
          simp only [Store.getLocal, hloc']]
        exact hframe0 f hf
      · simp only [firstFree, hfree, if_true]
        exact ⟨nr, hrows, hstore, hok, hocc, hkey, hvals, hlt⟩
    | false =>
      have hex := hmiss (by rw [hglb0]; exact hfree)
      obtain ⟨σ', hloop, hhp', hnx', hframe', hstate⟩ :=
        ih (i + 1) (σ.setLocal tmpJ (Value.u32 (UInt32.ofNat i)))
          (by rw [hglb0]; exact R) hframe0 (by rw [hj0]; rfl)
          (by rw [hglb0]; omega) (by rw [hglb0]; exact hrnd)
      rw [hglb0] at hloop hstate
      refine ⟨σ', ?_, by rw [hhp']; rfl, by rw [hnx']; rfl, hframe', ?_⟩
      · show (do
          match ← execAt p callee (freeSlotBody s)
              (σ.setLocal tmpJ (Value.u32 (UInt32.ofNat i))) with
          | (σ₁, .normal) =>
            forLoop (execAt p callee (freeSlotBody s)) tmpJ (i + 1) rem σ₁
          | (σ₁, .ret v)  => Except.ok (σ₁, .ret v)) = _
        rw [hex]
        simp only [bind, Except.bind]
        rw [hloop]
        simp only [firstFree, hfree, Bool.false_eq_true, if_false]
      · simp only [firstFree, hfree, Bool.false_eq_true, if_false]
        exact hstate

/-! ## The body

Three outcomes, and the shape of the proof is the shape of the generated code:
`find` first, then the update path if it hit, then the free-slot scan, then the
`return false` that only a full table reaches.

The update path and the fresh path both return `true` and both establish
`Abs.insert`, but for different reasons — one because the key stayed where it
was, the other because it appeared where nothing was. That is why the two
abstraction lemmas above are separate. -/

/-- **What `insert`'s body does.**

checked by: `lake build` -/
theorem exec_insertBody {p : Program} {d : Nat} {pk : Schema.Field}
    {k : Interface.Key} {vs : List Value}
    (C : InsCtx s pk k vs)
    (hlook : lookupFun p (Schema.names s).find = .ok (findDef s pk))
    (R : RepInv s σ.glb)
    (hframe : ∀ f ∈ s.fields, σ.getLocal f.name = some (frameVal s pk k vs f.name))
    (hat : (σ.getLocal tmpAt).isSome = true)
    (hjs : (σ.getLocal tmpJ).isSome = true)
    (hrnd : ∀ t, t < (rowsOf s σ.glb).length → (UInt32.ofNat t).toNat = t) :
    ∃ (σ' : Store) (b : Bool),
      execAt p (execStmt p (d + 1)) (insertDef s pk).body σ
        = .ok (σ', .ret (some (.bool b)))
      ∧ RepInv s σ'.glb
      ∧ (b = true → absOf s σ'.glb = Interface.Abs.insert (absOf s σ.glb) k vs)
      ∧ (b = false → σ'.glb = σ.glb ∧ absOf s σ.glb k = none)
      ∧ σ'.hp = σ.hp ∧ σ'.next = σ.next := by
  have hcapEq : (rowsOf s σ.glb).length = s.capacity := R.length
  have hpkmem : pk ∈ s.fields := pk_mem C.filter
  have hkloc : σ.getLocal pk.name = some k.toValue := by
    rw [hframe pk hpkmem, C.pkVal]
  have hneI : pk.name ≠ tmpI := ne_of_reserved (C.reserved pk hpkmem) (by decide)
  have hcall := exec_callFind (d := d) hlook C.pkey hneI C.kty R hkloc hat
    (by omega) hrnd
  have habs_iff := firstMatch_isSome_iff (s := s) (glb := σ.glb) (k := k) R
  rw [hcapEq] at habs_iff
  -- The pairs the update path writes: one per value field.
  have hpwA : (((Schema.valFields s).map
      (fun f => (f.name, frameVal s pk k vs f.name))).map Prod.fst).Pairwise (· ≠ ·) := by
    rw [show ((Schema.valFields s).map
        (fun f => (f.name, frameVal s pk k vs f.name))).map Prod.fst
        = (Schema.valFields s).map Schema.Field.name from by
      simp [List.map_map, Function.comp_def]]
    exact pw_val_names C.facts
  have hnepkA : ∀ q ∈ (Schema.valFields s).map
      (fun f => (f.name, frameVal s pk k vs f.name)), q.1 ≠ pk.name := by
    intro q hq
    obtain ⟨f, hf, hqe⟩ := List.mem_map.mp hq
    rw [← hqe]
    exact (pk_name_ne_val C.filter C.facts f hf).symm
  have hneoccA : ∀ q ∈ (Schema.valFields s).map
      (fun f => (f.name, frameVal s pk k vs f.name)),
      q.1 ≠ (Schema.names s).occupied := by
    intro q hq
    obtain ⟨f, hf, hqe⟩ := List.mem_map.mp hq
    rw [← hqe]
    exact C.notOcc f (val_mem hf).1
  have hmemA : ∀ t, ∀ (h1 : t < (Schema.valFields s).length) (h2 : t < vs.length),
      ((((Schema.valFields s)[t]'h1).name), vs[t]'h2) ∈ (Schema.valFields s).map
        (fun f => (f.name, frameVal s pk k vs f.name)) := by
    intro t h1 h2
    have h := List.mem_map_of_mem (f := fun f : Schema.Field =>
      (f.name, frameVal s pk k vs f.name)) (List.getElem_mem h1)
    simp only at h
    rwa [C.valVal t h1 h2] at h
  cases hfm : firstMatch s σ.glb k 0 s.capacity with
  | some j =>
    rw [hfm] at hcall
    simp only at hcall
    have hsm := firstMatch_some (s := s) (glb := σ.glb) (k := k) _ _ _ hfm
    have hrowr : (rowsOf s σ.glb)[j]? = some ((rowsOf s σ.glb)[j]'(by
      simp only [slotMatches] at hsm
      cases hr : (rowsOf s σ.glb)[j]? with
      | none => rw [hr] at hsm; simp at hsm
      | some _ => exact (List.getElem?_eq_some_iff.mp hr).1)) :=
      List.getElem?_eq_getElem _
    have hltj : j < (rowsOf s σ.glb).length :=
      (List.getElem?_eq_some_iff.mp hrowr).1
    obtain ⟨fs, b0, hstrct, hoccfs, hrocc⟩ :=
      strct_of_rowOk (R.rows _ (List.getElem_mem hltj))
    have hrow : (rowsOf s σ.glb)[j]? = some (.strct fs) := by rw [hrowr, hstrct]
    have hokfs : RowOk s (.strct fs) := hstrct ▸ R.rows _ (List.getElem_mem hltj)
    have hsm2 : rowOccupied s (.strct fs) = true
        ∧ rowKey? s (.strct fs) = some k := by
      simp only [slotMatches, hrow] at hsm
      rw [Bool.and_eq_true] at hsm
      exact ⟨hsm.1, of_decide_eq_true hsm.2⟩
    -- `_at` now points at slot `j`
    have hptr1 : (σ.setLocal tmpAt
        (Value.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩)).getLocal tmpAt
        = some (.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩) := by
      simp only [Store.setLocal, Store.getLocal, Env.get?_set_self]
      simp only [Store.getLocal] at hat
      cases hg : σ.loc.get? tmpAt with
      | none => rw [hg] at hat; exact absurd hat (by simp)
      | some _ => rfl
    have hglb1 : (σ.setLocal tmpAt
        (Value.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩)).glb = σ.glb := rfl
    have hframe1 : ∀ f ∈ s.fields, (σ.setLocal tmpAt
        (Value.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩)).getLocal f.name
          = some (frameVal s pk k vs f.name) := by
      intro f hf
      simp only [Store.setLocal, Store.getLocal,
        Env.get?_set_ne _ (ne_of_reserved (C.reserved f hf) (by decide : Schema.isReservedName tmpAt = true))]
      exact hframe f hf
    have hresA : ∀ (τ : Store) (n : Ident) (gs : Env),
        τ.loc = (σ.setLocal tmpAt
          (Value.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩)).loc →
        τ.glb.get? (Schema.names s).storage = some (.arr (rowsOf s τ.glb)) →
        (rowsOf s τ.glb)[j]? = some (.strct gs) →
        (Env.get? gs n).isSome = true →
        resolve τ (ptrField tmpAt n)
          = .ok (.glb ⟨.glob (Schema.names s).storage, [.idx j, .fld n]⟩) := by
      intro τ n gs hlocτ hglbτ hrowτ hdomn
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hdomn
      refine resolve_ptrField hglbτ ?_ hrowτ
        (show (Value.strct gs).getStep (.fld n) = some w from hw)
      simp only [Store.getLocal, hlocτ]
      exact hptr1
    obtain ⟨σ₂, hbody2, hrows2, hstore2, hloc2, hhp2, hnx2⟩ :=
      exec_assignFields (p := p) (callee := execStmt p (d + 1)) (i := j)
        (lv := ptrField tmpAt)
        (L := (σ.setLocal tmpAt
          (Value.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩)).loc) hresA
        ((Schema.valFields s).map (fun f => (f.name, frameVal s pk k vs f.name)))
        fs _ rfl (by rw [hglb1]; exact R.storage) (by rw [hglb1]; exact hrow)
        (fun q hq => by
          obtain ⟨f, hf, hqe⟩ := List.mem_map.mp hq
          rw [← hqe]
          exact rowOk_field_isSome C.pkey C.filter hokfs f (val_mem hf).1)
        (fun q hq => by
          obtain ⟨f, hf, hqe⟩ := List.mem_map.mp hq
          rw [← hqe]
          exact hframe1 f (val_mem hf).1)
    rw [hglb1] at hrows2
    have hvalsNew : rowVals? s (.strct (setFields fs
        ((Schema.valFields s).map (fun f => (f.name, frameVal s pk k vs f.name)))))
        = some vs :=
      rowVals_setFields_eq hpwA
        (fun f hf => rowOk_field_isSome C.pkey C.filter hokfs f (val_mem hf).1)
        C.vlen hmemA
    refine ⟨σ₂, true, ?_, ?_, ?_, by simp, by rw [hhp2]; rfl, by rw [hnx2]; rfl⟩
    · have hbranch : execAt p (execStmt p (d + 1))
          (Stmt.when (.bin .ne (.rd (.var tmpAt)) (nullRow s))
            (.block ((Schema.valFields s).map
                (fun f => .assign (ptrField tmpAt f.name) (.rd (.var f.name)))
              ++ [.ret (some (.lit (.bool true)))])))
          (σ.setLocal tmpAt (Value.ptr ⟨.glob (Schema.names s).storage, [.idx j]⟩))
          = .ok (σ₂, .ret (some (.bool true))) := by
        rw [Stmt.when, execAt_cond, eval_atGuard_ptr hptr1]
        simp only [bind, Except.bind]
        rw [show (Schema.valFields s).map
              (fun f => Stmt.assign (ptrField tmpAt f.name) (.rd (.var f.name)))
            = ((Schema.valFields s).map
              (fun f => (f.name, frameVal s pk k vs f.name))).map
              (fun q => Stmt.assign (ptrField tmpAt q.1) (.rd (.var q.1))) from by
          simp [List.map_map, Function.comp_def]]
        rw [execAt_block_append _ _ _ σ₂ hbody2]
        rfl
      simp only [insertDef, Stmt.block]
      rw [execAt_seq, hcall]
      simp only [bind, Except.bind]
      rw [execAt_seq, hbranch]
      rfl
    · exact repInv_update R C.pkey hnepkA hneoccA hrow (by rw [hvalsNew]; rfl)
        hrows2 hstore2
    · intro _
      exact absOf_update C.pkey hnepkA hneoccA hrow hsm2.1 hsm2.2
        (fun t ht => firstMatch_lt _ _ _ hfm t (Nat.zero_le _) ht) hvalsNew hrows2
  | none =>
    rw [hfm] at hcall
    simp only at hcall
    have hnull1 : (σ.setLocal tmpAt Value.null).getLocal tmpAt = some .null := by
      simp only [Store.setLocal, Store.getLocal, Env.get?_set_self]
      simp only [Store.getLocal] at hat
      cases hg : σ.loc.get? tmpAt with
      | none => rw [hg] at hat; exact absurd hat (by simp)
      | some _ => rfl
    have hglb1 : (σ.setLocal tmpAt Value.null).glb = σ.glb := rfl
    have hframe1 : ∀ f ∈ s.fields,
        (σ.setLocal tmpAt Value.null).getLocal f.name
          = some (frameVal s pk k vs f.name) := by
      intro f hf
      simp only [Store.setLocal, Store.getLocal,
        Env.get?_set_ne _ (ne_of_reserved (C.reserved f hf) (by decide : Schema.isReservedName tmpAt = true))]
      exact hframe f hf
    have hjs1 : ((σ.setLocal tmpAt Value.null).getLocal tmpJ).isSome = true := by
      simp only [Store.setLocal, Store.getLocal, Env.get?_set_ne _
        (by decide : tmpJ ≠ tmpAt)]
      exact hjs
    have hbranch : execAt p (execStmt p (d + 1))
        (Stmt.when (.bin .ne (.rd (.var tmpAt)) (nullRow s))
          (.block ((Schema.valFields s).map
              (fun f => .assign (ptrField tmpAt f.name) (.rd (.var f.name)))
            ++ [.ret (some (.lit (.bool true)))])))
        (σ.setLocal tmpAt Value.null)
        = .ok (σ.setLocal tmpAt Value.null, .normal) := by
      rw [Stmt.when, execAt_cond, eval_atGuard_null hnull1]
      rfl
    obtain ⟨σ₂, hloop, hhp2, hnx2, hframe2, hstate⟩ :=
      forLoop_free (p := p) (callee := execStmt p (d + 1)) C C.reserved
        s.capacity 0 (σ.setLocal tmpAt Value.null) (by rw [hglb1]; exact R)
        hframe1 hjs1 (by rw [hglb1, hcapEq]; omega) (by rw [hglb1]; exact hrnd)
    rw [hglb1] at hloop hstate
    have hnomatch : ∀ t, t < (rowsOf s σ.glb).length →
        slotMatches s σ.glb k t = false := by
      intro t ht
      exact firstMatch_none _ _ hfm t (Nat.zero_le _) (by omega)
    have habsnone : absOf s σ.glb k = none := by
      cases ha : absOf s σ.glb k with
      | none => rfl
      | some _ =>
        have h1 : (firstMatch s σ.glb k 0 s.capacity).isSome = true :=
          habs_iff.mpr (by rw [ha]; rfl)
        rw [hfm] at h1; exact absurd h1 (by simp)
    have hforN : execAt p (execStmt p (d + 1))
        (Stmt.forN tmpJ (.lit s.capacity) (freeSlotBody s))
        (σ.setLocal tmpAt Value.null)
        = .ok (σ₂, match firstFree s σ.glb 0 s.capacity with
                   | some _ => .ret (some (.bool true))
                   | none   => .normal) := by
      rw [execAt_forN]
      simp only [evalIndex, bind, Except.bind]
      exact hloop
    simp only [freeSlotBody] at hforN
    cases hff : firstFree s σ.glb 0 s.capacity with
    | some t =>
      rw [hff] at hforN hstate
      obtain ⟨nr, hrows, hstore, hok, hocc, hkey, hvals, hltt⟩ := hstate
      have hfree := firstFree_some (s := s) (glb := σ.glb) _ _ _ hff
      have hrowt : (rowsOf s σ.glb)[t]? = some ((rowsOf s σ.glb)[t]'hltt) :=
        List.getElem?_eq_getElem hltt
      have hoccOld : rowOccupied s ((rowsOf s σ.glb)[t]'hltt) = false := by
        simp only [slotFree, hrowt] at hfree
        cases hb : rowOccupied s ((rowsOf s σ.glb)[t]'hltt) with
        | false => rfl
        | true => rw [hb] at hfree; exact absurd hfree (by simp)
      refine ⟨σ₂, true, ?_, ?_, ?_, by simp, by rw [hhp2]; rfl, by rw [hnx2]; rfl⟩
      · simp only [insertDef, Stmt.block]
        rw [execAt_seq, hcall]
        simp only [bind, Except.bind]
        rw [execAt_seq, hbranch]
        simp only [bind, Except.bind]
        rw [execAt_seq, hforN]
        rfl
      · exact repInv_setRow R hok hkey hnomatch hrows hstore
      · intro _
        exact absOf_setRow hrowt hoccOld hocc hkey hvals hnomatch hrows
    | none =>
      rw [hff] at hforN hstate
      refine ⟨σ₂, false, ?_, ?_, by simp, ?_, by rw [hhp2]; rfl, by rw [hnx2]; rfl⟩
      · simp only [insertDef, Stmt.block]
        rw [execAt_seq, hcall]
        simp only [bind, Except.bind]
        rw [execAt_seq, hbranch]
        simp only [bind, Except.bind]
        rw [execAt_seq, hforN]
        simp only [bind, Except.bind]
        rfl
      · rw [show RepInv s σ₂.glb = RepInv s σ.glb from by rw [hstate]]
        exact R
      · intro _
        exact ⟨hstate, habsnone⟩

/-! ## The obligations

`call_insert` runs the body through `callFun`; the three milestone clauses are
read off it, and `milestoneTheorem` collects them with `find`'s and `erase`'s.
-/

theorem lookup_insert {pk : Schema.Field} (hpk : Schema.pkey? s = some pk) :
    lookupFun (genC s) (Schema.names s).insert = .ok (insertDef s pk) := by
  have hfuns : (genC s).funs = [findDef s pk, insertDef s pk, eraseDef s pk] := by
    simp only [genC, hpk]
  have h1 : ¬ ((findDef s pk).name = (Schema.names s).insert) := by
    simpa [findDef, Schema.names] using
      append_ne (s := s.name) (by decide : "_Find" ≠ "_InsertMaybe")
  simp [lookupFun, hfuns, h1, insertDef]

/-- The scan's context, assembled from the schema check. -/
theorem insCtx_of_wf {pk : Schema.Field} {k : Interface.Key} {vs : List Value}
    (hwf : Schema.wf s = true) (hpk : Schema.pkey? s = some pk)
    (hkty : k.ty = pk.ty) (hlen : vs.length = (Schema.valFields s).length) :
    InsCtx s pk k vs := by
  have F := facts_of_check (List.isEmpty_iff.mp hwf)
  have hfl := filter_of_pkey hpk
  have hpw := pw_pkcons_names hfl F
  exact
    { facts  := F
    , pkey   := hpk
    , filter := hfl
    , kty    := hkty
    , vlen   := hlen.symm
    , pkVal  := frameVal_pk (by simpa [parNames] using hpw)
    , valVal := fun t h1 h2 =>
        frameVal_val (by simpa [parNames] using hpw) t h1 h2 }

/-- **What a call to `insert` does.**

checked by: `lake build` -/
theorem call_insert {m : Mem} {pk : Schema.Field} {k : Interface.Key}
    {vs : List Value}
    (hwf : Schema.wf s = true) (hpk : Schema.pkey? s = some pk)
    (hkty : k.ty = pk.ty) (R : RepInv s m.glb)
    (hlen : vs.length = (Schema.valFields s).length) :
    ∃ (m' : Mem) (b : Bool),
      call s m (Schema.names s).insert (k.toValue :: vs) = .ok (m', some (.bool b))
      ∧ RepInv s m'.glb
      ∧ (b = true → absOf s m'.glb = Interface.Abs.insert (absOf s m.glb) k vs)
      ∧ (b = false → m' = m ∧ absOf s m.glb k = none) := by
  have F := facts_of_check (List.isEmpty_iff.mp hwf)
  have hfl := filter_of_pkey hpk
  have hpw : (parNames s pk).Pairwise (· ≠ ·) := pw_pkcons_names hfl F
  have C := insCtx_of_wf hwf hpk hkty hlen
  have hlookF : lookupFun (genC s) (Schema.names s).find = .ok (findDef s pk) :=
    (lookup_erase hpk).1
  have hcapLt : s.capacity < 4294967296 := by
    have := F.capLt; simp only [Wf.u32Bound] at this; omega
  have hrnd : ∀ t, t < (rowsOf s m.glb).length → (UInt32.ofNat t).toNat = t := by
    intro t ht
    have : t < 4294967296 := by rw [R.length] at ht; omega
    simpa [UInt32.toNat_ofNat'] using Nat.mod_eq_of_lt this
  have hframe : ∀ f ∈ s.fields,
      (m.toStore (insFrame s pk k vs)).getLocal f.name
        = some (frameVal s pk k vs f.name) := by
    intro f hf
    have hsome := insFrame_isSome (s := s) (pk := pk) (k := k) (vs := vs) hpw hlen hfl hf
    show Env.get? (insFrame s pk k vs) f.name = _
    simp only [frameVal]
    cases hg : (insFrame s pk k vs).get? f.name with
    | none => rw [hg] at hsome; exact absurd hsome (by simp)
    | some _ => rfl
  have hat : ((m.toStore (insFrame s pk k vs)).getLocal tmpAt).isSome = true := by
    show ((insFrame s pk k vs).get? tmpAt).isSome = true
    rw [insFrame_get_at F.notReserved hfl]; rfl
  have hjs : ((m.toStore (insFrame s pk k vs)).getLocal tmpJ).isSome = true := by
    show ((insFrame s pk k vs).get? tmpJ).isSome = true
    rw [insFrame_get_j F.notReserved hfl]; rfl
  obtain ⟨σ', b, hbody, R', habsT, habsF, hhp, hnx⟩ :=
    exec_insertBody (p := genC s) (d := 1) C hlookF
      (σ := m.toStore (insFrame s pk k vs)) (by simpa [Mem.toStore_glb] using R)
      hframe hat hjs (by simp only [Mem.toStore_glb]; exact hrnd)
  simp only [Mem.toStore_glb] at R' habsT habsF
  have hn : (genC s).funs.length = 2 + 1 := by simp only [genC, hpk]; rfl
  refine ⟨σ'.toMem, b, ?_, by simpa [Store.toMem_glb] using R', ?_, ?_⟩
  · simp only [call, callFun, lookup_insert hpk, buildFrame_insert hlen, bind,
      Except.bind, hn]
    rw [show execStmt (genC s) (2 + 1)
          = execAt (genC s) (execStmt (genC s) 2) from rfl, hbody]
  · intro hb; simpa [Store.toMem_glb] using habsT hb
  · intro hb
    obtain ⟨hglb, habs⟩ := habsF hb
    refine ⟨?_, habs⟩
    have : σ'.toMem = (m.toStore (insFrame s pk k vs)).toMem := by
      simp only [Store.toMem, hglb, hhp, hnx, Mem.toStore_glb]
    rw [this, Mem.toStore_toMem]

/-- **`insert` refines `Abs.insert`.**

checked by: `lake build` -/
theorem insertRefines : InsertRefines s := by
  intro m m' pk k vs b hwf hpk hkty R hlen hc
  obtain ⟨m₀, b₀, hcall, _, habsT, habsF⟩ := call_insert hwf hpk hkty R hlen
  rw [hcall] at hc
  obtain ⟨h₁, h₂⟩ := Prod.mk.injEq _ _ _ _ ▸ Except.ok.inj hc
  cases h₁
  have hb : b₀ = b := by
    have := Option.some.inj h₂
    cases this; rfl
  cases hb
  exact ⟨habsT, habsF⟩

/-- **`insert` never traps.**

checked by: `lake build` -/
theorem noTrapInsert : NoTrapInsert s := by
  intro m pk k vs hwf hpk hkty R hlen
  obtain ⟨m₀, b₀, hcall, _, _, _⟩ := call_insert hwf hpk hkty R hlen
  exact ⟨_, hcall⟩

/-- **Both writers preserve the representation invariant.**

checked by: `lake build` -/
theorem repInvPreserved : RepInvPreserved s := by
  intro m m' pk k vs r hwf hpk hkty R hlen
  constructor
  · intro hc
    obtain ⟨m₀, b₀, hcall, R', _, _⟩ := call_insert hwf hpk hkty R hlen
    rw [hcall] at hc
    obtain ⟨h₁, _⟩ := Prod.mk.injEq _ _ _ _ ▸ Except.ok.inj hc
    cases h₁; exact R'
  · intro hc; exact repInv_erase hwf hpk hkty R hc

/-- **The milestone: the generated table simulates the abstract map, for every
well-formed schema.**

Every clause of `Simulates` is now a theorem, so `MilestoneTheorem` is their
conjunction — one proof, quantified over schemas, which is the distinction the
project is arranged around.

checked by: `lake build` -/
theorem milestoneTheorem : MilestoneTheorem := by
  intro s hwf
  exact ⟨⟨noTrapFind, noTrapInsert, noTrapErase⟩, findCorrect, insertRefines,
    eraseRefines, repInvPreserved⟩

end ArrayTable
end Templates

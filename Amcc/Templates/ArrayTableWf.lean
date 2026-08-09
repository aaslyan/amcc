import Amcc.Templates.ArrayTable

/-!
# AMCC — Phase 3: the generator emits well-formed C, proved

`genWellFormed` at the bottom discharges `ArrayTable.GenWellFormed`: **every**
schema accepted by `Schema.check` generates a program accepted by `Wf.check`.
This is the project's first universally quantified theorem about the generator —
the instance checks in `ArrayTableChecks` are subsumed by it (and kept anyway,
because they also pin down concrete outputs).

The proof has three layers, and the file is ordered by them:

- **List facts** — the `dups`-based distinctness checks on both sides are
  characterised as `List.Pairwise (· ≠ ·)`, once, in both directions: the
  schema side is a *hypothesis* (`dups = []` gives pairwise-distinct field
  names) and the program side is a *goal* (pairwise-distinct generated names
  give `dups = []`).
- **Name algebra** — every generated C name is `s.name ++ <literal suffix>`,
  so distinctness reduces to cancelling the shared prefix and comparing
  literal suffixes. The one non-obvious case is a getter against `find`/
  `insert`/`erase`: `"_get_" ++ f` differs from `"_find"` at the second
  character, whatever `f` is.
- **Lookup facts** — the checker's `find?`-based scope lookups, resolved
  against the generated contexts. The reserved leading-underscore namespace
  is what makes every parameter lookup skip the generated temporaries, and
  the schema's no-`occupied`-collision rule is what makes the occupancy-flag
  lookup land on the generated field. Both schema rules are consumed here —
  neither is decorative.
-/

namespace Templates
namespace ArrayTable

open CSubset

/-! ## List facts -/

private theorem eraseDupsBy_loop_ne_nil {α} (r : α → α → Bool) :
    ∀ (l acc : List α), acc ≠ [] → List.eraseDupsBy.loop r l acc ≠ []
  | [], acc, h => by simpa [List.eraseDupsBy.loop] using h
  | b :: bs, acc, h => by
    cases hb : acc.any (r b) with
    | true => simpa [List.eraseDupsBy.loop, hb] using
        eraseDupsBy_loop_ne_nil r bs acc h
    | false => simpa [List.eraseDupsBy.loop, hb] using
        eraseDupsBy_loop_ne_nil r bs (b :: acc) (by simp)

private theorem eraseDups_ne_nil {α} [BEq α] {a : α} {as : List α} :
    (a :: as).eraseDups ≠ [] := by
  cases ha : ([] : List α).any (BEq.beq a) with
  | true => simp at ha
  | false =>
    show List.eraseDupsBy _ _ ≠ []
    simp only [List.eraseDupsBy, List.eraseDupsBy.loop, ha]
    exact eraseDupsBy_loop_ne_nil _ as [a] (by simp)

private theorem countP_le_one_of_pairwise {xs : List String}
    (h : xs.Pairwise (· ≠ ·)) : ∀ x ∈ xs, xs.countP (fun y => y == x) ≤ 1 := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons a l ih =>
    rw [List.pairwise_cons] at h
    intro x hx
    rw [List.countP_cons]
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · have hz : l.countP (fun y => y == x) = 0 := by
        rw [List.countP_eq_zero]
        intro b hb
        simp only [Bool.not_eq_true, beq_eq_false_iff_ne, ne_eq]
        exact fun e => (h.1 b hb) e.symm
      simp [hz]
    · have hne : (a == x) = false := beq_eq_false_iff_ne.mpr (h.1 x hx)
      simpa [hne] using ih h.2 x hx

private theorem pairwise_of_countP_le_one {xs : List String}
    (h : ∀ x ∈ xs, xs.countP (fun y => y == x) ≤ 1) : xs.Pairwise (· ≠ ·) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    rw [List.pairwise_cons]
    refine ⟨fun b hb hab => ?_, ih fun x hx => ?_⟩
    · have hcount : l.countP (fun y => y == a) + 1 ≤ 1 := by
        simpa [List.countP_cons] using h a (by simp)
      have hone : 0 < l.countP (fun y => y == a) :=
        List.countP_pos_iff.mpr ⟨b, hb, by simp [hab.symm]⟩
      omega
    · have htail : l.countP (fun y => y == x)
          ≤ (a :: l).countP (fun y => y == x) := by
        rw [List.countP_cons]; omega
      exact Nat.le_trans htail (h x (List.mem_cons_of_mem a hx))

/-- The `dups`-based distinctness check, characterised. Stated for `Wf.dups`;
`Schema.dups` has the same definition, so `schemaDups_eq_nil_iff` below reuses
this proof verbatim. -/
theorem dups_eq_nil_iff {xs : List Ident} :
    Wf.dups xs = [] ↔ xs.Pairwise (· ≠ ·) := by
  constructor
  · intro h
    rw [Wf.dups] at h
    have hfl : xs.filter (fun x => 1 < xs.countP (fun y => y == x)) = [] := by
      cases hfl : xs.filter (fun x => 1 < xs.countP (fun y => y == x)) with
      | nil => rfl
      | cons a as => rw [hfl] at h; exact absurd h eraseDups_ne_nil
    apply pairwise_of_countP_le_one
    intro x hx
    simpa using List.filter_eq_nil_iff.mp hfl x hx
  · intro h
    rw [Wf.dups]
    have hfl : xs.filter (fun x => 1 < xs.countP (fun y => y == x)) = [] :=
      List.filter_eq_nil_iff.mpr fun a ha => by
        simpa using countP_le_one_of_pairwise h a ha
    rw [hfl]
    rfl

theorem schemaDups_eq_nil_iff {xs : List Ident} :
    Schema.dups xs = [] ↔ xs.Pairwise (· ≠ ·) := dups_eq_nil_iff

/-- `Wf.distinct` succeeds exactly on pairwise-distinct names. `what` is
implicit so the lemma can serve as a `simp` rewrite for any message label. -/
theorem distinct_eq_nil {what : String} {xs : List Ident}
    (h : xs.Pairwise (· ≠ ·)) : Wf.distinct what xs = [] := by
  rw [Wf.distinct, dups_eq_nil_iff.mpr h]
  rfl

/-- Two *different* members of a pairwise-related list are related — the
symmetric-relation specialisation of `List.Pairwise`. -/
private theorem pairwise_rel_of_ne {α} {R : α → α → Prop}
    (hsym : ∀ x y, R x y → R y x) {l : List α} (h : l.Pairwise R)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : R a b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.pairwise_cons] at h
    cases ha with
    | head =>
      cases hb with
      | head => exact absurd rfl hne
      | tail _ hb => exact h.1 b hb
    | tail _ ha =>
      cases hb with
      | head => exact hsym _ _ (h.1 a ha)
      | tail _ hb => exact ih h.2 ha hb

/-- First-match lookup in a keyed association list with pairwise-distinct
keys finds exactly the member. This is the single lemma behind every scope
lookup in the proof: contexts, struct fields and parameter lists are all
`find?` over `(name, _)` pairs. -/
theorem find?_keyed {β} {l : List (Ident × β)} {x : Ident} {b : β}
    (hpw : (l.map Prod.fst).Pairwise (· ≠ ·)) (hmem : (x, b) ∈ l) :
    l.find? (fun p => p.1 == x) = some (x, b) := by
  induction l with
  | nil => cases hmem
  | cons hd tl ih =>
    rw [List.map_cons, List.pairwise_cons] at hpw
    cases hmem with
    | head => exact List.find?_cons_of_pos (by simp)
    | tail _ hmem =>
      have hne : hd.1 ≠ x := hpw.1 x (List.mem_map_of_mem hmem)
      rw [List.find?_cons_of_neg (by simp [hne])]
      exact ih hpw.2 hmem

/-- A `find?` that misses an entire keyed prefix continues in the suffix. -/
theorem find?_keyed_skip {β} {l₁ l₂ : List (Ident × β)} {x : Ident}
    (h : ∀ p ∈ l₁, p.1 ≠ x) :
    (l₁ ++ l₂).find? (fun p => p.1 == x) = l₂.find? (fun p => p.1 == x) := by
  rw [List.find?_append]
  have : l₁.find? (fun p => p.1 == x) = none :=
    List.find?_eq_none.mpr fun p hp => by simp [h p hp]
  rw [this]
  rfl

/-! ## Name algebra

Every generated name is `s.name ++ suffix` for a literal suffix (associating
`getterName` to expose that shape), so inequality of generated names reduces to
inequality of suffixes under a cancelled shared prefix. -/

private theorem append_cancel_left {s a b : String} (h : s ++ a = s ++ b) :
    a = b := by
  have hd := congrArg String.toList h
  simp only [String.toList_append] at hd
  exact String.ext (List.append_cancel_left hd)

private theorem append_ne {s a b : String} (h : a ≠ b) : s ++ a ≠ s ++ b :=
  fun e => h (append_cancel_left e)

private theorem append_inj {s a b : String} : s ++ a = s ++ b ↔ a = b :=
  ⟨append_cancel_left, fun h => h ▸ rfl⟩

/-- A name in the reserved leading-underscore namespace never equals one
outside it — how the generated temporaries stay clear of every schema name. -/
private theorem ne_of_reserved {a b : Ident}
    (ha : Schema.isReservedName a = false) (hb : Schema.isReservedName b = true) :
    a ≠ b := fun e => by rw [e, hb] at ha; cases ha

/-! ## Schema facts

Everything `Schema.check s = []` says that this proof consumes, extracted once.
(The C-identifier legality clauses are *not* here: `Wf.check` does not inspect
name shape — those clauses exist for the Phase 4 printer.) -/

/-- The consumed content of a passing schema check. -/
structure Facts (s : Schema) : Prop where
  capPos      : 0 < s.capacity
  capLt       : s.capacity < Wf.u32Bound
  pwNames     : (s.fields.map Schema.Field.name).Pairwise (· ≠ ·)
  notOccupied : ∀ f ∈ s.fields, f.name ≠ "occupied"
  notReserved : ∀ f ∈ s.fields, Schema.isReservedName f.name = false

private theorem true_of_if {c : Prop} [Decidable c] {m : String}
    (h : (if c then ([] : List String) else [m]) = []) : c := by
  split at h
  · assumption
  · exact absurd h (by simp)

private theorem false_of_if {c : Prop} [Decidable c] {m : String}
    (h : (if c then [m] else ([] : List String)) = []) : ¬c := by
  split at h
  · exact absurd h (by simp)
  · assumption

theorem facts_of_check {s : Schema} (h : Schema.check s = []) : Facts s := by
  simp only [Schema.check, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨_, hcap⟩, hcapLt⟩, _⟩, hdups⟩, hfields⟩, _⟩ := h
  refine ⟨true_of_if hcap, true_of_if hcapLt, ?_, ?_, ?_⟩
  · exact schemaDups_eq_nil_iff.mp (List.map_eq_nil_iff.mp hdups)
  · intro f hf
    have := List.flatMap_eq_nil_iff.mp hfields f hf
    simp only [List.append_eq_nil_iff] at this
    have hocc := false_of_if this.1.2
    simpa [beq_iff_eq, Schema.names] using hocc
  · intro f hf
    have := List.flatMap_eq_nil_iff.mp hfields f hf
    simp only [List.append_eq_nil_iff] at this
    have hres := false_of_if this.2
    simpa using hres

/-- A passing check has exactly one `Pkey` field. -/
theorem pkeyFilter_of_check {s : Schema} (h : Schema.check s = []) :
    ∃ pk, s.fields.filter (fun f => f.reftype == .Pkey) = [pk] := by
  simp only [Schema.check, List.append_eq_nil_iff] at h
  have hmatch := h.1.1.1.2
  cases hfl : s.fields.filter (fun f => f.reftype == .Pkey) with
  | nil => rw [hfl] at hmatch; simp at hmatch
  | cons a tl =>
    cases tl with
    | nil => exact ⟨a, rfl⟩
    | cons b tl2 => rw [hfl] at hmatch; simp at hmatch

/-! ## Derived field facts

Consequences of the facts for the `pk :: valFields` split the generator works
with. `hfl` is always the singleton-filter fact from `pkeyFilter_of_check`. -/

/-- The derived `BEq Schema.Reftype` is not registered lawful; two
constructors, so the characterisation is a case bash. -/
private theorem reftype_beq_iff {a b : Schema.Reftype} : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

section FieldFacts

variable {s : Schema} {pk : Schema.Field}
  (hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk])

include hfl

private theorem pk_mem : pk ∈ s.fields := by
  have : pk ∈ s.fields.filter (fun f => f.reftype == .Pkey) := by rw [hfl]; simp
  exact (List.mem_filter.mp this).1

private theorem pk_reftype : pk.reftype = .Pkey := by
  have : pk ∈ s.fields.filter (fun f => f.reftype == .Pkey) := by rw [hfl]; simp
  simpa [reftype_beq_iff] using (List.mem_filter.mp this).2

/-- Every schema field is the primary key or a value field: `Reftype` has two
constructors and the filter is a singleton. -/
private theorem mem_pk_cons {f : Schema.Field} (hf : f ∈ s.fields) :
    f ∈ pk :: Schema.valFields s := by
  cases hr : f.reftype with
  | Pkey =>
    have : f ∈ s.fields.filter (fun f => f.reftype == .Pkey) :=
      List.mem_filter.mpr ⟨hf, by rw [hr]; decide⟩
    rw [hfl] at this
    simp at this
    simp [this]
  | Val =>
    exact List.mem_cons_of_mem pk
      (List.mem_filter.mpr ⟨hf, by rw [hr]; decide⟩)

omit hfl

private theorem val_mem {f : Schema.Field} (hf : f ∈ Schema.valFields s) :
    f ∈ s.fields ∧ f.reftype = .Val := by
  have := List.mem_filter.mp hf
  exact ⟨this.1, by simpa [reftype_beq_iff] using this.2⟩

private theorem pw_val_names (F : Facts s) :
    ((Schema.valFields s).map Schema.Field.name).Pairwise (· ≠ ·) :=
  List.Pairwise.sublist (List.filter_sublist.map Schema.Field.name) F.pwNames

include hfl

private theorem pk_name_ne_val (F : Facts s) :
    ∀ g ∈ Schema.valFields s, pk.name ≠ g.name := by
  intro g hg
  obtain ⟨hgmem, hgref⟩ := val_mem hg
  have hne : pk ≠ g := fun e => by
    rw [← e, pk_reftype hfl] at hgref; cases hgref
  exact pairwise_rel_of_ne (fun _ _ h => h.symm)
    (List.pairwise_map.mp F.pwNames) (pk_mem hfl) hgmem hne

/-- The names of `pk :: valFields`, pairwise distinct — the parameter list of
the generated `insert`. -/
private theorem pw_pkcons_names (F : Facts s) :
    ((pk :: Schema.valFields s).map Schema.Field.name).Pairwise (· ≠ ·) := by
  rw [List.map_cons, List.pairwise_cons]
  refine ⟨?_, pw_val_names F⟩
  intro n hn
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
  exact pk_name_ne_val hfl F g hg

end FieldFacts

/-! ## The struct, global, and name-distinctness components -/

private theorem distinct_singleton (what : String) (x : Ident) :
    Wf.distinct what [x] = [] := distinct_eq_nil (by simp)

private theorem rowFields_fst (s : Schema) :
    (rowStructDef s).fields.map Prod.fst
      = s.fields.map Schema.Field.name ++ ["occupied"] := by
  simp [rowStructDef, Schema.names]

private theorem pw_rowFields {s : Schema} (F : Facts s) :
    ((rowStructDef s).fields.map Prod.fst).Pairwise (· ≠ ·) := by
  rw [rowFields_fst, List.pairwise_append]
  refine ⟨F.pwNames, by simp, ?_⟩
  intro a ha b hb
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
  simp at hb
  rw [hb]
  exact F.notOccupied f hf

/-- The generated row struct passes the struct checks: distinct field names,
scalar fields only (so sizes and layout dependencies are trivial). -/
private theorem checkStructs_gen {s : Schema} (F : Facts s) :
    Wf.checkStructs [rowStructDef s] = [] := by
  rw [Wf.checkStructs]
  simp only [List.map_cons, List.map_nil, List.zipIdx_cons, List.zipIdx_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.take_zero,
    List.append_eq_nil_iff]
  refine ⟨distinct_singleton _ _, distinct_eq_nil (pw_rowFields F), ?_⟩
  rw [List.flatMap_eq_nil_iff]
  intro fv hfv
  rw [rowStructDef] at hfv
  simp only [List.mem_append, List.mem_map, List.mem_cons] at hfv
  rcases hfv with ⟨f, _, rfl⟩ | hocc
  · simp [Wf.Ty.sizesOk, Wf.Ty.allStructs, Wf.Ty.layoutDeps]
  · simp at hocc
    rw [hocc]
    simp [Wf.Ty.sizesOk, Wf.Ty.allStructs, Wf.Ty.layoutDeps]

/-- The generated storage array passes the global checks: its size is the
capacity (positive and `u32`-bounded, by the schema check), it contains no
pointer, and its element struct is the one declared. -/
private theorem checkGlobals_gen {s : Schema} (F : Facts s) :
    Wf.checkGlobals [rowStructDef s] [storageDef s] = [] := by
  rw [Wf.checkGlobals]
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_eq_nil_iff]
  refine ⟨distinct_singleton _ _, ?_⟩
  simp [storageDef, rowStructDef, Wf.Ty.sizesOk, Wf.Ty.hasPtr,
    Wf.Ty.allStructs, F.capPos, F.capLt]

/-- The generated function names are pairwise distinct: the fixed suffixes
differ pairwise, a getter differs from every fixed name at the character after
the shared `s.name ++ "_"`, and getters of distinct fields differ because the
field names do. -/
private theorem pw_funNames (s : Schema) :
    ((Schema.names s).find :: (Schema.names s).insert :: [(Schema.names s).erase]).Pairwise
      (· ≠ ·) := by
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, by simp⟩⟩
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact append_ne (by decide)
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    exact append_ne (by decide)

/-! ## Lawful `BEq` for the syntax types

The checker compares types with `==` throughout; the derived `BEq` instances
are not registered lawful, so `a == a` on a *symbolic* type would be stuck.
These instances conceptually belong beside the `deriving` clauses in
`Syntax.lean`; they live here because this proof is their first consumer. -/

instance : LawfulBEq ScalarTy where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact Bool.noConfusion h
  rfl {a} := by cases a <;> rfl

private theorem ty_eq_of_beq : ∀ (a b : Ty), (a == b) = true → a = b
  | .scalar x, .scalar y, h => by rw [eq_of_beq (show (x == y) = true from h)]
  | .scalar _, .strct _, h => Bool.noConfusion h
  | .scalar _, .arr _ _, h => Bool.noConfusion h
  | .scalar _, .ptr _, h => Bool.noConfusion h
  | .strct _, .scalar _, h => Bool.noConfusion h
  | .strct m, .strct n, h => by rw [eq_of_beq (show (m == n) = true from h)]
  | .strct _, .arr _ _, h => Bool.noConfusion h
  | .strct _, .ptr _, h => Bool.noConfusion h
  | .arr _ _, .scalar _, h => Bool.noConfusion h
  | .arr _ _, .strct _, h => Bool.noConfusion h
  | .arr t m, .arr u n, h => by
    have h' := Bool.and_eq_true_iff.mp (show ((t == u) && (m == n)) = true from h)
    rw [ty_eq_of_beq t u h'.1, eq_of_beq h'.2]
  | .arr _ _, .ptr _, h => Bool.noConfusion h
  | .ptr _, .scalar _, h => Bool.noConfusion h
  | .ptr _, .strct _, h => Bool.noConfusion h
  | .ptr _, .arr _ _, h => Bool.noConfusion h
  | .ptr t, .ptr u, h => by rw [ty_eq_of_beq t u (show (t == u) = true from h)]

private theorem ty_beq_rfl : ∀ t : Ty, (t == t) = true
  | .scalar x => show (x == x) = true from beq_self_eq_true x
  | .strct n => show (n == n) = true from beq_self_eq_true n
  | .arr t n => show ((t == t) && (n == n)) = true by
      rw [ty_beq_rfl t, beq_self_eq_true n]; rfl
  | .ptr t => ty_beq_rfl t

instance : LawfulBEq Ty where
  eq_of_beq {a b} h := ty_eq_of_beq a b h
  rfl {a} := ty_beq_rfl a

instance : LawfulBEq ValTy where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> first
      | exact Bool.noConfusion h
      | rw [eq_of_beq (α := ScalarTy) h]
      | rw [eq_of_beq (α := Ty) h]
  rfl {a} := by cases a with
    | scalar t => exact beq_self_eq_true t
    | ptr t => exact beq_self_eq_true t

/-! ## Statement combinators distribute over `Stmt.block`

`Stmt.block` is sugar for nested `seq`, so the checker's statement traversals
distribute over it as `flatMap` — which is what lets the `insert` body's
schema-dependent lists of assignments be checked elementwise. -/

private theorem checkStmt_block (c : Wf.Ctx) (ret : Option ValTy) :
    ∀ l : List Stmt, Wf.checkStmt c ret (Stmt.block l) = l.flatMap (Wf.checkStmt c ret)
  | [] => by simp [Stmt.block, Wf.checkStmt]
  | [st] => by simp [Stmt.block]
  | st :: st2 :: rest => by
    show Wf.checkStmt c ret (.seq st (Stmt.block (st2 :: rest))) = _
    rw [show Wf.checkStmt c ret (.seq st (Stmt.block (st2 :: rest)))
        = Wf.checkStmt c ret st ++ Wf.checkStmt c ret (Stmt.block (st2 :: rest)) from rfl]
    rw [checkStmt_block c ret (st2 :: rest)]
    simp

private theorem assigns_block :
    ∀ l : List Stmt, Wf.Stmt.assigns (Stmt.block l) = l.flatMap Wf.Stmt.assigns
  | [] => rfl
  | [st] => by simp [Stmt.block]
  | st :: st2 :: rest => by
    show Wf.Stmt.assigns (.seq st (Stmt.block (st2 :: rest))) = _
    rw [show Wf.Stmt.assigns (.seq st (Stmt.block (st2 :: rest)))
        = Wf.Stmt.assigns st ++ Wf.Stmt.assigns (Stmt.block (st2 :: rest)) from rfl]
    rw [assigns_block (st2 :: rest)]
    simp

/-! ## The generated function bodies pass `checkFun`

One lemma per generated function. Each is a single `simp` over the checker's
definitions, driven by three kinds of rewrite: the lookup facts below (scope
resolutions that hold because of the schema's name rules), `rfl`-facts for the
closed operator typings, and `distinct_eq_nil` for the name lists. -/

section CheckFuns

variable {s : Schema} {pk : Schema.Field}

/-- Looking up a schema field in the generated row struct finds its slot: the
schema's distinct-names rule makes the first match the right one. -/
private theorem rowfield_lookup (F : Facts s) {f : Schema.Field} (hf : f ∈ s.fields) :
    ((s.fields.map (fun g => (g.name, Ty.scalar g.ty))
        ++ [((Schema.names s).occupied, Ty.scalar .bool)]).find?
      (fun fv => fv.1 == f.name)) = some (f.name, Ty.scalar f.ty) :=
  find?_keyed (pw_rowFields F) (List.mem_append_left _ (List.mem_map_of_mem hf))

/-- Looking up the occupancy flag skips every schema field — the schema's
no-`occupied`-collision rule earning its keep. -/
private theorem rowfield_occ_lookup (F : Facts s) :
    ((s.fields.map (fun g => (g.name, Ty.scalar g.ty))
        ++ [((Schema.names s).occupied, Ty.scalar .bool)]).find?
      (fun fv => fv.1 == (Schema.names s).occupied))
      = some ((Schema.names s).occupied, Ty.scalar .bool) := by
  rw [find?_keyed_skip fun p hp => ?_]
  · exact List.find?_cons_of_pos (by simp)
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
    exact F.notOccupied f hf

private theorem binTy_eq_scalar (t : ScalarTy) :
    Wf.binTy .eq (.scalar t) (.scalar t) = some (.scalar .bool) := by
  cases t <;> rfl

/-- `p != NULL` typechecks: both sides are the same pointer type. -/
private theorem binTy_ne_ptr (t : Ty) :
    Wf.binTy .ne (.ptr t) (.ptr t) = some (.scalar .bool) := by
  simp [Wf.binTy, Wf.isPtrTy, Wf.isWord]

private theorem checkFun_find (F : Facts s)
    (hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk])
    (earlier : List FunDef) :
    Wf.checkFun [rowStructDef s] [storageDef s] earlier (findDef s pk) = [] := by
  have hpkres := F.notReserved pk (pk_mem hfl)
  have hne_i : pk.name ≠ "_i" := ne_of_reserved hpkres (by decide)
  have hpk_i : (pk.name == "_i") = false := beq_eq_false_iff_ne.mpr hne_i
  have hpw : ([pk.name, "_i"] : List Ident).Pairwise (· ≠ ·) := by simp [hne_i]
  have hland : Wf.binTy .land (.scalar .bool) (.scalar .bool)
      = some (.scalar .bool) := rfl
  simp [Wf.checkFun, findDef, findLoopBody, findGuard, LocalDef.zeroed,
    rowStructDef, storageDef,
    tmpI, field, slot, capLit,
    Wf.checkStmt, Wf.addrChecks, Wf.inferExpr, Wf.inferLVal, Wf.indexOk,
    Wf.litTy, Wf.isValTy, Wf.Stmt.assigns, Wf.Stmt.alwaysReturns,
    Wf.Ctx.local?, Wf.Ctx.global?, Wf.Ctx.struct?, Wf.Ctx.field?,
    ValTy.toTy, Stmt.when, Stmt.block, List.find?,
    hpk_i, rowfield_lookup F (pk_mem hfl), rowfield_occ_lookup F,
    binTy_eq_scalar, hland, F.capLt, distinct_eq_nil hpw,
    rowTy, nullRow, Wf.rootIsLocal]

private theorem checkFun_erase (F : Facts s)
    (hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk])
    (rest : List FunDef) :
    Wf.checkFun [rowStructDef s] [storageDef s] (findDef s pk :: rest)
      (eraseDef s pk) = [] := by
  have hpkres := F.notReserved pk (pk_mem hfl)
  have hne_at : pk.name ≠ "_at" := ne_of_reserved hpkres (by decide)
  have hpk_at : (pk.name == "_at") = false := beq_eq_false_iff_ne.mpr hne_at
  have hpw : ([pk.name, "_at"] : List Ident).Pairwise (· ≠ ·) := by simp [hne_at]
  simp [Wf.checkFun, eraseDef, findDef, atLocal, LocalDef.zeroed,
    rowStructDef, storageDef, tmpAt, ptrField, rowTy, nullRow,
    Wf.checkStmt, Wf.addrChecks, Wf.inferExpr, Wf.inferLVal, Wf.indexOk,
    Wf.litTy, Wf.isValTy, Wf.Stmt.alwaysReturns,
    Wf.Ctx.local?, Wf.Ctx.global?, Wf.Ctx.struct?, Wf.Ctx.field?, Wf.Ctx.fun?,
    ValTy.toTy, Stmt.when, Stmt.block, List.find?,
    hpk_at, rowfield_occ_lookup F,
    binTy_ne_ptr, distinct_eq_nil hpw]

/-- Checking one generated assignment `g_<t>[i].<f> = <f>;` — the element step
for both of `insert`'s assignment lists. Stated against any context that
resolves the storage, the row struct, the index temporary `i`, and the
parameter `f.name`, so both branch proofs can instantiate it with `rfl`s. -/
private theorem check_assign_field (c : Wf.Ctx) (F : Facts s)
    {f : Schema.Field} (hf : f ∈ s.fields) {i : Ident}
    (hstr : c.structs = [rowStructDef s]) (hglb : c.globals = [storageDef s])
    (hloci : c.locals.find? (fun lv => lv.1 == i) = some (i, ValTy.scalar .u32))
    (hlocf : c.locals.find? (fun lv => lv.1 == f.name)
      = some (f.name, ValTy.scalar f.ty)) :
    Wf.checkStmt c (some (.scalar .bool))
      (.assign (field s i f.name) (.rd (.var f.name))) = [] := by
  simp [Wf.checkStmt, Wf.addrChecks, Wf.inferExpr, Wf.inferLVal, Wf.indexOk,
    Wf.isValTy, field, slot, Wf.Ctx.local?, Wf.Ctx.global?, Wf.Ctx.struct?,
    Wf.Ctx.field?, hstr, hglb, hloci, hlocf, storageDef, rowStructDef,
    rowfield_lookup F hf, ValTy.toTy]

/-- Checking one generated `p->f = f;` — the element step of `insert`'s
present-key branch, which now writes through the row pointer `Find` returned
rather than through a slot index. -/
private theorem check_assign_ptrField (c : Wf.Ctx) (F : Facts s)
    {f : Schema.Field} (hf : f ∈ s.fields) {p : Ident}
    (hstr : c.structs = [rowStructDef s])
    (hlocp : c.locals.find? (fun lv => lv.1 == p)
      = some (p, ValTy.ptr (rowTy s)))
    (hlocf : c.locals.find? (fun lv => lv.1 == f.name)
      = some (f.name, ValTy.scalar f.ty)) :
    Wf.checkStmt c (some (.scalar .bool))
      (.assign (ptrField p f.name) (.rd (.var f.name))) = [] := by
  simp [Wf.checkStmt, Wf.addrChecks, Wf.inferExpr, Wf.inferLVal,
    Wf.isValTy, ptrField, rowTy, Wf.Ctx.local?, Wf.Ctx.struct?, Wf.Ctx.field?,
    hstr, hlocp, hlocf, rowStructDef, rowfield_lookup F hf, ValTy.toTy]

/-- Checking `_at = <t>_Find(pk);` — resolves the callee at the head of the
`earlier` list, the argument against the parameter environment, and the
destination temporary. -/
private theorem check_call_find (c : Wf.Ctx) (ret? : Option ValTy)
    {rest : List FunDef} (hfuns : c.funs = findDef s pk :: rest)
    (hlocpk : c.locals.find? (fun lv => lv.1 == pk.name)
      = some (pk.name, ValTy.scalar pk.ty))
    (hlocat : c.locals.find? (fun lv => lv.1 == "_at")
      = some ("_at", ValTy.ptr (rowTy s))) :
    Wf.checkStmt c ret? (.call (some tmpAt) (Schema.names s).find
      [.rd (.var pk.name)]) = [] := by
  simp [Wf.checkStmt, Wf.Ctx.fun?, hfuns, findDef, Wf.addrChecks, Wf.inferExpr,
    Wf.inferLVal, Wf.isValTy, Wf.Ctx.local?, hlocpk, hlocat, ValTy.toTy, tmpAt,
    rowTy]

/-- Checking the present-key branch: every value field is rewritten in place,
then `return true`. -/
private theorem check_when_update (c : Wf.Ctx) (F : Facts s)
    (_hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk])
    (hstr : c.structs = [rowStructDef s]) (hglb : c.globals = [storageDef s])
    (hlocat : c.locals.find? (fun lv => lv.1 == "_at")
      = some ("_at", ValTy.ptr (rowTy s)))
    (hlocf : ∀ f ∈ pk :: Schema.valFields s,
      c.locals.find? (fun lv => lv.1 == f.name)
        = some (f.name, ValTy.scalar f.ty)) :
    Wf.checkStmt c (some (.scalar .bool))
      (.when (.bin .ne (.rd (.var tmpAt)) (nullRow s))
        (.block ((Schema.valFields s).map
            (fun f => .assign (ptrField tmpAt f.name) (.rd (.var f.name)))
          ++ [.ret (some (.lit (.bool true)))]))) = [] := by
  simp only [Stmt.when, Wf.checkStmt, checkStmt_block, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_eq_nil_iff]
  repeat' apply And.intro
  all_goals first
    | exact List.flatMap_eq_nil_iff.mpr fun st hst => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hst
        exact check_assign_ptrField c F (val_mem hf).1 hstr hlocat
          (hlocf f (List.mem_cons_of_mem pk hf))
    | simp [Wf.addrChecks, Wf.inferExpr, Wf.inferLVal,
        Wf.isValTy, Wf.Ctx.local?, hlocat, binTy_ne_ptr, nullRow, rowTy,
        tmpAt, Wf.litTy, ValTy.toTy]

/-- Checking the free-slot scan: claim the slot, write every field (key
included), `return true`; the loop body never assigns the loop variable
because every assignment targets a field lvalue. -/
private theorem check_forn (c : Wf.Ctx) (F : Facts s)
    (hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk])
    (hstr : c.structs = [rowStructDef s]) (hglb : c.globals = [storageDef s])
    (hlocj : c.locals.find? (fun lv => lv.1 == "_j")
      = some ("_j", ValTy.scalar .u32))
    (hlocf : ∀ f ∈ pk :: Schema.valFields s,
      c.locals.find? (fun lv => lv.1 == f.name)
        = some (f.name, ValTy.scalar f.ty)) :
    Wf.checkStmt c (some (.scalar .bool))
      (.forN tmpJ (.lit s.capacity) <|
        .when (.un .lnot (.rd (field s tmpJ (Schema.names s).occupied))) <|
          .block ([.assign (field s tmpJ (Schema.names s).occupied)
                    (.lit (.bool true))]
                  ++ s.fields.map
                       (fun f => .assign (field s tmpJ f.name)
                         (.rd (.var f.name)))
                  ++ [.ret (some (.lit (.bool true)))])) = [] := by
  have hassignsAll : List.flatMap Wf.Stmt.assigns
      (s.fields.map (fun f =>
        Stmt.assign (field s tmpJ f.name) (.rd (.var f.name)))) = [] :=
    List.flatMap_eq_nil_iff.mpr fun st hst => by
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hst; rfl
  have hlnot : Wf.unTy .lnot (.scalar .bool) = some (.scalar .bool) := rfl
  simp only [Stmt.when, Wf.checkStmt, checkStmt_block, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_eq_nil_iff]
  repeat' apply And.intro
  all_goals first
    | exact List.flatMap_eq_nil_iff.mpr fun st hst => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hst
        exact check_assign_field c F hf hstr hglb hlocj
          (hlocf f (mem_pk_cons hfl hf))
    | (simp only [Wf.Stmt.assigns, assigns_block, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, hassignsAll]
       simp [tmpJ, field, slot, Wf.Stmt.assigns])
    | simp [Wf.addrChecks, Wf.inferExpr, Wf.inferLVal,
        Wf.indexOk, Wf.isValTy, field, slot, tmpJ, Wf.Ctx.local?,
        Wf.Ctx.global?, Wf.Ctx.struct?, Wf.Ctx.field?, hstr, hglb,
        storageDef, rowStructDef, rowfield_occ_lookup F, hlocj, F.capLt,
        hlnot, Wf.litTy, ValTy.toTy]

private theorem checkFun_insert (F : Facts s)
    (hfl : s.fields.filter (fun f => f.reftype == .Pkey) = [pk])
    (rest : List FunDef) :
    Wf.checkFun [rowStructDef s] [storageDef s] (findDef s pk :: rest)
      (insertDef s pk) = [] := by
  have hpkres := F.notReserved pk (pk_mem hfl)
  have hmemfields : ∀ g ∈ pk :: Schema.valFields s, g ∈ s.fields := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact pk_mem hfl
    · exact (val_mem hg).1
  have hvalres : ∀ g ∈ Schema.valFields s, Schema.isReservedName g.name = false :=
    fun g hg => F.notReserved g (val_mem hg).1
  -- the parameter/local name list, pairwise distinct
  have hpwFull : (pk.name :: ((Schema.valFields s).map (fun g => g.name)
      ++ ["_at", "_j"])).Pairwise (· ≠ ·) := by
    rw [List.pairwise_cons]
    constructor
    · intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
        exact pk_name_ne_val hfl F g hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl <;> exact ne_of_reserved hpkres (by decide)
    · rw [List.pairwise_append]
      refine ⟨pw_val_names F, by simp, ?_⟩
      intro a ha b hb
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> exact ne_of_reserved (hvalres g hg) (by decide)
  -- the same list as the context's key list
  have hkeys : (((pk :: Schema.valFields s).map (fun g => (g.name, ValTy.scalar g.ty))
      ++ [("_at", ValTy.ptr (rowTy s)), ("_j", ValTy.scalar .u32)]).map Prod.fst)
      = pk.name :: ((Schema.valFields s).map (fun g => g.name) ++ ["_at", "_j"]) := by
    simp
  have hpwkeys := hkeys.symm ▸ hpwFull
  -- scope lookups against the full local environment
  have hskip : ∀ (x : Ident), Schema.isReservedName x = true →
      ∀ p ∈ (pk :: Schema.valFields s).map (fun g => (g.name, ValTy.scalar g.ty)),
        p.1 ≠ x := by
    intro x hx p hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
    exact ne_of_reserved (F.notReserved g (hmemfields g hg)) hx
  have ha : ((pk :: Schema.valFields s).map (fun g => (g.name, ValTy.scalar g.ty))
      ++ [("_at", ValTy.ptr (rowTy s)), ("_j", ValTy.scalar .u32)]).find?
        (fun lv => lv.1 == "_at") = some ("_at", ValTy.ptr (rowTy s)) := by
    rw [find?_keyed_skip (hskip "_at" (by decide))]
    exact List.find?_cons_of_pos (by simp)
  have hj : ((pk :: Schema.valFields s).map (fun g => (g.name, ValTy.scalar g.ty))
      ++ [("_at", ValTy.ptr (rowTy s)), ("_j", ValTy.scalar .u32)]).find?
        (fun lv => lv.1 == "_j") = some ("_j", ValTy.scalar .u32) := by
    rw [find?_keyed_skip (hskip "_j" (by decide))]
    rw [List.find?_cons_of_neg (by simp)]
    exact List.find?_cons_of_pos (by simp)
  have hvlookup : ∀ g ∈ pk :: Schema.valFields s,
      ((pk :: Schema.valFields s).map (fun g => (g.name, ValTy.scalar g.ty))
        ++ [("_at", ValTy.ptr (rowTy s)), ("_j", ValTy.scalar .u32)]).find?
          (fun lv => lv.1 == g.name) = some (g.name, ValTy.scalar g.ty) :=
    fun g hg => find?_keyed hpwkeys
      (List.mem_append_left _ (List.mem_map_of_mem hg))
  -- split the four checkFun components
  simp only [Wf.checkFun, List.append_eq_nil_iff]
  refine ⟨⟨⟨?dist, ?inits⟩, ?body⟩, ?rets⟩
  case dist =>
    refine distinct_eq_nil ?_
    have hnames : ((insertDef s pk).params.map Prod.fst
        ++ (insertDef s pk).locals.map LocalDef.name)
        = pk.name :: ((Schema.valFields s).map (fun g => g.name)
            ++ ["_at", "_j"]) := by
      simp [insertDef, atLocal, LocalDef.zeroed, tmpAt, tmpJ, Function.comp]
    rw [hnames]
    exact hpwFull
  case inits =>
    simp [insertDef, atLocal, LocalDef.zeroed, Wf.addrChecks, Wf.inferExpr,
      Wf.litTy, ValTy.toTy, nullRow, rowTy]
  case rets =>
    simp [insertDef, Stmt.block, Stmt.when, Wf.Stmt.alwaysReturns]
  case body =>
    simp only [insertDef, atLocal, LocalDef.zeroed, List.map_cons, List.map_nil]
    rw [checkStmt_block]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_eq_nil_iff]
    refine ⟨?hcall, ?hwhen, ?hforn, ?hret⟩
    case hcall =>
      exact check_call_find _ _ rfl
        (hvlookup pk (by simp)) ha
    case hwhen =>
      exact check_when_update _ F hfl rfl rfl ha hvlookup
    case hforn =>
      exact check_forn _ F hfl rfl rfl hj hvlookup
    case hret =>
      simp [Wf.checkStmt, Wf.addrChecks, Wf.inferExpr, Wf.litTy, ValTy.toTy]

end CheckFuns

/-! ## The theorem -/

/-- **The generator emits well-formed C, for every accepted schema.**

The first universally quantified theorem about `genC`: the instance checks in
`ArrayTableChecks` (`Wf.check (genC orders) = []` and its `keysOnly` twin) are
the `s := orders` / `s := keysOnly` cases of this.

checked by: `lake build` -/
theorem genWellFormed : GenWellFormed := by
  intro s hwf
  have hchk : Schema.check s = [] := List.isEmpty_iff.mp hwf
  have F := facts_of_check hchk
  obtain ⟨pk, hfl⟩ := pkeyFilter_of_check hchk
  have hpk : Schema.pkey? s = some pk := by
    simp only [Schema.pkey?, hfl]
  simp only [genC, hpk, Wf.check, List.append_eq_nil_iff]
  refine ⟨⟨⟨checkStructs_gen F, checkGlobals_gen F⟩, ?dist⟩, ?funs⟩
  case dist =>
    refine distinct_eq_nil ?_
    have hnames : (([findDef s pk, insertDef s pk, eraseDef s pk]).map FunDef.name)
        = (Schema.names s).find :: (Schema.names s).insert
          :: [(Schema.names s).erase] := by
      simp [findDef, insertDef, eraseDef]
    rw [hnames]
    exact pw_funNames s
  case funs =>
    rw [List.flatMap_eq_nil_iff]
    intro fdi hfdi
    obtain ⟨fd, i⟩ := fdi
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hfdi
    rcases hfdi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact checkFun_find F hfl _
    · exact checkFun_insert F hfl []
    · exact checkFun_erase F hfl [insertDef s pk]

end ArrayTable
end Templates

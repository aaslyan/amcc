import Amcc.CSubset.Calls

/-!
# AMCC — chains in the store

The array table's representation invariant quantifies over indices of a
`List Value` — the storage array is a *carrier*, and every clause is a
statement about it. A linked structure has no carrier: its shape is a property
of a graph in the heap. This module supplies the predicate that stands in for
the missing carrier, once, for every template that threads rows on a link
field.

Both consumers are here by construction rather than by coincidence: a `Thash`
bucket **is** a chain, so `Llist` and `Thash` use the same `Reaches` and the
same frame lemmas, with different field names.

## The one design decision

`Reaches m nx h qs` is an **inductive** predicate: following `nx` from the
head value `h` visits exactly the rows `qs`, in order, and ends at `NULL`.

Finiteness, acyclicity and `NULL`-termination are therefore *not clauses*.
They are consequences of inhabitation: a cyclic structure admits no finite
derivation, so no `qs` exists for it at all. That is sharper than carrying
"there is no cycle" as an invariant clause, because nothing has to maintain
it — and it is why `Reaches.nodup` below is a theorem rather than a fifth
field of a structure.

What *is* carried, because none of it follows:

- `Backlinked` — `prev` is the inverse of `nx` along the chain. `Thash` does
  not use it; `Llist` does, and it is what makes `Remove` O(1).
- `Flagged` — the membership flag marks exactly the chain's rows. Both
  templates carry one, for the same reason: `amc` marks not-in-list with
  `($Cpptype*)-1`, which the subset makes inexpressible (`docs/DIVERGENCE.md`
  §1.2, §2.4).
- `Counted` — the stored count is the chain's length.
- `RowsDisjoint` — distinct rows are distinct objects. This is what an
  allocator guarantees (`Spec/Pool.lean`'s `alloc_frame`), and here it is a
  hypothesis, because a chain does not allocate.

## Frame

Every clause has a frame lemma of the same shape: it survives any change to
the store that agrees with the old one on the paths the clause mentions. The
agreement itself comes from `Store.readPath_writePath_disjoint` in the
template, which knows which paths its writes touched. Keeping the two apart is
what lets one `Reaches.frame` serve a list insert and a bucket unlink.
-/

namespace CSubset

/-- A field of the row a pointer names. -/
def fldPath (q : Path) (x : Ident) : Path := ⟨q.root, q.steps ++ [.fld x]⟩

/-! ## Path disjointness

Rows that do not overlap have fields that do not overlap, whatever the field
names — which is the step from "these are different objects" to "this write
cannot be seen through that pointer". -/

theorem isPrefixOf_append_false {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ (as bs : List α) (x y : α),
      as.isPrefixOf bs = false → bs.isPrefixOf as = false →
      (as ++ [x]).isPrefixOf (bs ++ [y]) = false
  | [], _, _, _, h, _ => by simp [List.isPrefixOf] at h
  | _ :: _, [], _, _, _, h => by simp [List.isPrefixOf] at h
  | a :: as, b :: bs, x, y, h1, h2 => by
    by_cases hab : a = b
    · subst hab
      simp only [List.cons_append, List.isPrefixOf, beq_self_eq_true,
        Bool.true_and] at h1 h2 ⊢
      exact isPrefixOf_append_false as bs x y h1 h2
    · simp only [List.cons_append, List.isPrefixOf,
        beq_eq_false_iff_ne.mpr hab, Bool.false_and]

/-- **Distinct objects have distinct fields.** -/
theorem fldPath_disjoint {q r : Path} {x y : Ident} (h : q.overlaps r = false) :
    (fldPath q x).overlaps (fldPath r y) = false := by
  simp only [Path.overlaps, fldPath] at h ⊢
  by_cases hroot : q.root = r.root
  · simp only [hroot, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff] at h ⊢
    exact ⟨isPrefixOf_append_false _ _ _ _ h.1 h.2,
      isPrefixOf_append_false _ _ _ _ h.2 h.1⟩
  · simp only [beq_eq_false_iff_ne.mpr hroot, Bool.false_and]

theorem isPrefixOf_append_last {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ (as : List α) (a b : α), a ≠ b → (as ++ [a]).isPrefixOf (as ++ [b]) = false
  | [], a, b, hab => by
    simp only [List.nil_append, List.isPrefixOf, beq_eq_false_iff_ne.mpr hab,
      Bool.false_and]
  | c :: cs, a, b, hab => by
    simpa [List.isPrefixOf] using isPrefixOf_append_last cs a b hab

/-- A row's field does not overlap a *different* field of the same row. -/
theorem fldPath_ne_disjoint {q : Path} {x y : Ident} (h : x ≠ y) :
    (fldPath q x).overlaps (fldPath q y) = false := by
  have hne : PathStep.fld x ≠ PathStep.fld y := by
    intro e; exact h (by injection e)
  simp only [Path.overlaps, fldPath, beq_self_eq_true, Bool.true_and,
    Bool.or_eq_false_iff]
  exact ⟨isPrefixOf_append_last q.steps _ _ hne,
    isPrefixOf_append_last q.steps _ _ (Ne.symm hne)⟩

theorem isPrefixOf_of_append {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ (as bs : List α) (x : α),
      (as ++ [x]).isPrefixOf bs = true → as.isPrefixOf bs = true
  | [], _, _, _ => by simp [List.isPrefixOf]
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, x, h => by
    simp only [List.cons_append, List.isPrefixOf, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, isPrefixOf_of_append as bs x h.2⟩

theorem isPrefixOf_append_cases {α : Type _} [BEq α] [LawfulBEq α] :
    ∀ (bs as : List α) (x : α), bs.isPrefixOf (as ++ [x]) = true →
      bs.isPrefixOf as = true ∨ as.isPrefixOf bs = true
  | [], _, _, _ => Or.inl (by simp [List.isPrefixOf])
  | _ :: _, [], _, h => by
    simp only [List.nil_append, List.isPrefixOf, Bool.and_eq_true] at h
    exact Or.inr (by simp [List.isPrefixOf])
  | b :: bs, a :: as, x, h => by
    simp only [List.cons_append, List.isPrefixOf, Bool.and_eq_true] at h
    rcases isPrefixOf_append_cases bs as x h.2 with h1 | h2
    · exact Or.inl (by simp [List.isPrefixOf, h.1, h1])
    · exact Or.inr (by simp [List.isPrefixOf, eq_of_beq h.1, h2])

theorem overlaps_symm (p q : Path) : p.overlaps q = q.overlaps p := by
  simp only [Path.overlaps]
  by_cases h : p.root = q.root
  · simp [h, Bool.or_comm]
  · simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]

/-- **Extending a path keeps it clear of whatever it was already clear of.**
This is what turns "this row is not the parent's head field" into "no field of
this row is". -/
theorem overlaps_ext {q r : Path} {x : Ident} (h : q.overlaps r = false) :
    (fldPath q x).overlaps r = false := by
  simp only [Path.overlaps, fldPath] at h ⊢
  by_cases hroot : q.root = r.root
  · simp only [hroot, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff] at h ⊢
    refine ⟨?_, ?_⟩
    · cases hp : (q.steps ++ [PathStep.fld x]).isPrefixOf r.steps with
      | false => rfl
      | true => rw [isPrefixOf_of_append _ _ _ hp] at h; exact absurd h.1 (by simp)
    · cases hp : r.steps.isPrefixOf (q.steps ++ [PathStep.fld x]) with
      | false => rfl
      | true =>
        rcases isPrefixOf_append_cases _ _ _ hp with h1 | h2
        · rw [h1] at h; exact absurd h.2 (by simp)
        · rw [h2] at h; exact absurd h.1 (by simp)
  · simp only [beq_eq_false_iff_ne.mpr hroot, Bool.false_and]

/-! ## Reachability -/

/-- Following `nx` from the head value `h` visits exactly `qs`, in order, and
ends at `NULL`. -/
inductive Reaches (m : Mem) (nx : Ident) : Value → List Path → Prop
  | nil : Reaches m nx .null []
  | cons {q : Path} {v : Value} {qs : List Path} :
      readMem m (fldPath q nx) = some v → Reaches m nx v qs →
      Reaches m nx (.ptr q) (q :: qs)

/-- The head value is determined by the chain, and vice versa. -/
def headOf : List Path → Value
  | []     => .null
  | q :: _ => .ptr q

theorem Reaches.head_eq {m : Mem} {nx : Ident} {h : Value} {qs : List Path}
    (hr : Reaches m nx h qs) : h = headOf qs := by
  cases hr <;> rfl

/-- **The chain is a function of the store.** `nx` is a field, so following it
is deterministic; this is what makes `qs` an honest stand-in for the carrier
the array table had. -/
theorem Reaches.det {m : Mem} {nx : Ident} {h : Value} {qs : List Path}
    (h1 : Reaches m nx h qs) :
    ∀ {qs' : List Path}, Reaches m nx h qs' → qs = qs' := by
  induction h1 with
  | nil => intro qs' h2; cases h2; rfl
  | cons hq _ ih =>
    intro qs' h2
    cases h2 with
    | cons hq' hc' =>
      cases Option.some.inj (hq.symm.trans hq')
      rw [ih hc']

/-- Every row on a chain heads a sub-chain, no longer than the whole. -/
theorem Reaches.mem_sub {m : Mem} {nx : Ident} :
    ∀ {h : Value} {qs : List Path}, Reaches m nx h qs → ∀ q ∈ qs,
      ∃ rest, Reaches m nx (.ptr q) (q :: rest)
        ∧ (q :: rest).length ≤ qs.length := by
  intro h qs hr
  induction hr with
  | nil => intro q hq; exact absurd hq (by simp)
  | @cons q0 v qs0 hq hc ih =>
    intro q hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact ⟨qs0, .cons hq hc, Nat.le_refl _⟩
    · obtain ⟨rest, hrest, hlen⟩ := ih q hmem'
      refine ⟨rest, hrest, ?_⟩
      simp only [List.length_cons] at hlen ⊢
      omega

/-- **No row appears twice.** A repeat would make the chain a proper suffix of
itself, and `det` says there is only one chain from a given row. -/
theorem Reaches.nodup {m : Mem} {nx : Ident} :
    ∀ {h : Value} {qs : List Path}, Reaches m nx h qs →
      qs.Pairwise (· ≠ ·) := by
  intro h qs hr
  induction hr with
  | nil => exact List.Pairwise.nil
  | @cons q v qs0 hq hc ih =>
    refine List.pairwise_cons.mpr ⟨?_, ih⟩
    intro r hr' hqr
    obtain ⟨rest, hrest, hlen⟩ := hc.mem_sub r hr'
    rw [← hqr] at hrest hlen
    have hdet := (Reaches.cons hq hc).det hrest
    simp only [List.cons.injEq, true_and] at hdet
    rw [← hdet] at hlen
    simp only [List.length_cons] at hlen
    omega

/-- **Frame.** The chain survives any change that leaves its link fields
alone. -/
theorem Reaches.frame {m m' : Mem} {nx : Ident} :
    ∀ {h : Value} {qs : List Path}, Reaches m nx h qs →
      (∀ q ∈ qs, readMem m' (fldPath q nx) = readMem m (fldPath q nx)) →
      Reaches m' nx h qs := by
  intro h qs hr
  induction hr with
  | nil => intro _; exact .nil
  | @cons q v qs0 hq hc ih =>
    intro hag
    exact .cons (by rw [hag q (by simp)]; exact hq)
      (ih (fun r hr' => hag r (List.mem_cons_of_mem _ hr')))

/-- The link field of every row on a chain is readable — which is what makes
a walk over the chain trap-free. -/
theorem Reaches.readable {m : Mem} {nx : Ident} :
    ∀ {h : Value} {qs : List Path}, Reaches m nx h qs → ∀ q ∈ qs,
      (readMem m (fldPath q nx)).isSome = true := by
  intro h qs hr
  induction hr with
  | nil => intro q hq; exact absurd hq (by simp)
  | @cons q0 v qs0 hq hc ih =>
    intro q hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [hq]; rfl
    · exact ih q hmem'

theorem headOf_append_cons (pre : List Path) (a : Path) (l1 l2 : List Path) :
    headOf (pre ++ a :: l1) = headOf (pre ++ a :: l2) := by
  cases pre <;> rfl

/-- **Dropping the head.** What `Remove` does when the row it unlinks is the
first one. -/
theorem Reaches.tail {m m' : Mem} {nx : Ident} {q : Path} {qs : List Path}
    (hr : Reaches m nx (.ptr q) (q :: qs))
    (hag : ∀ r ∈ qs, readMem m' (fldPath r nx) = readMem m (fldPath r nx)) :
    Reaches m' nx (headOf qs) qs := by
  cases hr with
  | cons _ hc => exact (hc.head_eq ▸ hc).frame hag

/-- **Splicing a row out.** The predecessor's link now names the successor,
and nothing else on the chain moved. This is the whole content of an O(1)
unlink, and it is where the doubly-linked flavour pays for its extra field. -/
theorem Reaches.splice {m m' : Mem} {nx : Ident} :
    ∀ (pre : List Path) (h : Value) (pp q : Path) (post : List Path),
      Reaches m nx h (pre ++ pp :: q :: post) →
      (∀ r ∈ pre, readMem m' (fldPath r nx) = readMem m (fldPath r nx)) →
      readMem m' (fldPath pp nx) = some (headOf post) →
      (∀ r ∈ post, readMem m' (fldPath r nx) = readMem m (fldPath r nx)) →
      Reaches m' nx h (pre ++ pp :: post)
  | [], _, pp, q, post, hr, _, hpp, hpost => by
    cases hr with
    | cons _ hc =>
      exact .cons hpp (Reaches.tail (hc.head_eq ▸ hc) hpost)
  | a :: pre, _, pp, q, post, hr, hpre, hpp, hpost => by
    cases hr with
    | cons hq hc =>
      refine .cons (?_ : readMem m' (fldPath a nx)
        = some (headOf (pre ++ pp :: post))) ?_
      · rw [hpre a (by simp), hq, hc.head_eq]
        exact congrArg some (headOf_append_cons pre pp (q :: post) post)
      · have he : headOf (pre ++ pp :: q :: post) = headOf (pre ++ pp :: post) :=
          headOf_append_cons pre pp (q :: post) post
        have hc0 : Reaches m nx (headOf (pre ++ pp :: post))
            (pre ++ pp :: q :: post) := by rw [← he]; exact hc.head_eq ▸ hc
        exact Reaches.splice pre _ pp q post hc0
          (fun r hr' => hpre r (List.mem_cons_of_mem _ hr')) hpp hpost

/-- A row's link names whatever follows it on the chain. -/
theorem Reaches.next_of_mem {m : Mem} {nx : Ident} :
    ∀ (pre : List Path) (h : Value) (q : Path) (post : List Path),
      Reaches m nx h (pre ++ q :: post) →
      readMem m (fldPath q nx) = some (headOf post)
  | [], _, q, post, hr => by
    cases hr with | cons hq hc => rw [hq, hc.head_eq]
  | a :: pre, _, q, post, hr => by
    cases hr with
    | cons _ hc => exact Reaches.next_of_mem pre _ q post (hc.head_eq ▸ hc)

/-! ## The clauses a chain does not imply -/

/-- `pv` is the inverse of the link along the chain: each row's `pv` points at
its predecessor, and the head's is `back` (`NULL`, for a list rooted in a head
pointer). -/
def Backlinked (m : Mem) (pv : Ident) : List Path → Value → Prop
  | [],      _    => True
  | q :: qs, back => readMem m (fldPath q pv) = some back
                     ∧ Backlinked m pv qs (.ptr q)

theorem Backlinked.frame {m m' : Mem} {pv : Ident} :
    ∀ (qs : List Path) (back : Value), Backlinked m pv qs back →
      (∀ q ∈ qs, readMem m' (fldPath q pv) = readMem m (fldPath q pv)) →
      Backlinked m' pv qs back
  | [], _, _, _ => trivial
  | q :: qs, back, h, hag =>
    ⟨by rw [hag q (by simp)]; exact h.1,
     Backlinked.frame qs (.ptr q) h.2 (fun r hr => hag r (List.mem_cons_of_mem _ hr))⟩

/-- The membership flag marks exactly the chain's rows, **among the live
rows**.

The universe `rows` is not decoration. The backward direction — a row whose
flag reads `false` is not on the chain — is what makes `Insert`'s and
`Remove`'s guards sound, and it cannot be maintained over *all* paths: a write
to one row's flag is invisible only at paths that do not overlap it, and an
arbitrary path may well be a prefix of a row. Restricting to a pairwise
disjoint universe is the honest form, and it is what an allocator hands out —
`Spec/Pool.lean`'s `alloc_frame` is the statement that a pool's live records
stay put and stay disjoint. -/
def Flagged (m : Mem) (fl : Ident) (rows qs : List Path) : Prop :=
  ∀ q ∈ rows, (readMem m (fldPath q fl) = some (.bool true) ↔ q ∈ qs)

theorem Flagged.frame {m m' : Mem} {fl : Ident} {rows qs : List Path}
    (h : Flagged m fl rows qs)
    (hag : ∀ q ∈ rows, readMem m' (fldPath q fl) = readMem m (fldPath q fl)) :
    Flagged m' fl rows qs :=
  fun q hq => by rw [hag q hq]; exact h q hq

/-- Setting one row's flag adds exactly that row. -/
theorem Flagged.cons {m m' : Mem} {fl : Ident} {rows qs : List Path} {q : Path}
    (h : Flagged m fl rows qs) (hq : q ∈ rows)
    (hnew : readMem m' (fldPath q fl) = some (.bool true))
    (hag : ∀ r ∈ rows, r ≠ q →
      readMem m' (fldPath r fl) = readMem m (fldPath r fl)) :
    Flagged m' fl rows (q :: qs) := by
  intro r hr
  by_cases hrq : r = q
  · subst hrq; simp [hnew]
  · rw [hag r hr hrq, h r hr]
    simp [hrq]

/-- Clearing one row's flag removes exactly that row. -/
theorem Flagged.erase {m m' : Mem} {fl : Ident} {rows qs : List Path} {q : Path}
    (h : Flagged m fl rows qs) (hq : q ∈ rows)
    (hnd : qs.Pairwise (· ≠ ·))
    (hnew : readMem m' (fldPath q fl) = some (.bool false))
    (hag : ∀ r ∈ rows, r ≠ q →
      readMem m' (fldPath r fl) = readMem m (fldPath r fl)) :
    Flagged m' fl rows (qs.erase q) := by
  intro r hr
  by_cases hrq : r = q
  · subst hrq
    rw [hnew]
    constructor
    · intro e; exact absurd e (by simp)
    · intro hmem; exact absurd hmem (List.Nodup.not_mem_erase hnd)
  · rw [hag r hr hrq, h r hr]
    constructor
    · intro hmem
      exact (List.mem_erase_of_ne hrq).mpr hmem
    · intro hmem
      exact List.mem_of_mem_erase hmem

/-- The stored count is the chain's length. -/
def Counted (m : Mem) (cp : Path) (qs : List Path) : Prop :=
  readMem m cp = some (.u32 (UInt32.ofNat qs.length))

/-- Distinct rows are distinct objects.

A chain does not allocate, so this cannot be derived here; it is what an
allocator guarantees, and `Spec/Pool.lean`'s `alloc_frame` is the statement
that a pool does. -/
def RowsDisjoint (qs : List Path) : Prop :=
  ∀ q ∈ qs, ∀ r ∈ qs, q ≠ r → q.overlaps r = false

/-- **Where a row sits on the chain**, read off its back-pointer: it is either
the head, or its `prev` names the predecessor the chain splits around. This is
what lets `Remove` do surgery without walking. -/
theorem Backlinked.split {m : Mem} {pv : Ident} :
    ∀ (qs : List Path) (back : Value) (q : Path), Backlinked m pv qs back →
      q ∈ qs →
      (readMem m (fldPath q pv) = some back ∧ ∃ post, qs = q :: post)
      ∨ (∃ pp pre post, qs = pre ++ pp :: q :: post
           ∧ readMem m (fldPath q pv) = some (.ptr pp))
  | [], _, _, _, hm => absurd hm (by simp)
  | q0 :: qs0, back, q, hb, hm => by
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact Or.inl ⟨hb.1, ⟨qs0, rfl⟩⟩
    · rcases Backlinked.split qs0 (.ptr q0) q hb.2 hm' with ⟨h1, post, h2⟩ | ⟨pp, pre, post, h1, h2⟩
      · exact Or.inr ⟨q0, [], post, by simp [h2], h1⟩
      · exact Or.inr ⟨pp, q0 :: pre, post, by simp [h1], h2⟩

/-- The back-pointer a chain hung on the far side of `l` would carry: the last
row of `l`, or `back` if `l` is empty. Written so that the recursive step
threads the new back-pointer, which is exactly how `Backlinked` recurses. -/
def lastOr : List Path → Value → Value
  | [],      back => back
  | q :: qs, _    => lastOr qs (.ptr q)

theorem lastOr_append_singleton :
    ∀ (l : List Path) (a : Path) (back : Value), lastOr (l ++ [a]) back = .ptr a
  | [], _, _ => rfl
  | b :: l, a, _ => lastOr_append_singleton l a (.ptr b)

/-- **Splitting a back-linked chain.** Both halves are back-linked, the second
from the first's last row. -/
theorem Backlinked.of_append {m : Mem} {pv : Ident} :
    ∀ (l1 : List Path) (back : Value) (l2 : List Path),
      Backlinked m pv (l1 ++ l2) back →
      Backlinked m pv l1 back ∧ Backlinked m pv l2 (lastOr l1 back)
  | [], _, _, h => ⟨trivial, h⟩
  | a :: l1, _, l2, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h3, h4⟩ := Backlinked.of_append l1 (.ptr a) l2 h2
    exact ⟨⟨h1, h3⟩, h4⟩

/-- And putting them back together — which is what an unlink does, with a
shorter second half. -/
theorem Backlinked.append {m : Mem} {pv : Ident} :
    ∀ (l1 : List Path) (back : Value) (l2 : List Path),
      Backlinked m pv l1 back → Backlinked m pv l2 (lastOr l1 back) →
      Backlinked m pv (l1 ++ l2) back
  | [], _, _, _, h2 => h2
  | a :: l1, _, l2, h1, h2 =>
    ⟨h1.1, Backlinked.append l1 (.ptr a) l2 h1.2 h2⟩

/-! ## Erasing a row from the chain -/

theorem erase_cons_self (q : Path) (post : List Path) :
    (q :: post).erase q = post := by simp

theorem erase_append_cons_cons :
    ∀ (pre : List Path) (pp q : Path) (post : List Path),
      q ∉ pre → q ≠ pp → (pre ++ pp :: q :: post).erase q = pre ++ pp :: post
  | [], pp, q, post, _, hqp => by
    simp only [List.nil_append, List.erase_cons]
    rw [if_neg (by simp [Ne.symm hqp])]
    simp
  | a :: pre, pp, q, post, hq, hqp => by
    have hqa : ¬ (a = q) := fun e => hq (by rw [e]; simp)
    simp only [List.cons_append, List.erase_cons]
    rw [if_neg (by simp [hqa])]
    rw [erase_append_cons_cons pre pp q post (fun hm => hq (List.mem_cons_of_mem _ hm)) hqp]

theorem RowsDisjoint.sublist {qs : List Path} {q : Path}
    (h : RowsDisjoint (q :: qs)) : RowsDisjoint qs :=
  fun a ha b hb hab =>
    h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab

end CSubset

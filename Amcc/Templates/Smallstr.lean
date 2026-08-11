import Amcc.Dmmeta

/-!
# AMCC — `Smallstr`, and why only one of its three shapes is safe to emit

A `Smallstr` field is a fixed-capacity string stored inline in its parent. Its
shape lives in a `dmmeta.smallstr` record, joined onto the field by
`Dmmeta.Db.attr?`, and `Dmmeta.Strtype` is the discipline: `rpascal`,
`leftpad`, `rightpad`.

**All three abstraction functions are stated here.** Two of them are not
implemented, and stating them is the point: the reason they are absent is a
property of the abstraction, and a property is something to write down and
prove, not to describe in a comment. `rightpad_ambiguous` and
`leftpad_ambiguous` below are the two witnesses.

## What `amc` actually emits

From `cpp/amc/smallstr.cpp`, transcribed rather than guessed:

```c
// leftpad, rightpad
u8 ch[N];
// rpascal
u8 ch[N+1];
u8 n_ch;
```

So `rpascal`'s count is **out of band**, in a byte of its own, and the array is
one longer than the capacity. `_N` reads `n_ch` directly; for the padded
shapes it *scans* — `rightpad` walks back from the end while the byte is the
pad, `leftpad` walks forward from the start. That scan is the whole difference,
and it is where the ambiguity comes from.

## The three abstractions, and the one that is injective

An abstraction function takes a representation to the string it denotes. An
*encoder* goes the other way. What a read-back law needs is
`abs (encode s) = s`, and that is exactly what fails for the padded shapes:

- **`rpascal`** — `abs (ch, n) = ch.take n`, and `encode` writes the bytes and
  sets the count. `absRpascal_encode` proves the round trip for every string
  within the capacity, with no side condition. The count is stored, so nothing
  has to be recovered by scanning.
- **`rightpad`** — `abs` drops trailing pad bytes. A string that *ends* in the
  pad character encodes to the same bytes as the string without it, so `abs`
  cannot tell them apart. `rightpad_ambiguous` is that pair.
- **`leftpad`** — the mirror image, for a string that *begins* with the pad.
  `leftpad_ambiguous` is that pair.

`docs/DIVERGENCE.md` §3.7 records the research behind this: `dmmeta.smallstr`'s
`strict` flag does **not** forbid the ambiguous values. Every use of it in
`CheckSmallstr` guards a naming-convention check. So the ambiguity is `amc`'s
by design, and a read-back law for the padded shapes needs a side condition on
the value that AMCC would have to invent. §3.7 gives two routes to discharging
that; picking between them is not this module's business.

## Why nothing is generated yet

`amc` emits `u8`, and `CSubset.ScalarTy` is `u32 | u64 | bool`. The C subset
has no eight-bit scalar, so `Dmmeta.fieldTy` cannot lower a `Smallstr` field
and `Ssim.supported` does not list it. That is a subset change, not a design
question — `docs/GOALS.md`'s standing rule says the subset changes when it
cannot express what `amc` generates — and it is recorded as owed in
`docs/DIVERGENCE.md` §3.8 and `docs/PLAN.md`.

Everything below is therefore about the *representation*, stated over Lean
byte lists, and is independent of how the C subset eventually spells them.
-/

namespace Templates
namespace Smallstr

open Dmmeta

/-- The abstract value a `Smallstr` field denotes: its bytes, in order, with
no padding and no count. -/
abbrev Str := List UInt8

/-! ## `rpascal` — the count is stored

`u8 ch[N+1]; u8 n_ch;`. The representation is the pair. -/

/-- **The abstraction.** The first `n` bytes; the rest of the array is dead. -/
def absRpascal (ch : Str) (n : Nat) : Str := ch.take n

/-- **The representation invariant.** The array is `N + 1` long, as `amc`
sizes it, and the count is within the capacity — which is what `Add` maintains
(`if (n_ch < N)`) and what makes the subscript in range. -/
structure RpascalInv (N : Nat) (ch : Str) (n : Nat) : Prop where
  size  : ch.length = N + 1
  count : n ≤ N

/-- **The encoder.** Bytes into the array, count into `n_ch`, the tail zeroed —
which is what `Init` followed by `SetStrptr` leaves behind. -/
def encodeRpascal (N : Nat) (s : Str) : Str × Nat :=
  (s ++ List.replicate (N + 1 - s.length) 0, s.length)

/-- An encoded string satisfies the invariant.

checked by: `lake build` -/
theorem encodeRpascal_inv {N : Nat} {s : Str} (h : s.length ≤ N) :
    RpascalInv N (encodeRpascal N s).1 (encodeRpascal N s).2 := by
  refine ⟨?_, h⟩
  simp only [encodeRpascal, List.length_append, List.length_replicate]
  omega

/-- **The read-back law, with no side condition.** Every string within the
capacity comes back exactly. This is what `rightpad` and `leftpad` cannot have.

checked by: `lake build` -/
theorem absRpascal_encode {N : Nat} (s : Str) :
    absRpascal (encodeRpascal N s).1 (encodeRpascal N s).2 = s := by
  simp [absRpascal, encodeRpascal]

/-- **The encoding is injective**, which is the same fact read the other way:
two strings with the same representation are the same string. Nothing about
the capacity is needed — the read-back law already carries it.

checked by: `lake build` -/
theorem encodeRpascal_injective {N : Nat} {s t : Str}
    (h : encodeRpascal N s = encodeRpascal N t) : s = t := by
  have hs := absRpascal_encode (N := N) s
  have ht := absRpascal_encode (N := N) t
  rw [h] at hs
  exact hs.symm.trans ht

/-! ## `rightpad` — the count is recovered by scanning back -/

/-- Drop trailing `pad` bytes. `amc`'s `_N` computes the same length with a
`while (ret>0 && ch[ret-1]==pad) ret--`. -/
def dropTrailing (pad : UInt8) : Str → Str
  | []      => []
  | b :: bs =>
    match dropTrailing pad bs with
    | []      => if b == pad then [] else [b]
    | c :: cs => b :: c :: cs

/-- **The abstraction.** -/
def absRightpad (pad : UInt8) (ch : Str) : Str := dropTrailing pad ch

/-- **The encoder**: the bytes, then pad to the capacity. -/
def encodeRightpad (pad : UInt8) (N : Nat) (s : Str) : Str :=
  s ++ List.replicate (N - s.length) pad

/-- **The witness.** Two *different* strings, both within the capacity, with
the *same* representation — so `absRightpad` has no left inverse and the
read-back law is false as stated. `"a "` and `"a"` at capacity 2, padding with
a space.

This is not a defect in the model. `amc` generates exactly this, and
`dmmeta.smallstr.strict` does not forbid it — see `docs/DIVERGENCE.md` §3.7.

checked by: `lake build` -/
theorem rightpad_ambiguous :
    let pad : UInt8 := 32
    let s : Str := [97, 32]
    let t : Str := [97]
    s ≠ t
    ∧ s.length ≤ 2 ∧ t.length ≤ 2
    ∧ encodeRightpad pad 2 s = encodeRightpad pad 2 t := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- And the read-back law fails on the longer of the two: what comes back is
the *shorter* string.

checked by: `lake build` -/
theorem absRightpad_encode_fails :
    absRightpad 32 (encodeRightpad 32 2 [97, 32]) ≠ [97, 32] := by decide

/-! ## `leftpad` — the mirror image -/

/-- Drop leading `pad` bytes. `amc`'s `_N` walks forward and subtracts. -/
def dropLeading (pad : UInt8) : Str → Str
  | []      => []
  | b :: bs => if b == pad then dropLeading pad bs else b :: bs

/-- **The abstraction.** -/
def absLeftpad (pad : UInt8) (ch : Str) : Str := dropLeading pad ch

/-- **The encoder**: pad to the capacity, then the bytes. -/
def encodeLeftpad (pad : UInt8) (N : Nat) (s : Str) : Str :=
  List.replicate (N - s.length) pad ++ s

/-- **The witness**, with `amc`'s own `pad:"'0'"`: the numeric strings `"01"`
and `"1"` at capacity 2 are the same bytes.

checked by: `lake build` -/
theorem leftpad_ambiguous :
    let pad : UInt8 := 48
    let s : Str := [48, 49]
    let t : Str := [49]
    s ≠ t
    ∧ s.length ≤ 2 ∧ t.length ≤ 2
    ∧ encodeLeftpad pad 2 s = encodeLeftpad pad 2 t := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- checked by: `lake build` -/
theorem absLeftpad_encode_fails :
    absLeftpad 48 (encodeLeftpad 48 2 [48, 49]) ≠ [48, 49] := by decide

/-! ## The abstraction, by `Strtype`

One function over the vocabulary, so the three are visible together and the
two that are owed cannot be quietly forgotten. The padded arms are *stated*,
not stubbed: they compute the same thing `amc`'s `_N` computes. What is owed
is their read-back law, which the witnesses above show is false without a
side condition. -/

/-- The representation of a `Smallstr` field: the array, and the count byte
that only `rpascal` has. -/
structure Rep where
  ch : Str
  /-- `n_<field>`, present only for `rpascal`. -/
  n  : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **The abstraction, for every `strtype`.** -/
def abs (st : Strtype) (pad : UInt8) (r : Rep) : Str :=
  match st with
  | .rpascal  => absRpascal r.ch r.n
  | .rightpad => absRightpad pad r.ch
  | .leftpad  => absLeftpad pad r.ch

/-- **Which of the three has a read-back law today.** A single Boolean, so a
future arm cannot be added without deciding the question — and so
`docs/DIVERGENCE.md` §3.7's claim is a checked fact rather than prose.

checked by: `lake build` -/
def hasReadBack : Strtype → Bool
  | .rpascal  => true
  | .rightpad => false
  | .leftpad  => false

/-- checked by: `lake build` -/
example : Strtype.all.filter hasReadBack = [.rpascal] := rfl

/-- The `rpascal` arm of `abs` is the one the read-back law is about.

checked by: `lake build` -/
theorem abs_rpascal_encode {N : Nat} (pad : UInt8) (s : Str) :
    abs .rpascal pad ⟨(encodeRpascal N s).1, (encodeRpascal N s).2⟩ = s :=
  absRpascal_encode s

end Smallstr
end Templates

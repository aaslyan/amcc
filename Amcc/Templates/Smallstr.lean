import Amcc.Dmmeta
import Amcc.Templates.Layout
import Amcc.CSubset.Calls

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

## What is generated, and what is not

`u8` is in the C subset now, so `Dmmeta.fieldTy` lowers the array and this
module emits four of `amc`'s functions for an `rpascal` field:

```c
void  C_f_Init(C *row);            // row->n_f = 0
uint8_t C_f_N(C *row);             // return row->n_f
uint32_t C_f_Max(void);            // return N
void  C_f_Add(C *row, uint8_t c);  // if (n < N) { f[n] = c; n = n + 1; }
```

`Getary` and `SetStrptr` are **not** emitted: their signatures are
`algo::aryptr<char>` and `algo::strptr`, and the C subset has no aggregate
value type and no way to pass one. `docs/DIVERGENCE.md` §3.9.

Only `rpascal` is emitted at all. `leftpad` and `rightpad` lower to their
array — a schema declaring one gets the storage — and get no operations,
because their read-back law is false without a side condition AMCC would have
to invent (§3.7).

The abstraction functions below are stated over Lean byte lists and are
independent of how the C subset spells them; `Templates/SmallstrCorrect.lean`
is where the generated `Add` is tied to `absRpascal`.
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

/-! ## The generated code

Per-field, like `Upptr`: a smallstr has no storage of its own beyond the array
the layout pass already emits, plus one count byte this template adds. -/

open CSubset

/-- The C names, `amc`'s: `<ctype>_<field>_<Op>` for the functions, and
`n_<field>` for the count byte — the one *prefixed* generated name in AMCC,
which is why `Dmmeta.genPrefixes` exists. -/
structure Names where
  /-- The count byte, on the owning struct. -/
  count : CSubset.Ident
  init  : CSubset.Ident
  size  : CSubset.Ident
  max   : CSubset.Ident
  add   : CSubset.Ident
  deriving Repr, Inhabited, DecidableEq

def names (owner fld : CSubset.Ident) : Names where
  count := "n_" ++ fld
  init  := owner ++ "_" ++ fld ++ "_Init"
  size  := owner ++ "_" ++ fld ++ "_N"
  max   := owner ++ "_" ++ fld ++ "_Max"
  add   := owner ++ "_" ++ fld ++ "_Add"

def parRow : CSubset.Ident := "row"
def parCh  : CSubset.Ident := "c"
/-- The `u32` copy of the count. A subscript must be a `u32` local
(`Wf.indexOk`), and the count is a `u8` field, so the cast is not decoration. -/
def tmpI   : CSubset.Ident := "_i"

/-- `row-><x>` -/
def rowFld (x : CSubset.Ident) : LVal := .fld (.deref parRow) x

/-- The count byte the template adds to the owning struct. -/
def ownerFields (nm : Names) : List (CSubset.Ident × Ty) :=
  [(nm.count, .scalar .u8)]

/-- ```c
void C_f_Init(C *row) { row->n_f = 0u; }
``` -/
def initDef (nm : Names) (owner : CSubset.Ident) : FunDef where
  name   := nm.init
  params := [(parRow, .ptr (.strct owner))]
  ret    := none
  locals := []
  body   := .assign (rowFld nm.count) (.lit (.u8 0))

/-- ```c
uint8_t C_f_N(C *row) { return row->n_f; }
``` -/
def sizeDef (nm : Names) (owner : CSubset.Ident) : FunDef where
  name   := nm.size
  params := [(parRow, .ptr (.strct owner))]
  ret    := some (.scalar .u8)
  locals := []
  body   := .ret (some (.rd (rowFld nm.count)))

/-- ```c
uint32_t C_f_Max(void) { return N; }
```
`amc` emits it as an `enum` constant inside the struct; a function is the
subset's only way to expose a constant, and it is what the other templates'
`_N` already looks like. -/
def maxDef (nm : Names) (n : Nat) : FunDef where
  name   := nm.max
  params := []
  ret    := some (.scalar .u32)
  locals := []
  body   := .ret (some (.lit (.u32 (UInt32.ofNat n))))

/-- ```c
void C_f_Add(C *row, uint8_t c) {
  uint32_t _i = 0u;
  _i = (uint32_t)row->n_f;
  if ((_i < N)) {
    row->f[_i] = c;
    row->n_f = (uint8_t)(_i + 1u);
  }
}
```
`amc`'s `tfunc_Smallstr_Add`, with the count copied into a `u32` local because
a subscript must be one, and with the post-increment split into an assignment
because the subset's expressions are pure.

The guard is `< N`, not `< N + 1`: the array is `N + 1` long and the last
element is the dead byte `amc` also never writes. So the subscript is in range
with a whole element to spare, which is what makes `noTrapAdd` hold without a
precondition on the count. -/
def addDef (nm : Names) (owner fld : CSubset.Ident) (n : Nat) : FunDef where
  name   := nm.add
  params := [(parRow, .ptr (.strct owner)), (parCh, .scalar .u8)]
  ret    := none
  locals := [LocalDef.zeroed tmpI .u32]
  body   := .seq
    (.assign (.var tmpI) (.cast .u32 (.rd (rowFld nm.count))))
    (.cond (.bin .lt (.rd (.var tmpI)) (.lit (.u32 (UInt32.ofNat n))))
      (.seq
        (.assign (.idx (rowFld fld) (.var tmpI)) (.rd (.var parCh)))
        (.assign (rowFld nm.count)
          (.cast .u8 (.bin .add (.rd (.var tmpI)) (.lit (.u32 1))))))
      .skip)

/-- The four operations for one `rpascal` field. -/
def defsFor (nm : Names) (owner fld : CSubset.Ident) (n : Nat) : List FunDef :=
  [ initDef nm owner, sizeDef nm owner, maxDef nm n, addDef nm owner fld n ]

/-! ## Assembling a program -/

/-- Every `rpascal` `Smallstr` field in the schema, with its declared length.

The padded shapes are deliberately absent: they lower to their array and get
no operations. `hasReadBack` is the single place that decision is recorded,
and this filter is the only place it is spent. -/
def strFields (d : Dmmeta.Db) : List (Dmmeta.Ident × Dmmeta.Field × Nat) :=
  d.ctypes.flatMap (fun c =>
    c.fields.filterMap (fun f =>
      if f.reftype == .Smallstr then
        match d.withBuiltins.smallstr? c.name f.name with
        | some (n, .rpascal, _, _) => some (c.name, f, n)
        | _                        => none
      else none))

/-- **The generator.** The layout, each `rpascal` field's owning struct
extended with its count byte, and four operations per field. -/
def genSmallstr (d : Dmmeta.Db) : Program :=
  { structs := (strFields d).foldl
      (fun ss cf =>
        Layout.addFields (Dmmeta.mangle cf.1)
          (ownerFields (names (Dmmeta.mangle cf.1) (Dmmeta.mangle cf.2.1.name)))
          ss)
      (Dmmeta.genStructs d)
  , globals := Dmmeta.genGlobals d
  , funs    := (strFields d).flatMap (fun cf =>
      defsFor (names (Dmmeta.mangle cf.1) (Dmmeta.mangle cf.2.1.name))
        (Dmmeta.mangle cf.1) (Dmmeta.mangle cf.2.1.name) cf.2.2) }

/-! ## Examples

checked by: `lake build` -/

namespace Examples

open Dmmeta

/-- A record with a sixteen-byte `rpascal` name. -/
def strDb : Db where
  ctypes :=
    [ { name   := "name_row"
      , fields := [ { name := "id", arg := "u64", reftype := .Pkey }
                  , { name := "ch", arg := "char", reftype := .Smallstr } ] } ]
  attrs := [{ ctype := "name_row", field := "ch"
            , data := .smallstr 16 .rpascal "'0'" true }]

/-- checked by: `lake build` -/
example : Dmmeta.check strDb = [] := rfl

/-- The array is `N + 1` and the count byte follows it.

checked by: `lake build` -/
example : (genSmallstr strDb).structs.map
    (fun sd => (sd.name, sd.fields)) =
    [("name_row", [ ("id", Ty.scalar .u64)
                  , ("ch", Ty.arr (.scalar .u8) 17)
                  , ("n_ch", Ty.scalar .u8) ])] := rfl

/-- Four functions, `amc`'s names.

checked by: `lake build` -/
example : (genSmallstr strDb).funs.map FunDef.name =
    ["name_row_ch_Init", "name_row_ch_N", "name_row_ch_Max",
     "name_row_ch_Add"] := rfl

/-- And the generated program is accepted by the C subset's checker.

checked by: `lake build` -/
example : CSubset.Wf.check (genSmallstr strDb) = [] := rfl

/-- A padded field lowers to its array and gets no operations — the
`hasReadBack` decision, spent.

checked by: `lake build` -/
def padDb : Db :=
  { strDb with attrs := [{ ctype := "name_row", field := "ch"
                         , data := .smallstr 16 .rightpad "' '" false }] }

/-- checked by: `lake build` -/
example : Dmmeta.check padDb = [] := rfl

/-- checked by: `lake build` -/
example : (genSmallstr padDb).funs = [] := rfl

/-- checked by: `lake build` -/
example : (genSmallstr padDb).structs.map (fun sd => (sd.name, sd.fields)) =
    [("name_row", [("id", Ty.scalar .u64), ("ch", Ty.arr (.scalar .u8) 16)])] := rfl

/-- checked by: `lake build` -/
example : CSubset.Wf.check (genSmallstr padDb) = [] := rfl

/-- A field named `n_ch` alongside `ch` is what `genPrefixes` catches: the
count byte would collide with it.

checked by: `lake build` -/
example : Dmmeta.check { strDb with
      ctypes := [{ name := "name_row"
                 , fields := [ { name := "ch", arg := "char", reftype := .Smallstr }
                             , { name := "n_ch", arg := "u8", reftype := .Val } ] }] }
    = ["name_row.n_ch: collides with a field a template generates"] := rfl

end Examples

end Smallstr
end Templates

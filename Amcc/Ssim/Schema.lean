import Amcc.Ssim.Tuple

/-!
# AMCC — ssim tuples into the `Dmmeta` model, and back

`Ssim.Tuple` knows the *format*; this module knows the *records*. It is the
second half of the front end and the place where the standing rule bites:

> **The reader must never run ahead of what the generator can produce.**

`dmmeta` declares thirty-five reftypes. AMCC has templates or a lowering for
eight of them. A reader that accepted the other twenty-seven would parse a
schema, hand it to `Dmmeta.check`, and get a `Db` for which nothing can be
emitted — or worse,
a `Db` whose unsupported fields are silently dropped, so what is generated is
provably correct about a schema the user did not write. `supported` below is
the list, each entry justified by the template or the lowering that consumes
it, and everything else is a named rejection.

## The record types

```
dmmeta.ctype     ctype:<name>                                   comment:""
dmmeta.field     field:<ctype>.<name>  arg:<ctype>  reftype:<R>  comment:""
dmmeta.inlary    field:<ctype>.<name>  min:0  max:<n>           comment:""
dmmeta.smallstr  field:<ctype>.<name>  length:<n>  strtype:<T>  pad:<c>  strict:<Y|N>
amcc.root        ctype:<name>                                   comment:""
```

The two attribute tables — `inlary` and `smallstr` — are read and written by
**one** pair of functions over `Dmmeta.AttrTag`, not one pair each. That is the
join: adding `bitfld`, `charset`, `lenfld`, `substr` or `fconst` is a payload
arm here and a payload arm in `Dmmeta`, and nothing else.

The first four are `amc`'s, key for key (`data/dmmeta/ctype.ssim`,
`field.ssim`, `inlary.ssim`, `smallstr.ssim`). The fourth is not: `amc` designates the database
ctype by the `<ns>.FDb` naming convention inside a namespace declared by
`dmmeta.nsdb`, and AMCC's `Dmmeta.Db` has no namespaces — a schema is a flat
list of ctypes with one of them named as the root. Reusing `dmmeta.nsdb` would
mean reading its `ns:` key as a ctype name, which is a reinterpretation
pretending to be a match. A separate head under our own namespace says what is
happening. Recorded in `docs/DIVERGENCE.md` §3.5.

## Ordering, because the round trip is byte-for-byte

`ofDb` emits the tuple heads in table order — every `dmmeta.ctype`, then every
`dmmeta.field`, then every attribute record in file order, then `amcc.root` —
which is what a concatenation of `amc`'s per-table files looks like. Within a head, schema
declaration order is preserved. `readDb` is insensitive to the interleaving of
heads (it makes two passes, so a field may precede its ctype), so the round
trip pins a *canonical* form rather than the only accepted one.
-/

namespace Ssim

open Dmmeta

/-! ## What may be read

Each entry names the consumer that makes it emittable. Removing a template
should remove its line here, and adding one should add it — the point of the
list being in one place. -/

/-- The reftypes AMCC can act on. `Val`, `Base`, `Pkey`, `Upptr`, `Ptr` and
`Inlary` have a storage lowering (`Dmmeta.fieldTy`); `Thash` and `Llist` have
templates that emit their operations. The remaining twenty-seven of `dmmeta`'s
thirty-five are rejected by name.

`Smallstr` is **modelled** — `Dmmeta.AttrData.smallstr` and the
`dmmeta.smallstr` record round-trip — and still absent here, because
`Dmmeta.fieldTy` cannot lower it: `amc` emits `u8 ch[N+1]; u8 n_ch;` and the C
subset has no eight-bit scalar. `docs/DIVERGENCE.md` §3.8 is the entry, and
the line to add here is one line once `u8` lands. -/
def supported : List Reftype :=
  [.Val, .Base, .Pkey, .Upptr, .Ptr, .Inlary, .Thash, .Llist]

/-- Parse a reftype name, refusing the ones no template can emit. The two
failures are reported differently on purpose: an unknown name is a typo, an
unsupported one is a feature AMCC does not have yet, and a user needs to be
able to tell those apart. -/
def readReftype (s : String) : Except String Reftype :=
  match Reftype.ofName? s with
  | none   => .error s!"unknown reftype {s}"
  | some r =>
    if supported.contains r then .ok r
    else .error s!"reftype {s} is declared by dmmeta but no AMCC template emits it"

/-! ## Reading -/

/-- Split `<ctype>.<field>` at the **last** dot: `amc`'s ctype names are
themselves dotted (`abt.FBuilddir.select` is field `select` of ctype
`abt.FBuilddir`), so the last dot is the one that separates. -/
def splitQual (s : String) : Except String (String × String) :=
  match (splitOnChar '.' s.toList).reverse with
  | []            => .error s!"empty qualified name"
  | [_]           => .error s!"{s}: expected <ctype>.<field>"
  | f :: revOwner =>
    if f.isEmpty then .error s!"{s}: empty field name"
    else .ok (".".intercalate (revOwner.reverse.map String.ofList),
              String.ofList f)

/-- A required attribute, by name. -/
def need (t : Tuple) (k : String) : Except String String :=
  match t.get? k with
  | some v => .ok v
  | none   => .error s!"{t.head}: missing attribute {k}"

def readNat (s : String) : Except String Nat :=
  match digitsToNat? s.toList with
  | some n => .ok n
  | none   => .error s!"{s}: expected a number"

/-- What one pass accumulates. Kept as three lists rather than a partly-built
`Db` so that a field may be read before its ctype — the tuple order in a
concatenated ssim directory is by table, not by dependency. -/
structure Raw where
  ctypes : List Ident := []
  fields : List (Ident × Field) := []
  attrs  : List Dmmeta.Attr := []
  root   : Option Ident := none
  deriving Inhabited

/-- A builtin is not a declarable ctype: `Db.withBuiltins` supplies `u32`,
`u64` and `bool`, so declaring one would duplicate it. Rejecting is what keeps
`ofDb ∘ readDb` the identity — a reader that accepted and dropped them would
print back a shorter file. -/
def builtinNames : List Ident := builtins.map Ctype.name

/-! ### The attribute tables, once

`attrHeads` is the whole registry: a `dmmeta` head, the table it belongs to,
and how to read and write its payload. `readTuple` and `ofDb` consult it
rather than growing an arm per table, which is what makes the next attribute
record a data change instead of a code change. -/

def readBool (s : String) : Except String Bool :=
  if s == "Y" then .ok true
  else if s == "N" then .ok false
  else .error s!"{s}: expected Y or N"

def readStrtype (s : String) : Except String Strtype :=
  match Strtype.ofName? s with
  | some t => .ok t
  | none   => .error s!"unknown strtype {s}"

/-- One attribute table's reader and writer, keyed by its `dmmeta` head. The
`field:` key is shared — it is what the join is on — so only the payload
differs, and only the payload appears here. -/
structure AttrHead where
  head    : String
  tag     : AttrTag
  /-- Payload out of the record's other attributes. -/
  read    : Tuple → Except String Dmmeta.AttrData
  /-- Payload back into them, in `amc`'s key order, `field:` excluded. -/
  write   : Dmmeta.AttrData → List Ssim.Attr

def attrHeads : List AttrHead :=
  [ { head := "dmmeta.inlary", tag := .inlary
    , read := fun t => do .ok (.inlary (← readNat (← need t "max")))
    , write := fun a => match a with
        | .inlary n => [⟨"min", "0"⟩, ⟨"max", toString n⟩, ⟨"comment", ""⟩]
        | _         => [] }
  , { head := "dmmeta.smallstr", tag := .smallstr
    , read := fun t => do
        let length ← readNat (← need t "length")
        let strtype ← readStrtype (← need t "strtype")
        let pad ← need t "pad"
        let strict ← readBool (← need t "strict")
        .ok (.smallstr length strtype pad strict)
    , write := fun a => match a with
        | .smallstr n st pad strict =>
            [ ⟨"length", toString n⟩, ⟨"strtype", st.name⟩, ⟨"pad", pad⟩
            , ⟨"strict", if strict then "Y" else "N"⟩ ]
        | _ => [] } ]

/-- The writer for the table a payload belongs to. Total by construction: the
registry has an entry per `AttrTag`, pinned in `Ssim.Checks`. -/
def attrWrite (a : Dmmeta.AttrData) : List Ssim.Attr :=
  match attrHeads.find? (fun h => h.tag == a.tag) with
  | some h => h.write a
  | none   => []

def attrHeadName (a : Dmmeta.AttrData) : String :=
  match attrHeads.find? (fun h => h.tag == a.tag) with
  | some h => h.head
  | none   => "dmmeta." ++ a.tag.name

def readTuple (r : Raw) (t : Tuple) : Except String Raw := do
  match t.head with
  | "dmmeta.ctype" =>
    let n ← need t "ctype"
    if builtinNames.contains n then
      .error s!"ctype {n}: {n} is a builtin and is always in scope"
    else if r.ctypes.contains n then
      .error s!"ctype {n}: declared twice"
    else .ok { r with ctypes := r.ctypes ++ [n] }
  | "dmmeta.field" =>
    let q ← need t "field"
    let (owner, name) ← splitQual q
    let arg ← need t "arg"
    let rt ← readReftype (← need t "reftype")
    .ok { r with fields := r.fields ++ [(owner, { name, arg, reftype := rt })] }
  | "amcc.root" =>
    let n ← need t "ctype"
    match r.root with
    | some _ => .error "amcc.root: declared twice"
    | none   => .ok { r with root := some n }
  | h =>
    match attrHeads.find? (fun a => a.head == h) with
    | some ah =>
      let q ← need t "field"
      let (ctype, field) ← splitQual q
      let data ← ah.read t
      .ok { r with attrs := r.attrs ++ [{ ctype, field, data }] }
    | none => .error s!"unknown tuple head {h}"

/-- Attach each field to the ctype its qualified name names. A field whose
owner was never declared is an error rather than an implicit declaration:
`amc` requires the ctype record, and inventing one here would let a typo in a
ctype name produce a second, empty ctype instead of a diagnostic. -/
def assemble (r : Raw) : Except String Db := do
  for (owner, f) in r.fields do
    if !r.ctypes.contains owner then
      throw s!"field {owner}.{f.name}: ctype {owner} is not declared"
  for a in r.attrs do
    if !r.ctypes.contains a.ctype then
      throw s!"{a.data.tag.name} {a.ctype}.{a.field}: ctype {a.ctype} is not declared"
  match r.root with
  | some n =>
    if !r.ctypes.contains n then throw s!"amcc.root: ctype {n} is not declared"
  | none => pure ()
  .ok { ctypes := r.ctypes.map (fun n =>
          { name := n
          , fields := (r.fields.filter (fun cf => cf.1 == n)).map Prod.snd })
      , attrs  := r.attrs
      , root   := r.root }

/-- **Located tuples into a schema.** Record-level rejections are prefixed
with the line they came from; the whole-file conditions `assemble` checks are
not, because they are not about one line. -/
def toDb (ts : List (Nat × Tuple)) : Except String Db := do
  assemble (← ts.foldlM
    (fun r lt =>
      match readTuple r lt.2 with
      | .ok r'   => .ok r'
      | .error e => .error s!"line {lt.1}: {e}")
    ({} : Raw))

/-- **Text into a schema**, which is the front end. -/
def readDb (text : String) : Except String Db := do
  toDb (← parseFile text)

/-! ## Writing

The inverse, in canonical order. Every attribute `amc` writes is written,
including the `comment:""` that carries no information here — because the
round trip is against `amc`'s own files, and a reader that accepts them must
print something they would accept back. -/

def ctypeTuple (c : Ctype) : Tuple :=
  { head := "dmmeta.ctype"
  , attrs := [⟨"ctype", c.name⟩, ⟨"comment", ""⟩] }

def fieldTuple (owner : Ident) (f : Field) : Tuple :=
  { head := "dmmeta.field"
  , attrs := [ ⟨"field", owner ++ "." ++ f.name⟩
             , ⟨"arg", f.arg⟩
             , ⟨"reftype", f.reftype.name⟩
             , ⟨"comment", ""⟩ ] }

/-- An attribute record, through the registry: the shared `field:` key, then
whatever its table writes. -/
def attrTuple (a : Dmmeta.Attr) : Tuple :=
  { head  := attrHeadName a.data
  , attrs := ⟨"field", a.ctype ++ "." ++ a.field⟩ :: attrWrite a.data }

def rootTuple (n : Ident) : Tuple :=
  { head := "amcc.root", attrs := [⟨"ctype", n⟩, ⟨"comment", ""⟩] }

/-- **A schema as tuples**, grouped by head as the ssim directory groups them
by file, and in declaration order within each head. -/
def ofDb (d : Db) : List Tuple :=
  d.ctypes.map ctypeTuple
    ++ d.ctypes.flatMap (fun c => c.fields.map (fieldTuple c.name))
    ++ d.attrs.map attrTuple
    ++ (match d.root with | none => [] | some n => [rootTuple n])

/-- **A schema as ssim text.** -/
def printDb (d : Db) : String := printFile (ofDb d)

/-- **The round trip**, as one function so the checks and the CLI run the same
code: read the text, print the schema back, hand back both halves. A caller
diffs the result against the input. -/
def roundTrip (text : String) : Except String String := do
  .ok (printDb (← readDb text))

end Ssim

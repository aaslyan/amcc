import Amcc.Ssim.Tuple

/-!
# AMCC — ssim tuples into the `Dmmeta` model, and back

`Ssim.Tuple` knows the *format*; this module knows the *records*. It is the
second half of the front end and the place where the standing rule bites:

> **The reader must never run ahead of what the generator can produce.**

`dmmeta` declares twenty reftypes. AMCC has templates or a lowering for eight
of them. A reader that accepted the other twelve would parse a schema, hand it
to `Dmmeta.check`, and get a `Db` for which nothing can be emitted — or worse,
a `Db` whose unsupported fields are silently dropped, so what is generated is
provably correct about a schema the user did not write. `supported` below is
the list, each entry justified by the template or the lowering that consumes
it, and everything else is a named rejection.

## The four record types

```
dmmeta.ctype   ctype:<name>                              comment:""
dmmeta.field   field:<ctype>.<name>  arg:<ctype>  reftype:<R>  comment:""
dmmeta.inlary  field:<ctype>.<name>  min:0  max:<n>      comment:""
amcc.root      ctype:<name>                              comment:""
```

The first three are `amc`'s, key for key (`data/dmmeta/ctype.ssim`,
`field.ssim`, `inlary.ssim`). The fourth is not: `amc` designates the database
ctype by the `<ns>.FDb` naming convention inside a namespace declared by
`dmmeta.nsdb`, and AMCC's `Dmmeta.Db` has no namespaces — a schema is a flat
list of ctypes with one of them named as the root. Reusing `dmmeta.nsdb` would
mean reading its `ns:` key as a ctype name, which is a reinterpretation
pretending to be a match. A separate head under our own namespace says what is
happening. Recorded in `docs/DIVERGENCE.md` §3.5.

## Ordering, because the round trip is byte-for-byte

`ofDb` emits the tuple heads in table order — every `dmmeta.ctype`, then every
`dmmeta.field`, then every `dmmeta.inlary`, then `amcc.root` — which is what a
concatenation of `amc`'s per-table files looks like. Within a head, schema
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
templates that emit their operations. The remaining twelve of `dmmeta`'s
twenty are rejected by name. -/
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
  inlary : List Inlary := []
  root   : Option Ident := none
  deriving Inhabited

/-- A builtin is not a declarable ctype: `Db.withBuiltins` supplies `u32`,
`u64` and `bool`, so declaring one would duplicate it. Rejecting is what keeps
`ofDb ∘ readDb` the identity — a reader that accepted and dropped them would
print back a shorter file. -/
def builtinNames : List Ident := builtins.map Ctype.name

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
  | "dmmeta.inlary" =>
    let q ← need t "field"
    let (ctype, field) ← splitQual q
    let max ← readNat (← need t "max")
    .ok { r with inlary := r.inlary ++ [{ ctype, field, max }] }
  | "amcc.root" =>
    let n ← need t "ctype"
    match r.root with
    | some _ => .error "amcc.root: declared twice"
    | none   => .ok { r with root := some n }
  | h => .error s!"unknown tuple head {h}"

/-- Attach each field to the ctype its qualified name names. A field whose
owner was never declared is an error rather than an implicit declaration:
`amc` requires the ctype record, and inventing one here would let a typo in a
ctype name produce a second, empty ctype instead of a diagnostic. -/
def assemble (r : Raw) : Except String Db := do
  for (owner, f) in r.fields do
    if !r.ctypes.contains owner then
      throw s!"field {owner}.{f.name}: ctype {owner} is not declared"
  for i in r.inlary do
    if !r.ctypes.contains i.ctype then
      throw s!"inlary {i.ctype}.{i.field}: ctype {i.ctype} is not declared"
  match r.root with
  | some n =>
    if !r.ctypes.contains n then throw s!"amcc.root: ctype {n} is not declared"
  | none => pure ()
  .ok { ctypes := r.ctypes.map (fun n =>
          { name := n
          , fields := (r.fields.filter (fun cf => cf.1 == n)).map Prod.snd })
      , inlary := r.inlary
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

def inlaryTuple (i : Inlary) : Tuple :=
  { head := "dmmeta.inlary"
  , attrs := [ ⟨"field", i.ctype ++ "." ++ i.field⟩
             , ⟨"min", "0"⟩
             , ⟨"max", toString i.max⟩
             , ⟨"comment", ""⟩ ] }

def rootTuple (n : Ident) : Tuple :=
  { head := "amcc.root", attrs := [⟨"ctype", n⟩, ⟨"comment", ""⟩] }

/-- **A schema as tuples**, grouped by head as the ssim directory groups them
by file, and in declaration order within each head. -/
def ofDb (d : Db) : List Tuple :=
  d.ctypes.map ctypeTuple
    ++ d.ctypes.flatMap (fun c => c.fields.map (fieldTuple c.name))
    ++ d.inlary.map inlaryTuple
    ++ (match d.root with | none => [] | some n => [rootTuple n])

/-- **A schema as ssim text.** -/
def printDb (d : Db) : String := printFile (ofDb d)

/-- **The round trip**, as one function so the checks and the CLI run the same
code: read the text, print the schema back, hand back both halves. A caller
diffs the result against the input. -/
def roundTrip (text : String) : Except String String := do
  .ok (printDb (← readDb text))

end Ssim

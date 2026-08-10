import Amcc.Ssim.Schema

/-!
# AMCC — classifying a real `dmmeta` corpus

`docs/GOALS.md` measures AMCC against `amc`'s **actual capability**, and until
the ssim reader existed there was no way to say how far short of it the
generator falls except by counting reftypes by hand. This module is the
measurement: given `amc`'s own `data/dmmeta` as ssim text, it says of every
ctype and every field whether AMCC would generate code for it, would accept it
but emit nothing, or would reject it — and why.

## What is in Lean and what is not

Everything that decides a verdict is here, and reuses the shipping code:
`Ssim.parseFile` is the reader the round trip covers, `Ssim.supported` is the
same list `readReftype` refuses against, `Dmmeta.isCIdent` is the same
predicate `Dmmeta.check` applies. Nothing is re-implemented for the
measurement, so the numbers cannot drift from the generator.

`scripts/conformance/` is a throwaway Python pair that concatenates the
corpus and tallies the TSV this module prints. It decides nothing; if it
disappeared the verdicts would be unchanged.

## Why classification is not just "run the reader"

`Ssim.readDb` **aborts** on the first unsupported reftype, which is right for
a front end and useless for a census. This walks every tuple and records a
verdict per record instead, so one unsupported field does not hide the
thousands behind it.
-/

namespace Ssim
namespace Conformance

open Dmmeta

/-- What AMCC does with one declaration. -/
inductive Verdict where
  /-- A template emits operations for it. -/
  | generated (template : String)
  /-- It lowers to a struct field or a struct, but no template emits
  operations over it. -/
  | lowered
  /-- AMCC has no representation for it at all. -/
  | rejected (reason : String)
  deriving Repr, Inhabited

def Verdict.tag : Verdict → String
  | .generated _ => "generated"
  | .lowered     => "lowered"
  | .rejected _  => "rejected"

def Verdict.detail : Verdict → String
  | .generated t => t
  | .lowered     => ""
  | .rejected r  => r

/-- Which template emits operations for a field of this reftype. The six with
a `Dmmeta.fieldTy` lowering but no operations come back `lowered`; everything
else is outside `Ssim.supported` and is rejected by the same list the reader
refuses against. -/
def verdictOfReftype (r : Reftype) : Verdict :=
  match r with
  | .Pkey   => .generated "ArrayTable (key)"
  | .Val    => .generated "ArrayTable (value)"
  | .Inlary => .generated "Pool"
  | .Upptr  => .generated "Upptr"
  | .Llist  => .generated "Llist"
  | .Thash  => .generated "Thash"
  | .Base   => .lowered
  | .Ptr    => .lowered
  | _       => .rejected s!"reftype {r.name}"

/-- Sanity: `verdictOfReftype` is `rejected` exactly off `Ssim.supported`, so
the census and the reader cannot disagree about what is in scope. -/
theorem verdict_iff_supported (r : Reftype) :
    (verdictOfReftype r).tag ≠ "rejected" ↔ supported.contains r = true := by
  cases r <;> decide

/-- A name AMCC can emit as a C identifier. Real `dmmeta` names are
namespace-qualified (`abt.FArch`), which is not one — the single largest
reason the corpus is out of reach, and a mapping question rather than a
missing reftype. -/
def nameVerdict (n : String) : Verdict :=
  if !isCIdent n then .rejected "name is not a C identifier"
  else if isReservedName n then .rejected "name starts with an underscore"
  else .lowered

/-- One TSV row: `kind`, `name`, the overall verdict and its reason, the
reftype, and then the two verdicts **separately**.

The last two columns are the point of the format. Reporting only the overall
verdict hides the most useful number in the census: a field can be blocked by
its reftype, by its name, or by both, and "how many fields would AMCC generate
if the naming question were solved" is answerable only if the two are kept
apart. -/
def row (kind name tag detail reftype rtag ntag : String) : String :=
  kind ++ "\t" ++ name ++ "\t" ++ tag ++ "\t" ++ detail ++ "\t" ++ reftype
    ++ "\t" ++ rtag ++ "\t" ++ ntag

/-- Classify one tuple. Unknown heads are reported rather than skipped, so the
census says how much of `data/dmmeta` AMCC does not model at all. -/
def classify (t : Tuple) : List String :=
  match t.head with
  | "dmmeta.ctype" =>
    match t.get? "ctype" with
    | none   => [row "ctype" "?" "rejected" "missing ctype attribute" "" "" ""]
    | some n =>
      let v := nameVerdict n
      [row "ctype" n v.tag v.detail "" "" v.tag]
  | "dmmeta.field" =>
    match t.get? "field", t.get? "reftype" with
    | some q, some rs =>
      let rv := match Reftype.ofName? rs with
        | none   => Verdict.rejected s!"unknown reftype {rs}"
        | some r => verdictOfReftype r
      -- the field's own name and its owner's have to be emittable too, and a
      -- field is only generated if all three hold
      let nv := match splitQual q with
        | .error _        => Verdict.rejected "not <ctype>.<field>"
        | .ok (owner, fn) =>
          match nameVerdict owner, nameVerdict fn with
          | .rejected r, _ => .rejected s!"owner {r}"
          | _, .rejected r => .rejected s!"field {r}"
          | _, _           => .lowered
      let final := match rv, nv with
        | .rejected r, _ => Verdict.rejected r
        | _, .rejected r => Verdict.rejected r
        | v, _           => v
      [row "field" q final.tag final.detail rs rv.tag nv.tag]
    | _, _ => [row "field" (t.get? "field" |>.getD "?") "rejected"
                 "missing attribute" "" "" ""]
  | "dmmeta.inlary" =>
    [row "inlary" (t.get? "field" |>.getD "?") "lowered" "" "" "" ""]
  | h => [row "other" h "rejected" "tuple head not modelled" "" "" ""]

/-- Classify a whole corpus. Lines the tally script consumes; a parse failure
is one row rather than an abort, because a census that stops at the first bad
line measures nothing. -/
def report (text : String) : List String :=
  match parseFile text with
  | .error e => [row "parse" "" "rejected" e "" "" ""]
  | .ok ts   => ts.flatMap (fun nt => classify nt.2)

end Conformance
end Ssim

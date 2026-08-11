import Amcc.Ssim.Schema
import Amcc.Templates.Pool
import Amcc.Templates.Upptr
import Amcc.Templates.Llist
import Amcc.Templates.Thash

/-!
# AMCC — the ssim front end, exercised

There is no proof of the reader. What stands in for one, until there is, is the
**round trip**, and it is run here in both directions:

- `Db → text → Db` for every schema the generator actually uses. This is the
  sharper direction: it says the reader recovers *exactly* the term the
  templates were proved about, so a schema written as ssim and a schema written
  as a Lean term are the same input to every theorem in the repository.
- `text → Db → text` on hand-written text, which is the direction that catches
  a printer emitting something its own reader would reject.

Both are `rfl`, so they are kernel-checked equalities rather than sampled
tests.

The negative cases matter as much: a front end that accepts what the back end
cannot emit is the failure mode `docs/GOALS.md`'s standing rule exists to
prevent, so every rejection asserts the **exact** message, and a silently
weakened check fails visibly.
-/

-- The reader is a character-at-a-time fold, so a whole-file round trip is a
-- deep reduction. It is still cheap (the schemas are a handful of lines); it
-- is the *depth* the elaborator needs raised, not the time.
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Ssim
namespace Checks

open Dmmeta

/-! ## `Db → text → Db`, on the schemas the templates are proved about

If one of these breaks, a user writing the same schema as ssim would be handed
C proved correct about a different schema. -/

/-- The array table's example, via the ctype model it lowers to. -/
def ordersDb : Db where
  ctypes :=
    [ { name := "order_row"
      , fields := [ { name := "id",  arg := "u64", reftype := .Pkey }
                  , { name := "qty", arg := "u32", reftype := .Val } ] } ]

/-- checked by: `lake build` -/
example : readDb (printDb ordersDb) = .ok ordersDb := rfl

/-- checked by: `lake build` -/
example : readDb (printDb Dmmeta.Examples.boundedDb)
    = .ok Dmmeta.Examples.boundedDb := rfl

/-- checked by: `lake build` -/
example : readDb (printDb Templates.Upptr.Examples.upDb)
    = .ok Templates.Upptr.Examples.upDb := rfl

/-- Named, because the check below chains onto it: rewriting with the equation
is cheap where reducing through it is not.

checked by: `lake build` -/
theorem listDb_roundTrips : readDb (printDb Templates.Llist.Examples.listDb)
    = .ok Templates.Llist.Examples.listDb := rfl

/-- checked by: `lake build` -/
example : readDb (printDb Templates.Thash.Examples.hashDb)
    = .ok Templates.Thash.Examples.hashDb := rfl

/-- And the schemas survive the trip as *accepted* schemas, not merely as equal
terms — the front end cannot hand the generator something the checker rejects
without this failing too.

checked by: `lake build` -/
example : (readDb (printDb Templates.Llist.Examples.listDb)).map Dmmeta.check
    = .ok [] := by rw [listDb_roundTrips]; rfl

/-! ## `text → Db → text`, on hand-written input

The exact bytes matter, so these are written out rather than generated. -/

/-- The intrusive list's schema, as a user would write it. -/
def listText : String :=
  "dmmeta.ctype  ctype:task_row  comment:\"\"\n" ++
  "dmmeta.ctype  ctype:TaskDb  comment:\"\"\n" ++
  "dmmeta.field  field:task_row.id  arg:u64  reftype:Pkey  comment:\"\"\n" ++
  "dmmeta.field  field:TaskDb.zdl_todo  arg:task_row  reftype:Llist  comment:\"\"\n" ++
  "amcc.root  ctype:TaskDb  comment:\"\"\n"

/-- checked by: `lake build` -/
example : roundTrip listText = .ok listText := rfl

/-- And it is the schema `Templates.Llist` is proved about, not merely
something that round-trips.

checked by: `lake build` -/
example : readDb listText = .ok Templates.Llist.Examples.listDb := rfl

/-! ## The tuple layer

Quoting, escaping and the unquoted-colon split, which are where a
line-oriented reader goes wrong. -/

/-- A bare value needs no quotes; an empty one always does. `amc`'s
`PickSsimQuoteChar` is the rule.

checked by: `lake build` -/
example : printVal "task_row" = "task_row" := rfl
example : printVal "" = "\"\"" := rfl
example : printVal "a b" = "\"a b\"" := rfl

/-- `amc` picks whichever quote appears *less* often, so that fewer characters
need escaping. A value full of apostrophes is therefore printed in double
quotes, and one full of double quotes in single quotes.

checked by: `lake build` -/
example : printVal "it's" = "\"it's\"" := rfl
example : printVal "it's 'so'" = "\"it's 'so'\"" := rfl
example : printVal "say \"hi\"" = "'say \"hi\"'" := rfl

/-- A colon inside a quoted value does **not** split the attribute. This is the
one thing a naive `splitOn ":"` reader gets wrong, and it gets it wrong
silently.

checked by: `lake build` -/
example : parseLine "dmmeta.ctype  comment:\"a:b\""
    = .ok { head := "dmmeta.ctype", attrs := [⟨"comment", "a:b"⟩] } := rfl

/-- Neither does a space.

checked by: `lake build` -/
example : parseLine "dmmeta.field  comment:\"Path for this builddir\""
    = .ok { head := "dmmeta.field"
          , attrs := [⟨"comment", "Path for this builddir"⟩] } := rfl

/-- An empty value is an attribute, not an absent one — which is why the lexer
tracks whether a token is *open* rather than whether it is non-empty.

checked by: `lake build` -/
example : parseLine "dmmeta.ctype  ctype:\"\"  comment:\"\""
    = .ok { head := "dmmeta.ctype"
          , attrs := [⟨"ctype", ""⟩, ⟨"comment", ""⟩] } := rfl

/-- The escapes `amc` emits come back as the characters they stand for, octal
included.

checked by: `lake build` -/
example : parseLine "h  k:\"a\\tb\\nc\""
    = .ok { head := "h", attrs := [⟨"k", "a\tb\nc"⟩] } := rfl
example : parseLine "h  k:\"\\101\""
    = .ok { head := "h", attrs := [⟨"k", "A"⟩] } := rfl

/-- A real line from `data/dmmeta/charset.ssim`, whose value ends in an escaped
backslash — the case that breaks a reader treating `\\` as one character.

checked by: `lake build` -/
example : parseLine "dmmeta.charset  field:algo_lib.FDb.DirSep  expr:\"/\\\\\""
    = .ok { head := "dmmeta.charset"
          , attrs := [⟨"field", "algo_lib.FDb.DirSep"⟩, ⟨"expr", "/\\"⟩] } := rfl

/-- Blank lines and `#` comments are not tuples.

checked by: `lake build` -/
example : parseFile "\n# a comment\ndmmeta.ctype  ctype:x  comment:\"\"\n"
    = .ok [(3, { head := "dmmeta.ctype"
               , attrs := [⟨"ctype", "x"⟩, ⟨"comment", ""⟩] })] := rfl

/-! ## Qualified names

`dmmeta` names carry a namespace. The reader stores them **verbatim** — the
`Db` is the schema, not the C — and `Dmmeta.mangle` turns them into C
identifiers at the generator's boundary. So the round trip is unaffected by
mangling, which is the property this section pins. -/

/-- A namespace-qualified schema, as `amc` would write it. -/
def qualText : String :=
  "dmmeta.ctype  ctype:dev.Arch  comment:\"\"\n" ++
  "dmmeta.ctype  ctype:abt.FArch  comment:\"\"\n" ++
  "dmmeta.field  field:dev.Arch.arch  arg:u64  reftype:Pkey  comment:\"\"\n" ++
  "dmmeta.field  field:abt.FArch.p_arch  arg:dev.Arch  reftype:Upptr  comment:\"\"\n"

/-- **It round-trips**, dots and all: `splitQual` splits at the *last* dot, so
`abt.FArch.p_arch` is field `p_arch` of ctype `abt.FArch`.

checked by: `lake build` -/
example : roundTrip qualText = .ok qualText := rfl

-- `Dmmeta.check` mangles every name, and `mangle` is a character fold with a
-- keyword scan; running it under the *kernel* on top of the reader's own
-- reduction is past the boundary `CLAUDE.md` draws. These two are `#guard`:
-- compiled evaluation, still failing `lake build` on a wrong answer.
deriving instance BEq for Except

-- **And it is accepted**, which it was not before mangling existed: every
-- ctype name here fails `isCIdent` on its own.  checked by: `lake build`
#guard (readDb qualText).map Dmmeta.check == .ok []

-- A mangling collision is rejected, by the checker rather than by the mapping:
-- `a.b` and `a_b` are different ctypes and the same C name.
-- checked by: `lake build`
#guard (readDb
    ("dmmeta.ctype  ctype:a.b  comment:\"\"\n" ++
     "dmmeta.ctype  ctype:a_b  comment:\"\"\n")).map Dmmeta.check
    == .ok ["two ctypes generate the same C name: a_b"]

/-! ## The attribute join

The two tables go through one registry, so what is checked here is the
*mechanism*: a `dmmeta.smallstr` record reaches the model with its payload
intact and prints back byte-for-byte, on a schema whose field claims the
reftype that requires it. `Smallstr` is not in `supported` yet — the C subset
has no eight-bit scalar — so this is a `Db` term rather than ssim text going
in, and text is what comes back out. -/

/-- A `Smallstr` field with its `dmmeta.smallstr` record. -/
def strDb : Db where
  ctypes :=
    [ { name := "Name"
      , fields := [{ name := "ch", arg := "u32", reftype := .Smallstr }] } ]
  attrs := [{ ctype := "Name", field := "ch"
            , data := .smallstr 16 .rpascal "'0'" true }]

/-- The record prints in `amc`'s key order.

checked by: `lake build` -/
example : printDb strDb =
    "dmmeta.ctype  ctype:Name  comment:\"\"\n"
    ++ "dmmeta.field  field:Name.ch  arg:u32  reftype:Smallstr  comment:\"\"\n"
    ++ "dmmeta.smallstr  field:Name.ch  length:16  strtype:rpascal"
    ++ "  pad:\"'0'\"  strict:Y\n"
  := rfl

/-- And reading it back is the identity on the *attribute* half, which is the
join's own round trip. The field half cannot be read yet, so this asks the
question the reader can answer: the tuples parse, and the payload comes back.

checked by: `lake build` -/
example : (parseFile (printDb strDb)).map
    (fun ts => ts.filterMap (fun lt =>
      if lt.2.head == "dmmeta.smallstr" then
        (readTuple {} lt.2).toOption.map Raw.attrs
      else none))
    = .ok [[{ ctype := "Name", field := "ch"
            , data := .smallstr 16 .rpascal "'0'" true }]] := rfl

/-- **The named error the join exists for.** A field claims a reftype whose
attribute record is missing, and the message names the table rather than the
reftype's own vocabulary — the same message `Bitfld`, `Charset` and the rest
will get for free.

checked by: `lake build` -/
example : Dmmeta.check { strDb with attrs := [] }
    = ["Name.ch: Smallstr needs a dmmeta.smallstr record"] := rfl

/-- `amc` reports `smallstr.toobig` above 255, because the count is one byte.

checked by: `lake build` -/
example : Dmmeta.check { strDb with
      attrs := [{ ctype := "Name", field := "ch"
                , data := .smallstr 256 .rpascal "'0'" true }] }
    = ["Name.ch: rpascal smallstr length 256 exceeds 255"] := rfl

/-- The ceiling is `rpascal`'s alone: a padded string keeps no count, so its
length is bounded only by the array size.

checked by: `lake build` -/
example : Dmmeta.check { strDb with
      attrs := [{ ctype := "Name", field := "ch"
                , data := .smallstr 256 .rightpad "' '" false }] } = [] := rfl

/-- Every attribute table has a reader/printer entry, so `attrWrite` is total
in practice as well as by construction.

checked by: `lake build` -/
example : ([AttrTag.inlary, AttrTag.smallstr]).all
    (fun t => (attrHeads.find? (fun h => h.tag == t)).isSome) = true := rfl

/-! ## Rejections, with the exact message

Each of these is a way the front end could quietly run ahead of the back end. -/

/-- A reftype `dmmeta` declares and no AMCC template emits. The message says
so, rather than calling it unknown — the distinction is the difference between
"you typed it wrong" and "AMCC cannot do that yet".

checked by: `lake build` -/
example : readDb "dmmeta.field  field:D.f  arg:R  reftype:Bheap  comment:\"\"\n"
    = .error "line 1: reftype Bheap is declared by dmmeta but no AMCC template emits it"
  := rfl

/-- checked by: `lake build` -/
example : readDb "dmmeta.field  field:D.f  arg:R  reftype:Lary  comment:\"\"\n"
    = .error "line 1: reftype Lary is declared by dmmeta but no AMCC template emits it"
  := rfl

/-- A name that is not in the vocabulary at all. -/
example : readDb "dmmeta.field  field:D.f  arg:R  reftype:Nope  comment:\"\"\n"
    = .error "line 1: unknown reftype Nope" := rfl

/-- An unknown record type is refused rather than skipped. A reader that
skipped it would accept `amc`'s full `data/dmmeta` directory and silently
generate from the fraction it understood.

checked by: `lake build` -/
example : readDb "dmmeta.cppfunc  field:D.f  comment:\"\"\n"
    = .error "line 1: unknown tuple head dmmeta.cppfunc" := rfl

/-- A field whose owner was never declared. -/
example : readDb "dmmeta.field  field:D.f  arg:u32  reftype:Val  comment:\"\"\n"
    = .error "field D.f: ctype D is not declared" := rfl

/-- A builtin is always in scope and may not be redeclared — which is what
keeps the round trip exact.

checked by: `lake build` -/
example : readDb "dmmeta.ctype  ctype:u32  comment:\"\"\n"
    = .error "line 1: ctype u32: u32 is a builtin and is always in scope" := rfl

/-- checked by: `lake build` -/
example : readDb "dmmeta.ctype  ctype:R  comment:\"\"\ndmmeta.ctype  ctype:R  comment:\"\"\n"
    = .error "line 2: ctype R: declared twice" := rfl

/-- A qualified name with no dot cannot name a field of a ctype. -/
example : readDb "dmmeta.field  field:f  arg:u32  reftype:Val  comment:\"\"\n"
    = .error "line 1: f: expected <ctype>.<field>" := rfl

/-- A missing attribute names itself. -/
example : readDb "dmmeta.field  field:D.f  arg:u32  comment:\"\"\n"
    = .error "line 1: dmmeta.field: missing attribute reftype" := rfl

/-- An unterminated quote is a lexical error, reported with its line. -/
example : readDb "dmmeta.ctype  ctype:x  comment:\"oops\n"
    = .error "line 1: unterminated quote" := rfl

/-- An escape the printer never emits is refused rather than guessed at.

checked by: `lake build` -/
example : parseLine "h  k:\"a\\qb\"" = .error "unknown escape \\q" := rfl

/-- The root must name a declared ctype. -/
example : readDb "amcc.root  ctype:Nope  comment:\"\"\n"
    = .error "amcc.root: ctype Nope is not declared" := rfl

end Checks
end Ssim

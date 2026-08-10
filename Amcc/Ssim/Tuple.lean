import Amcc.Dmmeta

/-!
# AMCC — the ssim tuple format

`amc`'s input is not a Lean term. It is a directory of line-oriented text
files, and this module is the first half of reading them: the *tuple* layer,
independent of what any particular record means.

`txt/ssim.md` states the grammar:

```
<namespace>.<table>   <primary_key>  [<key>:<value>  ...  <key>:<value>]
```

One line is one tuple. The first token is the **tuple head**, and every
subsequent token is a `key:value` **attribute**; the first attribute is the
primary key.

## Why this exists at all, and why it comes with a printer

`docs/GOALS.md`: "A user writes a schema in `amc`'s reftype vocabulary." Until
now the only way to write one was as a Lean term, so the *front end* was
unwritten and unexamined — and a front-end bug is the one class of defect that
nothing downstream can see. `Dmmeta.check` accepts a misread schema, every
theorem proves about it, every smoke test passes, and the result is certified
code against a specification the user did not write. That is strictly worse
than a back-end defect, which at least fails loudly.

There is no proof of the reader yet. What stands in for one is the **round
trip**: `Ssim.Print` renders a parsed schema back as ssim text, and the text
must come back byte-identical. A reader that drops an attribute, mis-splits a
quoted value or silently coerces a name cannot survive that, because the
printer has no way to invent what the reader threw away. It is built here, in
the same module family, rather than added afterwards, because a round trip
retrofitted onto a reader tends to be a round trip the reader already passes.

## The quoting rule, taken from `amc` rather than invented

`algo::PickSsimQuoteChar` (`cpp/lib/algo/fmt.cpp`) is the authority and is
reproduced exactly:

- a value needs quotes if it is **empty**, or contains any character outside
  the `SsimQuotesafe` set (`data/dmmeta/charset.ssim`:
  `a-zA-Z0-9` with `_;&*^%$@.!:,+`, slash and dash), or is at least 127;
- the quote character is `"` unless the value contains strictly more `"` than
  `'`, in which case it is `'` — whichever quote appears less often is the one
  used, so fewer characters need escaping;
- inside quotes, `algo::_PrintQuotedChar` escapes the quote character and the
  backslash as `\c`, emits `\n` / `\t` / `\r`, and octal-escapes any other
  byte below 32 or at/above 127. Multi-byte UTF-8 is copied verbatim.

The reader accepts `\n \t \r \\ \" \'` and three-digit octal, and **rejects**
any other escape rather than guessing. Rejecting is what keeps the round trip
sound: a reader that silently drops an unknown escape prints back something
different, and the diff would be the only warning.
-/

namespace Ssim

/-- One `key:value` attribute of a tuple. -/
structure Attr where
  key : String
  val : String
  deriving DecidableEq, Repr, Inhabited, BEq

/-- One line: the tuple head and its attributes, in order. Order is kept
because the round trip is byte-for-byte and `amc`'s files are ordered. -/
structure Tuple where
  head  : String
  attrs : List Attr
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The attribute with this key, if the tuple has one. -/
def Tuple.get? (t : Tuple) (k : String) : Option String :=
  (t.attrs.find? (fun a => a.key == k)).map Attr.val

/-! ## Working in `List Char`

Every string function used below is one that reduces in the kernel, so the
round-trip checks in `Ssim.Checks` can be `rfl` rather than `#guard`.
`String.splitOn`, `String.trim` and `String.toNat?` are well-founded
recursions and do **not** reduce — the same hazard `Dmmeta`'s `pow2Exp?`
avoided for `Nat.log2` — so the three of them are re-done here structurally
over `List Char`. `String.toList`, `String.ofList`, `List.foldl` and
`toString` on a `Nat` all reduce, and are used freely.

Kernel-checked front-end tests are worth this much trouble: the round trip is
what stands in for a proof of the reader, and a round trip checked by the
*compiler* would be testing the compiled reader rather than the one the
theorems see. -/

/-- Split a character list on a separator, keeping empty pieces — `splitOn`'s
behaviour, structurally.

Written with an accumulator so the recursive call is in **tail** position. The
obvious non-tail version overflowed the stack on `amc`'s own `data/dmmeta`
(seven thousand lines, most of a megabyte): it recurses once per character,
and half a million frames is past the limit. A census that cannot read the
corpus it is measuring is no census, so the shape matters. -/
def splitOnCharAux (sep : Char) :
    List Char → List Char → List (List Char) → List (List Char)
  | [],      cur, acc => (cur.reverse :: acc).reverse
  | c :: cs, cur, acc =>
    if c == sep then splitOnCharAux sep cs [] (cur.reverse :: acc)
    else splitOnCharAux sep cs (c :: cur) acc

def splitOnChar (sep : Char) (l : List Char) : List (List Char) :=
  splitOnCharAux sep l [] []

/-- Digits into a number, refusing anything that is not all digits. -/
def digitsToNat? (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else cs.foldl (fun acc c =>
    match acc with
    | none => none
    | some n =>
      if '0' ≤ c && c ≤ '9' then some (n * 10 + (c.toNat - '0'.toNat)) else none)
    (some 0)

def isBlank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

/-! ## Lexing

A left fold over the characters, so the scanner is total and structural with
no fuel parameter: each character advances the state exactly once. The state
has to carry the position of the first **unquoted** colon, because that — not
the first colon of the assembled token — is what separates key from value.
`comment:"a:b"` has two colons and only the first one splits. -/

/-- Where an escape sequence is, inside a quoted run. -/
inductive Esc where
  /-- Not in an escape. -/
  | none
  /-- Just saw a backslash. -/
  | slash
  /-- Inside a three-digit octal escape: value so far, digits still wanted. -/
  | oct (val : Nat) (want : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The scanner's state. `cur`/`colon` describe the token being built; `tok`
says whether a token is open at all, which is what distinguishes `k:""`
(an attribute with an empty value) from trailing whitespace. -/
structure Lex where
  toks  : List (List Char × Option Nat) := []
  cur   : List Char := []
  colon : Option Nat := none
  tok   : Bool := false
  quote : Option Char := none
  esc   : Esc := .none
  err   : Option String := none
  deriving Inhabited

def Lex.push (s : Lex) (c : Char) : Lex := { s with cur := c :: s.cur, tok := true }

/-- Close the token being built, if any. -/
def Lex.close (s : Lex) : Lex :=
  if s.tok then
    { s with toks := (s.cur.reverse, s.colon) :: s.toks
           , cur := [], colon := none, tok := false }
  else s

def isSpace (c : Char) : Bool := c == ' ' || c == '\t'

def octDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '7' then some (c.toNat - '0'.toNat) else none

/-- One character. Inside quotes everything is literal except the escape
machinery and the closing quote; outside quotes, whitespace ends a token and a
quote character opens one. -/
def step (s : Lex) (c : Char) : Lex :=
  if s.err.isSome then s else
  match s.quote, s.esc with
  | some q, .slash =>
    if c == 'n' then { s.push '\n' with esc := .none }
    else if c == 't' then { s.push '\t' with esc := .none }
    else if c == 'r' then { s.push '\r' with esc := .none }
    else if c == '\\' || c == q || c == '"' || c == '\'' then
      { s.push c with esc := .none }
    else match octDigit? c with
      | some d => { s with esc := .oct d 2 }
      | none   => { s with err := some s!"unknown escape \\{c}" }
  | some _, .oct v 1 =>
    match octDigit? c with
    | some d =>
      let n := v * 8 + d
      if n < 256 then { (s.push (Char.ofNat n)) with esc := .none }
      else { s with err := some "octal escape out of range" }
    | none => { s with err := some "octal escape needs three digits" }
  | some _, .oct v w =>
    match octDigit? c with
    | some d => { s with esc := .oct (v * 8 + d) (w - 1) }
    | none   => { s with err := some "octal escape needs three digits" }
  | some q, .none =>
    if c == q then { s with quote := none, tok := true }
    else if c == '\\' then { s with esc := .slash }
    else s.push c
  | none, _ =>
    if isSpace c then s.close
    else if c == '"' || c == '\'' then { s with quote := some c, tok := true }
    else if c == ':' && s.colon.isNone then
      { (s.push c) with colon := some s.cur.length }
    else s.push c

/-- Split one token at its first unquoted colon. A token with no unquoted
colon is a bare value with no key, which is what the tuple head is. -/
def splitTok : List Char × Option Nat → String × Option String
  | (t, none)   => (String.ofList t, none)
  | (t, some i) => (String.ofList (t.take i), some (String.ofList (t.drop (i + 1))))

/-- **Lex one line into tokens**, each with its key/value split already made.
`none` on a malformed line, with the reason. -/
def tokens (line : String) : Except String (List (String × Option String)) :=
  let s := (line.toList.foldl step {}).close
  match s.err with
  | some e => .error e
  | none =>
    if s.quote.isSome then .error "unterminated quote"
    else .ok (s.toks.reverse.map splitTok)

/-- **Parse one line into a tuple.** The head is a bare token; every
subsequent token must be a `key:value`. -/
def parseLine (line : String) : Except String Tuple := do
  match ← tokens line with
  | [] => .error "empty line"
  | (h, hk) :: rest =>
    if hk.isSome then .error s!"tuple head {h} must not be a key:value"
    else do
      let attrs ← rest.mapM (fun tv =>
        match tv with
        | (k, some v) => Except.ok ({ key := k, val := v } : Attr)
        | (k, none)   => Except.error s!"attribute {k} has no value")
      .ok { head := h, attrs := attrs }

/-- Blank lines and `#` comments are skipped, as `acr` skips them. -/
def significant (line : String) : Bool :=
  match line.toList.dropWhile isBlank with
  | []     => false
  | c :: _ => c != '#'

/-- **Parse a whole file**, keeping each tuple's 1-based line number. The
number is carried rather than discarded because the *record* layer rejects
more than the tuple layer does — an unsupported reftype, an undeclared ctype —
and a front end whose diagnostics do not locate the problem is a front end
people work around. -/
def parseFile (text : String) : Except String (List (Nat × Tuple)) :=
  let lines := ((splitOnChar '\n' text.toList).map String.ofList).zipIdx
  -- accumulated reversed and flipped once: `ts ++ [t]` is quadratic, which on
  -- a seven-thousand-line corpus is twenty-five million conses for nothing
  match lines.foldl
      (fun (acc : Except String (List (Nat × Tuple))) li =>
        match acc with
        | .error e => .error e
        | .ok ts =>
          if significant li.1 then
            match parseLine li.1 with
            | .ok t    => Except.ok ((li.2 + 1, t) :: ts)
            | .error e => Except.error s!"line {li.2 + 1}: {e}"
          else Except.ok ts)
      (Except.ok []) with
  | .error e => .error e
  | .ok ts   => .ok ts.reverse

/-! ## Printing

The exact inverse of the above on everything the reader accepts, which is what
makes the round trip a test of the reader rather than of the pair. -/

/-- `data/dmmeta/charset.ssim`'s `SsimQuotesafe`: `a-zA-Z0-9` with
`_;&*^%$@.!:,+`, slash and dash. -/
def quoteSafe (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9')
    || "_;&*^%$@.!:,+/-".toList.contains c

/-- `algo::PickSsimQuoteChar`, transcribed. `none` when the value may be
printed bare. -/
def pickQuote (s : String) : Option Char :=
  let cs := s.toList
  let singleq : Int := cs.foldl (fun n c =>
    if c == '\'' then n + 1 else if c == '"' then n - 1 else n) 0
  let need := cs.isEmpty
    || cs.any (fun c => c == '\'' || c == '"' || c.toNat ≥ 127 || !quoteSafe c)
  if need then some (if singleq ≥ 0 then '"' else '\'') else none

private def octStr (n : Nat) : String :=
  let d (k : Nat) : Char := Char.ofNat ('0'.toNat + (n / k) % 8)
  String.ofList ['\\', d 64, d 8, d 1]

/-- `algo::_PrintQuotedChar`. Multi-byte UTF-8 is a single `Char` here, and
`Char.toNat ≥ 127` would octal-escape it, so the ≥ 127 test is written as
"not representable in one byte" — which is the same decision `amc` makes
after `Utf8SeqLen` has taken the multi-byte case away. -/
def escChar (q : Char) (c : Char) : String :=
  if c == q || c == '\\' then String.ofList ['\\', c]
  else if c == '\n' then "\\n"
  else if c == '\t' then "\\t"
  else if c == '\r' then "\\r"
  else if c.toNat < 32 then octStr c.toNat
  else if c.toNat == 127 then octStr 127
  else String.ofList [c]

/-- `algo::strptr_PrintSsim`. -/
def printVal (s : String) : String :=
  match pickQuote s with
  | none   => s
  | some q => String.ofList [q] ++ String.join (s.toList.map (escChar q)) ++ String.ofList [q]

/-- `algo::PrintAttr`. An empty key prints as a bare value, as `amc` does. -/
def printAttr (a : Attr) : String :=
  if a.key.isEmpty then printVal a.val else printVal a.key ++ ":" ++ printVal a.val

/-- `algo::PrintAttrSpace`: two spaces between the head and every attribute. -/
def printTuple (t : Tuple) : String :=
  printVal t.head ++ String.join (t.attrs.map (fun a => "  " ++ printAttr a))

/-- A whole file, one tuple per line, trailing newline. -/
def printFile (ts : List Tuple) : String :=
  String.join (ts.map (fun t => printTuple t ++ "\n"))

end Ssim

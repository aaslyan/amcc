import Amcc.CSubset.Syntax

/-!
# AMCC — Phase 2: the schema DSL

The generator's *input* language: what a user writes to describe a table.

This file deliberately knows nothing about the C subset beyond borrowing its
scalar types, and nothing at all about any template. A schema is a description
of data, not of code; which template consumes it is Phase 3's business.

## The `Reftype` vocabulary

`Reftype` names the *structural role* a field plays, which is the idea AMCC
takes from OpenACR's `dmmeta.reftype`: the same field type means different
generated code depending on whether it is a key, a value, or a link. Two
constructors is the whole vocabulary for now — `Pkey` and `Val` — because the
Phase 3 template can only act on those two, and a constructor with no template
to interpret it would be decoration. `Upptr`/`Ptrary`-style link reftypes are
what a Phase 5 intrusive-list template would add.

## Reserved names

The generator synthesises C names from the table name (see `Names`), one struct
field — the slot-occupancy flag — that has no schema counterpart, and a handful
of local temporaries. `check` rejects any schema whose field names would
collide:

- with the occupancy flag, by name; and
- with a temporary, by reserving the entire **leading-underscore** namespace
  for generated locals. One rule instead of a list the generator could outgrow
  — a template that needs another temporary just prefixes it.

Collecting the generated names in `Names` rather than spelling them out at each
use site is what keeps the collision check and the generator from drifting
apart.
-/

namespace Schema

abbrev Ident := String

/-- The structural role of a field. See the module docstring on why this is
only two constructors. -/
inductive Reftype where
  /-- Stored by value; no structural role. -/
  | Val
  /-- The table's unique primary key. Exactly one field must have this. -/
  | Pkey
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Field types are the C subset's scalar types.

Not a separate type language: the Phase 3 template stores fields in a struct
and compares keys with `==`, so anything it could express would map one-to-one
onto `CSubset.ScalarTy` anyway. A template that needs strings or nested records
is the point at which this should fork. -/
abbrev FieldTy := CSubset.ScalarTy

structure Field where
  name    : Ident
  ty      : FieldTy
  reftype : Reftype
  deriving DecidableEq, Repr, Inhabited

end Schema

/-- A schema: one table.

`capacity` is part of the schema rather than the template because it decides
the generated array's size, and array sizes are literals in the C subset — so
a schema fixes a program, not a family of them. -/
structure Schema where
  name     : Schema.Ident
  capacity : Nat
  fields   : List Schema.Field
  deriving DecidableEq, Repr, Inhabited

namespace Schema

/-! ## Derived views -/

/-- The primary key field, if the schema has exactly one. -/
def pkey? (s : Schema) : Option Field :=
  match s.fields.filter (fun f => f.reftype == .Pkey) with
  | [f] => some f
  | _   => none

/-- The non-key fields, in declaration order. -/
def valFields (s : Schema) : List Field :=
  s.fields.filter (fun f => f.reftype == .Val)

/-- Every C name a schema generates.

One place, so that `check`'s collision test and Phase 3's generator cannot
disagree about what gets emitted. -/
structure Names where
  /-- `struct <name>_row` — one slot of the table. -/
  row      : Ident
  /-- `static <row> g_<name>[CAP]` — the storage. -/
  storage  : Ident
  /-- The slot-occupancy flag. Has no schema counterpart, which is why it is
  the one name `check` must reserve. -/
  occupied : Ident
  find     : Ident
  insert   : Ident
  erase    : Ident
  deriving DecidableEq, Repr, Inhabited

/-- `<table>_get_<field>` — the accessor generated for each value field. Not a
`Names` field because there is one per value field rather than one per table.

There is deliberately **no** `<table>_at` returning a `<row> *`. Such a function
takes a slot index the caller must independently know is in range, so it can
trap — and a template whose no-trap theorem carries a precondition is a worse
deliverable than one whose does not. Reading a field goes through the key
instead, where the `!= CAP` guard makes the access provably safe. -/
def getterName (s : Schema) (field : Ident) : Ident := s.name ++ "_get_" ++ field

def names (s : Schema) : Names where
  row      := s.name ++ "_row"
  storage  := "g_" ++ s.name
  occupied := "occupied"
  find     := s.name ++ "_find"
  insert   := s.name ++ "_insert"
  erase    := s.name ++ "_erase"

/-! ## Well-formedness -/

/-- One past the largest capacity a `uint32_t` slot index can address. Matches
`CSubset.Wf.u32Bound`; the two are the same constraint seen from the input and
output ends. -/
def u32Bound : Nat := 4294967296

private def cKeywords : List String :=
  [ "auto", "break", "case", "char", "const", "continue", "default", "do",
    "double", "else", "enum", "extern", "float", "for", "goto", "if", "inline",
    "int", "long", "register", "restrict", "return", "short", "signed",
    "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned",
    "void", "volatile", "while", "_Bool", "_Complex", "_Imaginary",
    "bool", "true", "false", "NULL",
    "uint8_t", "uint16_t", "uint32_t", "uint64_t" ]

/-- A legal C identifier that is not a keyword.

Checked here rather than in Phase 4 because these strings come from *user
input*: a schema is where a bad name enters the system, and rejecting it at the
door beats emitting C that will not compile. -/
def isCIdent (s : String) : Bool :=
  match s.toList with
  | []      => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun d => d.isAlphanum || d == '_')
               && !cKeywords.contains s

/-- Reserved for the generator's local temporaries. Spelled with `toList`
rather than `String.startsWith` because the latter iterates UTF-8 byte
positions and does not reduce in the kernel — which would cost every schema
check in this file its `rfl` proof. -/
def isReservedName (n : Ident) : Bool := n.toList.head? == some '_'

/-- The names that occur more than once. Public (not `private`) because the
`GenWellFormed` proof needs to reason about `check`'s components by name. -/
def dups (xs : List Ident) : List Ident :=
  (xs.filter (fun x => 1 < xs.countP (fun y => y == x))).eraseDups

/-- Violations, empty when the schema is well-formed.

Same shape as `CSubset.Wf.check`, and for the same reason: the consumer is a
generator, and "which rule, where" is what makes a failure actionable. -/
def check (s : Schema) : List String :=
  (if isCIdent s.name then [] else [s!"table name {s.name} is not a legal C identifier"])
    ++ (if 0 < s.capacity then [] else ["capacity must be positive"])
    ++ (if s.capacity < u32Bound then [] else [s!"capacity {s.capacity} does not fit in u32"])
    ++ (match s.fields.filter (fun f => f.reftype == .Pkey) with
        | [_] => []
        | []  => ["no Pkey field"]
        | _   => ["more than one Pkey field"])
    ++ (dups (s.fields.map Field.name)).map (fun n => s!"duplicate field: {n}")
    ++ s.fields.flatMap (fun f =>
        (if isCIdent f.name then [] else [s!"field name {f.name} is not a legal C identifier"])
          ++ (if f.name == (names s).occupied then
                [s!"field name {f.name} collides with the generated occupancy flag"]
              else [])
          ++ (if isReservedName f.name then
                [s!"field name {f.name} is in the reserved leading-underscore namespace"]
              else []))
    -- The generated C names must themselves be legal, which the table name
    -- being legal does not quite guarantee once suffixes are appended.
    ++ (let n := names s
        ([n.row, n.storage, n.find, n.insert, n.erase]
          ++ s.fields.map (fun f => getterName s f.name)).flatMap (fun g =>
          if isCIdent g then [] else [s!"generated name {g} is not a legal C identifier"]))

def wf (s : Schema) : Bool := (check s).isEmpty

/-! ## Examples -/

namespace Examples

/-- A two-value table keyed by a `u64`, at a capacity small enough to compute
with. Generic on purpose: it exercises a key plus more than one value field,
which is the smallest shape that can get field order wrong. -/
def orders : Schema where
  name     := "order"
  capacity := 4
  fields :=
    [ { name := "id",    ty := .u64, reftype := .Pkey }
    , { name := "price", ty := .u64, reftype := .Val }
    , { name := "qty",   ty := .u64, reftype := .Val } ]

/-- The degenerate case: a table with a key and nothing else. Worth keeping,
because `valFields` is empty and the generator must not assume otherwise. -/
def keysOnly : Schema where
  name     := "tag"
  capacity := 2
  fields   := [{ name := "k", ty := .u32, reftype := .Pkey }]

-- checked by: `lake build`
example : wf orders = true := rfl

-- checked by: `lake build`
example : wf keysOnly = true := rfl

-- checked by: `lake build`
example : (pkey? orders).map Field.name = some "id" := rfl

-- checked by: `lake build`
example : (valFields orders).map Field.name = ["price", "qty"] := rfl

-- checked by: `lake build`
example : (valFields keysOnly) = [] := rfl

/-- A field colliding with the generated occupancy flag is rejected.

checked by: `lake build` -/
example : check { orders with
    fields := orders.fields ++ [{ name := "occupied", ty := .bool, reftype := .Val }] }
  = ["field name occupied collides with the generated occupancy flag"] := rfl

/-- No key, no table.

checked by: `lake build` -/
example : check { orders with
    fields := [{ name := "a", ty := .u64, reftype := .Val }] } = ["no Pkey field"] := rfl

/-- Two keys is not a unique primary key.

checked by: `lake build` -/
example : check { orders with
    fields := [{ name := "a", ty := .u64, reftype := .Pkey },
               { name := "b", ty := .u64, reftype := .Pkey }] }
  = ["more than one Pkey field"] := rfl

/-- A C keyword as a table name is rejected before it can become `struct
switch_row`.

checked by: `lake build` -/
example : check { orders with name := "switch" } =
    ["table name switch is not a legal C identifier"] := rfl

/-- A leading underscore is reserved for the generator's temporaries.

checked by: `lake build` -/
example : check { orders with
    fields := orders.fields ++ [{ name := "_i", ty := .u64, reftype := .Val }] }
  = ["field name _i is in the reserved leading-underscore namespace"] := rfl

/-- Zero capacity is rejected — the same rule as `CSubset.Wf`'s obligation 3,
seen from the input end.

checked by: `lake build` -/
example : check { orders with capacity := 0 } = ["capacity must be positive"] := rfl

end Examples
end Schema

import Amcc.CSubset.Wf

/-!
# AMCC — the ctype model

The schema model AMCC actually needs, transcribed from OpenACR's `dmmeta`.

The previous `Schema` type flattened three separate things into one record: the
*type* of a row, the *storage* that holds rows, and a capacity. It also fixed a
field's type to be a machine scalar. That last restriction is the one that
mattered — in `dmmeta`, a field's `arg` names **another ctype**, and a field
pointing at a record type is the entire basis of the relational model. Without
it none of `Upptr`, `Ptrary`, `Thash`, `Llist`, `Base` or foreign keys can even
be written down.

## The three records

Faithful to `data/dmmeta/`:

- **`Ctype`** — a named type. `dmmeta.ctype`.
- **`Field`** — belongs to a ctype, has an `arg` naming a ctype, and a
  `reftype` naming its structural role. `dmmeta.field`.
- **`Db`** — the ctypes in declaration order. Order is meaningful: it is what
  makes layout acyclic, exactly as in the C subset's obligation 2.

**Scalars are ctypes.** In `dmmeta`, `u32` is a ctype like any other, so `arg`
is uniformly a ctype name and there is no second type language. `Ctype.scalar`
distinguishes a builtin machine type from a record described by its fields.

## What is not here yet

Storage. In `amc` a pool is a *field* — `abt.FDb.target` with `reftype:Lary`
and `arg:abt.FTarget` — not a property of the ctype, and capacity belongs to
the pool field, not the row type. That is why `Ctype` has no capacity: putting
one there would repeat the mistake this file exists to correct. The pool
templates consume a pool field; they are the next step.
-/

namespace Dmmeta

abbrev Ident := String

/-! ## Reftypes

The full `dmmeta.reftype` vocabulary. The flags below are transcribed from
`data/dmmeta/reftype.ssim`; they are what the checker and the templates
dispatch on, so getting them right here is what stops each template from
re-deciding the same question differently. -/

/-- The structural role a field plays. -/
inductive Reftype where
  /-- Stored inline by value. -/
  | Val
  /-- Primary key, or a reference to another ctype's key. -/
  | Pkey
  /-- This ctype extends its `arg`. -/
  | Base
  /-- Cached pointer to a parent record — the in-memory form of a `Pkey`. -/
  | Upptr
  /-- A plain pointer to one record. -/
  | Ptr
  /-- Growable pool with **stable element addresses**. -/
  | Lary
  /-- Growable contiguous array; growth **moves** elements. -/
  | Tary
  /-- Bounded array stored inline in the parent. -/
  | Inlary
  /-- Fixed-size element allocator with a free list. -/
  | Tpool
  /-- Size-class allocator built from free lists. -/
  | Lpool
  /-- Block allocator for mostly-FIFO lifetimes. -/
  | Blkpool
  /-- Pass-through `malloc`/`free`. -/
  | Malloc
  /-- Base allocator over `sbrk`. -/
  | Sbrk
  /-- Lazily allocated value owned by its parent. -/
  | Delptr
  /-- Hash index. -/
  | Thash
  /-- Intrusive linked list. -/
  | Llist
  /-- Binary heap. -/
  | Bheap
  /-- AVL tree. -/
  | Atree
  /-- Red-Black tree (self-balancing sorted index). -/
  | Rbtree
  /-- Array of pointers. -/
  | Ptrary
  /-- Bookkeeping counter over linked records. -/
  | Count
  /-- A second name for another field of the same ctype. -/
  | Alias
  /-- Named bit range inside an integer field. -/
  | Bitfld
  /-- Character-class membership table. -/
  | Charset
  /-- Value whose lifetime is the enclosing C++ scope. -/
  | Cppstack
  /-- The field *is* a ctype, reflected. -/
  | Ctype
  /-- Command executed as a subprocess. -/
  | Exec
  /-- File-descriptor buffer. -/
  | Fbuf
  /-- Process-wide singleton. -/
  | Global
  /-- Call-out point the generated code invokes. -/
  | Hook
  /-- Command-line option. -/
  | Opt
  /-- Compiled regular expression. -/
  | Regx
  /-- Compiled SQL-style regular expression. -/
  | RegxSql
  /-- Fixed-capacity string stored inline: `rpascal`, `leftpad` or `rightpad`,
  with the shape in a `dmmeta.smallstr` record. -/
  | Smallstr
  /-- Variable-length trailing field. -/
  | Varlen
  /-- Zero-sized multi-threaded list. -/
  | ZSListMT
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The `deriving` handler registers `BEq` but not `LawfulBEq`, and without it
`f.reftype == r` cannot be turned back into `f.reftype = r` — which every
template's well-formedness proof needs, because the generators select their
fields with `==` and the laws are stated with `=`. The same gap
`Amcc/CSubset/Value.lean` closes for `PathStep`, `Root` and `Path`. -/
instance : LawfulBEq Reftype where
  eq_of_beq {a b} h := by revert h; cases a <;> cases b <;> decide
  rfl {a} := by cases a <;> rfl

namespace Reftype

/-- `dmmeta.reftype.isval` — the field stores its value inline. -/
def isval : Reftype → Bool
  | Val | Lary | Tary | Inlary | Tpool | Lpool | Blkpool | Malloc | Sbrk
  | Alias | Bitfld | Charset | Cppstack | Fbuf | Global | Opt | Smallstr
  | Varlen => true
  | _ => false

/-- `dmmeta.reftype.isxref` — the field is an index over another ctype's
records, maintained as those records come and go. -/
def isxref : Reftype → Bool
  | Thash | Llist | Bheap | Atree | Rbtree => true
  | _ => false

/-- `dmmeta.reftype.usebasepool` — the field obtains memory from a base pool,
so `dmmeta.basepool` composition applies to it. -/
def usebasepool : Reftype → Bool
  | Lary | Tary | Tpool | Lpool | Blkpool | Delptr | Thash | Bheap | Ptrary
  | Fbuf => true
  | _ => false

/-- `dmmeta.reftype.up` — the field points *up*, at a parent record. -/
def up : Reftype → Bool
  | Pkey | Base | Upptr | Regx | RegxSql => true
  | _ => false

/-- Storage provider: a field of this reftype is where records live. -/
def ispool : Reftype → Bool
  | Lary | Tary | Inlary | Tpool | Lpool | Blkpool | Malloc | Sbrk => true
  | _ => false

/-- **Does this field contribute to its ctype's layout?**

If so, the `arg` must be a ctype declared *earlier*, which is what makes
nest nesting acyclic — the schema-level form of the C subset's obligation 2.

`Val` and `Base` embed the argument outright. `Inlary` embeds a bounded array
of it. Everything else reaches its argument through a pointer, a pool, or an
index, so it needs the *name* but not the layout — which is exactly why a
self-referential list or an up-pointer to the enclosing ctype is legal. -/
def layoutDep : Reftype → Bool
  | Val | Base | Inlary => true
  | _ => false

/-- Does a field of this reftype provide **stable addresses** to the records
it stores?

The distinction that decides whether intrusive structures may be built over a
pool: `Lary` adds levels and never moves an element, `Tary` reallocates and
does. `Amcc.Spec.Pool.moving_not_stable` is the proof that the difference is
real rather than stylistic. -/
def stableAddresses : Reftype → Bool
  | Lary | Inlary | Tpool | Lpool | Blkpool => true
  | _ => false

/-- **Does this reftype require its `arg` to be a record?**

A pointer to a machine scalar and an index over machine scalars are both
meaningless — there is no record to point at or to thread — and every template
that emits one assumes a struct. Without this clause `Dmmeta.check` accepted
an `Upptr` at `u64` and the generated program failed `CSubset.Wf.check` with
four type errors: the emitted `row->f = NULL` has type `parent *` where the
struct field has type `uint64_t *`.

`Pkey` is deliberately **absent**: a key *is* a machine scalar in the common
case, and `fieldTy` lowers it to the scalar rather than to a pointer. -/
def needsRecordArg : Reftype → Bool
  | Upptr | Ptr | Thash | Llist | Bheap | Atree | Rbtree | Ptrary => true
  | _ => false

/-- The reftype's name, for error messages. A plain function rather than
`repr`: `Repr` produces a `Std.Format`, and rendering one does not reduce in
the kernel, which would cost every checker test in this file its `rfl`. -/
def name : Reftype → String
  | Val => "Val" | Pkey => "Pkey" | Base => "Base" | Upptr => "Upptr"
  | Ptr => "Ptr" | Lary => "Lary" | Tary => "Tary" | Inlary => "Inlary"
  | Tpool => "Tpool" | Lpool => "Lpool" | Blkpool => "Blkpool"
  | Malloc => "Malloc" | Sbrk => "Sbrk" | Delptr => "Delptr"
  | Thash => "Thash" | Llist => "Llist" | Bheap => "Bheap" | Atree => "Atree"
  | Rbtree => "Rbtree" | Ptrary => "Ptrary" | Count => "Count"
  | Alias => "Alias" | Bitfld => "Bitfld" | Charset => "Charset"
  | Cppstack => "Cppstack" | Ctype => "Ctype" | Exec => "Exec"
  | Fbuf => "Fbuf" | Global => "Global" | Hook => "Hook" | Opt => "Opt"
  | Regx => "Regx" | RegxSql => "RegxSql" | Smallstr => "Smallstr"
  | Varlen => "Varlen" | ZSListMT => "ZSListMT"

/-- The whole vocabulary, in `dmmeta/reftype.ssim`'s order. Written out rather
than derived because a front end has to turn a *name* back into a reftype, and
the two directions must not drift: `Checks` below pins that `all` has **all
thirty-six** entries and that `name` is injective on it, so a new constructor
that is not added here fails the count. -/
def all : List Reftype :=
  [ Val, Pkey, Base, Upptr, Ptr, Lary, Tary, Inlary, Tpool, Lpool, Blkpool
  , Malloc, Sbrk, Delptr, Thash, Llist, Bheap, Atree, Rbtree, Ptrary, Count
  , Alias, Bitfld, Charset, Cppstack, Ctype, Exec, Fbuf, Global, Hook, Opt
  , Regx, RegxSql, Smallstr, Varlen, ZSListMT ]

/-- The reftype with this name, if there is one. -/
def ofName? (s : String) : Option Reftype := all.find? (fun r => r.name == s)

end Reftype

/-! ## The records -/

/-- `dmmeta.field`. `arg` names a **ctype**, which may be a builtin scalar or
another record — that uniformity is the whole point. -/
structure Field where
  name    : Ident
  /-- The ctype this field's value is drawn from. -/
  arg     : Ident
  reftype : Reftype
  deriving DecidableEq, Repr, Inhabited

/-- `dmmeta.ctype`. A builtin machine type carries `scalar`; a record carries
fields. -/
structure Ctype where
  name   : Ident
  /-- `some t` for a builtin machine type, `none` for a record. -/
  scalar : Option CSubset.ScalarTy := none
  fields : List Field := []
  deriving DecidableEq, Repr, Inhabited

/-! ## Per-field attribute records — the join

A field's *shape* does not live in `dmmeta.field`. It lives in a table of its
own, keyed by the field: `dmmeta.inlary` carries an array bound,
`dmmeta.smallstr` carries a length and a padding discipline, and `bitfld`,
`charset`, `lenfld`, `substr` and `fconst` are all that same shape. Joining
one onto a field is therefore a *mechanism*, not a per-reftype chore, and it
is written once here:

- `AttrTag` names the table, so `Reftype.needsAttr` can say which record a
  reftype requires without naming its contents;
- `AttrData` carries the payload, one constructor per table;
- `Db.attr?` is the join, and the typed views below (`inlaryMax?`,
  `smallstr?`) are the only thing a client sees;
- `checkAttr` is the single checker clause: **a field that claims a reftype
  whose attribute record is missing is a named error**, for every table at
  once.

Adding the next table is one `AttrTag`, one `AttrData` constructor, one typed
view, one `checkAttrData` arm, and one reader/printer head. Nothing else moves.
-/

/-- Which `dmmeta` attribute table a record belongs to. -/
inductive AttrTag where
  /-- `dmmeta.inlary` — the bound on an inline array. -/
  | inlary
  /-- `dmmeta.smallstr` — the length and padding of an inline string. -/
  | smallstr
  deriving DecidableEq, Repr, Inhabited, BEq

/-- The `deriving` handler registers `BEq` but not the lawfulness, and the
join compares tags with `==` while every fact about it is stated with `=`. -/
instance : LawfulBEq AttrTag where
  eq_of_beq {a b} h := by revert h; cases a <;> cases b <;> decide
  rfl {a} := by cases a <;> rfl

/-- The table's `dmmeta` name, for the record head and for error messages. -/
def AttrTag.name : AttrTag → String
  | inlary   => "inlary"
  | smallstr => "smallstr"

/-- `dmmeta.strtype` — how a `Smallstr` field's bytes encode its length.

`rpascal` stores the count out of band, in a `n_<field>` byte, and pads
nothing; `leftpad` and `rightpad` store no count and recover the length by
scanning off the pad character. That difference is why only `rpascal`'s
abstraction is injective — see `docs/DIVERGENCE.md` §3.7. -/
inductive Strtype where
  | rpascal
  | leftpad
  | rightpad
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Same gap as `AttrTag`'s. -/
instance : LawfulBEq Strtype where
  eq_of_beq {a b} h := by revert h; cases a <;> cases b <;> decide
  rfl {a} := by cases a <;> rfl

def Strtype.name : Strtype → String
  | rpascal => "rpascal" | leftpad => "leftpad" | rightpad => "rightpad"

def Strtype.all : List Strtype := [.rpascal, .leftpad, .rightpad]

def Strtype.ofName? (s : String) : Option Strtype :=
  Strtype.all.find? (fun t => t.name == s)

/-- One attribute record's payload, one constructor per table.

`pad` is kept as the **text** `amc` writes (`"'0'"`, `"' '"`) rather than as a
character: it is a C character literal in the ssim file, the round trip is
byte-for-byte, and nothing AMCC emits yet interprets it. `strict` likewise —
`docs/DIVERGENCE.md` §3.7 records what it actually guards, which is naming
conventions and not values. -/
inductive AttrData where
  | inlary   (max : Nat)
  | smallstr (length : Nat) (strtype : Strtype) (pad : String) (strict : Bool)
  deriving DecidableEq, Repr, Inhabited

def AttrData.tag : AttrData → AttrTag
  | .inlary _      => .inlary
  | .smallstr .. => .smallstr

/-- One attribute record: which field it is about, and its payload. -/
structure Attr where
  ctype : Ident
  field : Ident
  data  : AttrData
  deriving DecidableEq, Repr, Inhabited

/-- **Which attribute record a reftype requires**, if any. This is the whole
requirement table; `checkAttr` turns it into the named error. -/
def Reftype.needsAttr : Reftype → Option AttrTag
  | .Inlary   => some .inlary
  | .Smallstr => some .smallstr
  | _         => none

/-- The ctypes of one schema, **in declaration order**. Order is meaningful:
a layout-carrying field may only name a ctype declared earlier. -/
structure Db where
  ctypes : List Ctype
  /-- The per-field attribute records, in file order. -/
  attrs  : List Attr := []
  /-- The database ctype, if there is one: `amc`'s `FDb`, the single global
  whose fields are the pools and the indexes. -/
  root   : Option Ident := none
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Db

def find? (d : Db) (n : Ident) : Option Ctype :=
  d.ctypes.find? (fun c => c.name == n)

def names (d : Db) : List Ident := d.ctypes.map Ctype.name

/-- A `find?` hit names what was asked for. Small, but every lowering proof
needs it: `fieldTy` builds `.strct ac.name` and the obligations are about
`f.arg`. -/
theorem find?_name {d : Db} {n : Ident} {c : Ctype} (h : d.find? n = some c) :
    c.name = n := by
  simp only [find?] at h
  have := List.find?_some h
  simpa using this

/-- **A ctype in a duplicate-free `Db` is what `find?` finds.** The converse of
`find?_name`, and the one that needs distinctness: `find?` returns the *first*
match, so without it a later ctype of the same name would be invisible. -/
theorem find?_of_mem_pairwise : ∀ (l : List Ctype),
    (l.map Ctype.name).Pairwise (· ≠ ·) → ∀ c ∈ l,
      l.find? (fun x => x.name == c.name) = some c
  | [], _, c, hc => absurd hc (by simp)
  | a :: l, hp, c, hc => by
    rw [List.map_cons, List.pairwise_cons] at hp
    rcases List.mem_cons.mp hc with rfl | hc'
    · simp [List.find?]
    · have hne : a.name ≠ c.name := hp.1 c.name (List.mem_map_of_mem hc')
      simp only [List.find?, beq_eq_false_iff_ne.mpr hne]
      exact find?_of_mem_pairwise l hp.2 c hc'

/-! ### The join, and the typed views over it -/

/-- **The join.** One field's record from one attribute table. The tag is part
of the key, so two tables may both carry a record for the same field — which
is what `bitfld` over a `Val` field will need. -/
def attr? (d : Db) (tag : AttrTag) (owner f : Ident) : Option AttrData :=
  (d.attrs.find? (fun a =>
    a.ctype == owner && a.field == f && a.data.tag == tag)).map Attr.data

/-- A joined record belongs to the table it was asked for. Needed wherever a
view has to rule out the wrong payload. -/
theorem attr?_tag {d : Db} {tag : AttrTag} {owner f : Ident} {a : AttrData}
    (h : d.attr? tag owner f = some a) : a.tag = tag := by
  simp only [attr?, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, ha⟩ := h
  have := List.find?_some hr
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  rw [← ha]; exact this.2

/-- The declared bound on one `Inlary` field. -/
def inlaryMax? (d : Db) (owner f : Ident) : Option Nat :=
  match d.attr? .inlary owner f with
  | some (.inlary n) => some n
  | _                => none

/-- The declared shape of one `Smallstr` field. -/
def smallstr? (d : Db) (owner f : Ident) :
    Option (Nat × Strtype × String × Bool) :=
  match d.attr? .smallstr owner f with
  | some (.smallstr n st pad strict) => some (n, st, pad, strict)
  | _                                => none

/-- **A joined `inlary` record always yields a bound.** The tag is part of the
key, so the payload cannot be a `smallstr`; the `_ => none` arm of
`inlaryMax?` is unreachable and this is what says so. -/
theorem inlaryMax?_of_attr? {d : Db} {owner f : Ident} {a : AttrData}
    (h : d.attr? .inlary owner f = some a) :
    ∃ n, a = .inlary n ∧ d.inlaryMax? owner f = some n := by
  have ht := attr?_tag h
  cases a with
  | inlary n => exact ⟨n, rfl, by simp [inlaryMax?, h]⟩
  | smallstr => exact absurd ht (by simp [AttrData.tag])

end Db

/-! ## Builtins

`u8`, `u32`, `u64` and `bool` are ctypes, declared first so that every user
ctype may name them. `char` is `u8`'s alias, because `dmmeta.field` writes
`arg:char` for every `Smallstr` and `amc` emits `u8` for it — the schema's
spelling and the emitted type differ, and this is where they meet. -/

def builtins : List Ctype :=
  [ { name := "u8",   scalar := some .u8 }
  , { name := "char", scalar := some .u8 }
  , { name := "u32",  scalar := some .u32 }
  , { name := "u64",  scalar := some .u64 }
  , { name := "bool", scalar := some .bool } ]

/-- A `Db` with the builtins prepended, which is what the checker and the
lowering both work against. -/
def Db.withBuiltins (d : Db) : Db :=
  { d with ctypes := builtins ++ d.ctypes }

/-! ## Lowering to the C subset

What a field becomes in the generated struct. `none` where the reftype has no
inline representation of its own — an xref lives in the *database* ctype, not
in the row. -/

def cKeywords : List String :=
  [ "auto", "break", "case", "char", "const", "continue", "default", "do",
    "double", "else", "enum", "extern", "float", "for", "goto", "if", "inline",
    "int", "long", "register", "restrict", "return", "short", "signed",
    "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned",
    "void", "volatile", "while", "_Bool", "bool", "true", "false", "NULL",
    "uint8_t", "uint16_t", "uint32_t", "uint64_t" ]

/-! ## Mangling a qualified name into a C identifier

`dmmeta` names are namespace-qualified — `abt.FArch`, `dmmeta.Ctype` — and a
dot is not a C identifier character. `docs/CONFORMANCE.md` measured this as
gating **4518 of 5659 real fields and 1381 of 1420 real ctypes**, eleven times
the largest missing reftype, so it is not an edge case: without a mapping the
whole corpus is unreachable for a reason that has nothing to do with data
structures.

The mapping is `amc`'s own, transcribed from `amc::strptr_PrintCppIdent`
(`cpp/amc/main.cpp`), in its order:

1. an empty name, or one starting with a digit, gets a leading `_`;
2. if the result is a keyword, a trailing `_` (`amc` masks C++ keywords; we
   mask C's, since that is what we emit);
3. `+` becomes `P`, `'` becomes `A`, `"` becomes `Q`, and
   `/ . - < > ! @ # $ % ^ & * ( ) : ;` space `| [ ] { }` all become `_`.

## It is deliberately not injective

`a.b_c` and `a_b.c` both mangle to `a_b_c`, and across 1420 real ctypes that
will actually happen. The response is **not** a cleverer encoding: it is to
let the collision reach the checker that already exists. `check` below gains
one clause on mangled ctype names, and `qualName` — which every generated
symbol is built from — mangles both halves, so the `dups (qualNames …)` clause
landed in 47ecf60 catches field-level collisions unchanged. A dumb mapping
plus a checker that already works beats an injective encoding nobody can read
in the generated C. -/

/-- `amc`'s character substitution. Characters outside the table pass through,
which is what lets `isCIdent` reject the ones no mapping can rescue. -/
def transChar (c : Char) : Char :=
  if c == '+' then 'P'
  else if c == '\'' then 'A'
  else if c == '"' then 'Q'
  else if "/.-<>!@#$%^&*():; |[]{}".toList.contains c then '_'
  else c

/-- The C identifier a schema name is emitted as. -/
def mangle (n : String) : String :=
  let lead : String :=
    match n.toList with
    | []     => "_"
    | c :: _ => if c.isDigit then "_" else ""
  let s := lead ++ n
  let s := if cKeywords.contains s then s ++ "_" else s
  String.ofList (s.toList.map transChar)

/-- The storage type of a field, resolved against the db. `owner` is the ctype
the field belongs to, needed because an `Inlary`'s bound is keyed by both. -/
def fieldTy (d : Db) (owner : Ident) (f : Field) : Option CSubset.Ty := do
  let c ← d.find? f.arg
  let base : CSubset.Ty :=
    match c.scalar with
    | some t => .scalar t
    | none   => .strct (mangle c.name)
  match f.reftype with
  | .Val | .Base  => some base
  -- A key at scalar argument is the key itself; at record argument it is a
  -- reference to that record.
  | .Pkey         => if c.scalar.isSome then some base else some (.ptr base)
  | .Upptr | .Ptr => some (.ptr base)
  -- The bounded inline array: `<arg> f[max];` inside the owning struct. This
  -- is the fixed-capacity case, now one storage choice among many rather than
  -- the shape of the whole model.
  | .Inlary       => (d.inlaryMax? owner f.name).map (fun n => .arr base n)
  -- The inline string. `amc` sizes the array `N` for the padded shapes and
  -- `N + 1` for `rpascal` ("extra 1 byte is required by rpascal",
  -- `cpp/amc/smallstr.cpp`). The element type is `u8` whatever the schema
  -- writes for `arg` — `dmmeta` writes `char` — because that is what `amc`
  -- emits. The `rpascal` count byte is not here: it is the template's state,
  -- added to the lowered struct the way `Llist` adds its links.
  | .Smallstr     =>
    (d.smallstr? owner f.name).map (fun sh =>
      .arr (.scalar .u8) (match sh.2.1 with | .rpascal => sh.1 + 1 | _ => sh.1))
  | _             => none

/-- The struct a record ctype lowers to: its inline fields, in order. -/
def structOf (d : Db) (c : Ctype) : CSubset.StructDef where
  name   := mangle c.name
  fields := c.fields.filterMap
              (fun f => (fieldTy d c.name f).map (fun t => (mangle f.name, t)))

/-! ## Lowering a whole `Db`

The layout half of code generation: every record ctype becomes a struct, and
the database ctype — if there is one — becomes the single global that holds
the pools, exactly as `amc` emits one `_db`. -/

/-- Every record ctype, as a struct, in declaration order. Builtins drop out
because they are scalars. -/
def genStructs (d : Db) : List CSubset.StructDef :=
  let full := d.withBuiltins
  full.ctypes.filterMap
    (fun c => if c.scalar.isSome then none else some (structOf full c))

/-- The single database instance, if a root ctype is declared. -/
def genGlobals (d : Db) : List CSubset.GlobalDef :=
  match d.root with
  | none   => []
  | some r => [{ name := "g_" ++ mangle r, ty := .strct (mangle r) }]

/-- The generated translation unit's **layout**: structs and storage, no
functions yet. -/
def genLayout (d : Db) : CSubset.Program where
  structs := genStructs d
  globals := genGlobals d
  funs    := []

/-! ## The checker

Same shape as `CSubset.Wf.check` and `Schema.check`: a list of violations, so
that a generator gets "which rule, where" rather than a bare `false`. -/

def isCIdent (s : String) : Bool :=
  match s.toList with
  | []      => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun d => d.isAlphanum || d == '_')
               && !cKeywords.contains s

/-- The field-name suffixes a template appends to a struct the layout pass
already emits: `Llist`'s links and flag, `Thash`'s bucket array, `Pool`'s free
list, and the count both structures keep.

A *blanket* reservation — reject any field ending in one of these — was tried
first and is wrong: this file's own `child_row.zd_next` is a legitimate
`Llist` field, and the corpus has `c_next`, `line_n` and `prev_head`. The
collision only exists when the stripped prefix is **itself a declared field
name**, because that is the only way a template generates the colliding name.
`clashesGenerated` below is that narrower test. -/
def genSuffixes : List String :=
  [ "_next", "_prev", "_inlist", "_inhash", "_buckets", "_head", "_tail", "_n"
  , "_freenext", "_freehead" ]

/-- Strip a suffix, if it is one. Reversed, so the suffix test is a **prefix**
test — the same trick `Templates.NameWf.append_ne_rev` uses, and for the same
reason: `List.isPrefixOf` is structural and reduces, where a suffix test needs
length arithmetic. -/
def dropSuffix (sfx n : List Char) : Option (List Char) :=
  if sfx.reverse.isPrefixOf n.reverse then some (n.take (n.length - sfx.length))
  else none

/-- The prefixes a template puts *in front* of a field's C name. `amc` names
an `rpascal` smallstr's count byte `n_$name`, so this is the mirror of
`genSuffixes` and needs the mirror test. -/
def genPrefixes : List String := ["n_"]

/-- Strip a prefix, if it is one. -/
def dropPrefix (pfx n : List Char) : Option (List Char) :=
  if pfx.isPrefixOf n then some (n.drop pfx.length) else none

/-- **Would a template generate this name?** `n` collides when stripping a
generated suffix — or prefix — leaves a name that is itself declared:
`zdl_todo_next` against a field `zdl_todo`, `n_ch` against a field `ch`. A
field merely *ending* in `_next` or *starting* with `n_` is fine, which is why
the test is not the blanket one. -/
def clashesGenerated (names : List Ident) (n : Ident) : Bool :=
  genSuffixes.any (fun sfx =>
    match dropSuffix sfx.toList n.toList with
    | none     => false
    | some pre => names.contains (String.ofList pre))
  || genPrefixes.any (fun pfx =>
    match dropPrefix pfx.toList n.toList with
    | none      => false
    | some rest => names.contains (String.ofList rest))

/-- Reserved for the generator's own locals. -/
def isReservedName (n : Ident) : Bool := n.toList.head? == some '_'

def dups (xs : List Ident) : List Ident :=
  (xs.filter (fun x => 1 < xs.countP (fun y => y == x))).eraseDups

/-- **Is one attribute record's payload usable?** One arm per table. The
join, the requirement and the missing-record error are `checkAttr`'s and are
shared; only this is per-table.

The `Inlary` bound becomes a C array size, and the subset's obligation 3 rules
out a zero-length array and one past the `u32` range. That arm was originally
only an `isNone` test, which let a schema with `max:0` pass `Dmmeta.check` and
then be *rejected* by `CSubset.Wf.check` — the front end running ahead of the
back end, and the reason `Layout.layoutWellFormed` could not be proved as
stated. See `PROGRESS.md` under Decisions.

The `rpascal` ceiling of 255 is `amc`'s own: `cpp/amc/smallstr.cpp` reports
`smallstr.toobig` above it, because the count is stored in one byte. -/
def checkAttrData (owner fname : Ident) : AttrData → List String
  | .inlary n =>
      if 0 < n && n < CSubset.Wf.u32Bound then []
      else [s!"{owner}.{fname}: Inlary bound {n} is not a legal array size"]
  | .smallstr n st _ _ =>
      (if 0 < n && n < CSubset.Wf.u32Bound then []
       else [s!"{owner}.{fname}: smallstr length {n} is not a legal array size"])
      ++ (if st == .rpascal && 255 < n then
            [s!"{owner}.{fname}: rpascal smallstr length {n} exceeds 255"]
          else [])

/-- **A field that claims a reftype whose attribute record is missing is a
named error** — for every table at once, from `Reftype.needsAttr`.

This is the clause the join exists for. Before it there was one bespoke test
for `Inlary`, and each of `Smallstr`, `Bitfld`, `Charset`, `lenfld`, `substr`
and `fconst` would have added another. -/
def checkAttr (d : Db) (owner : Ident) (f : Field) : List String :=
  match f.reftype.needsAttr with
  | none     => []
  | some tag =>
    match d.attr? tag owner f.name with
    | none   =>
      [s!"{owner}.{f.name}: {f.reftype.name} needs a dmmeta.{tag.name} record"]
    | some a => checkAttrData owner f.name a

/-- **The `Inlary` facts, back out of the generic clause.** `Layout` and every
template's well-formedness proof consume exactly this shape, and consumed it
from the bespoke clause before the join existed — so it is stated once here
rather than re-derived at each use.

checked by: `lake build` -/
theorem inlary_facts_of_checkAttr {d : Db} {owner : Ident} {f : Field}
    (hr : f.reftype = .Inlary) (h : checkAttr d owner f = []) :
    ∃ n, d.inlaryMax? owner f.name = some n ∧ 0 < n ∧ n < CSubset.Wf.u32Bound := by
  simp only [checkAttr, hr, Reftype.needsAttr] at h
  cases ha : d.attr? .inlary owner f.name with
  | none => rw [ha] at h; simp at h
  | some a =>
    obtain ⟨n, rfl, hn⟩ := Db.inlaryMax?_of_attr? ha
    refine ⟨n, hn, ?_⟩
    rw [ha] at h
    simp only [checkAttrData] at h
    by_cases hb : (0 < n && n < CSubset.Wf.u32Bound) = true
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      exact hb
    · simp [hb] at h

/-- The `smallstr` companion of `inlaryMax?_of_attr?`. -/
theorem smallstr?_of_attr? {d : Db} {owner f : Ident} {a : AttrData}
    (h : d.attr? .smallstr owner f = some a) :
    ∃ n st pad strict, a = .smallstr n st pad strict
      ∧ d.smallstr? owner f = some (n, st, pad, strict) := by
  have ht := Db.attr?_tag h
  cases a with
  | smallstr n st pad strict =>
    exact ⟨n, st, pad, strict, rfl, by simp [Db.smallstr?, h]⟩
  | inlary => exact absurd ht (by simp [AttrData.tag])

/-- **The `Smallstr` facts, back out of the generic clause**, in the shape the
layout obligation wants: the *array size* `fieldTy` builds is a legal C array
size. It is `N` for a padded string and `N + 1` for `rpascal`, and the
`rpascal` case needs `amc`'s own 255 ceiling and not merely the `u32` bound —
without it `N + 1` could be `u32Bound` exactly.

checked by: `lake build` -/
theorem smallstr_facts_of_checkAttr {d : Db} {owner : Ident} {f : Field}
    (hr : f.reftype = .Smallstr) (h : checkAttr d owner f = []) :
    ∃ n st pad strict, d.smallstr? owner f.name = some (n, st, pad, strict)
      ∧ 0 < (match st with | .rpascal => n + 1 | _ => n)
      ∧ (match st with | .rpascal => n + 1 | _ => n) < CSubset.Wf.u32Bound := by
  simp only [checkAttr, hr, Reftype.needsAttr] at h
  cases ha : d.attr? .smallstr owner f.name with
  | none => rw [ha] at h; simp at h
  | some a =>
    obtain ⟨n, st, pad, strict, rfl, hview⟩ := smallstr?_of_attr? ha
    refine ⟨n, st, pad, strict, hview, ?_⟩
    rw [ha] at h
    simp only [checkAttrData, List.append_eq_nil_iff] at h
    obtain ⟨hsz, hbig⟩ := h
    have hn : 0 < n ∧ n < CSubset.Wf.u32Bound := by
      by_cases hb : (0 < n && n < CSubset.Wf.u32Bound) = true
      · simpa only [Bool.and_eq_true, decide_eq_true_eq] using hb
      · simp [hb] at hsz
    cases st with
    | rpascal =>
      have h255 : ¬ (255 < n) := by
        by_cases hb : 255 < n
        · simp [hb] at hbig
        · exact hb
      exact ⟨Nat.succ_pos n, by simp only [CSubset.Wf.u32Bound]; omega⟩
    | leftpad  => exact hn
    | rightpad => exact hn

/-- Check one field against the ctypes declared **before** its owner. -/
def checkField (d : Db) (earlier : List Ident) (owner : Ident) (f : Field) :
    List String :=
  (if isCIdent (mangle f.name) then []
   else [s!"{owner}.{f.name}: does not mangle to a legal C identifier"])
  ++ (if isReservedName (mangle f.name) then
        [s!"{owner}.{f.name}: leading underscore is reserved for generated locals"]
      else [])
  ++ (match d.find? f.arg with
      | none => [s!"{owner}.{f.name}: unknown ctype {f.arg}"]
      | some c =>
        -- A layout-carrying field embeds its argument, so the argument's
        -- layout must already be known. A pointer, pool or index field needs
        -- only the name, which is what lets a ctype refer to itself.
        (if f.reftype.layoutDep && !earlier.contains f.arg then
           [s!"{owner}.{f.name}: {f.arg} is not declared earlier, and {f.reftype.name} needs its layout"]
         else [])
        ++ (if f.reftype == .Val && c.scalar.isNone && c.fields.isEmpty then
              [s!"{owner}.{f.name}: {f.arg} has no fields"]
            else [])
        -- A pointer or an index needs something to point at. See
        -- `Reftype.needsRecordArg`: without this, an `Upptr` at `u64` was
        -- accepted here and rejected by the C-subset checker.
        ++ (if f.reftype.needsRecordArg && c.scalar.isSome then
              [s!"{owner}.{f.name}: {f.reftype.name} needs a record, and {f.arg} is a machine scalar"]
            else [])
        ++ checkAttr d owner f)

def checkCtype (d : Db) (earlier : List Ident) (c : Ctype) : List String :=
  -- Builtin ctypes are named after the machine types they denote (`bool` is a
  -- ctype in `dmmeta` too), so the C-identifier rule applies to user ctypes,
  -- which are the ones that become emitted struct names.
  (if c.scalar.isSome || isCIdent (mangle c.name) then []
   else [s!"ctype {c.name}: does not mangle to a legal C identifier"])
  ++ (dups (c.fields.map Field.name)).map
       (fun n => s!"{c.name}: duplicate field {n}")
  ++ (match c.fields.filter (fun f => f.reftype == .Base) with
      | [] | [_] => []
      | _        => [s!"{c.name}: more than one Base field"])
  ++ (if c.scalar.isSome && !c.fields.isEmpty then
        [s!"{c.name}: a builtin scalar ctype may not have fields"]
      else [])
  ++ c.fields.flatMap (checkField d earlier c.name)

/-- The C name a field contributes to every generated symbol built from it:
`<ctype>_<field>`. Every template prefixes its operation names with this, so
two fields sharing it collide in the emitted translation unit however few
templates run. -/
def qualName (c : Ident) (f : Ident) : Ident := mangle c ++ "_" ++ mangle f

/-- Every field's C name, across the schema — what a generated field name
could collide with. -/
def fieldCNames (d : Db) : List Ident :=
  d.ctypes.flatMap (fun c => c.fields.map (fun f => mangle f.name))

/-- Every `<ctype>_<field>` in the schema. -/
def qualNames (d : Db) : List Ident :=
  d.ctypes.flatMap (fun c => c.fields.map (fun f => qualName c.name f.name))

/-- Violations, empty when the schema is well-formed. Checked against the db
**with builtins**, so `u32` and friends resolve. -/
def check (d : Db) : List String :=
  let full := d.withBuiltins
  (dups full.names).map (fun n => s!"duplicate ctype: {n}")
    -- `c ++ "_" ++ f` is **not** injective in the pair: ctype `a` with field
    -- `b_c` and ctype `a_b` with field `c` both qualify to `a_b_c`, and every
    -- generated symbol is built by suffixing that. Without this clause a legal
    -- schema can emit two functions with one name — and the accessor laws in
    -- `Templates/Upptr.lean` and friends, which assume the name resolves to
    -- the definition, would be vacuous for it with nothing to notice.
    -- Mangling is not injective — `a.b` and `a_b` both become `a_b` — so the
    -- collision it reintroduces is caught here rather than dodged inside the
    -- mapping. `docs/CONFORMANCE.md` §the headline is why the mapping exists.
    ++ (dups (full.ctypes.map (fun c => mangle c.name))).map
         (fun n => s!"two ctypes generate the same C name: {n}")
    ++ (dups (qualNames full)).map
         (fun n => s!"two fields generate the same C name: {n}")
    ++ (match d.root with
        | none   => []
        | some r =>
          match full.find? r with
          | none   => [s!"root ctype {r} is not declared"]
          | some c => if c.scalar.isSome then [s!"root ctype {r} is a scalar"] else [])
    ++ full.ctypes.zipIdx.flatMap (fun ci =>
        checkCtype full ((full.ctypes.take ci.2).map Ctype.name) ci.1)
    -- A declared field whose name is one a template would *generate* on the
    -- same struct: `task_row.zdl_todo_next` against `TaskDb.zdl_todo`. The
    -- struct then has two fields of one name, which `Dmmeta.check` accepted
    -- and `CSubset.Wf.check` rejected until this clause existed.
    ++ full.ctypes.flatMap (fun c => c.fields.filterMap (fun f =>
         if clashesGenerated (fieldCNames full) (mangle f.name) then
           some s!"{c.name}.{f.name}: collides with a field a template generates"
         else none))

def wf (d : Db) : Bool := (check d).isEmpty

/-! ## Examples

Small, and chosen to exercise what the old model could not express. -/

namespace Examples

/-- A record with a key and two values — the shape the array-table template
consumes today, now written as a ctype whose fields name other ctypes. -/
def orderRow : Ctype where
  name   := "order_row"
  fields :=
    [ { name := "id",    arg := "u64", reftype := .Pkey }
    , { name := "price", arg := "u64", reftype := .Val }
    , { name := "qty",   arg := "u64", reftype := .Val } ]

/-- A parent record. -/
def levelRow : Ctype where
  name   := "level_row"
  fields := [{ name := "price", arg := "u64", reftype := .Pkey }]

/-- A child that **points at another ctype** — inexpressible before this file.
`p_level` is an up-pointer; `zd_child` is an intrusive list *of the same
ctype*, which is legal precisely because a list does not carry layout. -/
def childRow : Ctype where
  name   := "child_row"
  fields :=
    [ { name := "id",      arg := "u64",       reftype := .Pkey }
    , { name := "p_level", arg := "level_row", reftype := .Upptr }
    , { name := "zd_next", arg := "child_row", reftype := .Llist } ]

/-- The database ctype: its fields are the pools and the indexes, exactly as
`amc`'s `FDb` is a ctype whose fields are `Lary`s and `Thash`es. -/
def db : Ctype where
  name   := "Db"
  fields :=
    [ { name := "level",     arg := "level_row", reftype := .Lary }
    , { name := "child",     arg := "child_row", reftype := .Lary }
    , { name := "ind_child", arg := "child_row", reftype := .Thash } ]

def relational : Db := { ctypes := [levelRow, childRow, db], root := some "Db" }

/-- checked by: `lake build` -/
example : check { ctypes := [orderRow] } = [] := rfl

/-- **Two fields that print to the same C name are rejected.** `a`/`b_c` and
`a_b`/`c` both qualify to `a_b_c`, and every generated symbol is that name with
a suffix — so without this the emitted translation unit would declare two
functions called `a_b_c_Get`, and the accessor laws, which assume the name
resolves to *the* definition, would be vacuous for a legal schema.

checked by: `lake build` -/
example : check
    { ctypes :=
        [ { name := "a",   fields := [{ name := "b_c", arg := "u32",
                                        reftype := .Val }] }
        , { name := "a_b", fields := [{ name := "c",   arg := "u32",
                                        reftype := .Val }] } ] }
    = ["two fields generate the same C name: a_b_c"] := rfl

/-- The same two ctypes with names that do not collide are accepted, so the
clause rejects the collision and not the shape.

checked by: `lake build` -/
example : check
    { ctypes :=
        [ { name := "a",   fields := [{ name := "bc",  arg := "u32",
                                        reftype := .Val }] }
        , { name := "a_b", fields := [{ name := "c",   arg := "u32",
                                        reftype := .Val }] } ] }
    = [] := rfl

/-- **An up-pointer needs something to point at.** This clause was missing,
and its absence was the second hole the every-schema proofs found: the schema
below passed `Dmmeta.check` and the generated accessors failed
`CSubset.Wf.check` with four type errors, because `row->f = NULL` has type
`u64 *` in the struct and `parent *` in the emitted assignment.

checked by: `lake build` -/
example : check
    { ctypes :=
        [ { name := "child_row"
          , fields := [{ name := "p_x", arg := "u64", reftype := .Upptr }] } ] }
    = ["child_row.p_x: Upptr needs a record, and u64 is a machine scalar"] := rfl

/-- The same for an index: threading machine scalars on a list is not a
thing the templates can emit. -/
example : check
    { ctypes :=
        [ { name := "D"
          , fields := [{ name := "zdl", arg := "u32", reftype := .Llist }] } ] }
    = ["D.zdl: Llist needs a record, and u32 is a machine scalar"] := rfl

/-- `Pkey` is deliberately exempt: a key *is* a scalar in the common case, and
`fieldTy` lowers it to the scalar rather than to a pointer. -/
example : check
    { ctypes :=
        [ { name := "r", fields := [{ name := "id", arg := "u64",
                                      reftype := .Pkey }] } ] } = [] := rfl

/-! ### Names a template would generate -/

/-- **A field named what a template generates is rejected.** `TaskDb.zdl_todo`
is an `Llist`, so the element struct gains `zdl_todo_next`; a schema declaring
that field too produced a struct with two fields of one name, which
`Dmmeta.check` accepted and `CSubset.Wf.check` rejected.

checked by: `lake build` -/
example : check
    { ctypes :=
        [ { name := "task_row"
          , fields := [ { name := "id", arg := "u64", reftype := .Pkey }
                      , { name := "zdl_todo_next", arg := "u64",
                          reftype := .Val } ] }
        , { name := "TaskDb"
          , fields := [{ name := "zdl_todo", arg := "task_row",
                         reftype := .Llist }] } ]
      , root := some "TaskDb" }
    = ["task_row.zdl_todo_next: collides with a field a template generates"] := rfl

/-- **A field merely *ending* in a generated suffix is fine.** The blanket rule
was tried first and rejected this file's own `child_row.zd_next`, and would
reject `c_next`, `line_n` and `prev_head` in the real corpus. The collision
needs the stripped prefix to be a declared field name.

checked by: `lake build` -/
example : check
    { ctypes :=
        [ { name := "r"
          , fields := [{ name := "zd_next", arg := "u64", reftype := .Val }] } ] }
    = [] := rfl

/-! ### Mangling, against `amc::strptr_PrintCppIdent` -/

/-- A plain name is its own C identifier. -/
example : mangle "task_row" = "task_row" := rfl
/-- A namespace-qualified name is the whole point. -/
example : mangle "abt.FArch" = "abt_FArch" := rfl
example : mangle "dmmeta.Ctype" = "dmmeta_Ctype" := rfl
/-- The three examples in `amc`'s own comment. -/
example : mangle "ab.cd" = "ab_cd" := rfl
example : mangle "+-$" = "P__" := rfl
example : mangle "int" = "int_" := rfl
/-- ...and the two degenerate ones. `amc` masks C++ keywords; we mask C's,
because that is what we emit. -/
example : mangle "" = "_" := rfl
example : mangle "3x" = "_3x" := rfl
/-- A character no substitution rescues passes through, and the checker then
rejects it by name rather than the mapping silently swallowing it. -/
example : mangle "a~b" = "a~b" := rfl

/-! ### The collision mangling reintroduces, and where it is caught -/

/-- **`a.b` and `a_b` mangle to the same C name.** The mapping does not dodge
this; the checker rejects it, which is the same discipline the field-level
qualified-name clause has used since 47ecf60.

checked by: `lake build` -/
example : check
    { ctypes := [ { name := "a.b", fields := [{ name := "x", arg := "u32",
                                                reftype := .Val }] }
                , { name := "a_b", fields := [{ name := "y", arg := "u32",
                                                reftype := .Val }] } ] }
    = ["two ctypes generate the same C name: a_b"] := rfl

/-- And the field-level form, now reachable through the dot: `a.b_c` and
`a_b.c` both qualify to `a_b_c`. -/
example : check
    { ctypes := [ { name := "a",   fields := [{ name := "b.c", arg := "u32",
                                                reftype := .Val }] }
                , { name := "a.b", fields := [{ name := "c",   arg := "u32",
                                                reftype := .Val }] } ] }
    = ["two fields generate the same C name: a_b_c"] := rfl

/-- A qualified schema is otherwise accepted, which is the whole point of the
change: this one was rejected outright before.

checked by: `lake build` -/
example : check
    { ctypes :=
        [ { name := "dev.Arch", fields := [{ name := "arch", arg := "u64",
                                             reftype := .Pkey }] }
        , { name := "abt.FArch"
          , fields := [{ name := "p_arch", arg := "dev.Arch",
                         reftype := .Upptr }] } ] } = [] := rfl

/-- ...and it lowers to C identifiers. -/
example : (genStructs
    { ctypes :=
        [ { name := "dev.Arch", fields := [{ name := "arch", arg := "u64",
                                             reftype := .Pkey }] }
        , { name := "abt.FArch"
          , fields := [{ name := "p_arch", arg := "dev.Arch",
                         reftype := .Upptr }] } ] }).map
    (fun sd => (sd.name, sd.fields.map Prod.fst))
    = [("dev_Arch", ["arch"]), ("abt_FArch", ["p_arch"])] := rfl

-- A ctype referring to other ctypes, one of them itself, is accepted. `#guard`
-- rather than `rfl`: `check` now mangles every name and tests every field
-- against the reserved suffixes, and kernel-normalising that for the largest
-- example is past the boundary `CLAUDE.md` draws.
-- checked by: `lake build`
#guard check relational == []

/-- The row lowers to the struct the C subset expects. `Pkey` at scalar
argument stays a scalar; `Upptr` becomes a pointer; the `Llist` link has no
inline representation of its own yet, so it contributes no field.

checked by: `lake build` -/
example : structOf relational.withBuiltins Examples.childRow =
    { name   := "child_row"
    , fields := [("id", .scalar .u64), ("p_level", .ptr (.strct "level_row"))] } := rfl

/-- An unknown `arg` is caught. -/
example : check { ctypes := [{ name := "a", fields := [{ name := "f", arg := "nope", reftype := .Val }] }] }
    = ["a.f: unknown ctype nope"] := rfl

/-- A `Val` field embeds its argument, so a forward reference is rejected —
this is what keeps struct nesting acyclic. -/
example : check { ctypes :=
    [ { name := "a", fields := [{ name := "b", arg := "b", reftype := .Val }] }
    , { name := "b", fields := [{ name := "x", arg := "u32", reftype := .Val }] } ] }
    = ["a.b: b is not declared earlier, and Val needs its layout"] := rfl

/-- The *same* forward reference through an up-pointer is fine: a pointer
needs the name, not the layout. -/
example : check { ctypes :=
    [ { name := "a", fields := [{ name := "p_b", arg := "b", reftype := .Upptr }] }
    , { name := "b", fields := [{ name := "x", arg := "u32", reftype := .Val }] } ] }
    = [] := rfl

/-- A field may not shadow the generated-local namespace. -/
example : check { ctypes := [{ name := "a", fields := [{ name := "_i", arg := "u32", reftype := .Val }] }] }
    = ["a._i: leading underscore is reserved for generated locals"] := rfl

/-- Two `Base` fields is not single inheritance. -/
example : check { ctypes :=
    [ { name := "b", fields := [{ name := "x", arg := "u32", reftype := .Val }] }
    , { name := "c", fields := [{ name := "y", arg := "u32", reftype := .Val }] }
    , { name := "a", fields := [{ name := "b", arg := "b", reftype := .Base },
                                { name := "c", arg := "c", reftype := .Base }] } ] }
    = ["a: more than one Base field"] := rfl

/-- The fixed-capacity table, expressed in this model: a database ctype whose
`row` field is an `Inlary` bounded at 4.

Note where the capacity is. It belongs to the **storage field**, not to
`order_row` — the row type says nothing about how many of them exist, which is
what lets the same ctype be held in a bounded array here and in a growable
pool elsewhere. -/
def boundedDb : Db where
  ctypes :=
    [ orderRow
    , { name   := "OrderDb"
      , fields := [{ name := "row", arg := "order_row", reftype := .Inlary }] } ]
  attrs  := [{ ctype := "OrderDb", field := "row", data := .inlary 4 }]
  root   := some "OrderDb"

/-- The dynamic chunk pool table: a database ctype with a Tpool field. -/
def tpoolDb : Db where
  ctypes :=
    [ orderRow
    , { name   := "OrderDb"
      , fields := [{ name := "row", arg := "order_row", reftype := .Tpool }] } ]
  root   := some "OrderDb"

/-- checked by: `lake build` -/
example : check boundedDb = [] := rfl
example : check tpoolDb = [] := rfl

/-- An `Inlary` without a declared bound is rejected: there is no capacity to
emit. -/
example : check { boundedDb with attrs := [] }
    = ["OrderDb.row: Inlary needs a dmmeta.inlary record"] := rfl

/-- And a bound that is not a legal C array size is rejected too.

This clause was **missing**, and its absence was a real hole rather than a
cosmetic one: `max:0` passed `Dmmeta.check` and `Layout.layoutCheck`, and the
generated program was then *rejected* by `CSubset.Wf.check` with
`"D.row: bad array size"`. The front end accepted what the back end could not
emit, which is the failure `docs/GOALS.md`'s standing rule is about, and it is
why `Layout.LayoutWellFormed` could not be proved as stated.

checked by: `lake build` -/
example : check { boundedDb with
      attrs := [{ ctype := "OrderDb", field := "row", data := .inlary 0 }] }
    = ["OrderDb.row: Inlary bound 0 is not a legal array size"] := rfl

/-- The other end of the range, where the bound would not survive the `u32`
literal the generator emits. -/
example : check { boundedDb with
      attrs := [{ ctype := "OrderDb", field := "row"
                , data := .inlary 4294967296 }] }
    = ["OrderDb.row: Inlary bound 4294967296 is not a legal array size"] := rfl

/-- A root that names nothing is rejected. -/
example : check { boundedDb with root := some "Nope" }
    = ["root ctype Nope is not declared"] := rfl

/-! ### The reftype table, spot-checked against `dmmeta/reftype.ssim` -/

/-- checked by: `lake build` -/
example : Reftype.stableAddresses .Lary = true := rfl
/-- The distinction `Amcc.Spec.Pool.moving_not_stable` proves is real. -/
example : Reftype.stableAddresses .Tary = false := rfl
/-- checked by: `lake build` -/
example : Reftype.isxref .Thash = true := rfl
example : Reftype.isxref .Ptrary = false := rfl
example : Reftype.usebasepool .Lary = true := rfl
example : Reftype.up .Upptr = true := rfl
example : Reftype.layoutDep .Val = true := rfl
example : Reftype.layoutDep .Llist = false := rfl

/-- `dmmeta/reftype.ssim` has thirty-six rows, and `Reftype.all` has
thirty-six entries. A constructor added without a line in `all` fails here.

checked by: `lake build` -/
example : Reftype.all.length = 36 := rfl

/-- `name` is injective on the vocabulary, so `ofName?` inverts it — which is
what the ssim front end needs and what makes a mistyped name a diagnostic
rather than a wrong reftype.

checked by: `lake build` -/
example : (Reftype.all.map Reftype.name).eraseDups.length = 36 := rfl

/-- checked by: `lake build` -/
example : Reftype.all.all (fun r => Reftype.ofName? r.name == some r) = true := rfl

end Examples

end Dmmeta

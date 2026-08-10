import Amcc.CSubset.Syntax

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
  /-- Array of pointers. -/
  | Ptrary
  /-- Bookkeeping counter over linked records. -/
  | Count
  deriving DecidableEq, Repr, Inhabited, BEq

namespace Reftype

/-- `dmmeta.reftype.isval` — the field stores its value inline. -/
def isval : Reftype → Bool
  | Val | Lary | Tary | Inlary | Tpool | Lpool | Blkpool | Malloc | Sbrk => true
  | _ => false

/-- `dmmeta.reftype.isxref` — the field is an index over another ctype's
records, maintained as those records come and go. -/
def isxref : Reftype → Bool
  | Thash | Llist | Bheap | Atree => true
  | _ => false

/-- `dmmeta.reftype.usebasepool` — the field obtains memory from a base pool,
so `dmmeta.basepool` composition applies to it. -/
def usebasepool : Reftype → Bool
  | Lary | Tary | Tpool | Lpool | Blkpool | Delptr | Thash | Bheap | Ptrary => true
  | _ => false

/-- `dmmeta.reftype.up` — the field points *up*, at a parent record. -/
def up : Reftype → Bool
  | Pkey | Base | Upptr => true
  | _ => false

/-- Storage provider: a field of this reftype is where records live. -/
def ispool : Reftype → Bool
  | Lary | Tary | Inlary | Tpool | Lpool | Blkpool | Malloc | Sbrk => true
  | _ => false

/-- **Does this field contribute to its ctype's layout?**

If so, the `arg` must be a ctype declared *earlier*, which is what makes
nesting acyclic — the schema-level form of the C subset's obligation 2.

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

/-- The reftype's name, for error messages. A plain function rather than
`repr`: `Repr` produces a `Std.Format`, and rendering one does not reduce in
the kernel, which would cost every checker test in this file its `rfl`. -/
def name : Reftype → String
  | Val => "Val" | Pkey => "Pkey" | Base => "Base" | Upptr => "Upptr"
  | Ptr => "Ptr" | Lary => "Lary" | Tary => "Tary" | Inlary => "Inlary"
  | Tpool => "Tpool" | Lpool => "Lpool" | Blkpool => "Blkpool"
  | Malloc => "Malloc" | Sbrk => "Sbrk" | Delptr => "Delptr"
  | Thash => "Thash" | Llist => "Llist" | Bheap => "Bheap" | Atree => "Atree"
  | Ptrary => "Ptrary" | Count => "Count"

/-- The whole vocabulary, in `dmmeta/reftype.ssim`'s order. Written out rather
than derived because a front end has to turn a *name* back into a reftype, and
the two directions must not drift: `Checks` below pins that `all` has twenty
entries and that `name` is injective on it, so a new constructor that is not
added here fails the count. -/
def all : List Reftype :=
  [ Val, Pkey, Base, Upptr, Ptr, Lary, Tary, Inlary, Tpool, Lpool, Blkpool
  , Malloc, Sbrk, Delptr, Thash, Llist, Bheap, Atree, Ptrary, Count ]

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

/-- `dmmeta.inlary` — the bound on an `Inlary` field's inline array.

A separate record keyed by field, as in `dmmeta`, rather than an extra column
on `Field`: attributes that apply to one reftype live in their own table, which
is what lets the vocabulary grow without disturbing every field. -/
structure Inlary where
  ctype : Ident
  field : Ident
  max   : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The ctypes of one schema, **in declaration order**. Order is meaningful:
a layout-carrying field may only name a ctype declared earlier. -/
structure Db where
  ctypes : List Ctype
  /-- Sizes for the `Inlary` fields. -/
  inlary : List Inlary := []
  /-- The database ctype, if there is one: `amc`'s `FDb`, the single global
  whose fields are the pools and the indexes. -/
  root   : Option Ident := none
  deriving DecidableEq, Repr, Inhabited

namespace Db

def find? (d : Db) (n : Ident) : Option Ctype :=
  d.ctypes.find? (fun c => c.name == n)

def names (d : Db) : List Ident := d.ctypes.map Ctype.name

/-- The declared bound on one `Inlary` field. -/
def inlaryMax? (d : Db) (owner f : Ident) : Option Nat :=
  (d.inlary.find? (fun i => i.ctype == owner && i.field == f)).map Inlary.max

end Db

/-! ## Builtins

`u32`, `u64` and `bool` are ctypes, declared first so that every user ctype may
name them. -/

def builtins : List Ctype :=
  [ { name := "u32",  scalar := some .u32 }
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

/-- The storage type of a field, resolved against the db. `owner` is the ctype
the field belongs to, needed because an `Inlary`'s bound is keyed by both. -/
def fieldTy (d : Db) (owner : Ident) (f : Field) : Option CSubset.Ty := do
  let c ← d.find? f.arg
  let base : CSubset.Ty :=
    match c.scalar with
    | some t => .scalar t
    | none   => .strct c.name
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
  | _             => none

/-- The struct a record ctype lowers to: its inline fields, in order. -/
def structOf (d : Db) (c : Ctype) : CSubset.StructDef where
  name   := c.name
  fields := c.fields.filterMap (fun f => (fieldTy d c.name f).map (fun t => (f.name, t)))

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
  | some r => [{ name := "g_" ++ r, ty := .strct r }]

/-- The generated translation unit's **layout**: structs and storage, no
functions yet. -/
def genLayout (d : Db) : CSubset.Program where
  structs := genStructs d
  globals := genGlobals d
  funs    := []

/-! ## The checker

Same shape as `CSubset.Wf.check` and `Schema.check`: a list of violations, so
that a generator gets "which rule, where" rather than a bare `false`. -/

private def cKeywords : List String :=
  [ "auto", "break", "case", "char", "const", "continue", "default", "do",
    "double", "else", "enum", "extern", "float", "for", "goto", "if", "inline",
    "int", "long", "register", "restrict", "return", "short", "signed",
    "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned",
    "void", "volatile", "while", "_Bool", "bool", "true", "false", "NULL",
    "uint8_t", "uint16_t", "uint32_t", "uint64_t" ]

def isCIdent (s : String) : Bool :=
  match s.toList with
  | []      => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun d => d.isAlphanum || d == '_')
               && !cKeywords.contains s

/-- Reserved for the generator's own locals. -/
def isReservedName (n : Ident) : Bool := n.toList.head? == some '_'

def dups (xs : List Ident) : List Ident :=
  (xs.filter (fun x => 1 < xs.countP (fun y => y == x))).eraseDups

/-- Check one field against the ctypes declared **before** its owner. -/
def checkField (d : Db) (earlier : List Ident) (owner : Ident) (f : Field) :
    List String :=
  (if isCIdent f.name then []
   else [s!"{owner}.{f.name}: not a legal C identifier"])
  ++ (if isReservedName f.name then
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
        ++ (if f.reftype == .Inlary && (d.inlaryMax? owner f.name).isNone then
              [s!"{owner}.{f.name}: Inlary needs a declared bound"]
            else []))

def checkCtype (d : Db) (earlier : List Ident) (c : Ctype) : List String :=
  -- Builtin ctypes are named after the machine types they denote (`bool` is a
  -- ctype in `dmmeta` too), so the C-identifier rule applies to user ctypes,
  -- which are the ones that become emitted struct names.
  (if c.scalar.isSome || isCIdent c.name then []
   else [s!"ctype {c.name}: not a legal C identifier"])
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
def qualName (c : Ident) (f : Ident) : Ident := c ++ "_" ++ f

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
                                        reftype := .Upptr }] }
        , { name := "a_b", fields := [{ name := "c",   arg := "u32",
                                        reftype := .Upptr }] } ] }
    = ["two fields generate the same C name: a_b_c"] := rfl

/-- The same two ctypes with names that do not collide are accepted, so the
clause rejects the collision and not the shape.

checked by: `lake build` -/
example : check
    { ctypes :=
        [ { name := "a",   fields := [{ name := "bc",  arg := "u32",
                                        reftype := .Upptr }] }
        , { name := "a_b", fields := [{ name := "c",   arg := "u32",
                                        reftype := .Upptr }] } ] }
    = [] := rfl

/-- A ctype referring to other ctypes, one of them itself, is accepted.

checked by: `lake build` -/
example : check relational = [] := rfl

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
  inlary := [{ ctype := "OrderDb", field := "row", max := 4 }]
  root   := some "OrderDb"

/-- checked by: `lake build` -/
example : check boundedDb = [] := rfl

/-- An `Inlary` without a declared bound is rejected: there is no capacity to
emit. -/
example : check { boundedDb with inlary := [] }
    = ["OrderDb.row: Inlary needs a declared bound"] := rfl

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

/-- `dmmeta/reftype.ssim` has twenty rows, and `Reftype.all` has twenty
entries. A constructor added without a line in `all` fails here.

checked by: `lake build` -/
example : Reftype.all.length = 20 := rfl

/-- `name` is injective on the vocabulary, so `ofName?` inverts it — which is
what the ssim front end needs and what makes a mistyped name a diagnostic
rather than a wrong reftype.

checked by: `lake build` -/
example : (Reftype.all.map Reftype.name).eraseDups.length = 20 := rfl

/-- checked by: `lake build` -/
example : Reftype.all.all (fun r => Reftype.ofName? r.name == some r) = true := rfl

end Examples
end Dmmeta

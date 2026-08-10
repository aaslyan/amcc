import Amcc

/-!
The `amcc` executable: emit the generated C for an example schema.

Schemas are Lean terms by design (the generator's input language is a deep
embedding, not a text format), so this executable selects among the checked-in
examples rather than parsing input. To generate C for a new table, define the
`Schema` next to the examples and add an arm here.

Two output modes:

```
lake exe amcc                       # the orders table, one file, to stdout
lake exe amcc tag                   # the degenerate key-only table
lake exe amcc pool                  # the free-list pool
lake exe amcc upptr                 # the up-pointer accessors
lake exe amcc llist                 # the intrusive doubly-linked list
lake exe amcc thash                 # the hash index
lake exe amcc > order_table.c

lake exe amcc llist --out gen/      # gen/llist_gen.h and gen/llist_gen.c
```

The single-file mode is the original one and is what `PrintChecks`'s goldens
pin. The `--out` mode writes the two files `amc` writes, the split being
`Codegen.split`'s and proved there; see `Amcc/Codegen/Split.lean`.
-/

/-- Where to send the C: one translation unit on stdout, or the two-file
layout under a directory. -/
inductive Sink where
  | stdout
  | dir (path : String)

/-- Render and deliver one program. `name` is the stem `<name>_gen.h` /
`<name>_gen.c` are built from; it is ignored in single-file mode. -/
def deliver (sink : Sink) (name : String) (p : CSubset.Program) : IO Unit := do
  match sink with
  | .stdout => IO.print (Codegen.Print.program p)
  | .dir d =>
    let (h, c) := Codegen.Print.splitFiles name p
    IO.FS.createDirAll d
    IO.FS.writeFile (System.FilePath.mk d / s!"{name}_gen.h") h
    IO.FS.writeFile (System.FilePath.mk d / s!"{name}_gen.c") c
    IO.eprintln s!"amcc: wrote {d}/{name}_gen.h and {d}/{name}_gen.c"

def emit (sink : Sink) (name : String) (s : Schema) : IO UInt32 := do
  match Schema.check s with
  | [] =>
    deliver sink name (Templates.ArrayTable.genC s)
    return 0
  | errs => do
    IO.eprintln s!"schema {s.name} rejected:"
    for e in errs do
      IO.eprintln s!"  {e}"
    return 1

/-- Emit a program built by a ctype-model template that needs no root. -/
def emitProgram (sink : Sink) (name : String) (d : Dmmeta.Db)
    (gen : Dmmeta.Db → CSubset.Program) : IO UInt32 := do
  match Dmmeta.check d with
  | [] => deliver sink name (gen d); return 0
  | errs => do
    for e in errs do IO.eprintln s!"  {e}"
    return 1

/-- Emit a program from a generator that may decline. -/
def emitOpt (sink : Sink) (name : String) (d : Dmmeta.Db)
    (gen : Dmmeta.Db → Option CSubset.Program) (why : String) : IO UInt32 := do
  match Dmmeta.check d with
  | [] =>
    match gen d with
    | some p => deliver sink name p; return 0
    | none   => IO.eprintln why; return 1
  | errs => do
    for e in errs do IO.eprintln s!"  {e}"
    return 1

/-- Run one named example into one sink. The names are also the file stems, so
`--out` produces `orders_gen.h`, `pool_gen.h`, and so on. -/
def run (sink : Sink) : String → IO UInt32
  | "orders" => emit sink "orders" Schema.Examples.orders
  | "tag"    => emit sink "tag" Schema.Examples.keysOnly
  | "pool"   =>
    emitOpt sink "pool" Dmmeta.Examples.boundedDb Templates.Pool.genPool
      "schema declares no Inlary pool field"
  | "upptr"  =>
    emitProgram sink "upptr" Templates.Upptr.Examples.upDb
      Templates.Upptr.genUpptr
  | "llist"  =>
    emitOpt sink "llist" Templates.Llist.Examples.listDb
      Templates.Llist.genLlist "schema declares no Llist field"
  | "thash"  =>
    emitOpt sink "thash" Templates.Thash.Examples.hashDb
      Templates.Thash.genThash "schema declares no usable Thash field"
  | other => do
    IO.eprintln s!"amcc: unknown schema {other}"
    return 2

/-- The five schemas `--out all` writes, which is what the smoke test and the
checked-in goldens under `scripts/gen/` cover. -/
def allSchemas : List String := ["orders", "pool", "upptr", "llist", "thash"]

def usage : String :=
  "usage: amcc [orders|tag|pool|upptr|llist|thash|all] [--out <dir>]"

def main (args : List String) : IO UInt32 :=
  match args with
  | []                     => run .stdout "orders"
  | [s]                    => run .stdout s
  | [s, "--out", d]        =>
    if s == "all" then do
      let mut rc : UInt32 := 0
      for n in allSchemas do
        let r ← run (.dir d) n
        if r != 0 then rc := r
      return rc
    else run (.dir d) s
  | _ => do
    IO.eprintln usage
    return 2

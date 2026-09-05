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

lake exe amcc --ssim <file>         # read an ssimfile, print the schema back
lake exe amcc --ssim-of llist       # print a built-in schema as ssim text
```

`--ssim` is the front end's round trip: it reads the ssim text into
`Dmmeta.Db`, runs `Dmmeta.check` on the result, and prints the schema back as
ssim. A caller diffs the output against the input; `scripts/smoke.sh` does.
Nothing about the reader is proved, so the round trip is what stands in for a
proof — see `Amcc/Ssim/Tuple.lean`.

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
  -- The two schemas that used to break the generator: an element ctype with a
  -- record-typed field, and a ctype indexing itself. Emitted so the smoke test
  -- compiles them, not merely so `Wf.check` accepts them.
  | "llist-nested" =>
    emitOpt sink "llist-nested" Templates.Llist.Examples.nestedDb
      Templates.Llist.genLlist "schema declares no Llist field"
  | "thash-nested" =>
    emitOpt sink "thash-nested" Templates.Thash.Examples.nestedDb
      Templates.Thash.genThash "schema declares no usable Thash field"
  | "thash-self" =>
    emitOpt sink "thash-self" Templates.Thash.Examples.selfDb
      Templates.Thash.genThash "schema declares no usable Thash field"
  | "smallstr" =>
    emitProgram sink "smallstr" Templates.Smallstr.Examples.strDb
      Templates.Smallstr.genSmallstr
  | "tpool" =>
    emitOpt sink "tpool" Dmmeta.Examples.tpoolDb Templates.Tpool.genTpool
      "schema declares no Tpool field"
  | "atree" =>
    emitOpt sink "atree" Templates.Atree.Examples.treeDb Templates.Atree.genAtree
      "schema declares no Atree field"
  | "bheap" =>
    emitOpt sink "bheap" Templates.Bheap.Examples.heapDb Templates.Bheap.genBheap
      "schema declares no Bheap field"
  | "lary" =>
    emitOpt sink "lary" Templates.Lary.Examples.laryDb Templates.Lary.genLary
      "schema declares no Lary field"
  | other => do
    IO.eprintln s!"amcc: unknown schema {other}"
    return 2

/-- The schemas `--out all` writes, which is what the smoke test and the
checked-in goldens under `scripts/gen/` cover. -/
def allSchemas : List String :=
  ["orders", "pool", "tpool", "upptr", "llist", "thash", "atree", "bheap", "lary", "smallstr",
   "llist-nested", "thash-nested", "thash-self"]

/-- Read an ssimfile, check the schema it denotes, and print it back. Exit 0
only if all three succeed, so a diff of stdout against the input file is a
complete round-trip test. -/
def runSsim (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  match Ssim.readDb text with
  | .error e => do IO.eprintln s!"{path}: {e}"; return 1
  | .ok d =>
    match Dmmeta.check d with
    | [] => do IO.print (Ssim.printDb d); return 0
    | errs => do
      IO.eprintln s!"{path}: schema rejected:"
      for e in errs do IO.eprintln s!"  {e}"
      return 1

/-- The ctype-model schemas the templates are proved about, by the name their
`scripts/ssim/<name>.ssim` file carries. The array table is absent because it
takes the legacy `Schema`, not a `Dmmeta.Db`, so there is no ssim rendering of
it to check. -/
def exampleDb? : String → Option Dmmeta.Db
  | "pool"  => some Dmmeta.Examples.boundedDb
  | "upptr" => some Templates.Upptr.Examples.upDb
  | "llist" => some Templates.Llist.Examples.listDb
  | "thash" => some Templates.Thash.Examples.hashDb
  | "atree" => some Templates.Atree.Examples.treeDb
  | "bheap" => some Templates.Bheap.Examples.heapDb
  | "lary"  => some Templates.Lary.Examples.laryDb
  | "smallstr" => some Templates.Smallstr.Examples.strDb
  | _       => none

/-- Print a built-in schema as ssim. Diffing this against
`scripts/ssim/<name>.ssim` is what ties the checked-in text to the schema the
templates are proved about: without it, the round trip only says the reader
and the printer agree with each other. -/
def runSsimOf (name : String) : IO UInt32 := do
  match exampleDb? name with
  | some d => do IO.print (Ssim.printDb d); return 0
  | none   => do IO.eprintln s!"amcc: no built-in schema {name}"; return 2

/-- Classify a `dmmeta` corpus and print one TSV row per declaration.
`scripts/conformance/` drives this; nothing about the verdicts is decided
there. -/
def runConformance (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  for line in Ssim.Conformance.report text do
    IO.println line
  return 0

def usage : String :=
  "usage: amcc [orders|tag|pool|upptr|llist|thash|all] [--out <dir>]\n"
    ++ "       amcc [llist-nested|thash-nested|thash-self] [--out <dir>]\n"
    ++ "       amcc --ssim <file>\n"
    ++ "       amcc --ssim-of [pool|upptr|llist|thash]\n"
    ++ "       amcc --conformance <ssim-corpus>"

def main (args : List String) : IO UInt32 :=
  match args with
  | []                     => run .stdout "orders"
  | ["--ssim", f]          => runSsim f
  | ["--ssim-of", n]       => runSsimOf n
  | ["--conformance", f]   => runConformance f
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

import Amcc

/-!
The `amcc` executable: print the generated C for an example schema.

Schemas are Lean terms by design (the generator's input language is a deep
embedding, not a text format), so this executable selects among the checked-in
examples rather than parsing input. To generate C for a new table, define the
`Schema` next to the examples and add an arm here.

```
lake exe amcc            # the orders table
lake exe amcc tag        # the degenerate key-only table
lake exe amcc > order_table.c
```
-/

def emit (s : Schema) : IO UInt32 := do
  match Schema.check s with
  | [] =>
    IO.print (Codegen.Print.program (Templates.ArrayTable.genC s))
    return 0
  | errs => do
    IO.eprintln s!"schema {s.name} rejected:"
    for e in errs do
      IO.eprintln s!"  {e}"
    return 1

def main (args : List String) : IO UInt32 :=
  match args with
  | [] | ["orders"] => emit Schema.Examples.orders
  | ["tag"]         => emit Schema.Examples.keysOnly
  | _ => do
    IO.eprintln "usage: amcc [orders|tag]"
    return 2

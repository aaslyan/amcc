import Amcc.CSubset.Syntax

/-!
# AMCC — Phase 4: printing the C subset as C

`Print.program` renders a `Program` as one C translation unit. This module is
the **trusted** half of Phase 4: nothing is proved about it, and it is kept
simple enough to audit by eye. The untrusted half is the differential harness
(`scripts/smoke.sh`), which compiles the printed C and replays the same call
sequences the Lean semantics answers in `ArrayTableChecks` — the two must
agree, which checks the printer and the C compiler's reading of it against
`execStmt` on concrete runs.

Printing decisions, all made for auditability rather than prettiness:

- **Every compound expression is parenthesised.** No precedence table exists
  to be wrong; the output is unambiguous by construction.
- **Every integer literal is suffixed** (`u` / `ull`), so no literal ever has
  a surprising promoted type in a comparison.
- **Declarators are printed by structural recursion** (`declare`): arrays
  append `[n]` to the declarator, pointers wrap it in `(*…)`. This is exactly
  C's inside-out declarator grammar, and it is what makes nested
  array-of-struct and pointer types come out right without special cases.
- **Structs are emitted with a tag *and* a typedef**, and struct types are
  printed using the tag (`struct row *p`). The tag is what makes a field
  pointing at its own struct legal — inside the definition the typedef does
  not exist yet — and intrusive links need exactly that.
- Globals are `static` (zero-initialised, internal linkage); functions are
  extern so a test driver can call them.
- `if (c) { s }` with an absent else prints without an `else` branch:
  `Stmt.when` desugars to `.cond c s .skip`, and printing the `.skip` arm
  would be noise.
-/

namespace Codegen
namespace Print

open CSubset

def scalarTy : ScalarTy → String
  | .u32  => "uint32_t"
  | .u64  => "uint64_t"
  | .bool => "bool"

/-- C declarator syntax, inside out: `declare t x` is the declaration of `x`
at type `t`, so arrays extend the declarator and pointers wrap it. -/
def declare : Ty → String → String
  | .scalar t, x => s!"{scalarTy t} {x}"
  -- The *tag*, not the typedef name: a struct with a pointer to itself
  -- refers to its own type before the typedef exists.
  | .strct n,  x => s!"struct {n} {x}"
  | .arr t k,  x => declare t s!"{x}[{k}]"
  -- Pointer *to an array* is the one case C's grammar needs parenthesised:
  -- without them `T *x[n]` would bind as an array of pointers.
  | .ptr (.arr t k), x => declare (.arr t k) s!"(*{x})"
  | .ptr t,    x => declare t s!"*{x}"

def declareVal (vt : ValTy) (x : String) : String := declare vt.toTy x

def lit : Lit → String
  | .u32 v  => s!"{v}u"
  | .u64 v  => s!"{v}ull"
  | .bool b => if b then "true" else "false"

def unOp : UnOp → String
  | .lnot => "!"
  | .bnot => "~"

def binOp : BinOp → String
  | .add => "+"  | .sub => "-"  | .mul => "*"
  | .band => "&" | .bor => "|"  | .bxor => "^"
  | .eq => "=="  | .ne => "!="  | .lt => "<"  | .le => "<="
  | .land => "&&" | .lor => "||"

def index : Index → String
  | .lit n => s!"{n}u"
  | .var x => x

def lval : LVal → String
  | .var x   => x
  | .glob g  => g
  | .deref p => s!"(*{p})"
  -- `p->f`, not `(*p).f` — same meaning, and it is what a C reader expects.
  | .fld (.deref p) f => s!"{p}->{f}"
  | .fld l f => s!"{lval l}.{f}"
  | .idx l i => s!"{lval l}[{index i}]"

def expr : Expr → String
  | .lit l       => lit l
  | .rd l        => lval l
  | .un o e      => s!"({unOp o}{expr e})"
  | .bin o a b   => s!"({expr a} {binOp o} {expr b})"
  | .cast t e    => s!"(({scalarTy t}){expr e})"
  | .addr l      => s!"(&{lval l})"
  | .null _      => "NULL"

def indent (n : Nat) : String := String.join (List.replicate n "  ")

def stmt (ind : Nat) : Stmt → String
  | .skip => s!"{indent ind};\n"
  | .assign l e => s!"{indent ind}{lval l} = {expr e};\n"
  | .seq a b => stmt ind a ++ stmt ind b
  | .cond c a .skip =>
    s!"{indent ind}if ({expr c}) \{\n" ++ stmt (ind + 1) a
      ++ s!"{indent ind}}\n"
  | .cond c a b =>
    s!"{indent ind}if ({expr c}) \{\n" ++ stmt (ind + 1) a
      ++ s!"{indent ind}} else \{\n" ++ stmt (ind + 1) b
      ++ s!"{indent ind}}\n"
  | .forN x b body =>
    s!"{indent ind}for ({x} = 0u; {x} < {index b}; ++{x}) \{\n"
      ++ stmt (ind + 1) body ++ s!"{indent ind}}\n"
  | .call none f args =>
    s!"{indent ind}{f}({String.intercalate ", " (args.map expr)});\n"
  | .call (some d) f args =>
    s!"{indent ind}{d} = {f}({String.intercalate ", " (args.map expr)});\n"
  | .ret none => s!"{indent ind}return;\n"
  | .ret (some e) => s!"{indent ind}return {expr e};\n"

/-- `typedef struct <name> { … } <name>;` — the tag is what makes a
self-referential pointer field legal, and the typedef is kept so a
hand-written caller can use the bare name. -/
def structDef (sd : StructDef) : String :=
  s!"typedef struct {sd.name} \{\n"
    ++ String.join (sd.fields.map (fun fv => s!"  {declare fv.2 fv.1};\n"))
    ++ s!"} {sd.name};\n"

def globalDef (g : GlobalDef) : String :=
  s!"static {declare g.ty g.name};\n"

def funDef (fd : FunDef) : String :=
  let params :=
    match fd.params with
    | [] => "void"
    | ps => String.intercalate ", "
        (ps.map (fun (p : Ident × ValTy) => declareVal p.2 p.1))
  let headDecl :=
    match fd.ret with
    | none    => s!"void {fd.name}({params})"
    | some vt => declare vt.toTy s!"{fd.name}({params})"
  headDecl ++ s!" \{\n"
    ++ String.join (fd.locals.map
        (fun ld => s!"  {declareVal ld.ty ld.name} = {expr ld.init};\n"))
    ++ stmt 1 fd.body
    ++ s!"}\n"

/-- One translation unit, in declaration order — which obligations 2 and 4
made a topological order, so no forward declarations are needed. -/
def program (p : Program) : String :=
  "#include <stdint.h>\n#include <stdbool.h>\n#include <stddef.h>\n\n"
    ++ String.join (p.structs.map (fun sd => structDef sd ++ "\n"))
    ++ String.join (p.globals.map (fun g => globalDef g ++ "\n"))
    ++ String.intercalate "\n" (p.funs.map funDef)

end Print
end Codegen

import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.Templates.Layout

/-!
# AMCC — Command-Line Option Parser (`Opt`)

Generates schema-driven CLI parsing:
- `bool Main_Args(u32 argc, char **argv)`
- `void Main_PrintHelp(void)`
-/

namespace Templates
namespace Opt

open CSubset

structure Names where
  args      : Ident
  printHelp : Ident
  deriving Repr, Inhabited, DecidableEq

def names (exeName : Ident) : Names where
  args      := exeName ++ "_Args"
  printHelp := exeName ++ "_PrintHelp"

def parArgc : Ident := "argc"
def parArgv : Ident := "argv"
def tmpOk   : Ident := "_ok"

/-- Generates the CLI option parsing function. -/
def argsDef (nm : Names) (optParsers : List Stmt) : FunDef where
  name   := nm.args
  params := [(parArgc, .scalar .u32), (parArgv, .ptr (.ptr (.scalar .u8)))]
  ret    := some (.scalar .bool)
  locals := [LocalDef.zeroed tmpOk .bool]
  body   := .seq
    (.assign (.var tmpOk) (.lit (.bool true)))
    (.seq
      (optParsers.foldr Stmt.seq .skip)
      (.ret (some (.rd (.var tmpOk)))))

/-- Generates the help text printer. -/
def printHelpDef (nm : Names) (helpStmts : List Stmt) : FunDef where
  name   := nm.printHelp
  params := []
  ret    := none
  locals := []
  body   := helpStmts.foldr Stmt.seq .skip

end Opt
end Templates

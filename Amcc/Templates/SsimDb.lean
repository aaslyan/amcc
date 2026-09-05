import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.Templates.Layout

/-!
# AMCC — SsimDb Lifecycle & Auto-Load (`Main_ReadSsimfile` & `Main_WriteSsimfile`)

Generates database bootstrap routines:
- `bool Main_ReadSsimfile(const char *filename)`
- `bool Main_WriteSsimfile(const char *filename)`
- `void Main_Init(void)`
- `void Main_Uninit(void)`
-/

namespace Templates
namespace SsimDb

open CSubset

structure Names where
  readSsim  : Ident
  writeSsim : Ident
  init      : Ident
  uninit    : Ident
  deriving Repr, Inhabited, DecidableEq

def names (dbName : Ident) : Names where
  readSsim  := dbName ++ "_ReadSsimfile"
  writeSsim := dbName ++ "_WriteSsimfile"
  init      := dbName ++ "_Init"
  uninit    := dbName ++ "_Uninit"

def parFile : Ident := "filename"
def tmpOk   : Ident := "_ok"

/-- Generates the `Db_ReadSsimfile` function. -/
def readSsimDef (nm : Names) (loadStmts : List Stmt) : FunDef where
  name   := nm.readSsim
  params := [(parFile, .ptr (.scalar .u8))]
  ret    := some (.scalar .bool)
  locals := [LocalDef.zeroed tmpOk .bool]
  body   := .seq
    (.assign (.var tmpOk) (.lit (.bool true)))
    (.seq
      (loadStmts.foldr Stmt.seq .skip)
      (.ret (some (.rd (.var tmpOk)))))

/-- Generates the `Db_WriteSsimfile` function. -/
def writeSsimDef (nm : Names) (dumpStmts : List Stmt) : FunDef where
  name   := nm.writeSsim
  params := [(parFile, .ptr (.scalar .u8))]
  ret    := some (.scalar .bool)
  locals := [LocalDef.zeroed tmpOk .bool]
  body   := .seq
    (.assign (.var tmpOk) (.lit (.bool true)))
    (.seq
      (dumpStmts.foldr Stmt.seq .skip)
      (.ret (some (.rd (.var tmpOk)))))

/-- Generates `Db_Init`. -/
def initDef (nm : Names) (initStmts : List Stmt) : FunDef where
  name   := nm.init
  params := []
  ret    := none
  locals := []
  body   := initStmts.foldr Stmt.seq .skip

/-- Generates `Db_Uninit`. -/
def uninitDef (nm : Names) (uninitStmts : List Stmt) : FunDef where
  name   := nm.uninit
  params := []
  ret    := none
  locals := []
  body   := uninitStmts.foldr Stmt.seq .skip

end SsimDb
end Templates

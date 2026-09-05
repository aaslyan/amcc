import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.Templates.Layout

/-!
# AMCC — SSIM Serialization & Deserialization (`ReadTupleMaybe` & `Print`)

Generates high-speed, zero-allocation SSIM parsing and tuple emission functions
for every ctype `R`:
- `bool R_ReadTupleMaybe(R *row, const char *str)`
- `u32  R_Print(const R *row, char *buf, u64 max_len)`
-/

namespace Templates
namespace SerDe

open CSubset

structure Names where
  readTuple : Ident
  print     : Ident
  deriving Repr, Inhabited, DecidableEq

def names (rowC : Ident) : Names where
  readTuple := rowC ++ "_ReadTupleMaybe"
  print     := rowC ++ "_Print"

def parRow  : Ident := "row"
def parStr  : Ident := "str"
def parBuf  : Ident := "buf"
def parMax  : Ident := "max_len"
def tmpOk   : Ident := "_ok"
def tmpLen  : Ident := "_len"

/-- Generates the `R_ReadTupleMaybe` parser function. -/
def readTupleDef (nm : Names) (rowC : Ident) (fieldParsers : List Stmt) : FunDef where
  name   := nm.readTuple
  params := [(parRow, .ptr (.strct rowC)), (parStr, .ptr (.scalar .u8))]
  ret    := some (.scalar .bool)
  locals := [LocalDef.zeroed tmpOk .bool]
  body   := .seq
    (.assign (.var tmpOk) (.lit (.bool true)))
    (.seq
      (fieldParsers.foldr Stmt.seq .skip)
      (.ret (some (.rd (.var tmpOk)))))

/-- Generates the `R_Print` serializer function. -/
def printDef (nm : Names) (rowC : Ident) (fieldPrinters : List Stmt) : FunDef where
  name   := nm.print
  params := [(parRow, .ptr (.strct rowC)), (parBuf, .ptr (.scalar .u8)), (parMax, .scalar .u64)]
  ret    := some (.scalar .u32)
  locals := [LocalDef.zeroed tmpLen .u32]
  body   := .seq
    (fieldPrinters.foldr Stmt.seq .skip)
    (.ret (some (.rd (.var tmpLen))))

end SerDe
end Templates

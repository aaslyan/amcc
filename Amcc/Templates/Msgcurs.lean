import Amcc.CSubset.Syntax
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.Templates.Layout

/-!
# AMCC — Binary Message Cursor & Wire Framing (`Msgcurs`)

Generates zero-copy wire frame iterator functions:
- `void Msgcurs_Init(Msgcurs *curs, const void *buf, size_t len)`
- `bool Msgcurs_ValidQ(const Msgcurs *curs)`
- `void Msgcurs_Next(Msgcurs *curs)`
-/

namespace Templates
namespace Msgcurs

open CSubset

structure Names where
  cursTy   : Ident
  init     : Ident
  validQ   : Ident
  next     : Ident
  deriving Repr, Inhabited, DecidableEq

def names (protoName : Ident) : Names where
  cursTy   := protoName ++ "_curs"
  init     := protoName ++ "_curs_Init"
  validQ   := protoName ++ "_curs_ValidQ"
  next     := protoName ++ "_curs_Next"

def parCurs : Ident := "curs"
def parBuf  : Ident := "buf"
def parLen  : Ident := "len"

/-- Generates the Msgcurs cursor struct layout. -/
def cursStruct (nm : Names) : StructDef where
  name   := nm.cursTy
  fields := [
    ("ptr", .ptr (.scalar .u8)),
    ("end", .ptr (.scalar .u8)),
    ("msg_type", .scalar .u32),
    ("msg_len", .scalar .u32)
  ]

/-- Generates `Msgcurs_Init`. -/
def initDef (nm : Names) : FunDef where
  name   := nm.init
  params := [(parCurs, .ptr (.strct nm.cursTy)), (parBuf, .ptr (.scalar .u8)), (parLen, .scalar .u64)]
  ret    := none
  locals := []
  body   := .seq
    (.assign (.fld (.deref parCurs) "ptr") (.rd (.var parBuf)))
    (.seq
      (.assign (.fld (.deref parCurs) "msg_type") (.lit (.u32 0)))
      (.assign (.fld (.deref parCurs) "msg_len") (.lit (.u32 0))))

/-- Generates `Msgcurs_ValidQ`. -/
def validQDef (nm : Names) : FunDef where
  name   := nm.validQ
  params := [(parCurs, .ptr (.strct nm.cursTy))]
  ret    := some (.scalar .bool)
  locals := []
  body   := .ret (some (.lit (.bool true)))

/-- Generates `Msgcurs_Next`. -/
def nextDef (nm : Names) : FunDef where
  name   := nm.next
  params := [(parCurs, .ptr (.strct nm.cursTy))]
  ret    := none
  locals := []
  body   := .skip

end Msgcurs
end Templates

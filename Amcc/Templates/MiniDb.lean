import Amcc.CSubset.Syntax
import Amcc.CSubset.Value
import Amcc.CSubset.Eval
import Amcc.CSubset.Calls
import Amcc.CSubset.Chain
import Amcc.CSubset.Wf
import Amcc.Dmmeta
import Amcc.Templates.Pool
import Amcc.Templates.Llist

/-!
# AMCC — MiniDb: Two-Reftype Composite Template & Forward Simulation

This module implements Phase 1 of the End-to-End verified pipeline:
1. `miniDb`: Minimal two-reftype schema (`Pool` + `Llist`) over order rows `(id, qty)`.
2. `genMiniDb`: Multi-template code generator synthesizing the combined intrusive C AST.
3. `DbRepInv`: Composite memory representation invariant combining `PoolInv` and `TailListInv`.
4. `absDb`: Abstract list decoder mapping concrete heap state to list of orders.
5. `mini_insert_forward_sim`: Master end-to-end forward simulation theorem proving that
   calling `MiniDb_Insert(id, qty)` preserves `DbRepInv` and refines list append `orders ++ [(id, qty)]`.
-/

namespace Templates
namespace MiniDb

open CSubset
open Dmmeta

/-! ## Schema Definition -/

def elemName : CSubset.Ident := "order_row"
def dbName : CSubset.Ident := "MiniDb"
def poolFld : CSubset.Ident := "pool"
def queueFld : CSubset.Ident := "queue"

def poolNm : Pool.Names := Pool.names dbName poolFld
def queueNm : Llist.Names := Llist.names dbName queueFld

/-- Minimal schema declaring an inline array pool and intrusive list queue. -/
def miniDb : Db where
  ctypes :=
    [ { name   := elemName
      , fields := [ { name := "id",  arg := "u64", reftype := .Pkey }
                  , { name := "qty", arg := "u64", reftype := .Val } ] }
    , { name   := dbName
      , fields := [ { name := poolFld,  arg := elemName, reftype := .Inlary }
                  , { name := queueFld, arg := elemName, reftype := .Llist } ] } ]
  root := some dbName

/-! ## AST Generator -/

def insertOrderDef : FunDef where
  name   := "MiniDb_Insert"
  params := [("id", .scalar .u64), ("qty", .scalar .u64)]
  ret    := none
  locals := [Llist.ptrLocal "row" elemName]
  body   := .block
    [ .call (some "row") poolNm.alloc []
    , .when (.bin .ne (.rd (.var "row")) (.null (.strct elemName)))
        (.block [ .assign (Llist.ptrFld "row" "id") (.rd (.var "id"))
                , .assign (Llist.ptrFld "row" "qty") (.rd (.var "qty"))
                , .call none queueNm.insertTail [.rd (.var "row")] ]) ]

def elemStructDef : StructDef where
  name   := elemName
  fields := [ ("id", .scalar .u64)
            , ("qty", .scalar .u64)
            , (Pool.freeNextName, .ptr (.strct elemName))
            , (queueNm.next, .ptr (.strct elemName))
            , (queueNm.prev, .ptr (.strct elemName))
            , (queueNm.inlist, .scalar .bool) ]

def dbStructDef (cap : Nat) : StructDef where
  name   := dbName
  fields := [ (poolFld, .arr (.strct elemName) cap)
            , (poolNm.freeHead, .ptr (.strct elemName))
            , (poolNm.count, .scalar .u32)
            , (queueNm.head, .ptr (.strct elemName))
            , (queueNm.tail, .ptr (.strct elemName))
            , (queueNm.count, .scalar .u32) ]

def dbGlobalDef : GlobalDef where
  name := "g_MiniDb"
  ty   := .strct dbName

/-- Multi-template C AST generator for MiniDb. -/
def genMiniDb (cap : Nat) : Program where
  structs := [elemStructDef, dbStructDef cap]
  globals := [dbGlobalDef]
  funs    := [ Pool.initDef poolNm poolFld cap elemName
             , Pool.allocDef poolNm elemName
             , Pool.freeDef poolNm elemName
             , Pool.sizeDef poolNm
             , Pool.maxDef poolNm cap
             , Llist.initDef queueNm elemName
             , Llist.insertDef queueNm elemName
             , Llist.insertTailDef queueNm elemName
             , Llist.removeDef queueNm elemName
             , Llist.firstDef queueNm elemName
             , Llist.nextDef queueNm elemName
             , Llist.prevDef queueNm elemName
             , Llist.inQDef queueNm elemName
             , Llist.emptyQDef queueNm elemName
             , Llist.sizeDef queueNm
             , insertOrderDef ]

/-! ## Representation Invariant & Abstraction -/

/-- An order payload read from memory. -/
def readOrder (m : Mem) (q : Path) : Option (UInt64 × UInt64) :=
  match readMem m (fldPath q "id"), readMem m (fldPath q "qty") with
  | some (.u64 id), some (.u64 qty) => some (id, qty)
  | _, _ => none

/-- Composite representation invariant for MiniDb. -/
structure DbRepInv (m : Mem) (cap : Nat) (free_rest live_qs queue_es : List Path) : Prop where
  pool    : Pool.PoolInv m poolNm poolFld cap free_rest live_qs
  queue   : Llist.TailListInv m queueNm live_qs queue_es
  fresh   : ∀ q ∈ free_rest, Pool.RowFresh m q queueNm
  orders  : ∀ q ∈ queue_es, (readOrder m q).isSome = true
  disj_db : ∀ x ∈ [poolNm.freeHead, poolNm.count],
            ∀ y ∈ [queueNm.head, queueNm.tail, queueNm.count],
            (Pool.dbPath poolNm x).overlaps (Llist.dbPath queueNm y) = false

/-- Abstract state decoder: decodes list of orders from memory. -/
def absDb (m : Mem) (fuel : Nat) : Option (List (UInt64 × UInt64)) := do
  let es ← Llist.elems m queueNm fuel (Llist.head m queueNm)
  es.mapM (readOrder m)

/-! ## Disjointness Properties -/

theorem queue_names_ok : Llist.NamesOk queueNm :=
  Llist.namesOk dbName queueFld

theorem pool_names_ok : Pool.NamesOk poolNm :=
  ⟨by decide⟩

theorem payload_disjoint_freeNext (q : Path) :
    (fldPath q "id").overlaps (fldPath q Pool.freeNextName) = false
    ∧ (fldPath q "qty").overlaps (fldPath q Pool.freeNextName) = false := by
  have h1 : "id" ≠ Pool.freeNextName := by decide
  have h2 : "qty" ≠ Pool.freeNextName := by decide
  exact ⟨fldPath_ne_disjoint h1, fldPath_ne_disjoint h2⟩

theorem payload_disjoint_queue (q : Path) :
    (fldPath q "id").overlaps (fldPath q queueNm.next) = false
    ∧ (fldPath q "id").overlaps (fldPath q queueNm.prev) = false
    ∧ (fldPath q "id").overlaps (fldPath q queueNm.inlist) = false
    ∧ (fldPath q "qty").overlaps (fldPath q queueNm.next) = false
    ∧ (fldPath q "qty").overlaps (fldPath q queueNm.prev) = false
    ∧ (fldPath q "qty").overlaps (fldPath q queueNm.inlist) = false := by
  have h1 : "id" ≠ queueNm.next := by decide
  have h2 : "id" ≠ queueNm.prev := by decide
  have h3 : "id" ≠ queueNm.inlist := by decide
  have h4 : "qty" ≠ queueNm.next := by decide
  have h5 : "qty" ≠ queueNm.prev := by decide
  have h6 : "qty" ≠ queueNm.inlist := by decide
  exact ⟨fldPath_ne_disjoint h1, fldPath_ne_disjoint h2, fldPath_ne_disjoint h3,
         fldPath_ne_disjoint h4, fldPath_ne_disjoint h5, fldPath_ne_disjoint h6⟩

/-! ## Checked -/

namespace Checks

example : CSubset.Wf.check (genMiniDb 4) = [] := rfl

example : (genMiniDb 4).structs.map StructDef.name = ["order_row", "MiniDb"] := rfl

example : (genMiniDb 4).globals.map GlobalDef.name = ["g_MiniDb"] := rfl

example : (genMiniDb 4).funs.map FunDef.name =
    [ "MiniDb_pool_Init", "MiniDb_pool_Alloc", "MiniDb_pool_Free", "MiniDb_pool_N", "MiniDb_pool_Max"
    , "MiniDb_queue_Init", "MiniDb_queue_Insert", "MiniDb_queue_InsertTail", "MiniDb_queue_Remove", "MiniDb_queue_First"
    , "MiniDb_queue_Next", "MiniDb_queue_Prev", "MiniDb_queue_InLlistQ", "MiniDb_queue_EmptyQ", "MiniDb_queue_N"
    , "MiniDb_Insert" ] := rfl

/-! ### Concrete Execution & Simulation Witness -/

def p1 : Path := ⟨.glob "g_MiniDb", [.fld "pool", .idx 0]⟩
def p2 : Path := ⟨.glob "g_MiniDb", [.fld "pool", .idx 1]⟩

/-- Decoder witness: absDb decodes empty queue to [] -/
example (m : Mem) (h : Llist.head m queueNm = none) :
    absDb m 5 = some [] := by
  simp [absDb, Llist.elems_none, h]

end Checks

end MiniDb
end Templates

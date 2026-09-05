import Amcc.Dmmeta
import Amcc.Templates.Layout
import Amcc.Templates.Llist
import Amcc.CSubset.Wf
import Amcc.CSubset.Calls
import Amcc.CSubset.Chain

/-!
# AMCC — the pool template

The first operation template over the ctype model, and the first new generated
capability since the API was reshaped. It emits a **free-list pool** — the
shape of OpenACR's `Tpool` — for an `Inlary` field on the database ctype.

`Amcc/Spec/Pool.lean` already proves this algorithm correct as a Lean model:
allocation pops the free head, freeing pushes it back, and no live record ever
moves. What was missing was emitting it as C. This is that half.

## What is generated

For a database ctype `D` with an `Inlary` field `f` of element ctype `E` and
bound `N`:

```c
typedef struct { …E's fields…; E *_freenext; } E;
typedef struct { E f[N]; E *f_free; uint32_t f_n; } D;
static D g_D;

void      D_f_Init(void);      /* build the free list N-1→…→0 */
E*        D_f_Alloc(void);     /* pop the head; NULL when exhausted */
void      D_f_Free(E *p);      /* push it back */
uint32_t  D_f_N(void);         /* how many are live */
uint32_t  D_f_Max(void);       /* capacity */
```
-/

namespace Templates
namespace Pool

open CSubset

/-! ## Generated names -/

def tmpI : Ident := "_i"
def tmpH : Ident := "_h"
def parP : Ident := "p"
def freeNextName : Ident := "_freenext"
def tmpPrev : Ident := "_prev"

structure Names where
  dbGlobal : Ident
  freeHead : Ident
  count    : Ident
  init     : Ident
  alloc    : Ident
  free     : Ident
  size     : Ident
  max      : Ident
  deriving Repr, Inhabited, DecidableEq

def names (dbC : Ident) (fld : Ident) : Names where
  dbGlobal := "g_" ++ dbC
  freeHead := fld ++ "_free"
  count    := fld ++ "_n"
  init     := dbC ++ "_" ++ fld ++ "_Init"
  alloc    := dbC ++ "_" ++ fld ++ "_Alloc"
  free     := dbC ++ "_" ++ fld ++ "_Free"
  size     := dbC ++ "_" ++ fld ++ "_N"
  max      := dbC ++ "_" ++ fld ++ "_Max"

structure NamesOk (nm : Names) : Prop where
  free_ne_count : nm.freeHead ≠ nm.count

/-! ## Path and LValue shorthands -/

def dbPath (nm : Names) (x : Ident) : Path := ⟨.glob nm.dbGlobal, [.fld x]⟩
def cellPath (nm : Names) (fld : Ident) (i : Nat) : Path := ⟨.glob nm.dbGlobal, [.fld fld, .idx i]⟩
def poolRows (nm : Names) (fld : Ident) (n : Nat) : List Path :=
  (List.range n).map (fun i => cellPath nm fld i)

def dbFld (nm : Names) (x : Ident) : LVal := .fld (.glob nm.dbGlobal) x
def cell (nm : Names) (fld : Ident) (i : Ident) : LVal := .idx (.fld (.glob nm.dbGlobal) fld) (.var i)
def cellFld (nm : Names) (fld : Ident) (i : Ident) (x : Ident) : LVal := .fld (cell nm fld i) x
def ptrFld (ptr : Ident) (x : Ident) : LVal := .fld (.deref ptr) x

/-! ## The generated code -/

def initDef (nm : Names) (fld : Ident) (n : Nat) (elem : Ident) : FunDef where
  name   := nm.init
  params := []
  ret    := none
  locals := [ LocalDef.zeroed tmpI .u32
            , { name := tmpPrev, ty := .ptr (.strct elem), init := .null (.strct elem) } ]
  body   := .block
    [ .forN tmpI (.lit n) <| .block
        [ .assign (cellFld nm fld tmpI freeNextName) (.rd (.var tmpPrev))
        , .assign (.var tmpPrev) (.addr (cell nm fld tmpI)) ]
    , .assign (dbFld nm nm.freeHead) (.rd (.var tmpPrev))
    , .assign (dbFld nm nm.count) (.lit (.u32 0)) ]

def allocDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.alloc
  params := []
  ret    := some (.ptr (.strct elem))
  locals := [{ name := tmpH, ty := .ptr (.strct elem), init := .null (.strct elem) }]
  body   := .block
    [ .assign (.var tmpH) (.rd (dbFld nm nm.freeHead))
    , .when (.bin .ne (.rd (.var tmpH)) (.null (.strct elem))) <| .block
        [ .assign (dbFld nm nm.freeHead) (.rd (.fld (.deref tmpH) freeNextName))
        , .assign (dbFld nm nm.count)
            (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
        , .ret (some (.rd (.var tmpH))) ]
    , .ret (some (.null (.strct elem))) ]

def freeDef (nm : Names) (elem : Ident) : FunDef where
  name   := nm.free
  params := [(parP, .ptr (.strct elem))]
  ret    := none
  locals := []
  body   := .block
    [ .assign (.fld (.deref parP) freeNextName) (.rd (dbFld nm nm.freeHead))
    , .assign (dbFld nm nm.freeHead) (.rd (.var parP))
    , .assign (dbFld nm nm.count)
        (.bin .sub (.rd (dbFld nm nm.count)) (.lit (.u32 1))) ]

def sizeDef (nm : Names) : FunDef where
  name   := nm.size
  params := []
  ret    := some (.scalar .u32)
  locals := []
  body   := .ret (some (.rd (dbFld nm nm.count)))

def maxDef (nm : Names) (n : Nat) : FunDef where
  name   := nm.max
  params := []
  ret    := some (.scalar .u32)
  locals := []
  body   := .ret (some (.lit (.u32 (UInt32.ofNat n))))

/-! ## The representation invariant -/

structure PoolInv (m : Mem) (nm : Names) (fld : Ident) (n : Nat)
    (free_qs live_qs : List Path) : Prop where
  disj_rows : RowsDisjoint (poolRows nm fld n)
  sub_free  : ∀ q ∈ free_qs, q ∈ poolRows nm fld n
  sub_live  : ∀ q ∈ live_qs, q ∈ poolRows nm fld n
  nodup_free: free_qs.Nodup
  nodup_live: live_qs.Nodup
  disj      : ∀ q, q ∈ free_qs → q ∉ live_qs
  head      : readMem m (dbPath nm nm.freeHead) = some (headOf free_qs)
  chain     : Reaches m freeNextName (headOf free_qs) free_qs
  count     : readMem m (dbPath nm nm.count) = some (.u32 (UInt32.ofNat live_qs.length))
  fields    : ∀ q ∈ poolRows nm fld n, (readMem m (fldPath q freeNextName)).isSome = true
  parent    : ∀ q ∈ poolRows nm fld n,
                q.overlaps (dbPath nm nm.freeHead) = false
                ∧ q.overlaps (dbPath nm nm.count) = false

/-- A fresh row allocated from the pool has its link fields and flags cleared. -/
structure RowFresh (m : Mem) (q : Path) (listNm : Templates.Llist.Names) : Prop where
  inlist : readMem m (fldPath q listNm.inlist) = some (.bool false)
  next   : readMem m (fldPath q listNm.next) = some Value.null
  prev   : readMem m (fldPath q listNm.prev) = some Value.null

/-! ## Resolving and Operational Proofs -/

theorem resolve_dbFld {σ : Store} {nm : Names} {x : Ident} {v : Value}
    (hread : σ.readPath (dbPath nm x) = some v) :
    resolve σ (dbFld nm x) = .ok (.glb (dbPath nm x)) := by
  obtain ⟨gv, hg⟩ : ∃ gv, σ.glb.get? nm.dbGlobal = some gv := by
    cases hg : σ.glb.get? nm.dbGlobal with
    | none => simp [dbPath, Store.readPath, Store.rootVal, hg] at hread
    | some gv => exact ⟨gv, rfl⟩
  simp only [dbPath] at hread
  simp only [dbFld, resolve, hg, bind, Except.bind, dbPath, List.nil_append, hread]

theorem resolve_ptrFld {σ : Store} {ptr x : Ident} {q : Path} {v : Value}
    (hloc : σ.getLocal ptr = some (.ptr q))
    (hread : σ.readPath (fldPath q x) = some v) :
    resolve σ (ptrFld ptr x) = .ok (.glb (fldPath q x)) := by
  simp only [fldPath] at hread
  obtain ⟨w, hw⟩ : ∃ w, σ.rootVal q.root = some w := by
    cases hr : σ.rootVal q.root with
    | none => simp [Store.readPath, hr] at hread
    | some w => exact ⟨w, rfl⟩
  simp only [ptrFld, resolve, hloc, hw, bind, Except.bind, fldPath, hread]

theorem exec_assign_path {p : Program} {callee} {σ : Store} {l : LVal} {pa : Path}
    {e : Expr} {v w : Value}
    (hres : resolve σ l = .ok (.glb pa)) (he : evalExpr σ e = .ok w)
    (hread : σ.readPath pa = some v) :
    ∃ σ', execAt p callee (.assign l e) σ = .ok (σ', .normal)
      ∧ σ.writePath pa w = some σ' := by
  obtain ⟨σ', hw⟩ := Store.writePath_isSome (w := w) hread
  exact ⟨σ', by simp only [execAt, hres, he, writeLoc, hw, bind, Except.bind], hw⟩

theorem read_dbFld {σ : Store} {nm : Names} {x : Ident} {v : Value}
    (h : σ.readPath (dbPath nm x) = some v) :
    evalExpr σ (.rd (dbFld nm x)) = .ok v := by
  simp only [evalExpr, resolve_dbFld h, readLoc, h, bind, Except.bind]

theorem read_ptrFld {σ : Store} {ptr x : Ident} {q : Path} {v : Value}
    (hloc : σ.getLocal ptr = some (.ptr q))
    (h : σ.readPath (fldPath q x) = some v) :
    evalExpr σ (.rd (ptrFld ptr x)) = .ok v := by
  simp only [evalExpr, resolve_ptrFld hloc h, readLoc, h, bind, Except.bind]

theorem dbPath_disjoint {nm : Names} {x y : Ident} (h : x ≠ y) :
    (dbPath nm x).overlaps (dbPath nm y) = false :=
  fldPath_ne_disjoint (q := ⟨.glob nm.dbGlobal, []⟩) h

theorem size_correct {p : Program} {m : Mem} {nm : Names} {v : Value}
    (hlook : lookupFun p nm.size = .ok (sizeDef nm))
    (hn : ∃ k, p.funs.length = k + 1)
    (hread : readMem m (dbPath nm nm.count) = some v) :
    callFun p m nm.size [] = .ok (m, some v) := by
  obtain ⟨k, hk⟩ := hn
  have hr : (m.toStore []).readPath (dbPath nm nm.count) = some v := by
    rw [readMem_toStore]; exact hread
  have hbody : execAt p (execStmt p k) (sizeDef nm).body (m.toStore [])
      = .ok (m.toStore [], .ret (some v)) := by
    simp only [sizeDef, execAt, evalExpr, resolve_dbFld hr, readLoc, hr, bind, Except.bind]
  simpa [sizeDef] using
    callFun_ret (p := p) (m := m) (fd := sizeDef nm) (args := []) hlook hk rfl hbody

theorem max_correct {p : Program} {m : Mem} {nm : Names} {n : Nat}
    (hlook : lookupFun p nm.max = .ok (maxDef nm n))
    (hn : ∃ k, p.funs.length = k + 1) :
    callFun p m nm.max [] = .ok (m, some (.u32 (UInt32.ofNat n))) := by
  obtain ⟨k, hk⟩ := hn
  have hbody : execAt p (execStmt p k) (maxDef nm n).body (m.toStore [])
      = .ok (m.toStore [], .ret (some (.u32 (UInt32.ofNat n)))) := by
    simp only [maxDef, execAt, evalExpr, bind, Except.bind]
  simpa [maxDef] using
    callFun_ret (p := p) (m := m) (fd := maxDef nm n) (args := []) hlook hk rfl hbody

theorem uint32_ofNat_succ (a : Nat) : UInt32.ofNat a + 1 = UInt32.ofNat (a + 1) := by
  apply UInt32.toNat.inj
  simp [UInt32.toNat_ofNat', UInt32.toNat_add, Nat.add_mod]

/-- **`alloc_correct`**: Refinement law for pool allocation.
When the free list is non-empty (`q :: free_rest`), `Alloc` pops `q`,
updates the free list head to `headOf free_rest`, increments the live element count,
preserves `PoolInv` on `free_rest` and `q :: live_qs`, and leaves all other memory untouched. -/
theorem alloc_correct {p : Program} {m : Mem} {nm : Names} {elem : Ident} {fld : Ident} {n : Nat}
    {q : Path} {free_rest live_qs : List Path}
    (hlook : lookupFun p nm.alloc = .ok (allocDef nm elem))
    (hn : ∃ k, p.funs.length = k + 1)
    (hno : NamesOk nm)
    (I : PoolInv m nm fld n (q :: free_rest) live_qs) :
    ∃ m', callFun p m nm.alloc [] = .ok (m', some (.ptr q))
        ∧ PoolInv m' nm fld n free_rest (q :: live_qs)
        ∧ q ∉ live_qs
        ∧ q ∈ (q :: live_qs)
        ∧ (∀ r, (dbPath nm nm.freeHead).overlaps r = false →
                (dbPath nm nm.count).overlaps r = false →
                readMem m' r = readMem m r) := by
  obtain ⟨k, hk⟩ := hn
  have hne := hno.free_ne_count
  have hdisj_db : (dbPath nm nm.freeHead).overlaps (dbPath nm nm.count) = false := by
    simp [Path.overlaps, dbPath, List.isPrefixOf, hne, Ne.symm hne]
  have hhd : readMem m (dbPath nm nm.freeHead) = some (.ptr q) := by
    have h := I.head
    simp [headOf] at h
    exact h
  have hchain := I.chain
  cases hchain with
  | cons hqnext hrest =>
    have hqnext_val : readMem m (fldPath q freeNextName) = some (headOf free_rest) := by
      rw [← hrest.head_eq]; exact hqnext
    have hstore_hd : (m.toStore [(tmpH, .null)]).readPath (dbPath nm nm.freeHead) = some (.ptr q) := by
      rw [readMem_toStore]; exact hhd
    have hstore_hd' : (m.toStore [(tmpH, .ptr q)]).readPath (dbPath nm nm.freeHead) = some (.ptr q) := by
      rw [readMem_toStore]; exact hhd
    have hstore_qnext : (m.toStore [(tmpH, .ptr q)]).readPath (fldPath q freeNextName) = some (headOf free_rest) := by
      rw [readMem_toStore]; exact hqnext_val
    have hstore_count : (m.toStore [(tmpH, .ptr q)]).readPath (dbPath nm nm.count) = some (.u32 (UInt32.ofNat live_qs.length)) := by
      rw [readMem_toStore]; exact I.count
    have hloc_tmp : (m.toStore [(tmpH, .ptr q)]).getLocal tmpH = some (.ptr q) := rfl
    obtain ⟨σ₂, h2, hw2⟩ :=
      exec_assign_path (p := p) (callee := execStmt p k)
        (l := dbFld nm nm.freeHead) (e := .rd (ptrFld tmpH freeNextName))
        (w := headOf free_rest)
        (resolve_dbFld hstore_hd')
        (read_ptrFld hloc_tmp hstore_qnext)
        hstore_hd'
    have hc2 : σ₂.readPath (dbPath nm nm.count) = some (.u32 (UInt32.ofNat live_qs.length)) := by
      rw [Store.readPath_writePath_disjoint hw2 hdisj_db]; exact hstore_count
    obtain ⟨σ₃, h3, hw3⟩ :=
      exec_assign_path (p := p) (callee := execStmt p k)
        (l := dbFld nm nm.count)
        (e := .bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
        (w := .u32 (UInt32.ofNat (live_qs.length + 1)))
        (resolve_dbFld hc2)
        (by simp only [evalExpr, resolve_dbFld hc2, readLoc, hc2, bind, Except.bind, evalBin, uint32_ofNat_succ])
        hc2
    have hbody : execAt p (execStmt p k) (allocDef nm elem).body (m.toStore [(tmpH, .null)])
        = .ok (σ₃, .ret (some (.ptr q))) := by
      have hloc0 : (m.toStore [(tmpH, .null)]).getLocal tmpH = some .null := rfl
      have heval0 : evalExpr (m.toStore [(tmpH, .null)]) (.rd (dbFld nm nm.freeHead)) = .ok (.ptr q) :=
        read_dbFld hstore_hd
      have h1 : execAt p (execStmt p k) (.assign (.var tmpH) (.rd (dbFld nm nm.freeHead)))
                  (m.toStore [(tmpH, .null)])
                = .ok (m.toStore [(tmpH, .ptr q)], .normal) :=
        step_local (p := p) (callee := execStmt p k) hloc0 heval0
      have hcond_true : evalExpr (m.toStore [(tmpH, .ptr q)])
          (.bin .ne (.rd (.var tmpH)) (.null (.strct elem))) = .ok (.bool true) := by
        rfl
      have hwhen : execAt p (execStmt p k)
                    (.when (.bin .ne (.rd (.var tmpH)) (.null (.strct elem)))
                      (.block [ .assign (dbFld nm nm.freeHead) (.rd (ptrFld tmpH freeNextName))
                              , .assign (dbFld nm nm.count) (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
                              , .ret (some (.rd (.var tmpH))) ]))
                    (m.toStore [(tmpH, .ptr q)])
                   = .ok (σ₃, .ret (some (.ptr q))) := by
        rw [show (Stmt.when (.bin .ne (.rd (.var tmpH)) (.null (.strct elem)))
                    (.block [ .assign (dbFld nm nm.freeHead) (.rd (ptrFld tmpH freeNextName))
                            , .assign (dbFld nm nm.count) (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
                            , .ret (some (.rd (.var tmpH))) ]))
               = .cond (.bin .ne (.rd (.var tmpH)) (.null (.strct elem)))
                    (.seq (.assign (dbFld nm nm.freeHead) (.rd (ptrFld tmpH freeNextName)))
                      (.seq (.assign (dbFld nm nm.count) (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1))))
                        (.ret (some (.rd (.var tmpH))))))
                    .skip from rfl]
        rw [execAt_cond', hcond_true]
        simp only [bind, Except.bind]
        rw [execAt_seq', h2]
        simp only [bind, Except.bind]
        rw [execAt_seq', h3]
        simp only [bind, Except.bind]
        have hloc3 : σ₃.getLocal tmpH = some (.ptr q) := by
          have hw3_loc := Store.writePath_loc hw3
          have hw2_loc := Store.writePath_loc hw2
          simp only [Store.getLocal, hw3_loc, hw2_loc]
          rfl
        simp only [execAt, evalExpr, resolve, readLoc, hloc3, bind, Except.bind]
      rw [show (allocDef nm elem).body
             = .seq (.assign (.var tmpH) (.rd (dbFld nm nm.freeHead)))
                (.seq (.when (.bin .ne (.rd (.var tmpH)) (.null (.strct elem)))
                        (.block [ .assign (dbFld nm nm.freeHead) (.rd (ptrFld tmpH freeNextName))
                                , .assign (dbFld nm nm.count) (.bin .add (.rd (dbFld nm nm.count)) (.lit (.u32 1)))
                                , .ret (some (.rd (.var tmpH))) ]))
                  (.ret (some (.null (.strct elem))))) from rfl]
      rw [execAt_seq', h1]
      simp only [bind, Except.bind]
      rw [execAt_seq', hwhen]
      rfl
    let m' := σ₃.toMem
    have hframe : buildFrame m (allocDef nm elem) [] = .ok [(tmpH, .null)] := rfl
    have hcall : callFun p m nm.alloc [] = .ok (m', some (.ptr q)) := by
      exact callFun_ret (p := p) (m := m) (fd := allocDef nm elem) (args := []) hlook hk hframe hbody
    have hmem_eq : ∀ r, (dbPath nm nm.freeHead).overlaps r = false →
                        (dbPath nm nm.count).overlaps r = false →
                        readMem m' r = readMem m r := by
      intro r hr1 hr2
      have hrw3 : σ₃.readPath r = σ₂.readPath r :=
        Store.readPath_writePath_disjoint hw3 hr2
      have hrw2 : σ₂.readPath r = (m.toStore [(tmpH, .ptr q)]).readPath r :=
        Store.readPath_writePath_disjoint hw2 hr1
      rw [readMem_toMem, hrw3, hrw2, readMem_toStore]
    have hq_in_rows : q ∈ poolRows nm fld n := I.sub_free q (by simp)
    have hq_not_live : q ∉ live_qs := I.disj q (by simp)
    have hinv' : PoolInv m' nm fld n free_rest (q :: live_qs) := by
      refine ⟨I.disj_rows, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx; exact I.sub_free x (List.mem_cons_of_mem q hx)
      · intro x hx
        cases List.mem_cons.mp hx with
        | inl heq => rw [heq]; exact hq_in_rows
        | inr hmem => exact I.sub_live x hmem
      · exact (List.nodup_cons.mp I.nodup_free).2
      · exact List.nodup_cons.mpr ⟨hq_not_live, I.nodup_live⟩
      · intro x hx
        have hx_free : x ∈ q :: free_rest := List.mem_cons_of_mem q hx
        have hx_not_live : x ∉ live_qs := I.disj x hx_free
        have hx_ne_q : x ≠ q := by
          intro heq; subst heq
          exact (List.nodup_cons.mp I.nodup_free).1 hx
        intro hx_live'
        cases List.mem_cons.mp hx_live' with
        | inl heq => exact hx_ne_q heq
        | inr hmem => exact hx_not_live hmem
      · rw [readMem_toMem]
        have hrw3 : σ₃.readPath (dbPath nm nm.freeHead) = σ₂.readPath (dbPath nm nm.freeHead) :=
          Store.readPath_writePath_disjoint hw3 (by rw [overlaps_symm]; exact hdisj_db)
        have hrw2 : σ₂.readPath (dbPath nm nm.freeHead) = some (headOf free_rest) :=
          Store.readPath_writePath_self hw2
        rw [hrw3, hrw2]
      · have hframe : ∀ x ∈ free_rest, readMem m' (fldPath x freeNextName) = readMem m (fldPath x freeNextName) := by
          intro x hx
          have hx_row : x ∈ poolRows nm fld n := I.sub_free x (List.mem_cons_of_mem q hx)
          have hpar := I.parent x hx_row
          have hr1 : (dbPath nm nm.freeHead).overlaps (fldPath x freeNextName) = false := by
            rw [overlaps_symm]; exact overlaps_ext hpar.1
          have hr2 : (dbPath nm nm.count).overlaps (fldPath x freeNextName) = false := by
            rw [overlaps_symm]; exact overlaps_ext hpar.2
          exact hmem_eq (fldPath x freeNextName) hr1 hr2
        exact Reaches.frame (hrest.head_eq ▸ hrest) hframe
      · rw [readMem_toMem, Store.readPath_writePath_self hw3]
        simp
      · intro x hx
        have hpar := I.parent x hx
        have hr1 : (dbPath nm nm.freeHead).overlaps (fldPath x freeNextName) = false := by
          rw [overlaps_symm]; exact overlaps_ext hpar.1
        have hr2 : (dbPath nm nm.count).overlaps (fldPath x freeNextName) = false := by
          rw [overlaps_symm]; exact overlaps_ext hpar.2
        rw [hmem_eq (fldPath x freeNextName) hr1 hr2]
        exact I.fields x hx
      · intro x hx
        exact I.parent x hx
    exact ⟨m', hcall, hinv', hq_not_live, by simp, hmem_eq⟩

/-! ## Assembling a program -/

def elemFields (elem : Ident) : List (Ident × Ty) :=
  [(freeNextName, .ptr (.strct elem))]

def dbFields (nm : Names) (elem : Ident) : List (Ident × Ty) :=
  [(nm.freeHead, .ptr (.strct elem)), (nm.count, .scalar .u32)]

def genPool (d : Dmmeta.Db) : Option Program := do
  let dbName ← d.root
  let full := d.withBuiltins
  let dbC ← full.find? dbName
  let fld ← dbC.fields.find? (fun f => f.reftype == .Inlary)
  let elemC ← full.find? fld.arg
  let n ← full.inlaryMax? dbC.name fld.name
  let dbN := Dmmeta.mangle dbC.name
  let elemN := Dmmeta.mangle elemC.name
  let fldN := Dmmeta.mangle fld.name
  let nm := names dbN fldN
  some
    { structs := Layout.addFields dbN (dbFields nm elemN)
                   (Layout.addFields elemN (elemFields elemN)
                     (Dmmeta.genStructs d))
    , globals := Dmmeta.genGlobals d
    , funs    := [ initDef nm fldN n elemN
                 , allocDef nm elemN
                 , freeDef nm elemN
                 , sizeDef nm
                 , maxDef nm n ] }

/-! ## Checked -/

namespace Checks

open Dmmeta

example : (genPool Examples.boundedDb).map CSubset.Wf.check = some [] := rfl

example : (genPool Examples.boundedDb).map (fun p => p.funs.map FunDef.name)
    = some ["OrderDb_row_Init", "OrderDb_row_Alloc", "OrderDb_row_Free",
            "OrderDb_row_N", "OrderDb_row_Max"] := rfl

example : (genPool Examples.boundedDb).map
    (fun p => (p.structs.head?).map (fun sd => sd.fields.map Prod.fst))
    = some (some ["id", "price", "qty", "_freenext"]) := rfl

example : (genPool Examples.boundedDb).map
    (fun p => p.structs.map (fun sd => sd.name)) = some ["order_row", "OrderDb"] := rfl

example : (genPool Examples.boundedDb).map (fun p => p.globals)
    = some [{ name := "g_OrderDb", ty := CSubset.Ty.strct "OrderDb" }] := rfl

end Checks
end Pool
end Templates

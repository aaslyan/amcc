import Amcc.CSubset.Syntax
import Amcc.CSubset.Value
import Amcc.CSubset.Eval
import Amcc.CSubset.Calls
import Amcc.CSubset.Chain
import Amcc.CSubset.Wf
import Amcc.Dmmeta
import Amcc.Templates.Pool
import Amcc.Templates.Llist

namespace Templates
namespace MiniDb

open CSubset

def elemName : CSubset.Ident := "order_row"
def dbName : CSubset.Ident := "MiniDb"
def poolFld : CSubset.Ident := "pool"
def queueFld : CSubset.Ident := "queue"

def poolNm : Pool.Names := Pool.names dbName poolFld
def queueNm : Llist.Names := Llist.names dbName queueFld

/-- Minimal schema declaring an inline array pool and intrusive list queue. -/
def miniDb (cap : Nat) : Dmmeta.Db where
  ctypes :=
    [ { name   := elemName
      , fields := [ { name := "id",  arg := "u64", reftype := .Pkey }
                  , { name := "qty", arg := "u64", reftype := .Val } ] }
    , { name   := dbName
      , fields := [ { name := poolFld,  arg := elemName, reftype := .Inlary }
                  , { name := queueFld, arg := elemName, reftype := .Llist } ] } ]
  attrs  := [ { ctype := dbName, field := poolFld, data := .inlary cap } ]
  root   := some dbName

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

/-- Multi-template C AST generator synthesizing code directly from a `Db` schema. -/
def genC (d : Dmmeta.Db) : Option Program := do
  let dbName ← d.root
  let full := d.withBuiltins
  let dbC ← full.find? dbName
  let poolFld ← dbC.fields.find? (fun f => f.reftype == .Inlary)
  let queueFld ← dbC.fields.find? (fun f => f.reftype == .Llist)
  let elemC ← full.find? poolFld.arg
  let cap ← d.inlaryMax? dbC.name poolFld.name
  let dbN := Dmmeta.mangle dbC.name
  let elemN := Dmmeta.mangle elemC.name
  let pNm := Pool.names dbN (Dmmeta.mangle poolFld.name)
  let qNm := Llist.names dbN (Dmmeta.mangle queueFld.name)
  let poolFldN := Dmmeta.mangle poolFld.name
  let poolDefs :=
    [ Pool.initDef pNm poolFldN cap elemN
    , Pool.allocDef pNm elemN
    , Pool.freeDef pNm elemN
    , Pool.sizeDef pNm
    , Pool.maxDef pNm cap ]
  let queueDefs :=
    [ Llist.initDef qNm elemN
    , Llist.insertDef qNm elemN
    , Llist.insertTailDef qNm elemN
    , Llist.removeDef qNm elemN
    , Llist.firstDef qNm elemN
    , Llist.nextDef qNm elemN
    , Llist.prevDef qNm elemN
    , Llist.inQDef qNm elemN
    , Llist.emptyQDef qNm elemN
    , Llist.sizeDef qNm ]
  let insDef : FunDef :=
    { name   := dbN ++ "_Insert"
    , params := [("id", .scalar .u64), ("qty", .scalar .u64)]
    , ret    := none
    , locals := [Llist.ptrLocal "row" elemN]
    , body   := .block
        [ .call (some "row") pNm.alloc []
        , .when (.bin .ne (.rd (.var "row")) (.null (.strct elemN)))
            (.block [ .assign (Llist.ptrFld "row" "id") (.rd (.var "id"))
                    , .assign (Llist.ptrFld "row" "qty") (.rd (.var "qty"))
                    , .call none qNm.insertTail [.rd (.var "row")] ]) ] }
  let elemExt :=
    [ (Pool.freeNextName, .ptr (.strct elemN))
    , (qNm.next, .ptr (.strct elemN))
    , (qNm.prev, .ptr (.strct elemN))
    , (qNm.inlist, .scalar .bool) ]
  let dbExt :=
    [ (pNm.freeHead, .ptr (.strct elemN))
    , (pNm.count, .scalar .u32)
    , (qNm.head, .ptr (.strct elemN))
    , (qNm.tail, .ptr (.strct elemN))
    , (qNm.count, .scalar .u32) ]
  some
    { structs := Layout.addFields dbN dbExt
                   (Layout.addFields elemN elemExt
                     (Dmmeta.genStructs d))
    , globals := Dmmeta.genGlobals d
    , funs    := poolDefs ++ queueDefs ++ [insDef] }

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

theorem genC_miniDb (cap : Nat) :
    genC (miniDb cap) = some (genMiniDb cap) := rfl

/-- Insertion statement calling MiniDb_Insert(v.1, v.2). -/
def insertStmt (v : UInt64 × UInt64) : Stmt :=
  .call none "MiniDb_Insert" [.lit (.u64 v.1), .lit (.u64 v.2)]

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
  payload : ∀ q ∈ Pool.poolRows poolNm poolFld cap,
              (readMem m (fldPath q "id")).isSome = true ∧ (readMem m (fldPath q "qty")).isSome = true
  disj_db : ∀ x ∈ [poolNm.freeHead, poolNm.count],
            ∀ y ∈ [queueNm.head, queueNm.tail, queueNm.count],
            (Pool.dbPath poolNm x).overlaps (Llist.dbPath queueNm y) = false

/-- Abstract state decoder: decodes list of orders from memory. -/
def absDb (m : Mem) (fuel : Nat) : Option (List (UInt64 × UInt64)) := do
  let es ← Llist.elems m queueNm fuel (Llist.head m queueNm)
  es.mapM (readOrder m)

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

theorem freeNext_disjoint_queue (q : Path) :
    (fldPath q Pool.freeNextName).overlaps (fldPath q queueNm.next) = false
    ∧ (fldPath q Pool.freeNextName).overlaps (fldPath q queueNm.prev) = false
    ∧ (fldPath q Pool.freeNextName).overlaps (fldPath q queueNm.inlist) = false := by
  have h1 : Pool.freeNextName ≠ queueNm.next := by decide
  have h2 : Pool.freeNextName ≠ queueNm.prev := by decide
  have h3 : Pool.freeNextName ≠ queueNm.inlist := by decide
  exact ⟨fldPath_ne_disjoint h1, fldPath_ne_disjoint h2, fldPath_ne_disjoint h3⟩

theorem poolRows_mem_fld_disjoint_poolDb (cap : Nat) {q : Path} (hq : q ∈ Pool.poolRows poolNm poolFld cap)
    (fldName : CSubset.Ident) (x : CSubset.Ident) (hx : x ≠ poolFld) :
    (fldPath q fldName).overlaps (Pool.dbPath poolNm x) = false := by
  simp [Pool.poolRows, Pool.cellPath] at hq
  obtain ⟨i, _, rfl⟩ := hq
  simp [fldPath, Pool.dbPath, Path.overlaps, List.isPrefixOf, hx]

theorem poolRows_mem_fld_disjoint_queueDb (cap : Nat) {q : Path} (hq : q ∈ Pool.poolRows poolNm poolFld cap)
    (fldName : CSubset.Ident) (x : CSubset.Ident) (hx : x ≠ poolFld) :
    (fldPath q fldName).overlaps (Llist.dbPath queueNm x) = false := by
  simp [Pool.poolRows, Pool.cellPath] at hq
  obtain ⟨i, _, rfl⟩ := hq
  simp [fldPath, Llist.dbPath, Path.overlaps, List.isPrefixOf, hx]

theorem poolRow_disjoint_queueDb (cap : Nat) {q : Path} (hq : q ∈ Pool.poolRows poolNm poolFld cap)
    (x : CSubset.Ident) (hx : x ≠ poolFld) :
    q.overlaps (Llist.dbPath queueNm x) = false := by
  simp [Pool.poolRows, Pool.cellPath] at hq
  obtain ⟨i, _, rfl⟩ := hq
  simp [Llist.dbPath, Path.overlaps, List.isPrefixOf, hx]

theorem poolRow_disjoint_queue_parent (cap : Nat) {q : Path} (hq : q ∈ Pool.poolRows poolNm poolFld cap) :
    q.overlaps (Llist.dbPath queueNm queueNm.head) = false
    ∧ q.overlaps (Llist.dbPath queueNm queueNm.tail) = false
    ∧ q.overlaps (Llist.dbPath queueNm queueNm.count) = false := by
  have h1 : queueNm.head ≠ poolFld := by decide
  have h2 : queueNm.tail ≠ poolFld := by decide
  have h3 : queueNm.count ≠ poolFld := by decide
  exact ⟨poolRow_disjoint_queueDb cap hq queueNm.head h1,
         poolRow_disjoint_queueDb cap hq queueNm.tail h2,
         poolRow_disjoint_queueDb cap hq queueNm.count h3⟩

theorem queue_fields_ne_poolFld {x : CSubset.Ident} (hx : x ∈ [queueNm.head, queueNm.tail, queueNm.count]) :
    x ≠ poolFld := by
  rcases List.mem_cons.mp hx with rfl | hx1
  · decide
  · rcases List.mem_cons.mp hx1 with rfl | hx2
    · decide
    · rcases List.mem_cons.mp hx2 with rfl | hx3
      · decide
      · nomatch hx3

theorem pool_fields_ne_poolFld {x : CSubset.Ident} (hx : x ∈ [poolNm.freeHead, poolNm.count]) :
    x ≠ poolFld := by
  rcases List.mem_cons.mp hx with rfl | hx1
  · decide
  · rcases List.mem_cons.mp hx1 with rfl | hx2
    · decide
    · nomatch hx2

theorem rowsDisjoint_sub {rows : List Path} (hdisj : RowsDisjoint rows) {sub : List Path}
    (hsub : ∀ x ∈ sub, x ∈ rows) : RowsDisjoint sub := by
  intro p1 h1 p2 h2 hne
  exact hdisj p1 (hsub p1 h1) p2 (hsub p2 h2) hne

theorem mapM_append_singleton {α β : Type} (f : α → Option β) (xs : List α) (x : α) (ys : List β) (y : β)
    (hxs : xs.mapM f = some ys) (hx : f x = some y) :
    (xs ++ [x]).mapM f = some (ys ++ [y]) := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil] at hxs
    cases hxs
    simp [List.mapM_cons, List.mapM_nil, hx]
  | cons a as ih =>
    simp only [List.mapM_cons] at hxs
    cases hfa : f a with
    | none => simp [hfa] at hxs
    | some a' =>
      cases has : as.mapM f with
      | none => simp [hfa, has] at hxs
      | some bs =>
        simp only [hfa, has] at hxs
        cases hxs
        have ih_res := ih bs has
        simp [List.cons_append, List.mapM_cons, hfa, ih_res]

theorem mapM_congr {α β : Type} (f g : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    have ha : f a = g a := h a (List.mem_cons.mpr (Or.inl rfl))
    have has : ∀ x ∈ as, f x = g x := fun x hx => h x (List.mem_cons_of_mem a hx)
    simp [List.mapM_cons, ha, ih has]

theorem mapM_isSome_iff_exists {α β : Type} (f : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, (f x).isSome = true) :
    ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    have has : ∀ x ∈ as, (f x).isSome = true := fun x hx => h x (List.mem_cons_of_mem a hx)
    obtain ⟨bs, hbs⟩ := ih has
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    exact ⟨a' :: bs, by simp [List.mapM_cons, ha', hbs]⟩

theorem execStmt_eq_execAt (p : Program) (d : Nat) (s : Stmt) (σ : Store) :
    execStmt p d s σ = execAt p (match d with | 0 => fun _ _ => .error .depth | d' + 1 => execStmt p d') s σ := by
  cases d <;> rfl

theorem step_assign_ptrFld {p : Program} {callee} {σ : Store} {ptr x : CSubset.Ident} {q : Path}
    {e : Expr} {v w : Value}
    (hloc : σ.getLocal ptr = some (.ptr q))
    (hread : σ.readPath (fldPath q x) = some v)
    (he : evalExpr σ e = .ok w) :
    ∃ σ', execAt p callee (.assign (Llist.ptrFld ptr x) e) σ = .ok (σ', .normal)
      ∧ σ.writePath (fldPath q x) w = some σ' := by
  have hres : resolve σ (Llist.ptrFld ptr x) = .ok (.glb (fldPath q x)) :=
    Pool.resolve_ptrFld hloc hread
  exact Pool.exec_assign_path (p := p) (callee := callee) hres he hread

theorem exec_allocBody (p : Program) (callee : Stmt → Store → Except Err (Store × Outcome))
    (m : Mem) (nm : Pool.Names) (elem fld : CSubset.Ident) (n : Nat)
    (q : Path) (free_rest live_qs : List Path)
    (hno : Pool.NamesOk nm)
    (I : Pool.PoolInv m nm fld n (q :: free_rest) live_qs) :
    ∃ σ₃, execAt p callee (Pool.allocDef nm elem).body (m.toStore [(Pool.tmpH, .null)])
        = .ok (σ₃, .ret (some (.ptr q)))
      ∧ Pool.PoolInv σ₃.toMem nm fld n free_rest (q :: live_qs)
      ∧ (∀ r, (Pool.dbPath nm nm.freeHead).overlaps r = false →
              (Pool.dbPath nm nm.count).overlaps r = false →
              readMem σ₃.toMem r = readMem m r) := by
  have hne := hno.free_ne_count
  have hdisj_db : (Pool.dbPath nm nm.freeHead).overlaps (Pool.dbPath nm nm.count) = false := by
    simp [Path.overlaps, Pool.dbPath, List.isPrefixOf, hne, Ne.symm hne]
  have hhd : readMem m (Pool.dbPath nm nm.freeHead) = some (.ptr q) := by
    have h := I.head
    simp [headOf] at h
    exact h
  have hchain := I.chain
  cases hchain with
  | cons hqnext hrest =>
    have hqnext_val : readMem m (fldPath q Pool.freeNextName) = some (headOf free_rest) := by
      rw [← hrest.head_eq]; exact hqnext
    have hstore_hd : (m.toStore [(Pool.tmpH, .null)]).readPath (Pool.dbPath nm nm.freeHead) = some (.ptr q) := by
      rw [readMem_toStore]; exact hhd
    have hstore_hd' : (m.toStore [(Pool.tmpH, .ptr q)]).readPath (Pool.dbPath nm nm.freeHead) = some (.ptr q) := by
      rw [readMem_toStore]; exact hhd
    have hstore_qnext : (m.toStore [(Pool.tmpH, .ptr q)]).readPath (fldPath q Pool.freeNextName) = some (headOf free_rest) := by
      rw [readMem_toStore]; exact hqnext_val
    have hstore_count : (m.toStore [(Pool.tmpH, .ptr q)]).readPath (Pool.dbPath nm nm.count) = some (.u32 (UInt32.ofNat live_qs.length)) := by
      rw [readMem_toStore]; exact I.count
    have hloc_tmp : (m.toStore [(Pool.tmpH, .ptr q)]).getLocal Pool.tmpH = some (.ptr q) := rfl
    obtain ⟨σ₂, h2, hw2⟩ :=
      Pool.exec_assign_path (p := p) (callee := callee)
        (l := Pool.dbFld nm nm.freeHead) (e := .rd (Pool.ptrFld Pool.tmpH Pool.freeNextName))
        (w := headOf free_rest)
        (Pool.resolve_dbFld hstore_hd')
        (Pool.read_ptrFld hloc_tmp hstore_qnext)
        hstore_hd'
    have hc2 : σ₂.readPath (Pool.dbPath nm nm.count) = some (.u32 (UInt32.ofNat live_qs.length)) := by
      rw [Store.readPath_writePath_disjoint hw2 hdisj_db]; exact hstore_count
    obtain ⟨σ₃, h3, hw3⟩ :=
      Pool.exec_assign_path (p := p) (callee := callee)
        (l := Pool.dbFld nm nm.count)
        (e := .bin .add (.rd (Pool.dbFld nm nm.count)) (.lit (.u32 1)))
        (w := .u32 (UInt32.ofNat (live_qs.length + 1)))
        (Pool.resolve_dbFld hc2)
        (by simp only [evalExpr, Pool.resolve_dbFld hc2, readLoc, hc2, bind, Except.bind, evalBin, Pool.uint32_ofNat_succ])
        hc2
    have hbody : execAt p callee (Pool.allocDef nm elem).body (m.toStore [(Pool.tmpH, .null)])
        = .ok (σ₃, .ret (some (.ptr q))) := by
      have hloc0 : (m.toStore [(Pool.tmpH, .null)]).getLocal Pool.tmpH = some .null := rfl
      have heval0 : evalExpr (m.toStore [(Pool.tmpH, .null)]) (.rd (Pool.dbFld nm nm.freeHead)) = .ok (.ptr q) :=
        Pool.read_dbFld hstore_hd
      have h1 : execAt p callee (.assign (.var Pool.tmpH) (.rd (Pool.dbFld nm nm.freeHead)))
                  (m.toStore [(Pool.tmpH, .null)])
                = .ok (m.toStore [(Pool.tmpH, .ptr q)], .normal) :=
        step_local (p := p) (callee := callee) hloc0 heval0
      have hcond_true : evalExpr (m.toStore [(Pool.tmpH, .ptr q)])
          (.bin .ne (.rd (.var Pool.tmpH)) (.null (.strct elem))) = .ok (.bool true) := by
        rfl
      have hwhen : execAt p callee
                    (.when (.bin .ne (.rd (.var Pool.tmpH)) (.null (.strct elem)))
                      (.block [ .assign (Pool.dbFld nm nm.freeHead) (.rd (Pool.ptrFld Pool.tmpH Pool.freeNextName))
                              , .assign (Pool.dbFld nm nm.count) (.bin .add (.rd (Pool.dbFld nm nm.count)) (.lit (.u32 1)))
                              , .ret (some (.rd (.var Pool.tmpH))) ]))
                    (m.toStore [(Pool.tmpH, .ptr q)])
                   = .ok (σ₃, .ret (some (.ptr q))) := by
        rw [show (Stmt.when (.bin .ne (.rd (.var Pool.tmpH)) (.null (.strct elem)))
                    (.block [ .assign (Pool.dbFld nm nm.freeHead) (.rd (Pool.ptrFld Pool.tmpH Pool.freeNextName))
                            , .assign (Pool.dbFld nm nm.count) (.bin .add (.rd (Pool.dbFld nm nm.count)) (.lit (.u32 1)))
                            , .ret (some (.rd (.var Pool.tmpH))) ]))
               = .cond (.bin .ne (.rd (.var Pool.tmpH)) (.null (.strct elem)))
                    (.seq (.assign (Pool.dbFld nm nm.freeHead) (.rd (Pool.ptrFld Pool.tmpH Pool.freeNextName)))
                      (.seq (.assign (Pool.dbFld nm nm.count) (.bin .add (.rd (Pool.dbFld nm nm.count)) (.lit (.u32 1))))
                        (.ret (some (.rd (.var Pool.tmpH))))))
                    .skip from rfl]
        rw [execAt_cond', hcond_true]
        simp only [bind, Except.bind]
        rw [execAt_seq', h2]
        simp only [bind, Except.bind]
        rw [execAt_seq', h3]
        simp only [bind, Except.bind]
        have hloc3 : σ₃.getLocal Pool.tmpH = some (.ptr q) := by
          have hw3_loc := Store.writePath_loc hw3
          have hw2_loc := Store.writePath_loc hw2
          simp only [Store.getLocal, hw3_loc, hw2_loc]
          rfl
        simp only [execAt, evalExpr, resolve, readLoc, hloc3, bind, Except.bind]
      rw [show (Pool.allocDef nm elem).body
             = .seq (.assign (.var Pool.tmpH) (.rd (Pool.dbFld nm nm.freeHead)))
                (.seq (.when (.bin .ne (.rd (.var Pool.tmpH)) (.null (.strct elem)))
                        (.block [ .assign (Pool.dbFld nm nm.freeHead) (.rd (Pool.ptrFld Pool.tmpH Pool.freeNextName))
                                , .assign (Pool.dbFld nm nm.count) (.bin .add (.rd (Pool.dbFld nm nm.count)) (.lit (.u32 1)))
                                , .ret (some (.rd (.var Pool.tmpH))) ]))
                  (.ret (some (.null (.strct elem))))) from rfl]
      rw [execAt_seq', h1]
      simp only [bind, Except.bind]
      rw [execAt_seq', hwhen]
      rfl
    let m' := σ₃.toMem
    have hmem_eq : ∀ r, (Pool.dbPath nm nm.freeHead).overlaps r = false →
                        (Pool.dbPath nm nm.count).overlaps r = false →
                        readMem m' r = readMem m r := by
      intro r hr1 hr2
      have hrw3 : σ₃.readPath r = σ₂.readPath r :=
        Store.readPath_writePath_disjoint hw3 hr2
      have hrw2 : σ₂.readPath r = (m.toStore [(Pool.tmpH, .ptr q)]).readPath r :=
        Store.readPath_writePath_disjoint hw2 hr1
      rw [readMem_toMem, hrw3, hrw2, readMem_toStore]
    have hq_in_rows : q ∈ Pool.poolRows nm fld n := I.sub_free q (by simp)
    have hq_not_live : q ∉ live_qs := I.disj q (by simp)
    have hinv' : Pool.PoolInv m' nm fld n free_rest (q :: live_qs) := by
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
        have hrw3 : σ₃.readPath (Pool.dbPath nm nm.freeHead) = σ₂.readPath (Pool.dbPath nm nm.freeHead) :=
          Store.readPath_writePath_disjoint hw3 (by rw [overlaps_symm]; exact hdisj_db)
        have hrw2 : σ₂.readPath (Pool.dbPath nm nm.freeHead) = some (headOf free_rest) :=
          Store.readPath_writePath_self hw2
        rw [hrw3, hrw2]
      · have hframe : ∀ x ∈ free_rest, readMem m' (fldPath x Pool.freeNextName) = readMem m (fldPath x Pool.freeNextName) := by
          intro x hx
          have hx_row : x ∈ Pool.poolRows nm fld n := I.sub_free x (List.mem_cons_of_mem q hx)
          have hpar := I.parent x hx_row
          have hr1 : (Pool.dbPath nm nm.freeHead).overlaps (fldPath x Pool.freeNextName) = false := by
            rw [overlaps_symm]; exact overlaps_ext hpar.1
          have hr2 : (Pool.dbPath nm nm.count).overlaps (fldPath x Pool.freeNextName) = false := by
            rw [overlaps_symm]; exact overlaps_ext hpar.2
          exact hmem_eq (fldPath x Pool.freeNextName) hr1 hr2
        exact Reaches.frame (hrest.head_eq ▸ hrest) hframe
      · rw [readMem_toMem, Store.readPath_writePath_self hw3]
        simp
      · intro x hx
        have hpar := I.parent x hx
        have hr1 : (Pool.dbPath nm nm.freeHead).overlaps (fldPath x Pool.freeNextName) = false := by
          rw [overlaps_symm]; exact overlaps_ext hpar.1
        have hr2 : (Pool.dbPath nm nm.count).overlaps (fldPath x Pool.freeNextName) = false := by
          rw [overlaps_symm]; exact overlaps_ext hpar.2
        rw [hmem_eq (fldPath x Pool.freeNextName) hr1 hr2]
        exact I.fields x hx
      · intro x hx
        exact I.parent x hx
    exact ⟨σ₃, hbody, hinv', hmem_eq⟩

/-- **`mini_insert_forward_sim`**: End-to-end forward simulation theorem for MiniDb insertion. -/
theorem mini_insert_forward_sim
    (cap fuel : Nat) (m : Mem) (v : UInt64 × UInt64)
    {free_rest live_qs queue_es : List Path}
    (I : DbRepInv m cap free_rest live_qs queue_es)
    (hfree : free_rest ≠ [])
    (hfuel : fuel ≥ queue_es.length + 2) :
    ∃ m' free' live' es',
      execStmt (genMiniDb cap) fuel (insertStmt v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal)
      ∧ DbRepInv m' cap free' live' es'
      ∧ absDb m' fuel = some ((absDb m fuel).getD [] ++ [v]) := by
  let p := genMiniDb cap
  cases hfr : free_rest with
  | nil => contradiction
  | cons q free_rest' =>
    have hq_in_rows : q ∈ Pool.poolRows poolNm poolFld cap :=
      I.pool.sub_free q (hfr ▸ by simp)
    have hq_not_live : q ∉ live_qs :=
      I.pool.disj q (hfr ▸ by simp)
    have hq_not_queue : q ∉ queue_es :=
      fun hq_q => hq_not_live (I.queue.sub q hq_q)
    obtain ⟨d, hd⟩ : ∃ d, fuel = d + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    let callee' : Stmt → Store → Except Err (Store × Outcome) :=
      match d' with
      | 0 => fun _ _ => .error .depth
      | d'' + 1 => execStmt p d''
    have hlook_ins : lookupFun p "MiniDb_Insert" = .ok insertOrderDef := rfl
    have hlook_alloc : lookupFun p poolNm.alloc = .ok (Pool.allocDef poolNm elemName) := rfl
    have hlook_tail : lookupFun p queueNm.insertTail = .ok (Llist.insertTailDef queueNm elemName) := rfl
    have hno_pool : Pool.NamesOk poolNm := pool_names_ok
    have hno_queue : Llist.NamesOk queueNm := queue_names_ok
    have I_pool_init : Pool.PoolInv m poolNm poolFld cap (q :: free_rest') live_qs :=
      hfr ▸ I.pool
    obtain ⟨σ_alloc, h_exec_alloc, I_pool_alloc, hframe_alloc⟩ :=
      exec_allocBody p callee' m poolNm elemName poolFld cap q free_rest' live_qs hno_pool I_pool_init
    let m₁ := σ_alloc.toMem
    let σ₀ := m.toStore [("id", .u64 v.1), ("qty", .u64 v.2), ("row", .null)]
    let σ₁ := m₁.toStore [("id", .u64 v.1), ("qty", .u64 v.2), ("row", .ptr q)]
    have hq_disj_freeHead : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath q "id") = false := by
      have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "id" poolNm.freeHead (by decide)
      rw [overlaps_symm]; exact h
    have hq_disj_count : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath q "id") = false := by
      have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "id" poolNm.count (by decide)
      rw [overlaps_symm]; exact h
    have hq_id_m1 : readMem m₁ (fldPath q "id") = readMem m (fldPath q "id") :=
      hframe_alloc (fldPath q "id") hq_disj_freeHead hq_disj_count
    obtain ⟨id_orig, hid_orig⟩ : ∃ w, readMem m (fldPath q "id") = some w :=
      Option.isSome_iff_exists.mp (I.payload q hq_in_rows).1
    have hread_id1 : σ₁.readPath (fldPath q "id") = some id_orig := by
      rw [readMem_toStore, hq_id_m1, hid_orig]
    obtain ⟨σ₂, h_exec_id, hw2⟩ :=
      step_assign_ptrFld (p := p) (callee := execStmt p d') (σ := σ₁) (ptr := "row") (x := "id") (q := q)
        (e := .rd (.var "id")) (v := id_orig) (w := .u64 v.1)
        rfl hread_id1 rfl
    let m₂ := σ₂.toMem
    have hq_disj_freeHead_qty : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath q "qty") = false := by
      have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "qty" poolNm.freeHead (by decide)
      rw [overlaps_symm]; exact h
    have hq_disj_count_qty : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath q "qty") = false := by
      have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "qty" poolNm.count (by decide)
      rw [overlaps_symm]; exact h
    have hq_qty_m1 : readMem m₁ (fldPath q "qty") = readMem m (fldPath q "qty") :=
      hframe_alloc (fldPath q "qty") hq_disj_freeHead_qty hq_disj_count_qty
    obtain ⟨qty_orig, hqty_orig⟩ : ∃ w, readMem m (fldPath q "qty") = some w :=
      Option.isSome_iff_exists.mp (I.payload q hq_in_rows).2
    have hq_id_ne_qty : (fldPath q "id").overlaps (fldPath q "qty") = false :=
      fldPath_ne_disjoint (by decide)
    have hread_qty2 : σ₂.readPath (fldPath q "qty") = some qty_orig := by
      rw [Store.readPath_writePath_disjoint hw2 hq_id_ne_qty, readMem_toStore, hq_qty_m1, hqty_orig]
    have hloc_row2 : σ₂.getLocal "row" = some (.ptr q) := by
      rw [Store.getLocal, Store.writePath_loc hw2]
      rfl
    have hloc_qty2 : σ₂.getLocal "qty" = some (.u64 v.2) := by
      rw [Store.getLocal, Store.writePath_loc hw2]
      rfl
    have heval_qty2 : evalExpr σ₂ (.rd (.var "qty")) = .ok (.u64 v.2) := by
      simp only [evalExpr, resolve, readLoc, hloc_qty2, bind, Except.bind]
    obtain ⟨σ₃, h_exec_qty, hw3⟩ :=
      step_assign_ptrFld (p := p) (callee := execStmt p d') (σ := σ₂) (ptr := "row") (x := "qty") (q := q)
        (e := .rd (.var "qty")) (v := qty_orig) (w := .u64 v.2)
        hloc_row2 hread_qty2 heval_qty2
    let m₃ := σ₃.toMem
    have hframe_m3 : ∀ r, (fldPath q "id").overlaps r = false → (fldPath q "qty").overlaps r = false →
        (Pool.dbPath poolNm poolNm.freeHead).overlaps r = false →
        (Pool.dbPath poolNm poolNm.count).overlaps r = false →
        readMem m₃ r = readMem m r := by
      intro r hid hqty hfree_hd hcnt
      have hrw3 : σ₃.readPath r = σ₂.readPath r :=
        Store.readPath_writePath_disjoint hw3 hqty
      have hrw2 : σ₂.readPath r = σ₁.readPath r :=
        Store.readPath_writePath_disjoint hw2 hid
      rw [readMem_toMem, hrw3, hrw2, readMem_toStore, hframe_alloc r hfree_hd hcnt]
    have I_queue3 : Llist.TailListInv m₃ queueNm (q :: live_qs) queue_es := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr; exact List.mem_cons_of_mem q (I.queue.sub r hr)
      · refine rowsDisjoint_sub I.pool.disj_rows ?_
        intro r hr
        cases List.mem_cons.mp hr with
        | inl heq => rw [heq]; exact hq_in_rows
        | inr hmem => exact I.pool.sub_live r hmem
      · have hdb_hd : (fldPath q "id").overlaps (Llist.dbPath queueNm queueNm.head) = false :=
          poolRows_mem_fld_disjoint_queueDb cap hq_in_rows "id" queueNm.head (by decide)
        have hdb_qty : (fldPath q "qty").overlaps (Llist.dbPath queueNm queueNm.head) = false :=
          poolRows_mem_fld_disjoint_queueDb cap hq_in_rows "qty" queueNm.head (by decide)
        have hdb_fh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (Llist.dbPath queueNm queueNm.head) = false :=
          I.disj_db poolNm.freeHead (by simp) queueNm.head (by simp)
        have hdb_cnt : (Pool.dbPath poolNm poolNm.count).overlaps (Llist.dbPath queueNm queueNm.head) = false :=
          I.disj_db poolNm.count (by simp) queueNm.head (by simp)
        rw [hframe_m3 (Llist.dbPath queueNm queueNm.head) hdb_hd hdb_qty hdb_fh hdb_cnt]
        exact I.queue.head
      · have hdb_hd : (fldPath q "id").overlaps (Llist.dbPath queueNm queueNm.tail) = false :=
          poolRows_mem_fld_disjoint_queueDb cap hq_in_rows "id" queueNm.tail (by decide)
        have hdb_qty : (fldPath q "qty").overlaps (Llist.dbPath queueNm queueNm.tail) = false :=
          poolRows_mem_fld_disjoint_queueDb cap hq_in_rows "qty" queueNm.tail (by decide)
        have hdb_fh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (Llist.dbPath queueNm queueNm.tail) = false :=
          I.disj_db poolNm.freeHead (by simp) queueNm.tail (by simp)
        have hdb_cnt : (Pool.dbPath poolNm poolNm.count).overlaps (Llist.dbPath queueNm queueNm.tail) = false :=
          I.disj_db poolNm.count (by simp) queueNm.tail (by simp)
        rw [hframe_m3 (Llist.dbPath queueNm queueNm.tail) hdb_hd hdb_qty hdb_fh hdb_cnt]
        exact I.queue.tail
      · have hframe_next : ∀ r ∈ queue_es, readMem m₃ (fldPath r queueNm.next) = readMem m (fldPath r queueNm.next) := by
          intro r hr
          have hr_live := I.queue.sub r hr
          have hr_row := I.pool.sub_live r hr_live
          have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
          have hid : (fldPath q "id").overlaps (fldPath r queueNm.next) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hqty : (fldPath q "qty").overlaps (fldPath r queueNm.next) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r queueNm.next) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.next poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r queueNm.next) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.next poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          exact hframe_m3 (fldPath r queueNm.next) hid hqty hfh hcnt
        exact Reaches.frame I.queue.chain hframe_next
      · have hframe_prev : ∀ r ∈ queue_es, readMem m₃ (fldPath r queueNm.prev) = readMem m (fldPath r queueNm.prev) := by
          intro r hr
          have hr_live := I.queue.sub r hr
          have hr_row := I.pool.sub_live r hr_live
          have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
          have hid : (fldPath q "id").overlaps (fldPath r queueNm.prev) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hqty : (fldPath q "qty").overlaps (fldPath r queueNm.prev) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r queueNm.prev) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.prev poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r queueNm.prev) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.prev poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          exact hframe_m3 (fldPath r queueNm.prev) hid hqty hfh hcnt
        exact Backlinked.frame queue_es .null I.queue.back hframe_prev
      · intro r hr
        cases List.mem_cons.mp hr with
        | inl heq =>
          have hq_eq : r = q := heq
          have hq_inlist_disj := (payload_disjoint_queue q).2.2.1
          have hq_qty_disj := (payload_disjoint_queue q).2.2.2.2.2
          have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath q queueNm.inlist) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.inlist poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath q queueNm.inlist) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.inlist poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have hrd : readMem m₃ (fldPath q queueNm.inlist) = readMem m (fldPath q queueNm.inlist) :=
            hframe_m3 (fldPath q queueNm.inlist) hq_inlist_disj hq_qty_disj hfh hcnt
          rw [hq_eq, hrd]
          have hfresh := I.fresh q (hfr ▸ List.mem_cons_self)
          simp [hfresh.inlist, hq_not_queue]
        | inr hmem =>
          have hr_row := I.pool.sub_live r hmem
          have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hmem)
          have hid : (fldPath q "id").overlaps (fldPath r queueNm.inlist) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hqty : (fldPath q "qty").overlaps (fldPath r queueNm.inlist) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r queueNm.inlist) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.inlist poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r queueNm.inlist) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.inlist poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          rw [hframe_m3 (fldPath r queueNm.inlist) hid hqty hfh hcnt]
          exact I.queue.flags r hmem
      · have hdb_hd : (fldPath q "id").overlaps (Llist.dbPath queueNm queueNm.count) = false :=
          poolRows_mem_fld_disjoint_queueDb cap hq_in_rows "id" queueNm.count (by decide)
        have hdb_qty : (fldPath q "qty").overlaps (Llist.dbPath queueNm queueNm.count) = false :=
          poolRows_mem_fld_disjoint_queueDb cap hq_in_rows "qty" queueNm.count (by decide)
        have hdb_fh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (Llist.dbPath queueNm queueNm.count) = false :=
          I.disj_db poolNm.freeHead (by simp) queueNm.count (by simp)
        have hdb_cnt : (Pool.dbPath poolNm poolNm.count).overlaps (Llist.dbPath queueNm queueNm.count) = false :=
          I.disj_db poolNm.count (by simp) queueNm.count (by simp)
        have h_cnt_eq : readMem m₃ (Llist.dbPath queueNm queueNm.count) = readMem m (Llist.dbPath queueNm queueNm.count) :=
          hframe_m3 (Llist.dbPath queueNm queueNm.count) hdb_hd hdb_qty hdb_fh hdb_cnt
        show readMem m₃ (Llist.dbPath queueNm queueNm.count) = some (.u32 (UInt32.ofNat queue_es.length))
        rw [h_cnt_eq]
        exact I.queue.count
      · intro r hr
        cases List.mem_cons.mp hr with
        | inl heq =>
          have hq_eq : r = q := heq
          have hfresh := I.fresh q (hfr ▸ List.mem_cons_self)
          have hq_next_disj := (payload_disjoint_queue q).1
          have hq_prev_disj := (payload_disjoint_queue q).2.1
          have hq_inlist_disj := (payload_disjoint_queue q).2.2.1
          have hq_qty_next_disj := (payload_disjoint_queue q).2.2.2.1
          have hq_qty_prev_disj := (payload_disjoint_queue q).2.2.2.2.1
          have hq_qty_inlist_disj := (payload_disjoint_queue q).2.2.2.2.2
          have hfh_next : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath q queueNm.next) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.next poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_next : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath q queueNm.next) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.next poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have hfh_prev : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath q queueNm.prev) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.prev poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_prev : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath q queueNm.prev) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.prev poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have hfh_inlist : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath q queueNm.inlist) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.inlist poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_inlist : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath q queueNm.inlist) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.inlist poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          rw [hq_eq]
          rw [hframe_m3 (fldPath q queueNm.next) hq_next_disj hq_qty_next_disj hfh_next hcnt_next,
              hframe_m3 (fldPath q queueNm.prev) hq_prev_disj hq_qty_prev_disj hfh_prev hcnt_prev,
              hframe_m3 (fldPath q queueNm.inlist) hq_inlist_disj hq_qty_inlist_disj hfh_inlist hcnt_inlist]
          simp [hfresh.next, hfresh.prev, hfresh.inlist]
        | inr hmem =>
          have hr_row := I.pool.sub_live r hmem
          have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hmem)
          have hid_next : (fldPath q "id").overlaps (fldPath r queueNm.next) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hqty_next : (fldPath q "qty").overlaps (fldPath r queueNm.next) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hid_prev : (fldPath q "id").overlaps (fldPath r queueNm.prev) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hqty_prev : (fldPath q "qty").overlaps (fldPath r queueNm.prev) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hid_inlist : (fldPath q "id").overlaps (fldPath r queueNm.inlist) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hqty_inlist : (fldPath q "qty").overlaps (fldPath r queueNm.inlist) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hfh_next : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r queueNm.next) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.next poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_next : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r queueNm.next) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.next poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have hfh_prev : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r queueNm.prev) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.prev poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_prev : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r queueNm.prev) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.prev poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have hfh_inlist : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r queueNm.inlist) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.inlist poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_inlist : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r queueNm.inlist) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.inlist poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          rw [hframe_m3 (fldPath r queueNm.next) hid_next hqty_next hfh_next hcnt_next,
              hframe_m3 (fldPath r queueNm.prev) hid_prev hqty_prev hfh_prev hcnt_prev,
              hframe_m3 (fldPath r queueNm.inlist) hid_inlist hqty_inlist hfh_inlist hcnt_inlist]
          exact I.queue.fields r hmem
      · intro r hr
        cases List.mem_cons.mp hr with
        | inl heq => rw [heq]; exact poolRow_disjoint_queue_parent cap hq_in_rows
        | inr hmem => exact poolRow_disjoint_queue_parent cap (I.pool.sub_live r hmem)
    have hflag_q_m3 : σ₃.readPath (fldPath q queueNm.inlist) = some (.bool false) := by
      have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath q queueNm.inlist) = false := by
        have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.inlist poolNm.freeHead (by decide)
        rw [overlaps_symm]; exact h
      have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath q queueNm.inlist) = false := by
        have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows queueNm.inlist poolNm.count (by decide)
        rw [overlaps_symm]; exact h
      have hid : (fldPath q "id").overlaps (fldPath q queueNm.inlist) = false := (payload_disjoint_queue q).2.2.1
      have hqty : (fldPath q "qty").overlaps (fldPath q queueNm.inlist) = false := (payload_disjoint_queue q).2.2.2.2.2
      have hfresh := I.fresh q (hfr ▸ List.mem_cons_self)
      change readMem m₃ (fldPath q queueNm.inlist) = some (.bool false)
      rw [hframe_m3 (fldPath q queueNm.inlist) hid hqty hfh hcnt, hfresh.inlist]
    let σ_tail_in := m₃.toStore [(Llist.parRow, .ptr q), (Llist.tmpOld, .null)]
    have hI_tail_in : Llist.TailListInv σ_tail_in.toMem queueNm (q :: live_qs) queue_es := by
      rw [Mem.toStore_toMem]; exact I_queue3
    have hflag_tail_in : σ_tail_in.readPath (fldPath q queueNm.inlist) = some (.bool false) := by
      rw [readMem_toStore, readMem_toMem]; exact hflag_q_m3
    obtain ⟨σ_tail_out, h_exec_tail, I_queue_final, _, _, _, _, hframe_tail⟩ :=
      Llist.exec_insertTailBody (p := p) (callee := callee') (elem := elemName) (σ := σ_tail_in)
        hno_queue hI_tail_in (by simp) hflag_tail_in rfl rfl
    let m' := σ_tail_out.toMem
    have hframe_tail_m : ∀ r,
        (∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps r = false) →
        (∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps r = false) →
        (∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps r = false) →
        readMem m' r = readMem m₃ r := by
      intro r hdb hqf htn
      rw [readMem_toMem, hframe_tail r hdb hqf htn, readMem_toStore]
    have hq_id_m' : readMem m' (fldPath q "id") = some (.u64 v.1) := by
      have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath q "id") = false := by
        intro x hx
        have h := poolRows_mem_fld_disjoint_queueDb cap hq_in_rows "id" x (queue_fields_ne_poolFld hx)
        rw [overlaps_symm]; exact h
      have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath q "id") = false := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · rw [overlaps_symm]; exact (payload_disjoint_queue q).1
        · rcases List.mem_cons.mp hy' with rfl | hy''
          · rw [overlaps_symm]; exact (payload_disjoint_queue q).2.1
          · rcases List.mem_cons.mp hy'' with rfl | hnil
            · rw [overlaps_symm]; exact (payload_disjoint_queue q).2.2.1
            · nomatch hnil
      have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath q "id") = false := by
        intro tail_node htl
        have htn_mem := getLast?_mem htl
        have htn_live := I.queue.sub tail_node htn_mem
        have htn_row := I.pool.sub_live tail_node htn_live
        have htn_ne_q : tail_node ≠ q := fun heq => hq_not_live (heq ▸ htn_live)
        exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row q hq_in_rows htn_ne_q)
      rw [hframe_tail_m (fldPath q "id") hdb hqf htn, readMem_toMem]
      rw [Store.readPath_writePath_disjoint hw3 (fldPath_ne_disjoint (by decide)),
          Store.readPath_writePath_self hw2]
    have hq_qty_m' : readMem m' (fldPath q "qty") = some (.u64 v.2) := by
      have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath q "qty") = false := by
        intro x hx
        have h := poolRows_mem_fld_disjoint_queueDb cap hq_in_rows "qty" x (queue_fields_ne_poolFld hx)
        rw [overlaps_symm]; exact h
      have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath q "qty") = false := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · rw [overlaps_symm]; exact (payload_disjoint_queue q).2.2.2.1
        · rcases List.mem_cons.mp hy' with rfl | hy''
          · rw [overlaps_symm]; exact (payload_disjoint_queue q).2.2.2.2.1
          · rcases List.mem_cons.mp hy'' with rfl | hnil
            · rw [overlaps_symm]; exact (payload_disjoint_queue q).2.2.2.2.2
            · nomatch hnil
      have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath q "qty") = false := by
        intro tail_node htl
        have htn_mem := getLast?_mem htl
        have htn_live := I.queue.sub tail_node htn_mem
        have htn_row := I.pool.sub_live tail_node htn_live
        have htn_ne_q : tail_node ≠ q := fun heq => hq_not_live (heq ▸ htn_live)
        exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row q hq_in_rows htn_ne_q)
      rw [hframe_tail_m (fldPath q "qty") hdb hqf htn, readMem_toMem,
          Store.readPath_writePath_self hw3]
    have h_order_q : readOrder m' q = some v := by
      simp [readOrder, hq_id_m', hq_qty_m']
    have h_exec_full : execStmt p fuel (insertStmt v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal) := by
      rw [hd]
      show execAt p (execStmt p d) (.call none "MiniDb_Insert" [.lit (.u64 v.1), .lit (.u64 v.2)]) (m.toStore ∅) = _
      simp only [execAt, hlook_ins, evalExpr, bind, Except.bind, List.mapM_cons, List.mapM_nil, buildFrame]
      rw [hd']
      show (do let (σ₁, out) ← execAt p (execStmt p d') insertOrderDef.body σ₀; .ok (σ₁.toMem.toStore ∅, Outcome.normal)) = _
      have h_body : insertOrderDef.body =
        .seq (.call (some "row") poolNm.alloc [])
          (.cond (.bin .ne (.rd (.var "row")) (.null (.strct elemName)))
            (.seq (.assign (Llist.ptrFld "row" "id") (.rd (.var "id")))
              (.seq (.assign (Llist.ptrFld "row" "qty") (.rd (.var "qty")))
                (.call none queueNm.insertTail [.rd (.var "row")])))
            .skip) := rfl
      rw [h_body]
      rw [execAt_seq']
      have h_alloc_step : execAt p (execStmt p d') (.call (some "row") poolNm.alloc []) σ₀
          = .ok (σ₁, Outcome.normal) := by
        simp only [execAt, hlook_alloc]
        have h_frame_alloc : buildFrame σ₀.toMem (Pool.allocDef poolNm elemName) []
            = .ok [(Pool.tmpH, Value.null)] := rfl
        simp only [List.mapM_nil, h_frame_alloc, pure, Except.pure, bind, Except.bind]
        dsimp [σ₀]
        have h_alloc_step_call : execStmt p d' (Pool.allocDef poolNm elemName).body (m.toStore [(Pool.tmpH, Value.null)])
            = .ok (σ_alloc, .ret (some (.ptr q))) := by
          rw [execStmt_eq_execAt]
          exact h_exec_alloc
        rw [h_alloc_step_call]
        rfl
      rw [h_alloc_step]
      simp only [bind, Except.bind]
      rw [execAt_cond']
      have hcond_true : evalExpr σ₁ (.bin .ne (.rd (.var "row")) (.null (.strct elemName)))
          = .ok (.bool true) := rfl
      rw [hcond_true]
      simp only [bind, Except.bind]
      rw [execAt_seq', h_exec_id]
      simp only [bind, Except.bind]
      rw [execAt_seq', h_exec_qty]
      simp only [bind, Except.bind]
      have h_call_tail : execAt p (execStmt p d') (.call none queueNm.insertTail [.rd (.var "row")]) σ₃
          = .ok (σ_tail_out.toMem.toStore σ₃.loc, Outcome.normal) := by
        simp only [execAt, hlook_tail]
        have hloc_row3 : σ₃.getLocal "row" = some (.ptr q) := by
          rw [Store.getLocal, Store.writePath_loc hw3, Store.writePath_loc hw2]
          rfl
        simp only [evalExpr, resolve, readLoc, hloc_row3,
                   bind, Except.bind, List.mapM_cons, List.mapM_nil, pure, Except.pure]
        have h_frame : buildFrame σ₃.toMem (Llist.insertTailDef queueNm elemName) [.ptr q]
            = .ok [(Llist.parRow, .ptr q), (Llist.tmpOld, .null)] := rfl
        rw [h_frame]
        dsimp [bind, Except.bind]
        have h_tail_step_call : execStmt p d' (Llist.insertTailDef queueNm elemName).body (σ₃.toMem.toStore [(Llist.parRow, Value.ptr q), (Llist.tmpOld, Value.null)])
            = .ok (σ_tail_out, Outcome.normal) := by
          rw [execStmt_eq_execAt]
          exact h_exec_tail
        rw [h_tail_step_call]
      rw [h_call_tail]
      rfl
    have I_pool_final : Pool.PoolInv m' poolNm poolFld cap free_rest' (q :: live_qs) := by
      refine ⟨I_pool_alloc.disj_rows, I_pool_alloc.sub_free, I_pool_alloc.sub_live,
              I_pool_alloc.nodup_free, I_pool_alloc.nodup_live, I_pool_alloc.disj,
              ?_, ?_, ?_, ?_, I_pool_alloc.parent⟩
      · have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false := by
          intro x hx
          have h := I.disj_db poolNm.freeHead (by simp) x hx
          rw [overlaps_symm]; exact h
        have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false := by
          intro y hy
          exact poolRows_mem_fld_disjoint_poolDb cap hq_in_rows y poolNm.freeHead (by decide)
        have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false := by
          intro tail_node htl
          have htn_mem := getLast?_mem htl
          have htn_live := I.queue.sub tail_node htn_mem
          have htn_row := I.pool.sub_live tail_node htn_live
          exact poolRows_mem_fld_disjoint_poolDb cap htn_row queueNm.next poolNm.freeHead (by decide)
        rw [hframe_tail_m (Pool.dbPath poolNm poolNm.freeHead) hdb hqf htn, readMem_toMem]
        have hqty : (fldPath q "qty").overlaps (Pool.dbPath poolNm poolNm.freeHead) = false :=
          poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "qty" poolNm.freeHead (by decide)
        have hid : (fldPath q "id").overlaps (Pool.dbPath poolNm poolNm.freeHead) = false :=
          poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "id" poolNm.freeHead (by decide)
        rw [Store.readPath_writePath_disjoint hw3 hqty,
            Store.readPath_writePath_disjoint hw2 hid,
            readMem_toStore]
        exact I_pool_alloc.head
      · have hframe_free_chain : ∀ r ∈ free_rest', readMem m' (fldPath r Pool.freeNextName) = readMem m₁ (fldPath r Pool.freeNextName) := by
          intro r hr
          have hr_in_free : r ∈ q :: free_rest' := List.mem_cons_of_mem q hr
          have hr_row := I.pool.sub_free r (hfr ▸ hr_in_free)
          have hr_ne_q : r ≠ q := by
            intro heq
            have : q ∈ free_rest' := heq ▸ hr
            exact (List.nodup_cons.mp (hfr ▸ I.pool.nodup_free)).1 this
          have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r Pool.freeNextName) = false := by
            intro x hx
            have h := poolRows_mem_fld_disjoint_queueDb cap hr_row Pool.freeNextName x (queue_fields_ne_poolFld hx)
            rw [overlaps_symm]; exact h
          have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r Pool.freeNextName) = false := by
            intro y _
            exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r Pool.freeNextName) = false := by
            intro tail_node htl
            have htn_mem := getLast?_mem htl
            have htn_live := I.queue.sub tail_node htn_mem
            have htn_row := I.pool.sub_live tail_node htn_live
            have htn_ne_r : tail_node ≠ r := fun heq => I.pool.disj r (hfr ▸ hr_in_free) (heq ▸ htn_live)
            exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr_row htn_ne_r)
          have hr_disj_qty : (fldPath q "qty").overlaps (fldPath r Pool.freeNextName) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hr_disj_id : (fldPath q "id").overlaps (fldPath r Pool.freeNextName) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          rw [hframe_tail_m (fldPath r Pool.freeNextName) hdb hqf htn, readMem_toMem,
              Store.readPath_writePath_disjoint hw3 hr_disj_qty,
              Store.readPath_writePath_disjoint hw2 hr_disj_id,
              readMem_toStore]
        exact Reaches.frame I_pool_alloc.chain hframe_free_chain
      · have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (Pool.dbPath poolNm poolNm.count) = false := by
          intro x hx
          have h := I.disj_db poolNm.count (by simp) x hx
          rw [overlaps_symm]; exact h
        have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (Pool.dbPath poolNm poolNm.count) = false := by
          intro y _
          exact poolRows_mem_fld_disjoint_poolDb cap hq_in_rows y poolNm.count (by decide)
        have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (Pool.dbPath poolNm poolNm.count) = false := by
          intro tail_node htl
          have htn_mem := getLast?_mem htl
          have htn_live := I.queue.sub tail_node htn_mem
          have htn_row := I.pool.sub_live tail_node htn_live
          exact poolRows_mem_fld_disjoint_poolDb cap htn_row queueNm.next poolNm.count (by decide)
        have hqty : (fldPath q "qty").overlaps (Pool.dbPath poolNm poolNm.count) = false :=
          poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "qty" poolNm.count (by decide)
        have hid : (fldPath q "id").overlaps (Pool.dbPath poolNm poolNm.count) = false :=
          poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "id" poolNm.count (by decide)
        rw [hframe_tail_m (Pool.dbPath poolNm poolNm.count) hdb hqf htn, readMem_toMem,
            Store.readPath_writePath_disjoint hw3 hqty,
            Store.readPath_writePath_disjoint hw2 hid,
            readMem_toStore]
        exact I_pool_alloc.count
      · intro r hr
        have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r Pool.freeNextName) = false := by
          intro x hx
          have h := poolRows_mem_fld_disjoint_queueDb cap hr Pool.freeNextName x (queue_fields_ne_poolFld hx)
          rw [overlaps_symm]; exact h
        have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r Pool.freeNextName) = false := by
          intro y hy
          by_cases heq : r = q
          · rcases List.mem_cons.mp hy with rfl | hy'
            · rw [heq, overlaps_symm]; exact (freeNext_disjoint_queue q).1
            · rcases List.mem_cons.mp hy' with rfl | hy''
              · rw [heq, overlaps_symm]; exact (freeNext_disjoint_queue q).2.1
              · rcases List.mem_cons.mp hy'' with rfl | hnil
                · rw [heq, overlaps_symm]; exact (freeNext_disjoint_queue q).2.2
                · nomatch hnil
          · exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm heq))
        have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r Pool.freeNextName) = false := by
          intro tail_node htl
          have htn_mem := getLast?_mem htl
          have htn_live := I.queue.sub tail_node htn_mem
          have htn_row := I.pool.sub_live tail_node htn_live
          by_cases heq : tail_node = r
          · subst heq; exact fldPath_ne_disjoint (by decide)
          · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr heq)
        have hr_disj_qty : (fldPath q "qty").overlaps (fldPath r Pool.freeNextName) = false := by
          by_cases heq : r = q
          · rw [heq]; exact (payload_disjoint_freeNext q).2
          · exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm heq))
        have hr_disj_id : (fldPath q "id").overlaps (fldPath r Pool.freeNextName) = false := by
          by_cases heq : r = q
          · rw [heq]; exact (payload_disjoint_freeNext q).1
          · exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm heq))
        rw [hframe_tail_m (fldPath r Pool.freeNextName) hdb hqf htn, readMem_toMem,
            Store.readPath_writePath_disjoint hw3 hr_disj_qty,
            Store.readPath_writePath_disjoint hw2 hr_disj_id,
            readMem_toStore]
        exact I_pool_alloc.fields r hr
    have I_rep_final : DbRepInv m' cap free_rest' (q :: live_qs) (queue_es ++ [q]) := by
      refine ⟨I_pool_final, I_queue_final, ?_, ?_, ?_, I.disj_db⟩
      · intro r hr
        have hr_in_free : r ∈ q :: free_rest' := List.mem_cons_of_mem q hr
        have hr_row := I.pool.sub_free r (hfr ▸ hr_in_free)
        have hr_ne_q : r ≠ q := by
          intro heq
          have : q ∈ free_rest' := heq ▸ hr
          exact (List.nodup_cons.mp (hfr ▸ I.pool.nodup_free)).1 this
        have hfresh := I.fresh r (hfr ▸ hr_in_free)
        have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r queueNm.inlist) = false := by
          intro x hx
          have h := poolRows_mem_fld_disjoint_queueDb cap hr_row queueNm.inlist x (queue_fields_ne_poolFld hx)
          rw [overlaps_symm]; exact h
        have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r queueNm.inlist) = false := by
          intro y _
          exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r queueNm.inlist) = false := by
          intro tail_node htl
          have htn_mem := getLast?_mem htl
          have htn_live := I.queue.sub tail_node htn_mem
          have htn_row := I.pool.sub_live tail_node htn_live
          have htn_ne_r : tail_node ≠ r := fun heq => I.pool.disj r (hfr ▸ hr_in_free) (heq ▸ htn_live)
          exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr_row htn_ne_r)
        have hr_disj_qty : (fldPath q "qty").overlaps (fldPath r queueNm.inlist) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hr_disj_id : (fldPath q "id").overlaps (fldPath r queueNm.inlist) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r queueNm.inlist) = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.inlist poolNm.freeHead (by decide)
          rw [overlaps_symm]; exact h
        have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r queueNm.inlist) = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.inlist poolNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_inlist : readMem m' (fldPath r queueNm.inlist) = some (.bool false) := by
          rw [hframe_tail_m (fldPath r queueNm.inlist) hdb hqf htn,
              hframe_m3 (fldPath r queueNm.inlist) hr_disj_id hr_disj_qty hfh hcnt,
              hfresh.inlist]
        have hdb_next : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r queueNm.next) = false := by
          intro x hx
          have h := poolRows_mem_fld_disjoint_queueDb cap hr_row queueNm.next x (queue_fields_ne_poolFld hx)
          rw [overlaps_symm]; exact h
        have hqf_next : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r queueNm.next) = false := by
          intro y _
          exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have htn_next : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r queueNm.next) = false := by
          intro tail_node htl
          have htn_mem := getLast?_mem htl
          have htn_live := I.queue.sub tail_node htn_mem
          have htn_row := I.pool.sub_live tail_node htn_live
          have htn_ne_r : tail_node ≠ r := fun heq => I.pool.disj r (hfr ▸ hr_in_free) (heq ▸ htn_live)
          exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr_row htn_ne_r)
        have hr_disj_qty_next : (fldPath q "qty").overlaps (fldPath r queueNm.next) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hr_disj_id_next : (fldPath q "id").overlaps (fldPath r queueNm.next) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hfh_next : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r queueNm.next) = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.next poolNm.freeHead (by decide)
          rw [overlaps_symm]; exact h
        have hcnt_next : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r queueNm.next) = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.next poolNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_next : readMem m' (fldPath r queueNm.next) = some .null := by
          rw [hframe_tail_m (fldPath r queueNm.next) hdb_next hqf_next htn_next,
              hframe_m3 (fldPath r queueNm.next) hr_disj_id_next hr_disj_qty_next hfh_next hcnt_next,
              hfresh.next]
        have hdb_prev : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r queueNm.prev) = false := by
          intro x hx
          have h := poolRows_mem_fld_disjoint_queueDb cap hr_row queueNm.prev x (queue_fields_ne_poolFld hx)
          rw [overlaps_symm]; exact h
        have hqf_prev : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r queueNm.prev) = false := by
          intro y _
          exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have htn_prev : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r queueNm.prev) = false := by
          intro tail_node htl
          have htn_mem := getLast?_mem htl
          have htn_live := I.queue.sub tail_node htn_mem
          have htn_row := I.pool.sub_live tail_node htn_live
          have htn_ne_r : tail_node ≠ r := fun heq => I.pool.disj r (hfr ▸ hr_in_free) (heq ▸ htn_live)
          exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr_row htn_ne_r)
        have hr_disj_qty_prev : (fldPath q "qty").overlaps (fldPath r queueNm.prev) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hr_disj_id_prev : (fldPath q "id").overlaps (fldPath r queueNm.prev) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hfh_prev : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r queueNm.prev) = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.prev poolNm.freeHead (by decide)
          rw [overlaps_symm]; exact h
        have hcnt_prev : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r queueNm.prev) = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row queueNm.prev poolNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_prev : readMem m' (fldPath r queueNm.prev) = some .null := by
          rw [hframe_tail_m (fldPath r queueNm.prev) hdb_prev hqf_prev htn_prev,
              hframe_m3 (fldPath r queueNm.prev) hr_disj_id_prev hr_disj_qty_prev hfh_prev hcnt_prev,
              hfresh.prev]
        exact ⟨h_inlist, h_next, h_prev⟩
      · intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr_es | rfl
        · have hr_live := I.queue.sub r hr_es
          have hr_row := I.pool.sub_live r hr_live
          have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
          have hdb_id : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r "id") = false := by
            intro x hx
            have h := poolRows_mem_fld_disjoint_queueDb cap hr_row "id" x (queue_fields_ne_poolFld hx)
            rw [overlaps_symm]; exact h
          have hqf_id : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r "id") = false := by
            intro y _
            exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have htn_id : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r "id") = false := by
            intro tail_node htl
            have htn_mem := getLast?_mem htl
            have htn_live := I.queue.sub tail_node htn_mem
            have htn_row := I.pool.sub_live tail_node htn_live
            by_cases heq : tail_node = r
            · subst heq; exact fldPath_ne_disjoint (by decide)
            · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr_row heq)
          have hr_disj_qty_id : (fldPath q "qty").overlaps (fldPath r "id") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hr_disj_id_id : (fldPath q "id").overlaps (fldPath r "id") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hfh_id : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row "id" poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_id : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row "id" poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_id_eq : readMem m' (fldPath r "id") = readMem m (fldPath r "id") := by
            rw [hframe_tail_m (fldPath r "id") hdb_id hqf_id htn_id,
                hframe_m3 (fldPath r "id") hr_disj_id_id hr_disj_qty_id hfh_id hcnt_id]
          have hdb_qty : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r "qty") = false := by
            intro x hx
            have h := poolRows_mem_fld_disjoint_queueDb cap hr_row "qty" x (queue_fields_ne_poolFld hx)
            rw [overlaps_symm]; exact h
          have hqf_qty : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r "qty") = false := by
            intro y _
            exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have htn_qty : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r "qty") = false := by
            intro tail_node htl
            have htn_mem := getLast?_mem htl
            have htn_live := I.queue.sub tail_node htn_mem
            have htn_row := I.pool.sub_live tail_node htn_live
            by_cases heq : tail_node = r
            · subst heq; exact fldPath_ne_disjoint (by decide)
            · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr_row heq)
          have hr_disj_qty_qty : (fldPath q "qty").overlaps (fldPath r "qty") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hr_disj_id_qty : (fldPath q "id").overlaps (fldPath r "qty") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hfh_qty : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row "qty" poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_qty : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr_row "qty" poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_qty_eq : readMem m' (fldPath r "qty") = readMem m (fldPath r "qty") := by
            rw [hframe_tail_m (fldPath r "qty") hdb_qty hqf_qty htn_qty,
                hframe_m3 (fldPath r "qty") hr_disj_id_qty hr_disj_qty_qty hfh_qty hcnt_qty]
          have h_ro : readOrder m' r = readOrder m r := by
            simp [readOrder, h_id_eq, h_qty_eq]
          rw [h_ro]
          exact I.orders r hr_es
        · rw [h_order_q]
          rfl
      · intro r hr
        by_cases heq : r = q
        · subst heq
          simp [hq_id_m', hq_qty_m']
        · have hdb_id : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r "id") = false := by
            intro x hx
            have h := poolRows_mem_fld_disjoint_queueDb cap hr "id" x (queue_fields_ne_poolFld hx)
            rw [overlaps_symm]; exact h
          have hqf_id : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r "id") = false := by
            intro y _
            exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm heq))
          have htn_id : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r "id") = false := by
            intro tail_node htl
            have htn_mem := getLast?_mem htl
            have htn_live := I.queue.sub tail_node htn_mem
            have htn_row := I.pool.sub_live tail_node htn_live
            by_cases heq_t : tail_node = r
            · subst heq_t; exact fldPath_ne_disjoint (by decide)
            · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr heq_t)
          have hr_disj_qty_id : (fldPath q "qty").overlaps (fldPath r "id") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm heq))
          have hr_disj_id_id : (fldPath q "id").overlaps (fldPath r "id") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm heq))
          have hfh_id : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr "id" poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_id : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr "id" poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_id_eq : readMem m' (fldPath r "id") = readMem m (fldPath r "id") := by
            rw [hframe_tail_m (fldPath r "id") hdb_id hqf_id htn_id,
                hframe_m3 (fldPath r "id") hr_disj_id_id hr_disj_qty_id hfh_id hcnt_id]
          have hdb_qty : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r "qty") = false := by
            intro x hx
            have h := poolRows_mem_fld_disjoint_queueDb cap hr "qty" x (queue_fields_ne_poolFld hx)
            rw [overlaps_symm]; exact h
          have hqf_qty : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r "qty") = false := by
            intro y _
            exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm heq))
          have htn_qty : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r "qty") = false := by
            intro tail_node htl
            have htn_mem := getLast?_mem htl
            have htn_live := I.queue.sub tail_node htn_mem
            have htn_row := I.pool.sub_live tail_node htn_live
            by_cases heq_t : tail_node = r
            · subst heq_t; exact fldPath_ne_disjoint (by decide)
            · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr heq_t)
          have hr_disj_qty_qty : (fldPath q "qty").overlaps (fldPath r "qty") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm heq))
          have hr_disj_id_qty : (fldPath q "id").overlaps (fldPath r "qty") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm heq))
          have hfh_qty : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr "qty" poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_qty : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hr "qty" poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_qty_eq : readMem m' (fldPath r "qty") = readMem m (fldPath r "qty") := by
            rw [hframe_tail_m (fldPath r "qty") hdb_qty hqf_qty htn_qty,
                hframe_m3 (fldPath r "qty") hr_disj_id_qty hr_disj_qty_qty hfh_qty hcnt_qty]
          rw [h_id_eq, h_qty_eq]
          exact I.payload r hr
    have h_abs_m : absDb m fuel = queue_es.mapM (readOrder m) := by
      simp only [absDb]
      have hlen_le : queue_es.length ≤ fuel - 1 := by omega
      have hreach := Llist.reaches_headOf_implies_elems m queueNm queue_es I.queue.chain (fuel - 1) hlen_le
      have hfuel_sub : fuel - 1 + 1 = fuel := by omega
      rw [hfuel_sub] at hreach
      have hhd_eq := Llist.head_eq_headOf m queueNm queue_es I.queue.head
      rw [← hhd_eq] at hreach
      rw [hreach]
      rfl
    obtain ⟨ords, hords⟩ :=
      mapM_isSome_iff_exists (readOrder m) queue_es I.orders
    have h_abs_m_eq : absDb m fuel = some ords := by
      rw [h_abs_m, hords]
    have h_abs_m'_val : absDb m' fuel = some (ords ++ [v]) := by
      simp only [absDb]
      have hlen_le' : (queue_es ++ [q]).length ≤ fuel - 1 := by
        simp only [List.length_append, List.length_singleton]; omega
      have hreach' := Llist.reaches_headOf_implies_elems m' queueNm (queue_es ++ [q]) I_queue_final.chain (fuel - 1) hlen_le'
      have hfuel_sub : fuel - 1 + 1 = fuel := by omega
      rw [hfuel_sub] at hreach'
      have hhd_eq' := Llist.head_eq_headOf m' queueNm (queue_es ++ [q]) I_queue_final.head
      rw [← hhd_eq'] at hreach'
      rw [hreach']
      simp only [bind]
      have hframe_order : ∀ r ∈ queue_es, readOrder m' r = readOrder m r := by
        intro r hr
        have hr_live := I.queue.sub r hr
        have hr_row := I.pool.sub_live r hr_live
        have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
        have hdb_id : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r "id") = false := by
          intro x hx
          have h := poolRows_mem_fld_disjoint_queueDb cap hr_row "id" x (queue_fields_ne_poolFld hx)
          rw [overlaps_symm]; exact h
        have hqf_id : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r "id") = false := by
          intro y _
          exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have htn_id : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r "id") = false := by
          intro tail_node htl
          have htn_mem := getLast?_mem htl
          have htn_live := I.queue.sub tail_node htn_mem
          have htn_row := I.pool.sub_live tail_node htn_live
          by_cases heq : tail_node = r
          · subst heq; exact fldPath_ne_disjoint (by decide)
          · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr_row heq)
        have hr_disj_qty_id : (fldPath q "qty").overlaps (fldPath r "id") = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hr_disj_id_id : (fldPath q "id").overlaps (fldPath r "id") = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hfh_id : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r "id") = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row "id" poolNm.freeHead (by decide)
          rw [overlaps_symm]; exact h
        have hcnt_id : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r "id") = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row "id" poolNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_id_eq : readMem m' (fldPath r "id") = readMem m (fldPath r "id") := by
          rw [hframe_tail_m (fldPath r "id") hdb_id hqf_id htn_id,
              hframe_m3 (fldPath r "id") hr_disj_id_id hr_disj_qty_id hfh_id hcnt_id]
        have hdb_qty : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r "qty") = false := by
          intro x hx
          have h := poolRows_mem_fld_disjoint_queueDb cap hr_row "qty" x (queue_fields_ne_poolFld hx)
          rw [overlaps_symm]; exact h
        have hqf_qty : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r "qty") = false := by
          intro y _
          exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have htn_qty : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r "qty") = false := by
          intro tail_node htl
          have htn_mem := getLast?_mem htl
          have htn_live := I.queue.sub tail_node htn_mem
          have htn_row := I.pool.sub_live tail_node htn_live
          by_cases heq : tail_node = r
          · subst heq; exact fldPath_ne_disjoint (by decide)
          · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr_row heq)
        have hr_disj_qty_qty : (fldPath q "qty").overlaps (fldPath r "qty") = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hr_disj_id_qty : (fldPath q "id").overlaps (fldPath r "qty") = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have hfh_qty : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r "qty") = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row "qty" poolNm.freeHead (by decide)
          rw [overlaps_symm]; exact h
        have hcnt_qty : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r "qty") = false := by
          have h := poolRows_mem_fld_disjoint_poolDb cap hr_row "qty" poolNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_qty_eq : readMem m' (fldPath r "qty") = readMem m (fldPath r "qty") := by
          rw [hframe_tail_m (fldPath r "qty") hdb_qty hqf_qty htn_qty,
              hframe_m3 (fldPath r "qty") hr_disj_id_qty hr_disj_qty_qty hfh_qty hcnt_qty]
        simp [readOrder, h_id_eq, h_qty_eq]
      have hmap_es : queue_es.mapM (readOrder m') = some ords := by
        rw [mapM_congr (readOrder m') (readOrder m) queue_es hframe_order]; exact hords
      exact mapM_append_singleton (readOrder m') queue_es q ords v hmap_es h_order_q
    have h_abs_refine : absDb m' fuel = some ((absDb m fuel).getD [] ++ [v]) := by
      rw [h_abs_m'_val, h_abs_m_eq]
      simp
    exact ⟨m', free_rest', q :: live_qs, queue_es ++ [q], h_exec_full, I_rep_final, h_abs_refine⟩

/-- Master forward simulation theorem for MiniDb derived from schema `miniDb cap`:
    Executing the generated C program synthesized from `genC (miniDb cap)` on a well-formed
    memory state `m` produces a state `m'` that preserves representation invariant `DbRepInv`
    and refines the abstract state `absDb` with `v`. -/
theorem mini_insert_forward_sim_schema
    (cap fuel : Nat) (m : Mem) (v : UInt64 × UInt64)
    {free_rest live_qs queue_es : List Path}
    (I : DbRepInv m cap free_rest live_qs queue_es)
    (hfree : free_rest ≠ [])
    (hfuel : fuel ≥ queue_es.length + 2) :
    ∃ (p : Program),
      genC (miniDb cap) = some p ∧
      ∃ m' free' live' es',
        execStmt p fuel (insertStmt v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal)
        ∧ DbRepInv m' cap free' live' es'
        ∧ absDb m' fuel = some ((absDb m fuel).getD [] ++ [v]) := by
  have hp : genC (miniDb cap) = some (genMiniDb cap) := rfl
  obtain ⟨m', free', live', es', hexec, I', habs⟩ :=
    mini_insert_forward_sim cap fuel m v I hfree hfuel
  exact ⟨genMiniDb cap, hp, m', free', live', es', hexec, I', habs⟩

/-- Forward simulation theorem parameterized by any AST `p` matching `genC (miniDb cap)`. -/
theorem mini_insert_forward_sim_of_gen
    (cap fuel : Nat) (m : Mem) (v : UInt64 × UInt64)
    {free_rest live_qs queue_es : List Path}
    {p : Program} (hp : genC (miniDb cap) = some p)
    (I : DbRepInv m cap free_rest live_qs queue_es)
    (hfree : free_rest ≠ [])
    (hfuel : fuel ≥ queue_es.length + 2) :
    ∃ m' free' live' es',
      execStmt p fuel (insertStmt v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal)
      ∧ DbRepInv m' cap free' live' es'
      ∧ absDb m' fuel = some ((absDb m fuel).getD [] ++ [v]) := by
  have h_eq : p = genMiniDb cap := Option.some.inj (hp.symm.trans (genC_miniDb cap))
  subst h_eq
  exact mini_insert_forward_sim cap fuel m v I hfree hfuel

end MiniDb
end Templates


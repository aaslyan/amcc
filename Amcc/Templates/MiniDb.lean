import Amcc.CSubset.Syntax
import Amcc.CSubset.Value
import Amcc.CSubset.Eval
import Amcc.CSubset.Calls
import Amcc.CSubset.Chain
import Amcc.CSubset.Wf
import Amcc.Dmmeta
import Amcc.Templates.Pool
import Amcc.Templates.Llist
import Amcc.Templates.Thash
import Amcc.Templates.ThashRefine

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
  let hashFld? := dbC.fields.find? (fun f => f.reftype == .Thash)
  match hashFld? with
  | none =>
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
  | some hFld =>
    let hNm := Thash.names dbN (Dmmeta.mangle hFld.name)
    let nb ← d.inlaryMax? dbC.name hFld.name
    let mask := nb - 1
    let thashDefs :=
      [ Thash.initDef hNm elemN nb
      , Thash.findDef hNm elemN "id" mask cap
      , Thash.insertDef hNm elemN "id" mask
      , Thash.removeDef hNm elemN "id" mask cap
      , Thash.sizeDef hNm ]
    let insDef : FunDef :=
      { name   := dbN ++ "_Insert"
      , params := [("id", .scalar .u32), ("qty", .scalar .u64)]
      , ret    := none
      , locals := [Llist.ptrLocal "row" elemN]
      , body   := .block
          [ .call (some "row") pNm.alloc []
          , .when (.bin .ne (.rd (.var "row")) (.null (.strct elemN)))
              (.block [ .assign (Llist.ptrFld "row" "id") (.rd (.var "id"))
                      , .assign (Llist.ptrFld "row" "qty") (.rd (.var "qty"))
                      , .call none qNm.insertTail [.rd (.var "row")]
                      , .call none hNm.insert [.rd (.var "row")] ]) ] }
    let elemExt :=
      [ (Pool.freeNextName, .ptr (.strct elemN))
      , (qNm.next, .ptr (.strct elemN))
      , (qNm.prev, .ptr (.strct elemN))
      , (qNm.inlist, .scalar .bool)
      , (hNm.next, .ptr (.strct elemN))
      , (hNm.inhash, .scalar .bool) ]
    let dbExt :=
      [ (pNm.freeHead, .ptr (.strct elemN))
      , (pNm.count, .scalar .u32)
      , (qNm.head, .ptr (.strct elemN))
      , (qNm.tail, .ptr (.strct elemN))
      , (qNm.count, .scalar .u32)
      , (hNm.buckets, .arr (.ptr (.strct elemN)) nb)
      , (hNm.count, .scalar .u32) ]
    some
      { structs := Layout.addFields dbN dbExt
                     (Layout.addFields elemN elemExt
                       (Dmmeta.genStructs d))
      , globals := Dmmeta.genGlobals d
      , funs    := poolDefs ++ queueDefs ++ thashDefs ++ [insDef] }

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
          have hr_in_free : r ∈ free_rest := hfr ▸ List.mem_cons_of_mem q hr
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
        have hr_in_free : r ∈ free_rest := hfr ▸ List.mem_cons_of_mem q hr
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


def hashFld : CSubset.Ident := "th_order"
def hashNm : Thash.Names := Thash.names dbName hashFld

def insertOrderDef3 : FunDef where
  name   := "MiniDb_Insert"
  params := [("id", .scalar .u32), ("qty", .scalar .u64)]
  ret    := none
  locals := [Llist.ptrLocal "row" elemName]
  body   := .block
    [ .call (some "row") poolNm.alloc []
    , .when (.bin .ne (.rd (.var "row")) (.null (.strct elemName)))
        (.block [ .assign (Llist.ptrFld "row" "id") (.rd (.var "id"))
                , .assign (Llist.ptrFld "row" "qty") (.rd (.var "qty"))
                , .call none queueNm.insertTail [.rd (.var "row")]
                , .call none hashNm.insert [.rd (.var "row")] ]) ]

def elemStructDef3 : StructDef where
  name   := elemName
  fields := [ ("id", .scalar .u32)
            , ("qty", .scalar .u64)
            , (Pool.freeNextName, .ptr (.strct elemName))
            , (queueNm.next, .ptr (.strct elemName))
            , (queueNm.prev, .ptr (.strct elemName))
            , (queueNm.inlist, .scalar .bool)
            , (hashNm.next, .ptr (.strct elemName))
            , (hashNm.inhash, .scalar .bool) ]

def dbStructDef3 (cap nb : Nat) : StructDef where
  name   := dbName
  fields := [ (poolFld, .arr (.strct elemName) cap)
            , (poolNm.freeHead, .ptr (.strct elemName))
            , (poolNm.count, .scalar .u32)
            , (queueNm.head, .ptr (.strct elemName))
            , (queueNm.tail, .ptr (.strct elemName))
            , (queueNm.count, .scalar .u32)
            , (hashNm.buckets, .arr (.ptr (.strct elemName)) nb)
            , (hashNm.count, .scalar .u32) ]

def genMiniDb3 (cap nb : Nat) : Program where
  structs := [elemStructDef3, dbStructDef3 cap nb]
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
             , Thash.initDef hashNm elemName nb
             , Thash.findDef hashNm elemName "id" (nb - 1) cap
             , Thash.insertDef hashNm elemName "id" (nb - 1)
             , Thash.removeDef hashNm elemName "id" (nb - 1) cap
             , Thash.sizeDef hashNm
             , insertOrderDef3 ]

def miniDb3 (cap nb : Nat) : Dmmeta.Db where
  ctypes :=
    [ { name   := elemName
      , fields := [ { name := "id",  arg := "u32", reftype := .Pkey }
                  , { name := "qty", arg := "u64", reftype := .Val } ] }
    , { name   := dbName
      , fields := [ { name := poolFld,  arg := elemName, reftype := .Inlary }
                  , { name := queueFld, arg := elemName, reftype := .Llist }
                  , { name := hashFld,  arg := elemName, reftype := .Thash } ] } ]
  attrs  := [ { ctype := dbName, field := poolFld, data := .inlary cap }
            , { ctype := dbName, field := hashFld, data := .inlary nb } ]
  root   := some dbName

theorem genC_miniDb3 (cap nb : Nat) :
    genC (miniDb3 cap nb) = some (genMiniDb3 cap nb) := rfl

def readOrder3 (m : Mem) (q : Path) : Option (UInt32 × UInt64) :=
  match readMem m (fldPath q "id"), readMem m (fldPath q "qty") with
  | some (.u32 id), some (.u64 qty) => some (id, qty)
  | _, _ => none

structure DbRepInv3 (m : Mem) (cap nb mask : Nat)
    (free_rest live_qs queue_es : List Path)
    (chains : List (List Path)) : Prop where
  pool               : Pool.PoolInv m poolNm poolFld cap free_rest live_qs
  queue              : Llist.TailListInv m queueNm live_qs queue_es
  thash              : Thash.RepInv m hashNm elemName "id" mask cap nb (Pool.poolRows poolNm poolFld cap) chains
  fresh_queue        : ∀ q ∈ free_rest, Pool.RowFresh m q queueNm
  fresh_hash         : ∀ q ∈ free_rest, readMem m (fldPath q hashNm.inhash) = some (.bool false)
  orders             : ∀ q ∈ queue_es, (readOrder3 m q).isSome = true
  payload            : ∀ q ∈ Pool.poolRows poolNm poolFld cap,
                         (readMem m (fldPath q "id")).isSome = true ∧ (readMem m (fldPath q "qty")).isSome = true
  disj_db            : ∀ x ∈ [poolNm.freeHead, poolNm.count],
                       ∀ y ∈ [queueNm.head, queueNm.tail, queueNm.count],
                       (Pool.dbPath poolNm x).overlaps (Llist.dbPath queueNm y) = false
  disj_pool_hash     : ∀ x ∈ [poolNm.freeHead, poolNm.count],
                       ∀ b : Nat, (Pool.dbPath poolNm x).overlaps (Thash.bucketPath hashNm b) = false
  disj_pool_hash_cnt : ∀ x ∈ [poolNm.freeHead, poolNm.count],
                       (Pool.dbPath poolNm x).overlaps (Thash.dbPath hashNm hashNm.count) = false
  disj_queue_hash    : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count],
                       ∀ b : Nat, (Llist.dbPath queueNm x).overlaps (Thash.bucketPath hashNm b) = false
  disj_queue_hash_cnt: ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count],
                       (Llist.dbPath queueNm x).overlaps (Thash.dbPath hashNm hashNm.count) = false
  hash_queue_match   : ∀ q, q ∈ chains.flatten ↔ q ∈ queue_es

def absDb3 (m : Mem) (fuel : Nat) : Option (List (UInt32 × UInt64)) := do
  let es ← Llist.elems m queueNm fuel (Llist.head m queueNm)
  es.mapM (readOrder3 m)

theorem queue_names_ok3 : Llist.NamesOk queueNm :=
  Llist.namesOk dbName queueFld

theorem pool_names_ok3 : Pool.NamesOk poolNm :=
  ⟨by decide⟩

theorem hash_names_ok3 : Thash.NamesOk hashNm :=
  Thash.namesOk dbName hashFld

theorem payload_disjoint_hash (q : Path) :
    (fldPath q "id").overlaps (fldPath q hashNm.next) = false
    ∧ (fldPath q "id").overlaps (fldPath q hashNm.inhash) = false
    ∧ (fldPath q "qty").overlaps (fldPath q hashNm.next) = false
    ∧ (fldPath q "qty").overlaps (fldPath q hashNm.inhash) = false := by
  have h1 : "id" ≠ hashNm.next := by decide
  have h2 : "id" ≠ hashNm.inhash := by decide
  have h3 : "qty" ≠ hashNm.next := by decide
  have h4 : "qty" ≠ hashNm.inhash := by decide
  exact ⟨fldPath_ne_disjoint h1, fldPath_ne_disjoint h2, fldPath_ne_disjoint h3, fldPath_ne_disjoint h4⟩

theorem queue_disjoint_hash (q : Path) :
    (fldPath q queueNm.next).overlaps (fldPath q hashNm.next) = false
    ∧ (fldPath q queueNm.next).overlaps (fldPath q hashNm.inhash) = false
    ∧ (fldPath q queueNm.prev).overlaps (fldPath q hashNm.next) = false
    ∧ (fldPath q queueNm.prev).overlaps (fldPath q hashNm.inhash) = false
    ∧ (fldPath q queueNm.inlist).overlaps (fldPath q hashNm.next) = false
    ∧ (fldPath q queueNm.inlist).overlaps (fldPath q hashNm.inhash) = false := by
  have h1 : queueNm.next ≠ hashNm.next := by decide
  have h2 : queueNm.next ≠ hashNm.inhash := by decide
  have h3 : queueNm.prev ≠ hashNm.next := by decide
  have h4 : queueNm.prev ≠ hashNm.inhash := by decide
  have h5 : queueNm.inlist ≠ hashNm.next := by decide
  have h6 : queueNm.inlist ≠ hashNm.inhash := by decide
  exact ⟨fldPath_ne_disjoint h1, fldPath_ne_disjoint h2, fldPath_ne_disjoint h3,
         fldPath_ne_disjoint h4, fldPath_ne_disjoint h5, fldPath_ne_disjoint h6⟩

theorem freeNext_disjoint_hash (q : Path) :
    (fldPath q Pool.freeNextName).overlaps (fldPath q hashNm.next) = false
    ∧ (fldPath q Pool.freeNextName).overlaps (fldPath q hashNm.inhash) = false := by
  have h1 : Pool.freeNextName ≠ hashNm.next := by decide
  have h2 : Pool.freeNextName ≠ hashNm.inhash := by decide
  exact ⟨fldPath_ne_disjoint h1, fldPath_ne_disjoint h2⟩

theorem poolRows_mem_fld_disjoint_hashDb (cap : Nat) {q : Path} (hq : q ∈ Pool.poolRows poolNm poolFld cap)
    (fldName : CSubset.Ident) (x : CSubset.Ident) (hx : x ≠ poolFld) :
    (fldPath q fldName).overlaps (Thash.dbPath hashNm x) = false := by
  simp [Pool.poolRows, Pool.cellPath] at hq
  obtain ⟨i, _, rfl⟩ := hq
  simp [fldPath, Thash.dbPath, Path.overlaps, List.isPrefixOf, hx]

theorem poolRows_mem_fld_disjoint_hashBucket (cap : Nat) {q : Path} (hq : q ∈ Pool.poolRows poolNm poolFld cap)
    (fldName : CSubset.Ident) (b : Nat) :
    (fldPath q fldName).overlaps (Thash.bucketPath hashNm b) = false := by
  simp [Pool.poolRows, Pool.cellPath] at hq
  obtain ⟨i, _, rfl⟩ := hq
  have hne : hashNm.buckets ≠ poolFld := by decide
  simp [fldPath, Thash.bucketPath, Path.overlaps, List.isPrefixOf, hne]

theorem hash_fields_ne_poolFld {x : CSubset.Ident} (hx : x ∈ [hashNm.count]) :
    x ≠ poolFld := by
  rcases List.mem_cons.mp hx with rfl | hx1
  · decide
  · nomatch hx1

theorem mem_flatten_of_mem_bucket {α : Type _} {chains : List (List α)} {b : Nat} (hb : b < chains.length)
    {r : α} (hr : r ∈ chains[b]'hb) : r ∈ chains.flatten :=
  List.mem_flatten.mpr ⟨chains[b]'hb, List.getElem_mem hb, hr⟩

def insertStmt3 (v : UInt32 × UInt64) : Stmt :=
  .call none "MiniDb_Insert" [.lit (.u32 v.1), .lit (.u64 v.2)]

/-- Master forward simulation theorem for MiniDb with 3 reftypes (Pool + Llist + Thash):
    Executing the generated C program on a well-formed memory state `m` produces a state `m'`
    that preserves representation invariant `DbRepInv3` and refines `absDb3` with `v`. -/
theorem mini_insert_forward_sim3
    (cap nb fuel : Nat) (m : Mem) (v : UInt32 × UInt64)
    {free_rest live_qs queue_es : List Path}
    {chains : List (List Path)}
    (I : DbRepInv3 m cap nb (nb - 1) free_rest live_qs queue_es chains)
    (hfree : free_rest ≠ [])
    (h_fresh : ∀ q', (v.1, q') ∉ Thash.elems m "id" chains)
    (hb : (v.1 &&& UInt32.ofNat (nb - 1)).toNat < nb)
    (hfits : (chains[(v.1 &&& UInt32.ofNat (nb - 1)).toNat]'(by rw [I.thash.nb_len]; exact hb)).length < cap)
    (hfuel : fuel ≥ queue_es.length + cap + 5) :
    ∃ m' free' live' es' chains',
      execStmt (genMiniDb3 cap nb) fuel (insertStmt3 v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal)
      ∧ DbRepInv3 m' cap nb (nb - 1) free' live' es' chains'
      ∧ absDb3 m' fuel = some ((absDb3 m fuel).getD [] ++ [v]) := by
  let p := genMiniDb3 cap nb
  cases hfr : free_rest with
  | nil => contradiction
  | cons q free_rest' =>
    have hq_in_rows : q ∈ Pool.poolRows poolNm poolFld cap :=
      I.pool.sub_free q (hfr ▸ by simp)
    have hq_not_live : q ∉ live_qs :=
      I.pool.disj q (hfr ▸ by simp)
    have hq_not_in_queue : q ∉ queue_es :=
      fun hq_q => hq_not_live (I.queue.sub q hq_q)
    have hq_not_in_chains : q ∉ chains.flatten :=
      fun hq_ch => hq_not_in_queue ((I.hash_queue_match q).mp hq_ch)
    obtain ⟨d, hd⟩ : ∃ d, fuel = d + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨d'', hd''⟩ : ∃ d'', d' = d'' + 1 := ⟨d' - 1, by omega⟩
    obtain ⟨d''', hd'''⟩ : ∃ d''', d'' = d''' + 1 := ⟨d'' - 1, by omega⟩
    obtain ⟨d'''', hd''''⟩ : ∃ d'''', d''' = d'''' + 1 := ⟨d''' - 1, by omega⟩

    let callee' : Stmt → Store → Except Err (Store × Outcome) :=
      match d''' with
      | 0 => fun _ _ => .error .depth
      | d5 + 1 => execStmt p d5

    have hlook_ins : lookupFun p "MiniDb_Insert" = .ok (insertOrderDef3) := rfl
    have hlook_alloc : lookupFun p poolNm.alloc = .ok (Pool.allocDef poolNm elemName) := rfl
    have hlook_tail : lookupFun p queueNm.insertTail = .ok (Llist.insertTailDef queueNm elemName) := rfl
    have hlook_hash_ins : lookupFun p hashNm.insert = .ok (Thash.insertDef hashNm elemName "id" (nb - 1)) := rfl
    have hlook_hash_find : lookupFun p hashNm.find = .ok (Thash.findDef hashNm elemName "id" (nb - 1) cap) := rfl

    have hno_pool : Pool.NamesOk poolNm := pool_names_ok3
    have hno_queue : Llist.NamesOk queueNm := queue_names_ok3
    have hno_hash : Thash.NamesOk hashNm := hash_names_ok3
    have hkey_next : "id" ≠ hashNm.next := by decide
    have hkey_inhash : "id" ≠ hashNm.inhash := by decide

    have I_pool_init : Pool.PoolInv m poolNm poolFld cap (q :: free_rest') live_qs :=
      hfr ▸ I.pool
    obtain ⟨σ_alloc, h_exec_alloc, I_pool_alloc, hframe_alloc⟩ :=
      exec_allocBody p (execStmt p d'') m poolNm elemName poolFld cap q free_rest' live_qs hno_pool I_pool_init
    let m₁ := σ_alloc.toMem
    let σ₀ := m.toStore [("id", .u32 v.1), ("qty", .u64 v.2), ("row", .null)]
    let σ₁ := m₁.toStore [("id", .u32 v.1), ("qty", .u64 v.2), ("row", .ptr q)]

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
        (e := .rd (.var "id")) (v := id_orig) (w := .u32 v.1)
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
    have hframe_m3_m1 : ∀ r,
        (fldPath q "id").overlaps r = false →
        (fldPath q "qty").overlaps r = false →
        readMem m₃ r = readMem m₁ r := by
      intro r hid hqty
      have hrw3 : σ₃.readPath r = σ₂.readPath r :=
        Store.readPath_writePath_disjoint hw3 hqty
      have hrw2 : σ₂.readPath r = σ₁.readPath r :=
        Store.readPath_writePath_disjoint hw2 hid
      rw [readMem_toMem, hrw3, hrw2, readMem_toStore]

    have hframe_m3 : ∀ r,
        (fldPath q "id").overlaps r = false →
        (fldPath q "qty").overlaps r = false →
        (Pool.dbPath poolNm poolNm.freeHead).overlaps r = false →
        (Pool.dbPath poolNm poolNm.count).overlaps r = false →
        readMem m₃ r = readMem m r := by
      intro r hid hqty hfree_hd hcnt
      rw [hframe_m3_m1 r hid hqty, hframe_alloc r hfree_hd hcnt]

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
          have hfresh := I.fresh_queue q (hfr ▸ by simp)
          simp [hfresh.inlist, hq_not_in_queue]
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
          have hfresh := I.fresh_queue q (hfr ▸ by simp)
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
          exact ⟨by simp [hfresh.next], by simp [hfresh.prev], by simp [hfresh.inlist]⟩
        | inr hmem =>
          have hr_row := I.pool.sub_live r hmem
          have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hmem)
          have hid_next : (fldPath q "id").overlaps (fldPath r queueNm.next) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hid_prev : (fldPath q "id").overlaps (fldPath r queueNm.prev) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hid_inlist : (fldPath q "id").overlaps (fldPath r queueNm.inlist) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hqty_next : (fldPath q "qty").overlaps (fldPath r queueNm.next) = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have hqty_prev : (fldPath q "qty").overlaps (fldPath r queueNm.prev) = false :=
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
      have hfresh := I.fresh_queue q (hfr ▸ by simp)
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
    let m₄ := σ_tail_out.toMem

    have hframe_tail_m : ∀ r,
        (∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps r = false) →
        (∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps r = false) →
        (∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps r = false) →
        readMem m₄ r = readMem m₃ r := by
      intro r hdb hqf htn
      rw [readMem_toMem, hframe_tail r hdb hqf htn, readMem_toStore]

    have hq_id_m4 : readMem m₄ (fldPath q "id") = some (.u32 v.1) := by
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

    have hq_qty_m4 : readMem m₄ (fldPath q "qty") = some (.u64 v.2) := by
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

    have hq_hash_inhash_m4 : readMem m₄ (fldPath q hashNm.inhash) = some (.bool false) := by
      have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath q hashNm.inhash) = false := by
        intro x hx
        have h := poolRows_mem_fld_disjoint_queueDb cap hq_in_rows hashNm.inhash x (queue_fields_ne_poolFld hx)
        rw [overlaps_symm]; exact h
      have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath q hashNm.inhash) = false := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact (queue_disjoint_hash q).2.1
        · rcases List.mem_cons.mp hy' with rfl | hy''
          · exact (queue_disjoint_hash q).2.2.2.1
          · rcases List.mem_cons.mp hy'' with rfl | hnil
            · exact (queue_disjoint_hash q).2.2.2.2.2
            · nomatch hnil
      have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath q hashNm.inhash) = false := by
        intro tail_node htl
        have htn_mem := getLast?_mem htl
        have htn_live := I.queue.sub tail_node htn_mem
        have htn_row := I.pool.sub_live tail_node htn_live
        have htn_ne_q : tail_node ≠ q := fun heq => hq_not_live (heq ▸ htn_live)
        exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row q hq_in_rows htn_ne_q)
      have hid : (fldPath q "id").overlaps (fldPath q hashNm.inhash) = false := (payload_disjoint_hash q).2.1
      have hqty : (fldPath q "qty").overlaps (fldPath q hashNm.inhash) = false := (payload_disjoint_hash q).2.2.2
      have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath q hashNm.inhash) = false := by
        have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows hashNm.inhash poolNm.freeHead (by decide)
        rw [overlaps_symm]; exact h
      have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath q hashNm.inhash) = false := by
        have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows hashNm.inhash poolNm.count (by decide)
        rw [overlaps_symm]; exact h
      rw [hframe_tail_m (fldPath q hashNm.inhash) hdb hqf htn,
          hframe_m3 (fldPath q hashNm.inhash) hid hqty hfh hcnt]
      exact I.fresh_hash q (hfr ▸ by simp)

    have h_frame_m4_m : ∀ r ∈ Pool.poolRows poolNm poolFld cap, r ≠ q →
        (∀ fld ∈ ["id", "qty", hashNm.next, hashNm.inhash], readMem m₄ (fldPath r fld) = readMem m (fldPath r fld)) := by
      intro r hr hr_ne_q fld hfld
      have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r fld) = false := by
        intro x hx
        have h := poolRows_mem_fld_disjoint_queueDb cap hr fld x (queue_fields_ne_poolFld hx)
        rw [overlaps_symm]; exact h
      have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r fld) = false := by
        intro y _
        exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
      have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r fld) = false := by
        intro tail_node htl
        have htn_mem := getLast?_mem htl
        have htn_live := I.queue.sub tail_node htn_mem
        have htn_row := I.pool.sub_live tail_node htn_live
        by_cases heq : tail_node = r
        · rw [heq]
          rcases List.mem_cons.mp hfld with rfl | hfld'
          · exact fldPath_ne_disjoint (by decide)
          · rcases List.mem_cons.mp hfld' with rfl | hfld''
            · exact fldPath_ne_disjoint (by decide)
            · rcases List.mem_cons.mp hfld'' with rfl | hfld'''
              · exact (queue_disjoint_hash r).1
              · rcases List.mem_cons.mp hfld''' with rfl | hnil
                · exact (queue_disjoint_hash r).2.1
                · nomatch hnil
        · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr heq)
      have hid : (fldPath q "id").overlaps (fldPath r fld) = false :=
        fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
      have hqty : (fldPath q "qty").overlaps (fldPath r fld) = false :=
        fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
      have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath r fld) = false := by
        have h := poolRows_mem_fld_disjoint_poolDb cap hr fld poolNm.freeHead (by
          rcases List.mem_cons.mp hfld with rfl | hfld'
          · decide
          · rcases List.mem_cons.mp hfld' with rfl | hfld''
            · decide
            · rcases List.mem_cons.mp hfld'' with rfl | hfld'''
              · decide
              · rcases List.mem_cons.mp hfld''' with rfl | hnil
                · decide
                · nomatch hnil)
        rw [overlaps_symm]; exact h
      have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath r fld) = false := by
        have h := poolRows_mem_fld_disjoint_poolDb cap hr fld poolNm.count (by
          rcases List.mem_cons.mp hfld with rfl | hfld'
          · decide
          · rcases List.mem_cons.mp hfld' with rfl | hfld''
            · decide
            · rcases List.mem_cons.mp hfld'' with rfl | hfld'''
              · decide
              · rcases List.mem_cons.mp hfld''' with rfl | hnil
                · decide
                · nomatch hnil)
        rw [overlaps_symm]; exact h
      rw [hframe_tail_m (fldPath r fld) hdb hqf htn,
          hframe_m3 (fldPath r fld) hid hqty hfh hcnt]

    have h_frame_m4_buckets : ∀ b < nb, readMem m₄ (Thash.bucketPath hashNm b) = readMem m (Thash.bucketPath hashNm b) := by
      intro b hb_lt
      have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (Thash.bucketPath hashNm b) = false := by
        intro x hx; exact I.disj_queue_hash x hx b
      have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (Thash.bucketPath hashNm b) = false := by
        intro y _
        exact poolRows_mem_fld_disjoint_hashBucket cap hq_in_rows y b
      have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (Thash.bucketPath hashNm b) = false := by
        intro tail_node htl
        have htn_mem := getLast?_mem htl
        have htn_live := I.queue.sub tail_node htn_mem
        have htn_row := I.pool.sub_live tail_node htn_live
        exact poolRows_mem_fld_disjoint_hashBucket cap htn_row queueNm.next b
      have hid : (fldPath q "id").overlaps (Thash.bucketPath hashNm b) = false :=
        poolRows_mem_fld_disjoint_hashBucket cap hq_in_rows "id" b
      have hqty : (fldPath q "qty").overlaps (Thash.bucketPath hashNm b) = false :=
        poolRows_mem_fld_disjoint_hashBucket cap hq_in_rows "qty" b
      have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (Thash.bucketPath hashNm b) = false :=
        I.disj_pool_hash poolNm.freeHead (by simp) b
      have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (Thash.bucketPath hashNm b) = false :=
        I.disj_pool_hash poolNm.count (by simp) b
      rw [hframe_tail_m (Thash.bucketPath hashNm b) hdb hqf htn,
          hframe_m3 (Thash.bucketPath hashNm b) hid hqty hfh hcnt]

    have h_frame_m4_hash_cnt : readMem m₄ (Thash.dbPath hashNm hashNm.count) = readMem m (Thash.dbPath hashNm hashNm.count) := by
      have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (Thash.dbPath hashNm hashNm.count) = false := by
        intro x hx; exact I.disj_queue_hash_cnt x hx
      have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (Thash.dbPath hashNm hashNm.count) = false := by
        intro y _
        exact poolRows_mem_fld_disjoint_hashDb cap hq_in_rows y hashNm.count (by decide)
      have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (Thash.dbPath hashNm hashNm.count) = false := by
        intro tail_node htl
        have htn_mem := getLast?_mem htl
        have htn_live := I.queue.sub tail_node htn_mem
        have htn_row := I.pool.sub_live tail_node htn_live
        exact poolRows_mem_fld_disjoint_hashDb cap htn_row queueNm.next hashNm.count (by decide)
      have hid : (fldPath q "id").overlaps (Thash.dbPath hashNm hashNm.count) = false :=
        poolRows_mem_fld_disjoint_hashDb cap hq_in_rows "id" hashNm.count (by decide)
      have hqty : (fldPath q "qty").overlaps (Thash.dbPath hashNm hashNm.count) = false :=
        poolRows_mem_fld_disjoint_hashDb cap hq_in_rows "qty" hashNm.count (by decide)
      have hfh : (Pool.dbPath poolNm poolNm.freeHead).overlaps (Thash.dbPath hashNm hashNm.count) = false :=
        I.disj_pool_hash_cnt poolNm.freeHead (by simp)
      have hcnt : (Pool.dbPath poolNm poolNm.count).overlaps (Thash.dbPath hashNm hashNm.count) = false :=
        I.disj_pool_hash_cnt poolNm.count (by simp)
      rw [hframe_tail_m (Thash.dbPath hashNm hashNm.count) hdb hqf htn,
          hframe_m3 (Thash.dbPath hashNm hashNm.count) hid hqty hfh hcnt]

    have I_thash4 : Thash.RepInv m₄ hashNm elemName "id" (nb - 1) cap nb (Pool.poolRows poolNm poolFld cap) chains := by
      refine ⟨I.thash.nb_len, I.thash.sub, I.thash.disj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro b hb_lt
        have hb_inv := I.thash.buckets b hb_lt
        refine ⟨?_, ?_, ?_, hb_inv.fits⟩
        · rw [h_frame_m4_buckets b hb_lt]; exact hb_inv.head
        · have hchain_frame : ∀ r ∈ chains[b]' (by rw [I.thash.nb_len]; exact hb_lt), readMem m₄ (fldPath r hashNm.next) = readMem m (fldPath r hashNm.next) := by
            intro r hr
            have hr_flat : r ∈ chains.flatten := mem_flatten_of_mem_bucket (by rw [I.thash.nb_len]; exact hb_lt) hr
            have hr_queue : r ∈ queue_es := (I.hash_queue_match r).mp hr_flat
            have hr_live := I.queue.sub r hr_queue
            have hr_row := I.pool.sub_live r hr_live
            have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
            exact h_frame_m4_m r hr_row hr_ne_q hashNm.next (by simp)
          exact Reaches.frame hb_inv.chain hchain_frame
        · intro r hr
          have hr_flat : r ∈ chains.flatten := mem_flatten_of_mem_bucket (by rw [I.thash.nb_len]; exact hb_lt) hr
          have hr_queue : r ∈ queue_es := (I.hash_queue_match r).mp hr_flat
          have hr_live := I.queue.sub r hr_queue
          have hr_row := I.pool.sub_live r hr_live
          have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
          have h_id := h_frame_m4_m r hr_row hr_ne_q "id" (by simp)
          rw [h_id]
          exact hb_inv.keys r hr
      · intro b hb_lt r hr
        have hr_flat : r ∈ chains.flatten := mem_flatten_of_mem_bucket (by rw [I.thash.nb_len]; exact hb_lt) hr
        have hr_queue : r ∈ queue_es := (I.hash_queue_match r).mp hr_flat
        have hr_live := I.queue.sub r hr_queue
        have hr_row := I.pool.sub_live r hr_live
        have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
        have h_id := h_frame_m4_m r hr_row hr_ne_q "id" (by simp)
        rw [h_id]
        exact I.thash.hash_mod b hb_lt r hr
      · intro b1 hb1 b2 hb2 q1 hq1 q2 hq2 k' hk1 hk2
        have hq1_flat : q1 ∈ chains.flatten := mem_flatten_of_mem_bucket (by rw [I.thash.nb_len]; exact hb1) hq1
        have hq2_flat : q2 ∈ chains.flatten := mem_flatten_of_mem_bucket (by rw [I.thash.nb_len]; exact hb2) hq2
        have hq1_queue : q1 ∈ queue_es := (I.hash_queue_match q1).mp hq1_flat
        have hq1_live := I.queue.sub q1 hq1_queue
        have hq1_row := I.pool.sub_live q1 hq1_live
        have hq1_ne_q : q1 ≠ q := fun heq_q => hq_not_live (heq_q ▸ hq1_live)
        have hq2_queue : q2 ∈ queue_es := (I.hash_queue_match q2).mp hq2_flat
        have hq2_live := I.queue.sub q2 hq2_queue
        have hq2_row := I.pool.sub_live q2 hq2_live
        have hq2_ne_q : q2 ≠ q := fun heq_q => hq_not_live (heq_q ▸ hq2_live)
        have h_id1 := h_frame_m4_m q1 hq1_row hq1_ne_q "id" (by simp)
        have h_id2 := h_frame_m4_m q2 hq2_row hq2_ne_q "id" (by simp)
        rw [h_id1] at hk1
        rw [h_id2] at hk2
        exact I.thash.keys_unique b1 hb1 b2 hb2 q1 hq1 q2 hq2 k' hk1 hk2
      · intro r hr
        by_cases heq_r : r = q
        · rcases heq_r.symm with rfl
          rw [hq_hash_inhash_m4]
          constructor
          · intro h_abs; cases h_abs
          · intro h_in_chains
            have hq_in_q := (I.hash_queue_match q).mp h_in_chains
            exact absurd hq_in_q hq_not_in_queue
        · have h_inhash := h_frame_m4_m r hr heq_r hashNm.inhash (by simp)
          rw [h_inhash]
          exact I.thash.flags r hr
      · rw [h_frame_m4_hash_cnt]; exact I.thash.count
      · intro r hr
        by_cases heq_r : r = q
        · rcases heq_r.symm with rfl
          have hdb_next : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath q hashNm.next) = false := by
            intro x hx
            have h := poolRows_mem_fld_disjoint_queueDb cap hq_in_rows hashNm.next x (queue_fields_ne_poolFld hx)
            rw [overlaps_symm]; exact h
          have hqf_next : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath q hashNm.next) = false := by
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact (queue_disjoint_hash q).1
            · rcases List.mem_cons.mp hy' with rfl | hy''
              · exact (queue_disjoint_hash q).2.2.1
              · rcases List.mem_cons.mp hy'' with rfl | hnil
                · exact (queue_disjoint_hash q).2.2.2.2.1
                · nomatch hnil
          have htn_next : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath q hashNm.next) = false := by
            intro tail_node htl
            have htn_mem := getLast?_mem htl
            have htn_live := I.queue.sub tail_node htn_mem
            have htn_row := I.pool.sub_live tail_node htn_live
            have htn_ne_q : tail_node ≠ q := fun heq => hq_not_live (heq ▸ htn_live)
            exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row q hq_in_rows htn_ne_q)
          have hid_next : (fldPath q "id").overlaps (fldPath q hashNm.next) = false := (payload_disjoint_hash q).1
          have hqty_next : (fldPath q "qty").overlaps (fldPath q hashNm.next) = false := (payload_disjoint_hash q).2.2.1
          have hfh_next : (Pool.dbPath poolNm poolNm.freeHead).overlaps (fldPath q hashNm.next) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows hashNm.next poolNm.freeHead (by decide)
            rw [overlaps_symm]; exact h
          have hcnt_next : (Pool.dbPath poolNm poolNm.count).overlaps (fldPath q hashNm.next) = false := by
            have h := poolRows_mem_fld_disjoint_poolDb cap hq_in_rows hashNm.next poolNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_next : readMem m₄ (fldPath q hashNm.next) = readMem m (fldPath q hashNm.next) := by
            rw [hframe_tail_m (fldPath q hashNm.next) hdb_next hqf_next htn_next,
                hframe_m3 (fldPath q hashNm.next) hid_next hqty_next hfh_next hcnt_next]
          refine ⟨by rw [h_next]; exact (I.thash.fields q hq_in_rows).1, by rw [hq_hash_inhash_m4]; rfl, by rw [hq_id_m4]; rfl⟩
        · have h_next := h_frame_m4_m r hr heq_r hashNm.next (by simp)
          have h_inhash := h_frame_m4_m r hr heq_r hashNm.inhash (by simp)
          have h_id := h_frame_m4_m r hr heq_r "id" (by simp)
          rw [h_next, h_inhash, h_id]
          exact I.thash.fields r hr
      · intro r hr
        exact I.thash.parent r hr

    have h_fresh4 : ∀ q', (v.1, q') ∉ Thash.elems m₄ "id" chains := by
      intro q' h_in
      rw [Thash.mem_elems_iff] at h_in
      obtain ⟨hq'_flat, hq'_id⟩ := h_in
      have hq'_queue : q' ∈ queue_es := (I.hash_queue_match q').mp hq'_flat
      have hq'_live := I.queue.sub q' hq'_queue
      have hq'_row := I.pool.sub_live q' hq'_live
      have hq'_ne_q : q' ≠ q := fun heq => hq_not_live (heq ▸ hq'_live)
      have h_id := h_frame_m4_m q' hq'_row hq'_ne_q "id" (by simp)
      rw [h_id] at hq'_id
      have h_in_m : (v.1, q') ∈ Thash.elems m "id" chains := Thash.mem_elems_iff.mpr ⟨hq'_flat, hq'_id⟩
      exact h_fresh q' h_in_m

    obtain ⟨σ5, h_exec_hash, I_thash_final, hq_inhash_m5, hq_next_m5, hq_bkt_m5, h_cnt_m5, hframe_hash⟩ :=
      Thash.exec_insertBody (d := d'''')
        hlook_hash_find hno_hash hkey_next hkey_inhash I_thash4
        hq_in_rows hq_not_in_chains hq_hash_inhash_m4 hq_id_m4 hb hfits h_fresh4
    let m' := σ5.toMem

    have h_exec_full : execStmt p fuel (insertStmt3 v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal) := by
      rw [hd]
      show execAt p (execStmt p d) (.call none "MiniDb_Insert" [.lit (.u32 v.1), .lit (.u64 v.2)]) (m.toStore ∅) = _
      have h_frame_ins : buildFrame (m.toStore ∅).toMem (insertOrderDef3) [Value.u32 v.1, Value.u64 v.2]
          = .ok [("id", .u32 v.1), ("qty", .u64 v.2), ("row", .null)] := rfl
      simp only [execAt, hlook_ins, evalExpr, bind, Except.bind, pure, Except.pure, List.mapM_cons, List.mapM_nil, h_frame_ins]
      rw [hd']
      show (do let (σ₁, out) ← execAt p (execStmt p d') (insertOrderDef3).body σ₀; .ok (σ₁.toMem.toStore ∅, Outcome.normal)) = _
      have h_body : (insertOrderDef3).body =
        .seq (.call (some "row") poolNm.alloc [])
          (.cond (.bin .ne (.rd (.var "row")) (.null (.strct elemName)))
            (.seq (.assign (Llist.ptrFld "row" "id") (.rd (.var "id")))
              (.seq (.assign (Llist.ptrFld "row" "qty") (.rd (.var "qty")))
                (.seq (.call none queueNm.insertTail [.rd (.var "row")])
                  (.call none hashNm.insert [.rd (.var "row")]))))
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
          rw [hd'', execStmt_eq_execAt]
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
      rw [execAt_seq']
      have h_tail_step : execAt p (execStmt p d') (.call none queueNm.insertTail [.rd (.var "row")]) σ₃
          = .ok (m₄.toStore σ₃.loc, Outcome.normal) := by
        simp only [execAt, hlook_tail]
        have hloc_row3 : σ₃.getLocal "row" = some (.ptr q) := by
          rw [Store.getLocal, Store.writePath_loc hw3, Store.writePath_loc hw2]
          rfl
        simp only [evalExpr, resolve, readLoc, hloc_row3,
                   bind, Except.bind, List.mapM_cons, List.mapM_nil, pure, Except.pure]
        have h_frame_tail : buildFrame σ₃.toMem (Llist.insertTailDef queueNm elemName) [.ptr q]
            = .ok [(Llist.parRow, .ptr q), (Llist.tmpOld, .null)] := rfl
        rw [h_frame_tail]
        dsimp [bind, Except.bind]
        have h_tail_step_call : execStmt p d' (Llist.insertTailDef queueNm elemName).body (σ₃.toMem.toStore [(Llist.parRow, Value.ptr q), (Llist.tmpOld, Value.null)])
            = .ok (σ_tail_out, Outcome.normal) := by
          rw [hd'', hd''', execStmt_eq_execAt]
          exact h_exec_tail
        rw [h_tail_step_call]
      rw [h_tail_step]
      simp only [bind, Except.bind]
      have h_hash_step : execAt p (execStmt p d') (.call none hashNm.insert [.rd (.var "row")]) (m₄.toStore σ₃.loc)
          = .ok (m'.toStore σ₃.loc, Outcome.normal) := by
        simp only [execAt, hlook_hash_ins]
        have hloc_row4 : (m₄.toStore σ₃.loc).getLocal "row" = some (.ptr q) := by
          rw [Store.getLocal, Store.writePath_loc hw3, Store.writePath_loc hw2]
          rfl
        simp only [evalExpr, resolve, readLoc, hloc_row4,
                   bind, Except.bind, List.mapM_cons, List.mapM_nil, pure, Except.pure]
        have h_frame_hash_call : buildFrame (m₄.toStore σ₃.loc).toMem (Thash.insertDef hashNm elemName "id" (nb - 1)) [.ptr q]
            = .ok [(Thash.parRow, .ptr q), (Thash.tmpB, .u32 0), (Thash.tmpP, .null)] := rfl
        rw [h_frame_hash_call]
        dsimp [bind, Except.bind]
        have h_hash_step_call : execStmt p d' (Thash.insertDef hashNm elemName "id" (nb - 1)).body
            (m₄.toStore [(Thash.parRow, .ptr q), (Thash.tmpB, .u32 0), (Thash.tmpP, .null)])
            = .ok (σ5, .ret (some (.bool true))) := by
          rw [hd'', hd''', hd'''', execStmt_eq_execAt]
          exact h_exec_hash
        rw [h_hash_step_call]
        rfl
      rw [h_hash_step]
      rfl

    have hb_len : (v.1 &&& UInt32.ofNat (nb - 1)).toNat < chains.length := by
      rw [I.thash.nb_len]; exact hb
    have I_rep_final : DbRepInv3 m' cap nb (nb - 1) free_rest' (q :: live_qs) (queue_es ++ [q])
        (chains.set (v.1 &&& UInt32.ofNat (nb - 1)).toNat (q :: chains[(v.1 &&& UInt32.ofNat (nb - 1)).toNat]'hb_len)) := by
      refine ⟨?_, ?_, I_thash_final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨I_pool_alloc.disj_rows, I_pool_alloc.sub_free, I_pool_alloc.sub_live, I_pool_alloc.nodup_free, I_pool_alloc.nodup_live, I_pool_alloc.disj, ?_, ?_, ?_, ?_, I_pool_alloc.parent⟩
        · have h_disj_hash_next : (fldPath q hashNm.next).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false :=
            poolRows_mem_fld_disjoint_poolDb cap hq_in_rows hashNm.next poolNm.freeHead (by decide)
          have h_disj_hash_inhash : (fldPath q hashNm.inhash).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false :=
            poolRows_mem_fld_disjoint_poolDb cap hq_in_rows hashNm.inhash poolNm.freeHead (by decide)
          have h_disj_bucket : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false := by
            have h := I.disj_pool_hash poolNm.freeHead (by simp) (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_hash_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false := by
            have h := I.disj_pool_hash_cnt poolNm.freeHead (by simp)
            rw [overlaps_symm]; exact h
          rw [hframe_hash (Pool.dbPath poolNm poolNm.freeHead) h_disj_hash_next h_disj_hash_inhash h_disj_bucket h_disj_hash_cnt]
          have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false := by
            intro x hx; have h := I.disj_db poolNm.freeHead (by simp) x hx; rw [overlaps_symm]; exact h
          have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false := by
            intro y _; exact poolRows_mem_fld_disjoint_poolDb cap hq_in_rows y poolNm.freeHead (by decide)
          have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (Pool.dbPath poolNm poolNm.freeHead) = false := by
            intro tail_node htl
            have htn_mem := getLast?_mem htl
            have htn_live := I.queue.sub tail_node htn_mem
            have htn_row := I.pool.sub_live tail_node htn_live
            exact poolRows_mem_fld_disjoint_poolDb cap htn_row queueNm.next poolNm.freeHead (by decide)
          rw [hframe_tail_m (Pool.dbPath poolNm poolNm.freeHead) hdb hqf htn]
          have hid : (fldPath q "id").overlaps (Pool.dbPath poolNm poolNm.freeHead) = false :=
            poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "id" poolNm.freeHead (by decide)
          have hqty : (fldPath q "qty").overlaps (Pool.dbPath poolNm poolNm.freeHead) = false :=
            poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "qty" poolNm.freeHead (by decide)
          rw [hframe_m3_m1 (Pool.dbPath poolNm poolNm.freeHead) hid hqty]
          exact I_pool_alloc.head
        · have hframe_free : ∀ r ∈ free_rest', readMem m' (fldPath r Pool.freeNextName) = readMem m₁ (fldPath r Pool.freeNextName) := by
            intro r hr
            have hr_in_free : r ∈ free_rest := hfr ▸ List.mem_cons_of_mem q hr
            have hr_row := I.pool.sub_free r (hfr ▸ hr_in_free)
            have hr_ne_q : r ≠ q := by intro heq; subst heq; exact (List.nodup_cons.mp (hfr ▸ I.pool.nodup_free)).1 hr
            have h_disj_hash_next : (fldPath q hashNm.next).overlaps (fldPath r Pool.freeNextName) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            have h_disj_hash_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r Pool.freeNextName) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            have h_disj_bucket : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r Pool.freeNextName) = false := by
              have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row Pool.freeNextName (v.1 &&& UInt32.ofNat (nb - 1)).toNat
              rw [overlaps_symm]; exact h
            have h_disj_hash_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r Pool.freeNextName) = false := by
              have h := poolRows_mem_fld_disjoint_hashDb cap hr_row Pool.freeNextName hashNm.count (by decide)
              rw [overlaps_symm]; exact h
            rw [hframe_hash (fldPath r Pool.freeNextName) h_disj_hash_next h_disj_hash_inhash h_disj_bucket h_disj_hash_cnt]
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
              by_cases heq_t : tail_node = r
              · rw [heq_t, overlaps_symm]; exact (freeNext_disjoint_queue r).1
              · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr_row heq_t)
            rw [hframe_tail_m (fldPath r Pool.freeNextName) hdb hqf htn]
            have hid : (fldPath q "id").overlaps (fldPath r Pool.freeNextName) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            have hqty : (fldPath q "qty").overlaps (fldPath r Pool.freeNextName) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            rw [hframe_m3_m1 (fldPath r Pool.freeNextName) hid hqty]
          exact Reaches.frame I_pool_alloc.chain hframe_free
        · have h_disj_hash_next : (fldPath q hashNm.next).overlaps (Pool.dbPath poolNm poolNm.count) = false :=
            poolRows_mem_fld_disjoint_poolDb cap hq_in_rows hashNm.next poolNm.count (by decide)
          have h_disj_hash_inhash : (fldPath q hashNm.inhash).overlaps (Pool.dbPath poolNm poolNm.count) = false :=
            poolRows_mem_fld_disjoint_poolDb cap hq_in_rows hashNm.inhash poolNm.count (by decide)
          have h_disj_bucket : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (Pool.dbPath poolNm poolNm.count) = false := by
            have h := I.disj_pool_hash poolNm.count (by simp) (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_hash_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (Pool.dbPath poolNm poolNm.count) = false := by
            have h := I.disj_pool_hash_cnt poolNm.count (by simp)
            rw [overlaps_symm]; exact h
          rw [hframe_hash (Pool.dbPath poolNm poolNm.count) h_disj_hash_next h_disj_hash_inhash h_disj_bucket h_disj_hash_cnt]
          have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (Pool.dbPath poolNm poolNm.count) = false := by
            intro x hx; have h := I.disj_db poolNm.count (by simp) x hx; rw [overlaps_symm]; exact h
          have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (Pool.dbPath poolNm poolNm.count) = false := by
            intro y _; exact poolRows_mem_fld_disjoint_poolDb cap hq_in_rows y poolNm.count (by decide)
          have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (Pool.dbPath poolNm poolNm.count) = false := by
            intro tail_node htl
            have htn_mem := getLast?_mem htl
            have htn_live := I.queue.sub tail_node htn_mem
            have htn_row := I.pool.sub_live tail_node htn_live
            exact poolRows_mem_fld_disjoint_poolDb cap htn_row queueNm.next poolNm.count (by decide)
          rw [hframe_tail_m (Pool.dbPath poolNm poolNm.count) hdb hqf htn]
          have hid : (fldPath q "id").overlaps (Pool.dbPath poolNm poolNm.count) = false :=
            poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "id" poolNm.count (by decide)
          have hqty : (fldPath q "qty").overlaps (Pool.dbPath poolNm poolNm.count) = false :=
            poolRows_mem_fld_disjoint_poolDb cap hq_in_rows "qty" poolNm.count (by decide)
          rw [hframe_m3_m1 (Pool.dbPath poolNm poolNm.count) hid hqty]
          exact I_pool_alloc.count
        · intro r hr
          by_cases heq : r = q
          · have h_disj_hash_next : (fldPath q hashNm.next).overlaps (fldPath r Pool.freeNextName) = false := by
              rw [heq, overlaps_symm]; exact (freeNext_disjoint_hash q).1
            have h_disj_hash_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r Pool.freeNextName) = false := by
              rw [heq, overlaps_symm]; exact (freeNext_disjoint_hash q).2
            have h_disj_bucket : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r Pool.freeNextName) = false := by
              have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) Pool.freeNextName (v.1 &&& UInt32.ofNat (nb - 1)).toNat
              rw [overlaps_symm]; exact h
            have h_disj_hash_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r Pool.freeNextName) = false := by
              have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) Pool.freeNextName hashNm.count (by decide)
              rw [overlaps_symm]; exact h
            rw [hframe_hash (fldPath r Pool.freeNextName) h_disj_hash_next h_disj_hash_inhash h_disj_bucket h_disj_hash_cnt]
            have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r Pool.freeNextName) = false := by
              intro x hx
              have h := poolRows_mem_fld_disjoint_queueDb cap (heq ▸ hq_in_rows) Pool.freeNextName x (queue_fields_ne_poolFld hx)
              rw [overlaps_symm]; exact h
            have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r Pool.freeNextName) = false := by
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy'
              · rw [heq, overlaps_symm]; exact (freeNext_disjoint_queue q).1
              · rcases List.mem_cons.mp hy' with rfl | hy''
                · rw [heq, overlaps_symm]; exact (freeNext_disjoint_queue q).2.1
                · rcases List.mem_cons.mp hy'' with rfl | hnil
                  · rw [heq, overlaps_symm]; exact (freeNext_disjoint_queue q).2.2
                  · nomatch hnil
            have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r Pool.freeNextName) = false := by
              intro tail_node htl
              have htn_mem := getLast?_mem htl
              have htn_live := I.queue.sub tail_node htn_mem
              have htn_row := I.pool.sub_live tail_node htn_live
              have htn_ne_q : tail_node ≠ q := fun heq_t => hq_not_live (heq_t ▸ htn_live)
              have htn_ne_r : tail_node ≠ r := by rw [heq]; exact htn_ne_q
              exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr htn_ne_r)
            rw [hframe_tail_m (fldPath r Pool.freeNextName) hdb hqf htn]
            have hid : (fldPath q "id").overlaps (fldPath r Pool.freeNextName) = false := by
              rw [heq]; exact (payload_disjoint_freeNext q).1
            have hqty : (fldPath q "qty").overlaps (fldPath r Pool.freeNextName) = false := by
              rw [heq]; exact (payload_disjoint_freeNext q).2
            rw [hframe_m3_m1 (fldPath r Pool.freeNextName) hid hqty]
            exact I_pool_alloc.fields r hr
          · have hr_ne_q : r ≠ q := heq
            have h_disj_hash_next : (fldPath q hashNm.next).overlaps (fldPath r Pool.freeNextName) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
            have h_disj_hash_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r Pool.freeNextName) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
            have h_disj_bucket : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r Pool.freeNextName) = false := by
              have h := poolRows_mem_fld_disjoint_hashBucket cap hr Pool.freeNextName (v.1 &&& UInt32.ofNat (nb - 1)).toNat
              rw [overlaps_symm]; exact h
            have h_disj_hash_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r Pool.freeNextName) = false := by
              have h := poolRows_mem_fld_disjoint_hashDb cap hr Pool.freeNextName hashNm.count (by decide)
              rw [overlaps_symm]; exact h
            rw [hframe_hash (fldPath r Pool.freeNextName) h_disj_hash_next h_disj_hash_inhash h_disj_bucket h_disj_hash_cnt]
            have hdb : ∀ x ∈ [queueNm.head, queueNm.tail, queueNm.count], (Llist.dbPath queueNm x).overlaps (fldPath r Pool.freeNextName) = false := by
              intro x hx
              have h := poolRows_mem_fld_disjoint_queueDb cap hr Pool.freeNextName x (queue_fields_ne_poolFld hx)
              rw [overlaps_symm]; exact h
            have hqf : ∀ y ∈ [queueNm.next, queueNm.prev, queueNm.inlist], (fldPath q y).overlaps (fldPath r Pool.freeNextName) = false := by
              intro y _
              exact fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
            have htn : ∀ tail_node, queue_es.getLast? = some tail_node → (fldPath tail_node queueNm.next).overlaps (fldPath r Pool.freeNextName) = false := by
              intro tail_node htl
              have htn_mem := getLast?_mem htl
              have htn_live := I.queue.sub tail_node htn_mem
              have htn_row := I.pool.sub_live tail_node htn_live
              by_cases heq_t : tail_node = r
              · rw [heq_t, overlaps_symm]; exact (freeNext_disjoint_queue r).1
              · exact fldPath_disjoint (I.pool.disj_rows tail_node htn_row r hr heq_t)
            rw [hframe_tail_m (fldPath r Pool.freeNextName) hdb hqf htn]
            have hid : (fldPath q "id").overlaps (fldPath r Pool.freeNextName) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
            have hqty : (fldPath q "qty").overlaps (fldPath r Pool.freeNextName) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
            rw [hframe_m3_m1 (fldPath r Pool.freeNextName) hid hqty]
            exact I_pool_alloc.fields r hr
      · refine ⟨I_queue_final.sub, I_queue_final.disj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, I_queue_final.parent⟩
        · have h_disj_next : (fldPath q hashNm.next).overlaps (Llist.dbPath queueNm queueNm.head) = false :=
            poolRows_mem_fld_disjoint_hashDb cap hq_in_rows hashNm.next queueNm.head (by decide)
          have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (Llist.dbPath queueNm queueNm.head) = false :=
            poolRows_mem_fld_disjoint_hashDb cap hq_in_rows hashNm.inhash queueNm.head (by decide)
          have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (Llist.dbPath queueNm queueNm.head) = false := by
            have h := I.disj_queue_hash queueNm.head (by simp) (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (Llist.dbPath queueNm queueNm.head) = false := by
            have h := I.disj_queue_hash_cnt queueNm.head (by simp)
            rw [overlaps_symm]; exact h
          rw [hframe_hash (Llist.dbPath queueNm queueNm.head) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt]
          exact I_queue_final.head
        · have h_disj_next : (fldPath q hashNm.next).overlaps (Llist.dbPath queueNm queueNm.tail) = false :=
            poolRows_mem_fld_disjoint_hashDb cap hq_in_rows hashNm.next queueNm.tail (by decide)
          have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (Llist.dbPath queueNm queueNm.tail) = false :=
            poolRows_mem_fld_disjoint_hashDb cap hq_in_rows hashNm.inhash queueNm.tail (by decide)
          have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (Llist.dbPath queueNm queueNm.tail) = false := by
            have h := I.disj_queue_hash queueNm.tail (by simp) (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (Llist.dbPath queueNm queueNm.tail) = false := by
            have h := I.disj_queue_hash_cnt queueNm.tail (by simp)
            rw [overlaps_symm]; exact h
          rw [hframe_hash (Llist.dbPath queueNm queueNm.tail) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt]
          exact I_queue_final.tail
        · have hframe_next : ∀ r ∈ (queue_es ++ [q]), readMem m' (fldPath r queueNm.next) = readMem m₄ (fldPath r queueNm.next) := by
            intro r hr
            simp only [List.mem_append, List.mem_singleton] at hr
            cases hr with
            | inl hr_es =>
              have hr_live := I.queue.sub r hr_es
              have hr_row := I.pool.sub_live r hr_live
              have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
              have h_disj_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.next) = false :=
                fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
              have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.next) = false :=
                fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
              have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.next) = false := by
                have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row queueNm.next (v.1 &&& UInt32.ofNat (nb - 1)).toNat
                rw [overlaps_symm]; exact h
              have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.next) = false := by
                have h := poolRows_mem_fld_disjoint_hashDb cap hr_row queueNm.next hashNm.count (by decide)
                rw [overlaps_symm]; exact h
              exact hframe_hash (fldPath r queueNm.next) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt
            | inr heq =>
              have h_disj_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.next) = false := by
                rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).1
              have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.next) = false := by
                rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.1
              have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.next) = false := by
                have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) queueNm.next (v.1 &&& UInt32.ofNat (nb - 1)).toNat
                rw [overlaps_symm]; exact h
              have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.next) = false := by
                have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) queueNm.next hashNm.count (by decide)
                rw [overlaps_symm]; exact h
              exact hframe_hash (fldPath r queueNm.next) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt
          exact Reaches.frame I_queue_final.chain hframe_next
        · have hframe_prev : ∀ r ∈ (queue_es ++ [q]), readMem m' (fldPath r queueNm.prev) = readMem m₄ (fldPath r queueNm.prev) := by
            intro r hr
            simp only [List.mem_append, List.mem_singleton] at hr
            cases hr with
            | inl hr_es =>
              have hr_live := I.queue.sub r hr_es
              have hr_row := I.pool.sub_live r hr_live
              have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
              have h_disj_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.prev) = false :=
                fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
              have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.prev) = false :=
                fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
              have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.prev) = false := by
                have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row queueNm.prev (v.1 &&& UInt32.ofNat (nb - 1)).toNat
                rw [overlaps_symm]; exact h
              have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.prev) = false := by
                have h := poolRows_mem_fld_disjoint_hashDb cap hr_row queueNm.prev hashNm.count (by decide)
                rw [overlaps_symm]; exact h
              exact hframe_hash (fldPath r queueNm.prev) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt
            | inr heq =>
              have h_disj_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.prev) = false := by
                rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.2.1
              have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.prev) = false := by
                rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.2.2.1
              have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.prev) = false := by
                have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) queueNm.prev (v.1 &&& UInt32.ofNat (nb - 1)).toNat
                rw [overlaps_symm]; exact h
              have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.prev) = false := by
                have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) queueNm.prev hashNm.count (by decide)
                rw [overlaps_symm]; exact h
              exact hframe_hash (fldPath r queueNm.prev) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt
          exact Backlinked.frame (queue_es ++ [q]) Value.null I_queue_final.back hframe_prev
        · have hframe_inlist : ∀ r ∈ (q :: live_qs), readMem m' (fldPath r queueNm.inlist) = readMem m₄ (fldPath r queueNm.inlist) := by
            intro r hr
            cases List.mem_cons.mp hr with
            | inl heq =>
              have h_disj_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.inlist) = false := by
                rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.2.2.2.1
              have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.inlist) = false := by
                rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.2.2.2.2
              have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.inlist) = false := by
                have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) queueNm.inlist (v.1 &&& UInt32.ofNat (nb - 1)).toNat
                rw [overlaps_symm]; exact h
              have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.inlist) = false := by
                have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) queueNm.inlist hashNm.count (by decide)
                rw [overlaps_symm]; exact h
              exact hframe_hash (fldPath r queueNm.inlist) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt
            | inr hr_live =>
              have hr_row := I.pool.sub_live r hr_live
              have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
              have h_disj_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.inlist) = false :=
                fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
              have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.inlist) = false :=
                fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
              have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.inlist) = false := by
                have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row queueNm.inlist (v.1 &&& UInt32.ofNat (nb - 1)).toNat
                rw [overlaps_symm]; exact h
              have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.inlist) = false := by
                have h := poolRows_mem_fld_disjoint_hashDb cap hr_row queueNm.inlist hashNm.count (by decide)
                rw [overlaps_symm]; exact h
              exact hframe_hash (fldPath r queueNm.inlist) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt
          exact Flagged.frame I_queue_final.flags hframe_inlist
        · have h_disj_next : (fldPath q hashNm.next).overlaps (Llist.dbPath queueNm queueNm.count) = false :=
            poolRows_mem_fld_disjoint_hashDb cap hq_in_rows hashNm.next queueNm.count (by decide)
          have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (Llist.dbPath queueNm queueNm.count) = false :=
            poolRows_mem_fld_disjoint_hashDb cap hq_in_rows hashNm.inhash queueNm.count (by decide)
          have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (Llist.dbPath queueNm queueNm.count) = false := by
            have h := I.disj_queue_hash queueNm.count (by simp) (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (Llist.dbPath queueNm queueNm.count) = false := by
            have h := I.disj_queue_hash_cnt queueNm.count (by simp)
            rw [overlaps_symm]; exact h
          simp only [Counted] at *
          rw [hframe_hash (Llist.dbPath queueNm queueNm.count) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt]
          exact I_queue_final.count
        · intro r hr
          have hr_row : r ∈ Pool.poolRows poolNm poolFld cap := by
            cases List.mem_cons.mp hr with
            | inl heq => exact heq ▸ hq_in_rows
            | inr hr_live => exact I.pool.sub_live r hr_live
          by_cases heq : r = q
          · have h_disj_next_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.next) = false := by
              rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).1
            have h_disj_inhash_next : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.next) = false := by
              rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.1
            have h_disj_bkt_next : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.next) = false := by
              have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) queueNm.next (v.1 &&& UInt32.ofNat (nb - 1)).toNat
              rw [overlaps_symm]; exact h
            have h_disj_cnt_next : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.next) = false := by
              have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) queueNm.next hashNm.count (by decide)
              rw [overlaps_symm]; exact h
            have h_next : (readMem m' (fldPath r queueNm.next)).isSome = true := by
              rw [hframe_hash (fldPath r queueNm.next) h_disj_next_next h_disj_inhash_next h_disj_bkt_next h_disj_cnt_next, heq]
              exact (I_queue_final.fields q (List.mem_cons_self)).1
            have h_disj_next_prev : (fldPath q hashNm.next).overlaps (fldPath r queueNm.prev) = false := by
              rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.2.1
            have h_disj_inhash_prev : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.prev) = false := by
              rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.2.2.1
            have h_disj_bkt_prev : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.prev) = false := by
              have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) queueNm.prev (v.1 &&& UInt32.ofNat (nb - 1)).toNat
              rw [overlaps_symm]; exact h
            have h_disj_cnt_prev : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.prev) = false := by
              have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) queueNm.prev hashNm.count (by decide)
              rw [overlaps_symm]; exact h
            have h_prev : (readMem m' (fldPath r queueNm.prev)).isSome = true := by
              rw [hframe_hash (fldPath r queueNm.prev) h_disj_next_prev h_disj_inhash_prev h_disj_bkt_prev h_disj_cnt_prev, heq]
              exact (I_queue_final.fields q (List.mem_cons_self)).2.1
            have h_disj_next_inlist : (fldPath q hashNm.next).overlaps (fldPath r queueNm.inlist) = false := by
              rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.2.2.2.1
            have h_disj_inhash_inlist : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.inlist) = false := by
              rw [heq, overlaps_symm]; exact (queue_disjoint_hash q).2.2.2.2.2
            have h_disj_bkt_inlist : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.inlist) = false := by
              have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) queueNm.inlist (v.1 &&& UInt32.ofNat (nb - 1)).toNat
              rw [overlaps_symm]; exact h
            have h_disj_cnt_inlist : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.inlist) = false := by
              have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) queueNm.inlist hashNm.count (by decide)
              rw [overlaps_symm]; exact h
            have h_inlist : (readMem m' (fldPath r queueNm.inlist)).isSome = true := by
              rw [hframe_hash (fldPath r queueNm.inlist) h_disj_next_inlist h_disj_inhash_inlist h_disj_bkt_inlist h_disj_cnt_inlist, heq]
              exact (I_queue_final.fields q (List.mem_cons_self)).2.2
            exact ⟨h_next, h_prev, h_inlist⟩
          · have hr_ne_q : r ≠ q := heq
            have h_disj_next_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.next) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            have h_disj_inhash_next : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.next) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            have h_disj_bkt_next : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.next) = false := by
              have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row queueNm.next (v.1 &&& UInt32.ofNat (nb - 1)).toNat
              rw [overlaps_symm]; exact h
            have h_disj_cnt_next : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.next) = false := by
              have h := poolRows_mem_fld_disjoint_hashDb cap hr_row queueNm.next hashNm.count (by decide)
              rw [overlaps_symm]; exact h
            have h_next : (readMem m' (fldPath r queueNm.next)).isSome = true := by
              rw [hframe_hash (fldPath r queueNm.next) h_disj_next_next h_disj_inhash_next h_disj_bkt_next h_disj_cnt_next]
              exact (I_queue_final.fields r hr).1
            have h_disj_next_prev : (fldPath q hashNm.next).overlaps (fldPath r queueNm.prev) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            have h_disj_inhash_prev : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.prev) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            have h_disj_bkt_prev : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.prev) = false := by
              have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row queueNm.prev (v.1 &&& UInt32.ofNat (nb - 1)).toNat
              rw [overlaps_symm]; exact h
            have h_disj_cnt_prev : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.prev) = false := by
              have h := poolRows_mem_fld_disjoint_hashDb cap hr_row queueNm.prev hashNm.count (by decide)
              rw [overlaps_symm]; exact h
            have h_prev : (readMem m' (fldPath r queueNm.prev)).isSome = true := by
              rw [hframe_hash (fldPath r queueNm.prev) h_disj_next_prev h_disj_inhash_prev h_disj_bkt_prev h_disj_cnt_prev]
              exact (I_queue_final.fields r hr).2.1
            have h_disj_next_inlist : (fldPath q hashNm.next).overlaps (fldPath r queueNm.inlist) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            have h_disj_inhash_inlist : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.inlist) = false :=
              fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
            have h_disj_bkt_inlist : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.inlist) = false := by
              have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row queueNm.inlist (v.1 &&& UInt32.ofNat (nb - 1)).toNat
              rw [overlaps_symm]; exact h
            have h_disj_cnt_inlist : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.inlist) = false := by
              have h := poolRows_mem_fld_disjoint_hashDb cap hr_row queueNm.inlist hashNm.count (by decide)
              rw [overlaps_symm]; exact h
            have h_inlist : (readMem m' (fldPath r queueNm.inlist)).isSome = true := by
              rw [hframe_hash (fldPath r queueNm.inlist) h_disj_next_inlist h_disj_inhash_inlist h_disj_bkt_inlist h_disj_cnt_inlist]
              exact (I_queue_final.fields r hr).2.2
            exact ⟨h_next, h_prev, h_inlist⟩
      · intro r hr
        have hr_in_free : r ∈ free_rest := hfr ▸ List.mem_cons_of_mem q hr
        have hr_row := I.pool.sub_free r hr_in_free
        have hr_ne_q : r ≠ q := by intro heq; subst heq; exact (List.nodup_cons.mp (hfr ▸ I.pool.nodup_free)).1 hr
        have hfresh := I.fresh_queue r hr_in_free
        have h_disj_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.inlist) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.inlist) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.inlist) = false := by
          have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row queueNm.inlist (v.1 &&& UInt32.ofNat (nb - 1)).toNat
          rw [overlaps_symm]; exact h
        have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.inlist) = false := by
          have h := poolRows_mem_fld_disjoint_hashDb cap hr_row queueNm.inlist hashNm.count (by decide)
          rw [overlaps_symm]; exact h
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
          have htn_ne_r : tail_node ≠ r := fun heq => I.pool.disj r hr_in_free (heq ▸ htn_live)
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
          rw [hframe_hash (fldPath r queueNm.inlist) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt,
              hframe_tail_m (fldPath r queueNm.inlist) hdb hqf htn,
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
          have htn_ne_r : tail_node ≠ r := fun heq => I.pool.disj r hr_in_free (heq ▸ htn_live)
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
        have h_disj_hash_next_next : (fldPath q hashNm.next).overlaps (fldPath r queueNm.next) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_hash_inhash_next : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.next) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_bkt_next : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.next) = false := by
          have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row queueNm.next (v.1 &&& UInt32.ofNat (nb - 1)).toNat
          rw [overlaps_symm]; exact h
        have h_disj_cnt_next : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.next) = false := by
          have h := poolRows_mem_fld_disjoint_hashDb cap hr_row queueNm.next hashNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_next : readMem m' (fldPath r queueNm.next) = some .null := by
          rw [hframe_hash (fldPath r queueNm.next) h_disj_hash_next_next h_disj_hash_inhash_next h_disj_bkt_next h_disj_cnt_next,
              hframe_tail_m (fldPath r queueNm.next) hdb_next hqf_next htn_next,
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
          have htn_ne_r : tail_node ≠ r := fun heq => I.pool.disj r hr_in_free (heq ▸ htn_live)
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
        have h_disj_hash_next_prev : (fldPath q hashNm.next).overlaps (fldPath r queueNm.prev) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_hash_inhash_prev : (fldPath q hashNm.inhash).overlaps (fldPath r queueNm.prev) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_bkt_prev : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r queueNm.prev) = false := by
          have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row queueNm.prev (v.1 &&& UInt32.ofNat (nb - 1)).toNat
          rw [overlaps_symm]; exact h
        have h_disj_cnt_prev : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r queueNm.prev) = false := by
          have h := poolRows_mem_fld_disjoint_hashDb cap hr_row queueNm.prev hashNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_prev : readMem m' (fldPath r queueNm.prev) = some .null := by
          rw [hframe_hash (fldPath r queueNm.prev) h_disj_hash_next_prev h_disj_hash_inhash_prev h_disj_bkt_prev h_disj_cnt_prev,
              hframe_tail_m (fldPath r queueNm.prev) hdb_prev hqf_prev htn_prev,
              hframe_m3 (fldPath r queueNm.prev) hr_disj_id_prev hr_disj_qty_prev hfh_prev hcnt_prev,
              hfresh.prev]
        exact ⟨h_inlist, h_next, h_prev⟩
      · intro r hr
        have hr_in_free : r ∈ free_rest := hfr ▸ List.mem_cons_of_mem q hr
        have hr_row := I.pool.sub_free r hr_in_free
        have hr_ne_q : r ≠ q := by intro heq; subst heq; exact (List.nodup_cons.mp (hfr ▸ I.pool.nodup_free)).1 hr
        have h_disj_next : (fldPath q hashNm.next).overlaps (fldPath r hashNm.inhash) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_inhash : (fldPath q hashNm.inhash).overlaps (fldPath r hashNm.inhash) = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_bkt : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r hashNm.inhash) = false := by
          have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row hashNm.inhash (v.1 &&& UInt32.ofNat (nb - 1)).toNat
          rw [overlaps_symm]; exact h
        have h_disj_cnt : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r hashNm.inhash) = false := by
          have h := poolRows_mem_fld_disjoint_hashDb cap hr_row hashNm.inhash hashNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_inhash_m := I.fresh_hash r hr_in_free
        have h_m4 := h_frame_m4_m r hr_row hr_ne_q hashNm.inhash (by simp)
        rw [hframe_hash (fldPath r hashNm.inhash) h_disj_next h_disj_inhash h_disj_bkt h_disj_cnt,
            h_m4, h_inhash_m]
      · intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        cases hr with
        | inl hr_es =>
          have hr_live := I.queue.sub r hr_es
          have hr_row := I.pool.sub_live r hr_live
          have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
          have h_disj_next_id : (fldPath q hashNm.next).overlaps (fldPath r "id") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have h_disj_inhash_id : (fldPath q hashNm.inhash).overlaps (fldPath r "id") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have h_disj_bkt_id : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row "id" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt_id : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_hashDb cap hr_row "id" hashNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_id_m' : readMem m' (fldPath r "id") = readMem m₄ (fldPath r "id") :=
            hframe_hash (fldPath r "id") h_disj_next_id h_disj_inhash_id h_disj_bkt_id h_disj_cnt_id
          have h_id_m4 : readMem m₄ (fldPath r "id") = readMem m (fldPath r "id") :=
            h_frame_m4_m r hr_row hr_ne_q "id" (by simp)
          have h_disj_next_qty : (fldPath q hashNm.next).overlaps (fldPath r "qty") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have h_disj_inhash_qty : (fldPath q hashNm.inhash).overlaps (fldPath r "qty") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
          have h_disj_bkt_qty : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row "qty" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt_qty : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_hashDb cap hr_row "qty" hashNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_qty_m' : readMem m' (fldPath r "qty") = readMem m₄ (fldPath r "qty") :=
            hframe_hash (fldPath r "qty") h_disj_next_qty h_disj_inhash_qty h_disj_bkt_qty h_disj_cnt_qty
          have h_qty_m4 : readMem m₄ (fldPath r "qty") = readMem m (fldPath r "qty") :=
            h_frame_m4_m r hr_row hr_ne_q "qty" (by simp)
          have h_ro : readOrder3 m' r = readOrder3 m r := by
            simp [readOrder3, h_id_m', h_id_m4, h_qty_m', h_qty_m4]
          rw [h_ro]
          exact I.orders r hr_es
        | inr heq =>
          have h_disj_next_id : (fldPath q hashNm.next).overlaps (fldPath r "id") = false := by
            rw [heq, overlaps_symm]; exact (payload_disjoint_hash q).1
          have h_disj_inhash_id : (fldPath q hashNm.inhash).overlaps (fldPath r "id") = false := by
            rw [heq, overlaps_symm]; exact (payload_disjoint_hash q).2.1
          have h_disj_bkt_id : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) "id" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt_id : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) "id" hashNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_id_m' : readMem m' (fldPath r "id") = some (.u32 v.1) := by
            rw [hframe_hash (fldPath r "id") h_disj_next_id h_disj_inhash_id h_disj_bkt_id h_disj_cnt_id, heq, hq_id_m4]
          have h_disj_next_qty : (fldPath q hashNm.next).overlaps (fldPath r "qty") = false := by
            rw [heq, overlaps_symm]; exact (payload_disjoint_hash q).2.2.1
          have h_disj_inhash_qty : (fldPath q hashNm.inhash).overlaps (fldPath r "qty") = false := by
            rw [heq, overlaps_symm]; exact (payload_disjoint_hash q).2.2.2
          have h_disj_bkt_qty : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) "qty" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt_qty : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) "qty" hashNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_qty_m' : readMem m' (fldPath r "qty") = some (.u64 v.2) := by
            rw [hframe_hash (fldPath r "qty") h_disj_next_qty h_disj_inhash_qty h_disj_bkt_qty h_disj_cnt_qty, heq, hq_qty_m4]
          simp [readOrder3, h_id_m', h_qty_m']
      · intro r hr
        by_cases heq : r = q
        · have h_disj_next_id : (fldPath q hashNm.next).overlaps (fldPath r "id") = false := by
            rw [heq, overlaps_symm]; exact (payload_disjoint_hash q).1
          have h_disj_inhash_id : (fldPath q hashNm.inhash).overlaps (fldPath r "id") = false := by
            rw [heq, overlaps_symm]; exact (payload_disjoint_hash q).2.1
          have h_disj_bkt_id : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) "id" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt_id : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) "id" hashNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_id_m' : readMem m' (fldPath r "id") = some (.u32 v.1) := by
            rw [hframe_hash (fldPath r "id") h_disj_next_id h_disj_inhash_id h_disj_bkt_id h_disj_cnt_id, heq, hq_id_m4]
          have h_disj_next_qty : (fldPath q hashNm.next).overlaps (fldPath r "qty") = false := by
            rw [heq, overlaps_symm]; exact (payload_disjoint_hash q).2.2.1
          have h_disj_inhash_qty : (fldPath q hashNm.inhash).overlaps (fldPath r "qty") = false := by
            rw [heq, overlaps_symm]; exact (payload_disjoint_hash q).2.2.2
          have h_disj_bkt_qty : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_hashBucket cap (heq ▸ hq_in_rows) "qty" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt_qty : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_hashDb cap (heq ▸ hq_in_rows) "qty" hashNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_qty_m' : readMem m' (fldPath r "qty") = some (.u64 v.2) := by
            rw [hframe_hash (fldPath r "qty") h_disj_next_qty h_disj_inhash_qty h_disj_bkt_qty h_disj_cnt_qty, heq, hq_qty_m4]
          simp [h_id_m', h_qty_m']
        · have hr_ne_q : r ≠ q := heq
          have h_disj_next_id : (fldPath q hashNm.next).overlaps (fldPath r "id") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
          have h_disj_inhash_id : (fldPath q hashNm.inhash).overlaps (fldPath r "id") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
          have h_disj_bkt_id : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_hashBucket cap hr "id" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt_id : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "id") = false := by
            have h := poolRows_mem_fld_disjoint_hashDb cap hr "id" hashNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_id_m' : readMem m' (fldPath r "id") = readMem m (fldPath r "id") := by
            rw [hframe_hash (fldPath r "id") h_disj_next_id h_disj_inhash_id h_disj_bkt_id h_disj_cnt_id,
                h_frame_m4_m r hr hr_ne_q "id" (by simp)]
          have h_disj_next_qty : (fldPath q hashNm.next).overlaps (fldPath r "qty") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
          have h_disj_inhash_qty : (fldPath q hashNm.inhash).overlaps (fldPath r "qty") = false :=
            fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr (Ne.symm hr_ne_q))
          have h_disj_bkt_qty : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_hashBucket cap hr "qty" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
            rw [overlaps_symm]; exact h
          have h_disj_cnt_qty : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "qty") = false := by
            have h := poolRows_mem_fld_disjoint_hashDb cap hr "qty" hashNm.count (by decide)
            rw [overlaps_symm]; exact h
          have h_qty_m' : readMem m' (fldPath r "qty") = readMem m (fldPath r "qty") := by
            rw [hframe_hash (fldPath r "qty") h_disj_next_qty h_disj_inhash_qty h_disj_bkt_qty h_disj_cnt_qty,
                h_frame_m4_m r hr hr_ne_q "qty" (by simp)]
          rw [h_id_m', h_qty_m']
          exact I.payload r hr
      · exact I.disj_db
      · exact I.disj_pool_hash
      · exact I.disj_pool_hash_cnt
      · exact I.disj_queue_hash
      · exact I.disj_queue_hash_cnt
      · intro r
        have h_flat := Thash.mem_flatten_set_cons (q := q) (r := r) (hb := (by rw [I.thash.nb_len]; exact hb))
        rw [h_flat]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · intro h
          rcases h with rfl | h_ch
          · exact Or.inr rfl
          · exact Or.inl ((I.hash_queue_match r).mp h_ch)
        · intro h
          rcases h with h_q | rfl
          · exact Or.inr ((I.hash_queue_match r).mpr h_q)
          · exact Or.inl rfl

    have h_abs_m : absDb3 m fuel = queue_es.mapM (readOrder3 m) := by
      simp only [absDb3]
      have hlen_le : queue_es.length ≤ fuel - 1 := by omega
      have hreach := Llist.reaches_headOf_implies_elems m queueNm queue_es I.queue.chain (fuel - 1) hlen_le
      have hfuel_sub : fuel - 1 + 1 = fuel := by omega
      rw [hfuel_sub] at hreach
      have hhd_eq := Llist.head_eq_headOf m queueNm queue_es I.queue.head
      rw [← hhd_eq] at hreach
      rw [hreach]
      rfl
    obtain ⟨ords, hords⟩ : ∃ ords, queue_es.mapM (readOrder3 m) = some ords :=
      mapM_isSome_iff_exists (readOrder3 m) queue_es I.orders
    have h_abs_m_eq : absDb3 m fuel = some ords := by rw [h_abs_m, hords]
    have h_abs_m'_val : absDb3 m' fuel = some (ords ++ [v]) := by
      simp only [absDb3]
      have hlen_le' : (queue_es ++ [q]).length ≤ fuel - 1 := by
        simp only [List.length_append, List.length_singleton]; omega
      have hreach' := Llist.reaches_headOf_implies_elems m' queueNm (queue_es ++ [q]) I_rep_final.queue.chain (fuel - 1) hlen_le'
      have hfuel_sub : fuel - 1 + 1 = fuel := by omega
      rw [hfuel_sub] at hreach'
      have hhd_eq' := Llist.head_eq_headOf m' queueNm (queue_es ++ [q]) I_rep_final.queue.head
      rw [← hhd_eq'] at hreach'
      rw [hreach']
      simp only [bind]
      have hframe_order : ∀ r ∈ queue_es, readOrder3 m' r = readOrder3 m r := by
        intro r hr
        have hr_live := I.queue.sub r hr
        have hr_row := I.pool.sub_live r hr_live
        have hr_ne_q : r ≠ q := fun heq => hq_not_live (heq ▸ hr_live)
        have h_disj_next_id : (fldPath q hashNm.next).overlaps (fldPath r "id") = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_inhash_id : (fldPath q hashNm.inhash).overlaps (fldPath r "id") = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_bkt_id : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "id") = false := by
          have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row "id" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
          rw [overlaps_symm]; exact h
        have h_disj_cnt_id : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "id") = false := by
          have h := poolRows_mem_fld_disjoint_hashDb cap hr_row "id" hashNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_id_m' : readMem m' (fldPath r "id") = readMem m (fldPath r "id") := by
          rw [hframe_hash (fldPath r "id") h_disj_next_id h_disj_inhash_id h_disj_bkt_id h_disj_cnt_id,
              h_frame_m4_m r hr_row hr_ne_q "id" (by simp)]
        have h_disj_next_qty : (fldPath q hashNm.next).overlaps (fldPath r "qty") = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_inhash_qty : (fldPath q hashNm.inhash).overlaps (fldPath r "qty") = false :=
          fldPath_disjoint (I.pool.disj_rows q hq_in_rows r hr_row (Ne.symm hr_ne_q))
        have h_disj_bkt_qty : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath r "qty") = false := by
          have h := poolRows_mem_fld_disjoint_hashBucket cap hr_row "qty" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
          rw [overlaps_symm]; exact h
        have h_disj_cnt_qty : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath r "qty") = false := by
          have h := poolRows_mem_fld_disjoint_hashDb cap hr_row "qty" hashNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_qty_m' : readMem m' (fldPath r "qty") = readMem m (fldPath r "qty") := by
          rw [hframe_hash (fldPath r "qty") h_disj_next_qty h_disj_inhash_qty h_disj_bkt_qty h_disj_cnt_qty,
              h_frame_m4_m r hr_row hr_ne_q "qty" (by simp)]
        simp [readOrder3, h_id_m', h_qty_m']
      have hmap_es : queue_es.mapM (readOrder3 m') = some ords := by
        rw [mapM_congr (readOrder3 m') (readOrder3 m) queue_es hframe_order]; exact hords
      have h_order_q : readOrder3 m' q = some v := by
        have h_disj_next_id : (fldPath q hashNm.next).overlaps (fldPath q "id") = false := by
          rw [overlaps_symm]; exact (payload_disjoint_hash q).1
        have h_disj_inhash_id : (fldPath q hashNm.inhash).overlaps (fldPath q "id") = false := by
          rw [overlaps_symm]; exact (payload_disjoint_hash q).2.1
        have h_disj_bkt_id : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath q "id") = false := by
          have h := poolRows_mem_fld_disjoint_hashBucket cap hq_in_rows "id" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
          rw [overlaps_symm]; exact h
        have h_disj_cnt_id : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath q "id") = false := by
          have h := poolRows_mem_fld_disjoint_hashDb cap hq_in_rows "id" hashNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_id_m' : readMem m' (fldPath q "id") = some (.u32 v.1) := by
          rw [hframe_hash (fldPath q "id") h_disj_next_id h_disj_inhash_id h_disj_bkt_id h_disj_cnt_id, hq_id_m4]
        have h_disj_next_qty : (fldPath q hashNm.next).overlaps (fldPath q "qty") = false := by
          rw [overlaps_symm]; exact (payload_disjoint_hash q).2.2.1
        have h_disj_inhash_qty : (fldPath q hashNm.inhash).overlaps (fldPath q "qty") = false := by
          rw [overlaps_symm]; exact (payload_disjoint_hash q).2.2.2
        have h_disj_bkt_qty : (Thash.bucketPath hashNm (v.1 &&& UInt32.ofNat (nb - 1)).toNat).overlaps (fldPath q "qty") = false := by
          have h := poolRows_mem_fld_disjoint_hashBucket cap hq_in_rows "qty" (v.1 &&& UInt32.ofNat (nb - 1)).toNat
          rw [overlaps_symm]; exact h
        have h_disj_cnt_qty : (Thash.dbPath hashNm hashNm.count).overlaps (fldPath q "qty") = false := by
          have h := poolRows_mem_fld_disjoint_hashDb cap hq_in_rows "qty" hashNm.count (by decide)
          rw [overlaps_symm]; exact h
        have h_qty_m' : readMem m' (fldPath q "qty") = some (.u64 v.2) := by
          rw [hframe_hash (fldPath q "qty") h_disj_next_qty h_disj_inhash_qty h_disj_bkt_qty h_disj_cnt_qty, hq_qty_m4]
        simp [readOrder3, h_id_m', h_qty_m']
      exact mapM_append_singleton (readOrder3 m') queue_es q ords v hmap_es h_order_q

    have h_abs_refine : absDb3 m' fuel = some ((absDb3 m fuel).getD [] ++ [v]) := by
      rw [h_abs_m'_val, h_abs_m_eq]
      simp

    exact ⟨m', free_rest', q :: live_qs, queue_es ++ [q],
           chains.set (v.1 &&& UInt32.ofNat (nb - 1)).toNat (q :: chains[(v.1 &&& UInt32.ofNat (nb - 1)).toNat]'hb_len),
           h_exec_full, I_rep_final, h_abs_refine⟩

/-- Master forward simulation theorem for MiniDb derived from schema `miniDb3 cap nb`:
    Executing the generated C program synthesized from `genC (miniDb3 cap nb)` on a well-formed
    memory state `m` produces a state `m'` that preserves representation invariant `DbRepInv3`
    and refines the abstract state `absDb3` with `v`. -/
theorem mini_insert_forward_sim3_schema
    (cap nb fuel : Nat) (m : Mem) (v : UInt32 × UInt64)
    {free_rest live_qs queue_es : List Path}
    {chains : List (List Path)}
    (I : DbRepInv3 m cap nb (nb - 1) free_rest live_qs queue_es chains)
    (hfree : free_rest ≠ [])
    (h_fresh : ∀ q', (v.1, q') ∉ Thash.elems m "id" chains)
    (hb : (v.1 &&& UInt32.ofNat (nb - 1)).toNat < nb)
    (hfits : (chains[(v.1 &&& UInt32.ofNat (nb - 1)).toNat]'(by rw [I.thash.nb_len]; exact hb)).length < cap)
    (hfuel : fuel ≥ queue_es.length + cap + 5) :
    ∃ (p : Program),
      genC (miniDb3 cap nb) = some p ∧
      ∃ m' free' live' es' chains',
        execStmt p fuel (insertStmt3 v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal)
        ∧ DbRepInv3 m' cap nb (nb - 1) free' live' es' chains'
        ∧ absDb3 m' fuel = some ((absDb3 m fuel).getD [] ++ [v]) := by
  have hp : genC (miniDb3 cap nb) = some (genMiniDb3 cap nb) := rfl
  obtain ⟨m', free', live', es', chains', hexec, I', habs⟩ :=
    mini_insert_forward_sim3 cap nb fuel m v I hfree h_fresh hb hfits hfuel
  exact ⟨genMiniDb3 cap nb, hp, m', free', live', es', chains', hexec, I', habs⟩

/-- Forward simulation theorem parameterized by any AST `p` matching `genC (miniDb3 cap nb)`. -/
theorem mini_insert_forward_sim3_of_gen
    (cap nb fuel : Nat) (m : Mem) (v : UInt32 × UInt64)
    {free_rest live_qs queue_es : List Path}
    {chains : List (List Path)}
    {p : Program} (hp : genC (miniDb3 cap nb) = some p)
    (I : DbRepInv3 m cap nb (nb - 1) free_rest live_qs queue_es chains)
    (hfree : free_rest ≠ [])
    (h_fresh : ∀ q', (v.1, q') ∉ Thash.elems m "id" chains)
    (hb : (v.1 &&& UInt32.ofNat (nb - 1)).toNat < nb)
    (hfits : (chains[(v.1 &&& UInt32.ofNat (nb - 1)).toNat]'(by rw [I.thash.nb_len]; exact hb)).length < cap)
    (hfuel : fuel ≥ queue_es.length + cap + 5) :
    ∃ m' free' live' es' chains',
      execStmt p fuel (insertStmt3 v) (m.toStore ∅) = .ok (m'.toStore ∅, .normal)
      ∧ DbRepInv3 m' cap nb (nb - 1) free' live' es' chains'
      ∧ absDb3 m' fuel = some ((absDb3 m fuel).getD [] ++ [v]) := by
  have h_eq : p = genMiniDb3 cap nb := Option.some.inj (hp.symm.trans (genC_miniDb3 cap nb))
  subst h_eq
  exact mini_insert_forward_sim3 cap nb fuel m v I hfree h_fresh hb hfits hfuel


end MiniDb
end Templates


import Solidity.Semantics.Erased
import Solidity.Semantics.HeapErase

/-!
# The typed state

What `EState` becomes at M4 (`docs/intrinsic.md`, "M4 lane", wiring
items 1 and 2), over the typed values of `Semantics/Storage.lean` and
`Semantics/Heap.lean`: a local holds a value of its type
(`LTy.TDenote`), an alias a typed storage reference, a memory local a
reference its heap typing types; the state holds a typed storage and a heap
whose typing `H` is a field, not an index, so a statement's run keeps its
type.  An allocation grows the heap (`State.adopt`, from a `Grown` heap)
and weakens the locals along the extension (`TEnv.wk`), which only rewrites
a memory local's proof: the identities stay, so the erasure does too.

`State.erase` is the `EState` the closer reads, so each operation's
agreement is one lemma here (`State.adopt_erase`, `State.copyStToM_erase`,
…), from which each typed step's erasure follows
(`Semantics/StepErase.lean`).
-/

namespace Solidity

variable {C : Contract}

/-! ## Locals -/

/-- What a local of type `t` holds, typed: a value of its type, the storage
reference an alias is bound to (`none` while unset), a memory reference the
heap typing `H` types (`none` while unset: no statement leaves one so, only
a hidden binder ranges over it, decision 17'), a whole storage, a ledger. -/
@[reducible] def LTy.TDenote (C : Contract) (H : HTy) : LTy → Type
  | .val p => p.Denote
  | .alias R => Option (SRef C (.ref R))
  | .mem R => Option (HRef H R)
  | .old => Storage C
  | .oldNet => List (Int × Int)

namespace LTy

/-- A local over a grown heap: a memory reference weakened, the rest kept. -/
def TDenote.wk {H H' : HTy} (e : H <+: H') : (t : LTy) → t.TDenote C H → t.TDenote C H'
  | .val _, v => v
  | .alias _, a => a
  | .mem _, r => r.map (HRef.wk e)
  | .old, st => st
  | .oldNet, l => l

/-- What `EState` holds for the local. -/
def TDenote.erase {H : HTy} : (t : LTy) → t.TDenote C H → t.Denote C
  | .val p, v => PrimTy.erase (p := p) v
  | .alias _, a => a.map SRef.erase
  | .mem _, r => (r : Option (HRef H _)).map (·.id)
  | .old, st => Storage.erase (st : Storage C)
  | .oldNet, l => l

theorem TDenote.erase_wk {H H' : HTy} (e : H <+: H') :
    (t : LTy) → (v : t.TDenote C H) → TDenote.erase t (TDenote.wk e t v) = TDenote.erase t v
  | .val _, _ | .alias _, _ | .mem _, none | .mem _, some _ | .old, _ | .oldNet, _ => rfl

end LTy

/-- The locals of `Γ`, typed over the heap typing `H`: computed from `Γ`, as
`Env` (Gate G0, condition 4). -/
def TEnv (C : Contract) (H : HTy) : Ctx → Type
  | [] => Unit
  | t :: Γ => t.TDenote C H × TEnv C H Γ

namespace TEnv

variable {H : HTy}

/-- The local at a position. -/
def get : {Γ : Ctx} → {t : LTy} → Idx Γ t → TEnv C H Γ → t.TDenote C H
  | _, _, i => Idx.casesOn (motive := fun Γ t _ => TEnv C H Γ → t.TDenote C H) i
      (fun e => e.1) (fun i e => TEnv.get i e.2)
  termination_by structural _ _ i => i

/-- The local at a position, set. -/
def set : {Γ : Ctx} → {t : LTy} → Idx Γ t → t.TDenote C H → TEnv C H Γ → TEnv C H Γ
  | _, _, i => Idx.casesOn (motive := fun Γ t _ => t.TDenote C H → TEnv C H Γ → TEnv C H Γ) i
      (fun w e => (w, e.2)) (fun i w e => (e.1, TEnv.set i w e.2))
  termination_by structural _ _ i => i

/-- The locals a suffix pushed, popped. -/
def drop {Γ : Ctx} : {Δ : Ctx} → Ext Γ Δ → TEnv C H Δ → TEnv C H Γ
  | _, h => Ext.casesOn (motive := fun Δ _ => TEnv C H Δ → TEnv C H Γ) h (fun e => e)
      (fun h e => TEnv.drop h e.2)
  termination_by structural _ h => h

/-- The locals over a grown heap. -/
def wk {H' : HTy} (e : H <+: H') : (Γ : Ctx) → TEnv C H Γ → TEnv C H' Γ
  | [], _ => ()
  | t :: Γ, x => (LTy.TDenote.wk e t x.1, TEnv.wk e Γ x.2)

/-- `EState`'s locals. -/
def erase : (Γ : Ctx) → TEnv C H Γ → Env C Γ
  | [], _ => ()
  | t :: Γ, x => (LTy.TDenote.erase t x.1, TEnv.erase Γ x.2)

theorem erase_wk {H' : HTy} (e : H <+: H') : (Γ : Ctx) → (x : TEnv C H Γ) →
    TEnv.erase Γ (TEnv.wk e Γ x) = TEnv.erase Γ x
  | [], _ => rfl
  | t :: Γ, x => by
    simp only [TEnv.erase, TEnv.wk, LTy.TDenote.erase_wk, TEnv.erase_wk e Γ x.2]

theorem get_erase : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → (x : TEnv C H Γ) →
    Env.get i (TEnv.erase Γ x) = LTy.TDenote.erase t (TEnv.get i x)
  | _, _, .here, _ => rfl
  | _, _, .there i, x => get_erase i x.2

theorem set_erase : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → (v : t.TDenote C H) →
    (x : TEnv C H Γ) →
    Env.set i (LTy.TDenote.erase t v) (TEnv.erase Γ x) = TEnv.erase Γ (TEnv.set i v x)
  | _, _, .here, _, _ => rfl
  | _ :: _, _, .there i, v, x =>
    congrArg (Prod.mk (LTy.TDenote.erase _ x.1)) (set_erase i v x.2)

theorem drop_erase {Γ Δ : Ctx} (h : Ext Γ Δ) (x : TEnv C H Δ) :
    Env.drop h (TEnv.erase Δ x) = TEnv.erase Γ (TEnv.drop h x) := by
  induction h with
  | refl => rfl
  | push h ih => exact ih x.2

end TEnv

/-! ## States -/

/-- The transaction, typed (`Semantics.TxEnv`): its words are `uint`s, so
`msg.sender` and the other values of the environment are in range by
construction.  The outcomes of external calls stay untyped data, read back
at their types when a `try` decodes them. -/
structure TTx where
  msgSender : PrimTy.uint.Denote := PrimTy.dflt .uint
  selfAddress : PrimTy.uint.Denote := PrimTy.dflt .uint
  msgValue : PrimTy.uint.Denote := PrimTy.dflt .uint
  timestamp : PrimTy.uint.Denote := PrimTy.dflt .uint
  ext : List (Semantics.ExtKey × Semantics.ExtResult) := []

/-- The untyped transaction. -/
def TTx.erase (t : TTx) : Semantics.TxEnv :=
  { msgSender := t.msgSender.1, selfAddress := t.selfAddress.1, msgValue := t.msgValue.1,
    timestamp := t.timestamp.1, ext := t.ext }

/-- A state in the context `Γ`, typed: the storage at the contract's
types, a heap and its typing, the locals typed over it, the contract's own
funds a `uint` (no statement changes them: a payment moves the ledger). -/
structure State (C : Contract) (Γ : Ctx) where
  storage : Storage C
  H : HTy
  heap : Heap H
  env : TEnv C H Γ
  net : List (Int × Int) := []
  selfBalance : PrimTy.uint.Denote := PrimTy.dflt .uint
  tx : TTx := {}

namespace State

variable {Γ : Ctx}

/-- `EState` of the same state: the storage and the heap erased, the next
identity the heap's length, the locals erased. -/
def erase (σ : State C Γ) : EState C Γ :=
  { storage := σ.storage.erase, heap := σ.heap.erase, nextId := σ.H.length,
    env := TEnv.erase Γ σ.env, net := σ.net, selfBalance := σ.selfBalance.1, tx := σ.tx.erase }

/-- The state a contract starts in: every state variable at its default, no
memory, no locals. -/
def init (C : Contract) : State C [] :=
  { storage := Storage.init C, H := [], heap := Heap.empty, env := () }

theorem init_erase (C : Contract) :
    (State.init C).erase = EState.ofSem { storage := C.initStorage } := by
  simp only [erase, init, Storage.init_erase]
  rfl

/-- A local declared. -/
def push {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) : State C (t :: Γ) :=
  { σ with env := (v, σ.env) }

/-- A local set. -/
def setLocal {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) : State C Γ :=
  { σ with env := TEnv.set i v σ.env }

/-- A scope's locals popped. -/
def drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) : State C Γ :=
  { σ with env := TEnv.drop h σ.env }

/-- The storage replaced. -/
def withStorage (σ : State C Γ) (st : Storage C) : State C Γ := { σ with storage := st }

theorem push_erase {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) :
    (σ.push v).erase = σ.erase.push (LTy.TDenote.erase t v) := rfl

theorem setLocal_erase {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (σ.setLocal i v).erase = σ.erase.setLocal i (LTy.TDenote.erase t v) := by
  simp only [erase, setLocal, EState.setLocal, EState.withEnv, TEnv.set_erase]

theorem drop_erase {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) :
    (σ.drop h).erase = σ.erase.drop h := by
  simp only [erase, drop, EState.drop, EState.withEnv, TEnv.drop_erase]

theorem withStorage_erase (σ : State C Γ) (st : Storage C) :
    (σ.withStorage st).erase = σ.erase.withGlob { σ.erase.glob with storage := st.erase } := rfl

theorem glob_heap (σ : State C Γ) : σ.erase.glob.heap = σ.heap.erase := rfl

theorem glob_nextId (σ : State C Γ) : σ.erase.glob.nextId = σ.H.length := rfl

/-! ### Allocation -/

/-- A grown heap adopted: its typing and objects, the locals weakened along
its extension, and the value it carries, typed over the new typing. -/
def adopt {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    (σ' : State C Γ) × α σ'.H :=
  ⟨{ σ with H := g.H', heap := g.heap, env := TEnv.wk g.ext Γ σ.env }, g.val⟩

/-- The adopted state erases to the old one with the grown heap: the locals
are the same. -/
theorem adopt_erase {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    (σ.adopt g).1.erase = σ.erase.withGlob (Heap.into σ.erase.glob g.heap) := by
  simp only [adopt, erase, EState.withGlob, EState.ofGlob, Heap.into, EState.glob,
    TEnv.erase_wk]

/-- A fresh object (`State.alloc`): the heap grows by its type. -/
def alloc {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) :
    (σ' : State C Γ) × MVal σ'.H (.ref R) :=
  σ.adopt (Grown.alloc ⟨List.prefix_refl _, σ.heap, o⟩)

theorem alloc_erase {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) :
    σ.erase.glob.alloc (MObj.erase R o) =
      ((σ.alloc o).1.erase.glob, ((σ.alloc o).2 : HRef _ R).id) := by
  rw [Heap.alloc_erase (glob_heap σ) (glob_nextId σ) o, alloc, adopt_erase]
  rfl

/-- A storage value copied into fresh objects (`copyStToM`). -/
def copyStToM {T : Ty} (σ : State C Γ) (v : SVal T) (h : T.mapFree = true) :
    (σ' : State C Γ) × MVal σ'.H T :=
  σ.adopt (v.copyStToM σ.heap h)

theorem copyStToM_erase {T : Ty} (σ : State C Γ) (v : SVal T) (h : T.mapFree = true) :
    Semantics.copyStToM σ.erase.glob v.erase =
      .ok ((σ.copyStToM v h).1.erase.glob, MVal.erase T (σ.copyStToM v h).2) := by
  rw [SVal.copyStToM_erase v h σ.heap σ.erase.glob (glob_heap σ) (glob_nextId σ), copyStToM,
    adopt_erase]
  rfl

/-- A fresh default object (`allocDefault`). -/
def allocDefault (σ : State C Γ) (R : RefTy) (h : (Ty.ref R).mapFree = true) :
    (σ' : State C Γ) × MVal σ'.H (.ref R) :=
  σ.adopt (σ.heap.allocDefault R h)

theorem allocDefault_erase (σ : State C Γ) (R : RefTy) (h : (Ty.ref R).mapFree = true) :
    Semantics.allocDefault σ.erase.glob R =
      .ok ((σ.allocDefault R h).1.erase.glob, ((σ.allocDefault R h).2 : HRef _ (R)).id) := by
  rw [Heap.allocDefault_erase (glob_heap σ) (glob_nextId σ) R h, allocDefault, adopt_erase]
  rfl

/-- A memory value copied to storage (`copyMem`). -/
def copyMToSt {T : Ty} (σ : State C Γ) (v : MVal σ.H T) : SVal T := MVal.copyMToSt σ.heap v

theorem copyMem_erase {T : Ty} (σ : State C Γ) (v : MVal σ.H T) :
    Semantics.copyMem σ.erase.glob (MVal.erase T v) = .ok (σ.copyMToSt v).erase :=
  MVal.copyMem_erase (glob_heap σ) v

/-- A fresh `Person` in memory: its members' objects first, then its own,
so the heap typing grows by three; its `age` reads its default.  By the
kernel: the copy is a fold. -/
example : (let g := (State.init StandardExample).allocDefault (.struct "Person") rfl
    (g.1.H.length, MVal.erase (.prim .uint) (g.1.heap.field g.2 (f := "age") rfl))) =
    (3, .int 0) := by
  decide +kernel

end State

end Solidity

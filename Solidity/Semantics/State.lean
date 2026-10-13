import Solidity.Syntax.Quote
import Solidity.Semantics.Heap

/-!
# The typed state

A local holds a value of its type (`LTy.TDenote`), an alias a typed storage
reference, a memory local a reference its heap typing types; the state
holds a typed storage and a heap whose typing `H` is a field, not an index,
so a statement's run keeps its type.  An allocation grows the heap
(`State.adopt`, from a `Grown` heap) and weakens the locals along the
extension (`TEnv.wk`), which only rewrites a memory local's proof: the
identities stay.

The terms read the typed state itself (`Signature.lean`, W9.8), and so do
the run's invariants (`Typing/`), the EVM simulation (`Evm/Sim.lean`) and
the tools: there is no untyped state (W10.5.6).
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
  | .oldNet => Ledger
  | .kint => Int

namespace LTy

/-- A local over a grown heap: a memory reference weakened, the rest kept. -/
def TDenote.wk {H H' : HTy} (e : H <+: H') : (t : LTy) → t.TDenote C H → t.TDenote C H'
  | .val _, v => v
  | .alias _, a => a
  | .mem _, r => r.map (HRef.wk e)
  | .old, st => st
  | .oldNet, l => l
  | .kint, n => n

end LTy

/-- The locals of `Γ`, typed over the heap typing `H`: computed from `Γ`, as
a type computed from the context, not an inductive family (Gate G0, condition 4). -/
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

theorem get_wk {H' : HTy} (e : H <+: H') {t : LTy} : {Γ : Ctx} → (i : Idx Γ t) →
    (x : TEnv C H Γ) → TEnv.get i (TEnv.wk e Γ x) = LTy.TDenote.wk e t (TEnv.get i x)
  | _, .here, _ => rfl
  | _, .there i, x => get_wk e i x.2

end TEnv

/-! ## States -/

/-- The transaction: KeY's program variables `msgSender` and `msgValue`
(`netHeader.key`), the contract's own address and the block's timestamp,
`uint`s, so in range by construction; and how each external call it makes
ends (`ext`), a call it has no entry for reaching an address with no code
(which a `try` reverts on, and a `send` pays: `sendT`).  Two identical
calls, or two `send`s of one amount to one address, read the same entry.
No statement changes them, and a callback leaves them as they were: a
re-entrant call runs in its own transaction, which the caller never sees.
The outcomes are ABI data (`Semantics.ExtResult`), read back at their types
when a `try` decodes them.  The calculus reads none of `ext`: a `try` has a
goal for every way its call may end (`tryCallNoCallbackBox`), a `send` one
for each outcome (`sendNoCallbackBox`), so a proof holds whatever the table
says. -/
structure TTx where
  msgSender : PrimTy.uint.Denote := PrimTy.dflt .uint
  selfAddress : PrimTy.uint.Denote := PrimTy.dflt .uint
  msgValue : PrimTy.uint.Denote := PrimTy.dflt .uint
  timestamp : PrimTy.uint.Denote := PrimTy.dflt .uint
  ext : List (Semantics.ExtKey × Semantics.ExtResult) := []

/-- A state in the context `Γ`, typed: the storage at the contract's
types, a heap and its typing, the locals typed over it, the contract's own
funds a `uint` (no statement changes them: a payment moves the ledger). -/
structure State (C : Contract) (Γ : Ctx) where
  storage : Storage C
  H : HTy
  heap : Heap H
  env : TEnv C H Γ
  net : Ledger := []
  selfBalance : PrimTy.uint.Denote := PrimTy.dflt .uint
  tx : TTx := {}

namespace State

variable {Γ : Ctx}

/-- The state a contract starts in: every state variable at its default, no
memory, no locals. -/
def init (C : Contract) : State C [] :=
  { storage := Storage.init C, H := [], heap := Heap.empty, env := () }

/-- A local declared. -/
def push {t : LTy} (σ : State C Γ) (v : t.TDenote C σ.H) : State C (t :: Γ) :=
  { σ with env := (v, σ.env) }

/-- A local set. -/
def setLocal {t : LTy} (σ : State C Γ) (i : Idx Γ t) (v : t.TDenote C σ.H) : State C Γ :=
  { σ with env := TEnv.set i v σ.env }

/-- A scope's locals popped. -/
def drop {Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) : State C Γ :=
  { σ with env := TEnv.drop h σ.env }

/-- The global part of a typed state: the state without its locals. -/
def glob (σ : State C Γ) : State C [] :=
  { storage := σ.storage, H := σ.H, heap := σ.heap, env := (), net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

/-- The storage replaced. -/
def withStorage (σ : State C Γ) (st : Storage C) : State C Γ := { σ with storage := st }

/-! ### Allocation -/

/-- A grown heap adopted: its typing and objects, the locals weakened along
its extension, and the value it carries, typed over the new typing. -/
def adopt {α : HTy → Type} (σ : State C Γ) (g : Grown σ.H α) :
    (σ' : State C Γ) × α σ'.H :=
  ⟨{ σ with H := g.H', heap := g.heap, env := TEnv.wk g.ext Γ σ.env }, g.val⟩

/-- A fresh object (`State.alloc`): the heap grows by its type. -/
def alloc {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) :
    (σ' : State C Γ) × MVal σ'.H (.ref R) :=
  σ.adopt (Grown.alloc ⟨List.prefix_refl _, σ.heap, o⟩)

/-- A storage value copied into fresh objects (`copyStToM`). -/
def copyStToM {T : Ty} (σ : State C Γ) (v : SVal T) (h : T.mapFree = true) :
    (σ' : State C Γ) × MVal σ'.H T :=
  σ.adopt (v.copyStToM σ.heap h)

/-- A fresh default object (`allocDefault`). -/
def allocDefault (σ : State C Γ) (R : RefTy) (h : (Ty.ref R).mapFree = true) :
    (σ' : State C Γ) × MVal σ'.H (.ref R) :=
  σ.adopt (σ.heap.allocDefault R h)

/-- A memory value copied to storage (`copyMem`). -/
def copyMToSt {T : Ty} (σ : State C Γ) (v : MVal σ.H T) : SVal T := MVal.copyMToSt σ.heap v

/-- A fresh `Person` in memory: its members' objects first, then its own,
so the heap typing grows by three; its `age` reads its default.  By the
kernel: the copy is a fold. -/
example : (let g := (State.init StandardExample).allocDefault (.struct "Person") rfl
    (g.1.H.length, (g.1.heap.field g.2 (f := "age") rfl : PrimTy.uint.Denote).1)) =
    (3, 0) := by
  decide +kernel

end State

end Solidity

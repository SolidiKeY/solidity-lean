import Solidity.Semantics.RunFrame
import Solidity.Semantics.StateErase

/-!
# A typed state, named

A typed state printed as `Semantics.lean`'s, for `#run` (`Tools/Run.lean`):
`State.toSem ns` erases its storage and heap and binds its locals under the
names `ns` (innermost first), each as `Semantics.lean` binds it
(`LTy.TDenote.bind`).
-/

namespace Solidity

open Semantics (Binding)

variable {C : Contract}

/-! ## Bindings -/

/-- A typed local as `Semantics.lean` binds it. -/
def LTy.TDenote.bind {H : HTy} : (t : LTy) → t.TDenote C H → Binding
  | .val p, v => .val (PrimTy.erase (p := p) v)
  | .alias _, some r => .spath (SRef.erase r).1 (SRef.erase r).2
  | .alias _, none => .unset
  | .mem _, some r => .mref (r : HRef H _).id
  | .mem _, none => .unset
  | .old, st => .store (Storage.erase (st : Storage C))
  | .oldNet, l => .ledger l

/-! ## Locals -/

namespace TEnv

variable {H : HTy}

/-- The locals as `Semantics.lean`'s environment, named by `ns` (innermost
first). -/
def toSem : {Γ : Ctx} → List Var → TEnv C H Γ → List (Var × Binding)
  | [], _, _ => []
  | _ :: _, [], _ => []
  | t :: _, x :: ns, e => (x, LTy.TDenote.bind t e.1) :: TEnv.toSem ns e.2

end TEnv

/-! ## States -/

namespace State

variable {Γ : Ctx}

/-- **A typed state as `Semantics.lean`'s**: the storage and the heap
erased, the next identity the heap's length, the locals named by `ns`. -/
def toSem (ns : List Var) (σ : State C Γ) : Semantics.State :=
  { storage := σ.storage.erase, heap := σ.heap.erase, nextId := σ.H.length,
    env := TEnv.toSem ns σ.env, net := σ.net, selfBalance := σ.selfBalance.1,
    tx := σ.tx.erase }

end State

end Solidity

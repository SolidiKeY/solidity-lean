import Solidity.Backend.InternalDispatch.Controls
import Solidity.Backend.InternalDispatch.FrozenV1

/-! Inhabited dependent selector tests, NOT instances of the pending P1
producers. Conditional P1 theorems keep the full frozen structures as inputs. -/
namespace Solidity.Backend.InternalDispatch.FrozenV1Controls
open FrozenV1 Controls

def token (i : Fin table.size) : Fin (i.val+1) := ⟨i.val, Nat.lt_succ_self _⟩

theorem first : select table (fun i => Fin (i.val+1)) token (Evm.wmod 1) =
    some ⟨⟨0, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩ := by rfl

theorem second : select table (fun i => Fin (i.val+1)) token (Evm.wmod 2) =
    some ⟨⟨1, by decide +kernel⟩, ⟨1, by decide +kernel⟩⟩ := by rfl

def payload (p : Sigma (fun i : Fin table.size => Fin (i.val+1))) : Nat := p.2.val

theorem wrong_payload_refused : select table (fun i => Fin (i.val+1)) token (Evm.wmod 2) ≠
    some ⟨⟨1, by decide +kernel⟩, ⟨0, by decide +kernel⟩⟩ := by
  rw [second]
  intro h
  have equality : (some (1 : Nat) : Option Nat) = some 0 :=
    congrArg (Option.map payload) h
  cases equality

theorem zero : select table (fun i => Fin (i.val+1)) token (Evm.wmod 0) = none :=
  zero_refused table _ token

theorem foreign : select table (fun i => Fin (i.val+1)) token (Evm.wmod 5) = none :=
  foreign_refused table _ token _ (by decide +kernel)

#print axioms first
#print axioms second
#print axioms wrong_payload_refused
#print axioms zero
#print axioms foreign
end Solidity.Backend.InternalDispatch.FrozenV1Controls

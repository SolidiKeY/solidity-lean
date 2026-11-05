import SolidityBridge.HashBridge.StaticQueries

/-! Constructed checked-boundary controls. Root fuel and call fuel differ:
X2 reaches call0 and exhausts BEFORE depth handling, even at depth1024.
These are kernel controls, not native/source/canonical-input witnesses. -/
namespace Solidity.HashBridge.StaticQueryControls
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

def input (gas depth : Nat) : EVM.State :=
  {(default : EVM.State) with
    accountMap := ∅
    gasAvailable := .ofNat gas
    activeWords := .ofNat 0
    stack := [.ofNat 0,.ofNat 0,.ofNat 0,.ofNat 0,.ofNat 0,.ofNat 0]
    executionEnv := {(default : ExecutionEnv .EVM) with code := ⟨#[0xfa]⟩, depth := depth, perm := false}}

theorem fuel_and_check_order (dest : Array UInt256) :
    X 0 dest (input 0 0) = .error .OutOfFuel ∧
    StaticCodeQueryReceipt 1 dest (input 0 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0)
      (.ofNat 0) (.ofNat 0) [] .empty [] [] (.error .OutOfGass) ∧
    X 1 dest (input 0 0) = .error .OutOfGass ∧
    StaticCodeQueryReceipt 2 dest (input 100000 1024) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0)
      (.ofNat 0) (.ofNat 0) [] .empty [] [] (.error .OutOfFuel) ∧
    X 2 dest (input 100000 1024) = .error .OutOfFuel := by
  have low : StaticCodeQueryReceipt 1 dest (input 0 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0)
      (.ofNat 0) (.ofNat 0) [] .empty [] [] (.error .OutOfGass) := ⟨rfl,rfl,rfl⟩
  have guard : staticGuard (input 100000 1024) = .ok () := rfl
  have short : StaticCodeQueryReceipt 2 dest (input 100000 1024) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0)
      (.ofNat 0) (.ofNat 0) [] .empty [] [] (.error .OutOfFuel) := by
    simp only [StaticCodeQueryReceipt,guard]
    exact ⟨.error .OutOfFuel,⟨rfl,rfl⟩,True.intro,rfl⟩
  exact ⟨rfl,low,StaticCodeQueryReceipt.sound 1 dest (input 0 0) _ _ _ _ _ _ [] .empty [] [] _
    rfl rfl rfl low,short,StaticCodeQueryReceipt.sound 2 dest (input 100000 1024) _ _ _ _ _ _ [] .empty
    [] [] _ rfl rfl rfl short⟩

end Solidity.HashBridge.StaticQueryControls

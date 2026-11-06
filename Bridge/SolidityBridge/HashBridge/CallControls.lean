import SolidityBridge.HashBridge.CallQueries

/-! Constructed kernel controls, not source/native fixtures. A call with one
fuel can reject depth and return bit0 before invoking Theta; it is not uniformly
OutOfFuel. Output memory bytes stay at the actual write expression. -/
namespace Solidity.HashBridge.CallControls
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

def input (depth : Nat) (snapshot : AccountMap .EVM) : EVM.State :=
  {(default : EVM.State) with
    accountMap := ∅
    σ₀ := snapshot
    gasAvailable := .ofNat 64
    activeWords := .ofNat 0
    executionEnv := {(default : ExecutionEnv .EVM) with depth := depth}}

theorem low_fuel_and_depth (snapshot : AccountMap .EVM) :
    call 0 0 [] (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0)
      (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) false (input 0 snapshot) = .error .OutOfFuel ∧
    CallCodeQueryReceipt 1 0 [] (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0)
      (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) false (input 0 snapshot) .empty [] (.error .OutOfFuel) ∧
    call 1 0 [] (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0)
      (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) false (input 0 snapshot) = .error .OutOfFuel ∧
    ∃ out : EVM.State,
      CallCodeQueryReceipt 1 0 [] (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0)
        (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) false (input 1024 snapshot) .empty []
        (.ok (.ofNat 0,out)) ∧
      call 1 0 [] (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0)
        (.ofNat 0) (.ofNat 0) (.ofNat 0) (.ofNat 0) false (input 1024 snapshot) = .ok (.ofNat 0,out) ∧
      out.accountMap = ∅ ∧ out.σ₀ = snapshot ∧ out.returnData = .empty := by
  refine ⟨rfl,?_,rfl,?_⟩
  · exact ⟨.error .OutOfFuel,⟨rfl,rfl⟩,rfl⟩
  · let s := input 1024 snapshot
    let cost : Nat := 0
    let requested : UInt256 := .ofNat 0
    let recipient : UInt256 := .ofNat 0
    let target : UInt256 := .ofNat 0
    let value : UInt256 := .ofNat 0
    let inOffset : UInt256 := .ofNat 0
    let inSize : UInt256 := .ofNat 0
    let outOffset : UInt256 := .ofNat 0
    let outSize : UInt256 := .ofNat 0
    let callgas := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 recipient)
      value requested s.accountMap s.toMachineState s.substate
    let debited : EVM.State := {s with gasAvailable := s.gasAvailable - UInt256.ofNat cost}
    let accrued := (debited.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
    let finish := fun (reply : Batteries.RBSet AccountAddress compare × AccountMap .EVM ×
        UInt256 × Substate × Bool × ByteArray) =>
      let (created,world,refund,substate,ok,bytes) := reply
      let written := writeBytes bytes 0 debited.toMachineState outOffset.toNat
        (min outSize (UInt256.ofNat bytes.size)).toNat
      let notEnoughFunds : Bool := value >
        (s.accountMap.find? debited.executionEnv.codeOwner |>.elim (UInt256.ofNat 0) (·.balance))
      let bit : UInt256 := if !ok || notEnoughFunds || debited.executionEnv.depth == 1024
        then ⟨0⟩ else ⟨1⟩
      let machine : MachineState := {written with
        returnData := bytes
        gasAvailable := written.gasAvailable + refund
        activeWords := .ofNat (MachineState.M
          (MachineState.M debited.activeWords.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat)}
      (bit,{{debited with accountMap := world, substate := substate, createdAccounts := created}
        with toMachineState := machine})
    let out := (finish
      (debited.createdAccounts,debited.accountMap,.ofNat callgas,accrued,false,.empty)).2
    refine ⟨out,?_,?_,rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
    · rfl

end Solidity.HashBridge.CallControls

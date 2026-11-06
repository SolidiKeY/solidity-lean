import SolidityBridge.HashBridge.XiQueries
import SolidityBridge.HashBridge.ChargedControls

/-! Constructed public-invocation controls. Xi starts with its own empty stack;
a parent frame's two hash operands are not silently inherited by the child.
No source installation or native execution witness is asserted. -/
namespace Solidity.HashBridge.XiControls
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

def bareHashEnv : ExecutionEnv .EVM :=
  {(default : ExecutionEnv .EVM) with code := ⟨#[0x20]⟩, perm := false}

/-- Actual Xi initialization rejects the bare hash before a query is executed.
The destination scanner stays opaque; this nonjump guard needs no membership. -/
theorem bare_hash_refused (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (accrued : Substate) :
    XiQueryReceipt 2 created genesis blocks world snapshot (.ofNat 30) accrued bareHashEnv []
      (.error .StackUnderflow) ∧
    Ξ 2 created genesis blocks world snapshot (.ofNat 30) accrued bareHashEnv =
      .error .StackUnderflow := by
  let initial : EVM.State := {(default : EVM.State) with
    accountMap := world
    σ₀ := snapshot
    executionEnv := bareHashEnv
    substate := accrued
    createdAccounts := created
    gasAvailable := .ofNat 30
    blocks := blocks
    genesisBlockHeader := genesis}
  have hc : checks (D_J bareHashEnv.code (.ofNat 0)) initial = .error .StackUnderflow := by
    rw [hash_checks _ _ (show fetched initial = (.KECCAK256,none) from rfl)]
    have hg : hashGuard initial = .error .StackUnderflow := by
      change hashGuard (ChargedControls.input 30 []) = .error .StackUnderflow
      exact ChargedControls.affordable_underflow
    rw [hg]
    rfl
  have receipt : DriverQueryReceipt 1 (D_J bareHashEnv.code (.ofNat 0)) initial []
      (.error .StackUnderflow) :=
    ⟨.guard 0 _ initial .StackUnderflow hc,.guard 0 _ initial .StackUnderflow hc⟩
  have hpub : XiQueryReceipt 2 created genesis blocks world snapshot (.ofNat 30) accrued
      bareHashEnv [] (.error .StackUnderflow) := ⟨.error .StackUnderflow,receipt,rfl⟩
  exact ⟨hpub,XiQueryReceipt.sound 2 created genesis blocks world snapshot (.ofNat 30) accrued bareHashEnv [] _ hpub⟩

end Solidity.HashBridge.XiControls

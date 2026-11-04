import SolidityBridge.HashBridge.FrameSound
import SolidityBridge.ExternalEvm.Assembly.Driver

/-! Query refinement of the published actual STOP producer. No new terminal
semantics: zero memory/base charge and physical capacity are checked, then
Assembly.X_stop supplies the real terminal state/bytes. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof Solidity.Evm.External

theorem stop_gate (dest : Array UInt256) (s : EVM.State) (room : s.stack.length ≤ 1024) :
    Assembly.driverGate dest s .STOP = .ok (s,0) := by
  have expansion : memoryExpansionCost s .STOP = 0 := by
    simp only [memoryExpansionCost,memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : C' s .STOP = 0 := rfl
  simp only [Assembly.driverGate]
  rw [expansion,word_sub_zero]
  simp only [cost,δ,α,Option.getD_some,Nat.not_lt_zero,if_false,reduceCtorEq,
    Nat.sub_zero,Nat.add_zero,if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

/-- A positive checked STOP has an empty direct-query receipt, with the exact
published terminal state. Arbitrary gas/memory/world and tables are retained. -/
theorem stop_query_success (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (hf : fetched s = (.STOP,none)) (room : s.stack.length ≤ 1024) :
    DriverQueryReceipt (fuel+2) dest s [] (.ok (.success (Assembly.stopAfter s 0) .empty)) ∧
      X (fuel+2) dest s = .ok (.success (Assembly.stopAfter s 0) .empty) := by
  have gate : Assembly.driverGate dest s .STOP = .ok (s,0) := stop_gate dest s room
  have checked : checks dest s = .ok (s,0) := by
    unfold checks
    rw [hf]
    change Assembly.driverGate dest s .STOP = .ok (s,0)
    exact gate
  have evaluated : step (fuel+1) 0 (some (fetched s)) s = .ok (Assembly.stopAfter s 0) := by
    rw [hf]
    rfl
  have terminal : terminalData (Assembly.stopAfter s 0) (fetched s).1 = some .empty := by
    rw [hf]
    rfl
  have normal : ((fetched s).1 == .REVERT) = false := by rw [hf]; rfl
  refine ⟨?_,Assembly.X_stop fuel dest s s 0 hf gate⟩
  refine ⟨.success (fuel+1) dest s s 0 (Assembly.stopAfter s 0) .empty checked evaluated terminal normal,?_⟩
  simpa only [hf,directQueries,Bool.false_eq_true,if_false] using
    (ClassifiedQueries.success (fuel+1) dest s s 0 (Assembly.stopAfter s 0) .empty
      checked evaluated terminal normal)

end Solidity.HashBridge

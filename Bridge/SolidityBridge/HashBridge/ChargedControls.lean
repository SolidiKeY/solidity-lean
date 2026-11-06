import SolidityBridge.HashBridge.Charged

/-! Constructed charged-X controls. No canonical empty hash input, native run,
installed source account, or successful whole-program witness is supplied. -/
namespace Solidity.HashBridge.ChargedControls
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

/-- One actual KECCAK byte at PC0, static permission, explicit zero active words.
The word input later readWithPadding remains symbolic. -/
def input (gas : Nat) (stack : List UInt256) : EVM.State :=
  { (default : EVM.State) with
    gasAvailable := .ofNat gas
    activeWords := .ofNat 0
    memory := .empty
    pc := .ofNat 0
    stack := stack
    executionEnv := {(default : ExecutionEnv .EVM) with code := ⟨#[0x20]⟩, perm := false} }

theorem input_fetch (gas : Nat) (stack : List UInt256) :
    fetched (input gas stack) = (.KECCAK256,none) := rfl

/-- Actual base-gas failure precedes underflow for the same empty stack. -/
theorem low_gas_before_underflow : hashGuard (input 0 []) = .error .OutOfGass := rfl

/-- Paying the real base charge exposes the actual next underflow check. -/
theorem affordable_underflow : hashGuard (input 30 []) = .error .StackUnderflow := rfl

/-- The actual 32-byte memory expansion charge fails before the base charge.
The wrapped candidate debit is not asserted to be a reached state. -/
theorem memory_charge_failure :
    memoryExpansionCost (input 2 [.ofNat 0,.ofNat 32]) .KECCAK256 = 3 ∧
    hashOpcodeCost (input 2 [.ofNat 0,.ofNat 32]) = 36 ∧
    hashGuard (input 2 [.ofNat 0,.ofNat 32]) = .error .OutOfGass :=
  ⟨rfl,rfl,rfl⟩

/-- No capacity waiver is inferred from the two consumed operands. -/
theorem capacity_failure :
    hashGuard (input 32 (.ofNat 0 :: .ofNat 0 :: List.replicate 1024 (.ofNat 0))) =
      .error .StackOverflow := by
  have hl : (input 32 (.ofNat 0 :: .ofNat 0 :: List.replicate 1024 (.ofNat 0))).stack.length =
      1026 := by simp only [input, List.length_cons, List.length_replicate]
  unfold hashGuard
  rw [hl]
  rfl

/-- Fuel0 suppresses all checks; fuel1 still encounters the real gas error. -/
theorem low_fuel_order (dest : Array UInt256) :
    X 0 dest (input 0 []) = .error .OutOfFuel ∧
    X 1 dest (input 0 []) = .error .OutOfGass := by
  refine ⟨X_zero dest _,?_⟩
  apply check_failure 0 dest _ .OutOfGass
  rw [hash_checks dest _ (input_fetch 0 []),low_gas_before_underflow]
  rfl

/-- A nonvacuous checked hash edge in static mode, with actual symbolic bytes.
Residual X has fuel1, not a proved successful whole program. -/
theorem actual_edge (dest : Array UInt256) :
    ∃ next, CheckedHashEdge 0 dest (input 32 [.ofNat 0,.ofNat 0])
      (.ofNat 0) (.ofNat 0) [] next ∧
      next.gasAvailable = .ofNat 2 ∧ next.pc = .ofNat 1 := by
  obtain ⟨next,edge⟩ := checked_hash_edge 0 dest (input 32 [.ofNat 0,.ofNat 0])
    (.ofNat 0) (.ofNat 0) [] (input_fetch 32 [.ofNat 0,.ofNat 0]) rfl (by rfl)
  exact ⟨next,edge,edge.gas,edge.pc⟩

end Solidity.HashBridge.ChargedControls

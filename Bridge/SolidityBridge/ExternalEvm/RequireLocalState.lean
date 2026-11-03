import SolidityBridge.ExternalEvm.RequireLocalCut

/-! Exact complete-state equations for the finite ORIGINAL require corridor.
Numeric calculations reuse the published dispatcher; no new machine/evaluator. -/
namespace EvmYul.EVM.DriverProof
open Solidity.Evm.External (BinaryOpcode UnaryOpcode)

def localAfter (s : State) (cost : Nat) (nextPC : UInt256) (stack : Stack UInt256) : State :=
  {s with
    execLength := s.execLength + 1
    gasAvailable := s.gasAvailable - UInt256.ofNat cost
    pc := nextPC
    stack := stack}

theorem localAfter_fields (s : State) (cost : Nat) (pc : UInt256) (xs : Stack UInt256) :
    (localAfter s cost pc xs).toState = s.toState ∧
    (localAfter s cost pc xs).memory = s.memory ∧
    (localAfter s cost pc xs).returnData = s.returnData ∧
    (localAfter s cost pc xs).H_return = s.H_return ∧
    (localAfter s cost pc xs).activeWords = s.activeWords ∧
    (localAfter s cost pc xs).gasAvailable = s.gasAvailable - UInt256.ofNat cost ∧
    (localAfter s cost pc xs).execLength = s.execLength + 1 ∧
    (localAfter s cost pc xs).pc = pc ∧ (localAfter s cost pc xs).stack = xs :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem local_stack_eta (s : State) (xs : Stack UInt256) (hs : s.stack = xs) :
    {s with stack := xs} = s := by rw [← hs]

theorem local_push0 (fuel cost : Nat) (s : State) :
    step (fuel + 1) cost (some (.Push .PUSH0, none)) s =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 1) ((UInt256.ofNat 0) :: s.stack)) := by rfl

theorem local_push1 (fuel cost : Nat) (s : State) (v : UInt256):
    step (fuel + 1) cost (some (.Push .PUSH1, (some (v, 1)))) s =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 2) (v :: s.stack)) := by rfl

theorem local_push2 (fuel cost : Nat) (s : State) (v : UInt256):
    step (fuel + 1) cost (some (.Push .PUSH2, (some (v, 2)))) s =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 3) (v :: s.stack)) := by rfl

theorem local_push4 (fuel cost : Nat) (s : State) (v : UInt256):
    step (fuel + 1) cost (some (.Push .PUSH4, (some (v, 4)))) s =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 5) (v :: s.stack)) := by rfl

theorem local_push20 (fuel cost : Nat) (s : State) (v : UInt256):
    step (fuel + 1) cost (some (.Push .PUSH20, (some (v, 20)))) s =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 21) (v :: s.stack)) := by rfl

theorem local_jumpdest (fuel cost : Nat) (s : State) :
    step (fuel + 1) cost (some (.JUMPDEST, none)) s =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 1) s.stack) := by rfl

theorem local_binary (op : BinaryOpcode) (fuel cost : Nat) (s : State)
    (a b : UInt256) (tail : Stack UInt256) :
    step (fuel + 1) cost (some (op.code, none)) {s with stack := a :: b :: tail} =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 1) (op.value a b :: tail)) := by
  rw [op.charged_dispatch, op.dispatch]
  simp only [Solidity.Evm.External.prepare, Solidity.Evm.External.debitOpcodeCost, word_sub_zero]
  rfl

theorem local_unary (op : UnaryOpcode) (fuel cost : Nat) (s : State)
    (a : UInt256) (tail : Stack UInt256) :
    step (fuel + 1) cost (some (op.code, none)) {s with stack := a :: tail} =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 1) (op.value a :: tail)) := by
  rw [op.charged_dispatch, op.dispatch]
  simp only [Solidity.Evm.External.prepare, Solidity.Evm.External.debitOpcodeCost, word_sub_zero]
  rfl

theorem local_dup1 (fuel cost : Nat) (s : State) (a : UInt256)
    (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.DUP1, none))
      {s with stack := a :: tail} =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 1) (a :: a :: tail)) := by rfl

theorem local_dup2 (fuel cost : Nat) (s : State) (a b : UInt256)
    (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.DUP2, none))
      {s with stack := a :: b :: tail} =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 1) (b :: a :: b :: tail)) := by rfl

theorem local_swap1 (fuel cost : Nat) (s : State) (a b : UInt256)
    (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.SWAP1, none))
      {s with stack := a :: b :: tail} =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 1) (b :: a :: tail)) := by rfl

theorem local_swap2 (fuel cost : Nat) (s : State) (a b c : UInt256)
    (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.SWAP2, none))
      {s with stack := a :: b :: c :: tail} =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 1) (c :: b :: a :: tail)) := by rfl

theorem local_swap5 (fuel cost : Nat) (s : State) (a b c d e f : UInt256)
    (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.SWAP5, none))
      {s with stack := a :: b :: c :: d :: e :: f :: tail} =
      .ok (localAfter s cost (s.pc + UInt256.ofNat 1) (f :: b :: c :: d :: e :: a :: tail)) := by rfl

theorem local_jump (fuel cost : Nat) (s : State) (target : UInt256)
    (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.JUMP, none)) {s with stack := target :: tail} =
      .ok (localAfter s cost target tail) := require_jump_step fuel cost s target tail

theorem local_jumpi (fuel cost : Nat) (s : State) (target condition : UInt256)
    (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.JUMPI, none)) {s with stack := target :: condition :: tail} =
      .ok (localAfter s cost (if condition != ⟨0⟩ then target else s.pc + ⟨1⟩) tail) :=
  require_jumpi_step fuel cost s target condition tail

theorem local_word_roundtrip (word : UInt256) : UInt256.ofNat word.toNat = word := by
  cases word with
  | mk word =>
    apply congrArg UInt256.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt word.isLt

/-- Zero-size REVERT still retains the actual padded-reader expression.
No logical specification of opaque ffi.ByteArray.zeroes is assumed. -/
theorem local_revert_zero (fuel cost : Nat) (s : State) (tail : Stack UInt256) :
    step (fuel + 1) cost (some (.REVERT, none))
      {s with stack := UInt256.ofNat 0 :: UInt256.ofNat 0 :: tail} =
      .ok {localAfter s cost (s.pc + UInt256.ofNat 1) tail with
        H_return := s.memory.readWithPadding 0 0} := by
  have form : step (fuel + 1) cost (some (.REVERT, none))
      {s with stack := UInt256.ofNat 0 :: UInt256.ofNat 0 :: tail} =
      .ok {localAfter s cost (s.pc + UInt256.ofNat 1) tail with
        H_return := s.memory.readWithPadding 0 0
        activeWords := UInt256.ofNat (UInt256.ofNat s.activeWords.toNat).toNat} := by rfl
  simpa only [local_word_roundtrip] using form

theorem local_revert_zero_expansion (s : State) (tail : Stack UInt256) :
    memoryExpansionCost {s with stack := UInt256.ofNat 0 :: UInt256.ofNat 0 :: tail} .REVERT = 0 := by
  change Cₘ (UInt256.ofNat s.activeWords.toNat) - Cₘ s.activeWords = 0
  rw [local_word_roundtrip]
  exact Nat.sub_self _

#print axioms localAfter_fields
#print axioms local_binary
#print axioms local_unary
#print axioms local_swap5
#print axioms local_jump
#print axioms local_jumpi
#print axioms local_word_roundtrip
#print axioms local_revert_zero
#print axioms local_revert_zero_expansion
end EvmYul.EVM.DriverProof

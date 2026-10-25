import SolidityBridge.ExternalEvm.Environment
import EvmYul.EVM.Semantics

/-!
Checked counterexamples to a blanket one-opcode correspondence. The core's
instruction language contains deliberate macro instructions and abstractions;
they cannot be silently treated as EVM opcodes with the same input stack.
-/
namespace Solidity.Evm.External

/-- No globally collision-free numeric interpretation of symbolic storage
slots exists: the symbolic address space is infinite and EVM words are finite.
Faithful separation of arbitrary symbolic cells therefore requires a restricted
address domain or a store relation that accounts for aliases. -/
theorem no_injective_slot_encoding : ¬ ∃ f : Slot → Fin W, Function.Injective f := by
  rintro ⟨f, hf⟩
  letI : Infinite Slot := Infinite.of_injective Slot.root (fun _ _ h => Slot.root.inj h)
  letI : Finite Slot := Finite.of_injective f hf
  exact not_finite Slot

/-- The core's two-argument payment instruction is not the upstream CALL
opcode, which requires seven arguments. This is an unconditional concrete
disagreement, before callee execution, gas accounting or account lookup. -/
theorem call_arity_mismatch (s : EvmYul.EVM.State) :
    (∃ m', Instr.call.step {Machine.init with stack := [w[0], w[1]]} = .ok m' 0) ∧
    EvmYul.EVM.step 1 0 (some (.CALL, none))
      {s with stack := [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 1]} =
        .error .StackUnderflow := by
  exact ⟨⟨_, rfl⟩, rfl⟩

/-- REVERT is a no-argument core halt. The actual opcode reads the return
data's memory offset and length before the evaluator reports the halt. -/
theorem revert_arity_mismatch (s : EvmYul.EVM.State) :
    Instr.revert.step Machine.init = .revert ∧
    EvmYul.EVM.step 1 0 (some (.REVERT, none)) {s with stack := []} =
      .error .StackUnderflow := ⟨rfl, rfl⟩

/-- A direct JUMP requires a destination on the upstream stack. The core
relative jump carries its destination in the instruction itself. -/
theorem jump_arity_mismatch (s : EvmYul.EVM.State) (n : Nat) :
    (Instr.jump n).step Machine.init = .ok Machine.init n ∧
    EvmYul.EVM.step 1 0 (some (.JUMP, none)) {s with stack := []} =
      .error .StackUnderflow := ⟨rfl, rfl⟩

/-- The same mismatch for conditional jumps, with one versus two operands. -/
theorem jumpi_arity_mismatch (s : EvmYul.EVM.State) (n : Nat) :
    (Instr.jumpi n).step {Machine.init with stack := [w[0]]} = .ok Machine.init 0 ∧
    EvmYul.EVM.step 1 0 (some (.JUMPI, none))
      {s with stack := [EvmYul.UInt256.ofNat 0]} = .error .StackUnderflow := ⟨rfl, rfl⟩

/-- Fixed-cell loads are macros: the EVM opcode first needs an address. -/
theorem mload_arity_mismatch (s : EvmYul.EVM.State) (n : Nat) :
    (∃ m', (Instr.mload n).step Machine.init = .ok m' 0) ∧
    EvmYul.EVM.step 1 0 (some (.MLOAD, none)) {s with stack := []} =
      .error .StackUnderflow := ⟨⟨_, rfl⟩, rfl⟩

/-- Fixed-cell stores likewise carry the address in the core instruction. -/
theorem mstore_arity_mismatch (s : EvmYul.EVM.State) (n : Nat) :
    (∃ m', (Instr.mstore n).step {Machine.init with stack := [w[0]]} = .ok m' 0) ∧
    EvmYul.EVM.step 1 0 (some (.MSTORE, none))
      {s with stack := [EvmYul.UInt256.ofNat 0]} = .error .StackUnderflow := ⟨⟨_, rfl⟩, rfl⟩

/-- Symbolic slot offsets do not wrap, whereas the EVM's ADD does. This
prevents treating unrestricted symbolic-slot addition as a numeric ADD. -/
theorem slot_add_wrap_mismatch :
    (Slot.root (W - 1)).add 1 = .root W ∧
    EvmYul.UInt256.add (encode wMax) (EvmYul.UInt256.ofNat 1) = EvmYul.UInt256.ofNat 0 := by
  constructor
  · change Slot.root (W - 1 + 1) = Slot.root W
    congr 1
  · apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    change (W - 1 + 1) % EvmYul.UInt256.size = 0
    rw [size_eq, Nat.sub_add_cancel (by have := W_pos; omega), Nat.mod_self]

end Solidity.Evm.External

/-- info: 'Solidity.Evm.External.no_injective_slot_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.no_injective_slot_encoding

/-- info: 'Solidity.Evm.External.call_arity_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.call_arity_mismatch

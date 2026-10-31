import EvmYul.Semantics
import EvmYul.EVM.Gas
import EvmYul.EVM.Instr

/-!
Actual vendored EVM MSTORE dispatcher and memory-expansion components.
No zero-fill/word-byte specification, source interpretation, bytecode execution
or whole-driver resource adequacy is assumed or asserted.
-/
namespace Solidity.Evm.External.TryMemory
open EvmYul

/-- The real opcode consumes its two actual stack operands and increments PC. -/
theorem mstore_dispatch (s : EVM.State) (a v : UInt256) (tail : List UInt256) :
    EvmYul.step (.MSTORE : Operation .EVM) none {s with stack := a :: v :: tail} =
      .ok (({s with toMachineState := s.toMachineState.mstore a v}).replaceStackAndIncrPC tail) := rfl

/-- An empty actual opcode stack is underflow, not a completed revert. -/
theorem mstore_empty (s : EVM.State) :
    EvmYul.step (.MSTORE : Operation .EVM) none {s with stack := []} =
      .error .StackUnderflow := rfl

/-- A lone address is still underflow: the value is a separate operand. -/
theorem mstore_one (s : EVM.State) (a : UInt256) :
    EvmYul.step (.MSTORE : Operation .EVM) none {s with stack := [a]} =
      .error .StackUnderflow := rfl

/-- Exact memory expression in the original vendor, including opaque padding. -/
theorem mstore_memory (m : MachineState) (a v : UInt256) :
    (MachineState.mstore m a v).memory =
      _root_.ByteArray.write (UInt256.toByteArray v) 0 m.memory a.toNat 32 := by
  simp only [MachineState.mstore, MachineState.writeWord, EvmYul.writeBytes]

/-- Stores preserve the actual gas and return buffers; driver charging is separate. -/
theorem mstore_frame (m : MachineState) (a v : UInt256) :
    (m.mstore a v).gasAvailable = m.gasAvailable ∧
    (m.mstore a v).returnData = m.returnData ∧
    (m.mstore a v).H_return = m.H_return := by
  simp only [MachineState.mstore, MachineState.writeWord, EvmYul.writeBytes]
  exact ⟨True.intro, True.intro, True.intro⟩

/-- The source prologue's byte offset64 touches exactly three words from zero. -/
theorem prologue_words : MachineState.M 0 64 32 = 3 := rfl

/-- Both overlapping stores stay within that already resident interval. -/
theorem overlap_words : MachineState.M (MachineState.M 3 0 32) 4 32 = 3 := rfl

/-- Moving the prologue one word is observably different in expansion accounting. -/
theorem wrong_prologue_words : MachineState.M 0 96 32 = 4 ∧
    MachineState.M 0 96 32 ≠ MachineState.M 0 64 32 := ⟨rfl, by decide⟩

/-- The pinned vendor parses the actual MSTORE byte as that opcode. -/
theorem mstore_byte : EvmYul.EVM.parseInstr 0x52 = some .MSTORE := rfl

/-- Conditional expansion charge from a fresh active-word count, not a gas-success premise. -/
theorem prologue_expansion (s : EVM.State) :
    EVM.memoryExpansionCost
      {s with
        activeWords := UInt256.ofNat 0
        stack := [UInt256.ofNat 64, UInt256.ofNat 128]} .MSTORE = 9 := by
  simp only [EVM.memoryExpansionCost, EVM.memoryExpansionCost.μᵢ']
  rfl

/-- After the prologue, actual offsets0 and4 each require no further expansion. -/
theorem overlap_expansion (s : EVM.State) (v : UInt256) :
    EVM.memoryExpansionCost
      {s with
        activeWords := UInt256.ofNat 3
        stack := [UInt256.ofNat 0, v]} .MSTORE = 0 ∧
    EVM.memoryExpansionCost
      {s with
        activeWords := UInt256.ofNat 3
        stack := [UInt256.ofNat 4, v]} .MSTORE = 0 := by
  constructor <;> simp only [EVM.memoryExpansionCost, EVM.memoryExpansionCost.μᵢ', List.getElem!_cons_zero] <;> rfl

/-- The exact fresh-state record shape used inside vendor Ξ preserves its
supplied globals and derives empty machine memory/stack/PC, not an assumed frame. -/
theorem fresh_fields (s : EVM.State) :
    let fresh : EVM.State :=
      { (default : EVM.State) with
        accountMap := s.accountMap
        σ₀ := s.σ₀
        executionEnv := s.executionEnv
        substate := s.substate
        createdAccounts := s.createdAccounts
        gasAvailable := s.gasAvailable
        blocks := s.blocks
        genesisBlockHeader := s.genesisBlockHeader }
    fresh.memory = ByteArray.empty ∧ fresh.activeWords = UInt256.ofNat 0 ∧
    fresh.stack = [] ∧ fresh.pc = UInt256.ofNat 0 ∧
    fresh.executionEnv = s.executionEnv ∧ fresh.accountMap = s.accountMap :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Existing dispatcher fee, separate from expansion and actual driver success. -/
theorem mstore_base_cost (s : EVM.State) : EVM.C' s .MSTORE = 3 := rfl

/-- MSTORE8's actual byte is not accepted as MSTORE. -/
theorem wrong_opcode : EVM.parseInstr 0x53 ≠ some .MSTORE := by decide

/-- Actual ordered stores at0/4; padding remains exactly the vendor expression. -/
theorem overlap_memory (m : MachineState) (x y : UInt256) :
    ((m.mstore (UInt256.ofNat 0) x).mstore (UInt256.ofNat 4) y).memory =
      _root_.ByteArray.write (UInt256.toByteArray y) 0
        (_root_.ByteArray.write (UInt256.toByteArray x) 0 m.memory 0 32) 4 32 := by
  rw [mstore_memory, mstore_memory]
  congr 1

end Solidity.Evm.External.TryMemory

import Solidity.Backend.Executable.TransferCall
import Solidity.Backend.Executable.StipendCallChecks

/-! Concrete transfer branch assembly behind a populated caller prelude and
actual requested-gas CALL. Neither assembler layout nor the terminal slice
supplies a general fetched execution theorem. -/
namespace Solidity.Backend.Executable.TransferCallChecks
open Scalar ScalarSequence TransferCall
open ScalarSequenceChecks (caller)
open ValueCallChecks (recipient)

def prelude : Program :=
  [Failure.pushByte 0x55, Failure.pushNat 0, .op .MSTORE8] ++
    (frameTail caller [17,29]).reverse.map pushWord

def payment : Program := prelude ++ StipendCall.code recipient

/-- The concrete all32 layout range is discharged, not supplied as a future
simulation certificate. Only two actual branch labels occur. -/
theorem available : (assembleAfter payment).isSome = true := by
  apply assembly_available payment
  intro l member
  change l ∈ [0,1] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

def output : Assembled Empty := (assembleAfter payment).get available

theorem assembled : assembleAfter payment = some output := (Option.some_get available).symm

theorem prefix_lengths : (encode prelude).length = 168 ∧ (encode payment).length = 244 := by
  constructor <;> decide +kernel

/-- A concrete protected PUSH32 immediate rejects PC8. The actual selected-target
subtraction is separately refused in relative_false_target below. -/
theorem wrong_relative_destination : validJumpdest (encode output.code) 8 = false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  obtain ⟨byte,_⟩ := (validJumpdest_iff _ _).mp bad
  rw [prefix_preserved payment assembled, encode_append,
    List.getElem?_append_left (by rw [prefix_lengths.2]; decide)] at byte
  have zeroByte : (encode payment)[8]? = some 0 := by decide +kernel
  rw [zeroByte] at byte
  cases byte

/-- A nonempty actual assembled consumer preserving the caller preparation;
both checked branch targets are separately in destinations_inhabited. Exact global jump
execution is not inferred from this layout result. -/
theorem kernel_client :
    ∃ suffix : Program, output.code = payment ++ suffix ∧
      decode (encode output.code) = some output.code ∧
      validJumpdest (encode output.code) 8 = false :=
  ⟨_,prefix_preserved payment assembled,decode_encode _,wrong_relative_destination⟩

/-- Both published assembler jump certificates are inhabited by this actual
combined prelude/CALL program, without supplying an arbitrary assembled output. -/
theorem destinations_inhabited :
    ∃ jf je : Nat, validJumpdest (encode output.code) jf = true ∧
      validJumpdest (encode output.code) je = true ∧
      ∃ wf we : Fin 33, ∃ bf : Vector UInt8 wf, ∃ be : Vector UInt8 we,
        output.code[payment.length+1]? = some (.push wf bf) ∧
        output.code[payment.length+3]? = some (.push we be) ∧
        jf = ofBytesBE bf.toList ∧ je = ofBytesBE be.toList := by
  obtain ⟨⟨jf,bf,_,_,pf,_,vf⟩,⟨je,be,_,_,pe,_,ve⟩⟩ := branch_destinations payment assembled
  exact ⟨_,_,vf,ve,_,_,bf,be,pf,pe,rfl,rfl⟩

def terminalMachine : Failure.Slice.Machine :=
  ⟨[⟨17,by decide⟩,⟨29,by decide⟩],fun _ => 0x55⟩

theorem terminal_control :
    Failure.Slice.checkedRun (Failure.emit 0 .empty ++ [.op .ADD]) terminalMachine =
      some (terminalMachine,some (.revert [])) :=
  failure_terminal terminalMachine (by decide) [.op .ADD]

theorem wrong_failure_bytes :
    Failure.Slice.checkedRun (Failure.emit 0 .empty ++ [.op .ADD]) terminalMachine ≠
      some (terminalMachine,some (.revert [0xde,0xad])) := by
  rw [terminal_control]
  intro bad
  have obs := congrArg (fun r : Option (Failure.Slice.Machine × Option Roadmap.Outcome) =>
    r.map (fun pair => pair.2)) bad
  cases obs

theorem assembled_terminal_control :
    Failure.Slice.checkedRun (output.code.drop (payment.length+6)) terminalMachine =
      some (terminalMachine,some (.revert [])) :=
  assembled_failure_terminal payment assembled terminalMachine (by decide)

private theorem false_offset (W : Widths Nat) :
    tagOffset W (items payment) 0 = 244+5+(W 0).val+(W 1).val := by
  have index : tagIndex (items payment) 0 = some 23 := by decide +kernel
  rw [tagOffset, index]
  simp only [itemOffset, items, payment, prelude, branch, Block.expand,
    StipendCall.code, StipendCall.operands, StipendCall.gasCode,
    ValueCall.emptyBuffers, ValueCall.localAmount, Scalar.literal, Scalar.pushWord,
    Scalar.pushByte, ScalarSequence.frameTail, ScalarSequence.callerFrame,
    Failure.emit, Failure.Input.bytes, Failure.Input.terminal, Failure.writes,
    Failure.pushNat, Failure.pushByte, List.cons_append, List.nil_append,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil,
    List.take_succ_cons, List.take_zero, Item.size, Instr.size, List.sum_cons, List.sum_nil, Nat.reduceAdd]
  omega

private theorem no_prelude_destination (k : Nat) (small : k < 168) :
    validJumpdest (encode output.code) k = false := by
  apply Bool.eq_false_iff.mpr
  intro bad
  obtain ⟨byte,_⟩ := (validJumpdest_iff _ _).mp bad
  rw [prefix_preserved payment assembled, encode_append,
    List.getElem?_append_left (by rw [prefix_lengths.2]; omega)] at byte
  rw [payment, encode_append,
    List.getElem?_append_left (by rw [prefix_lengths.1]; exact small)] at byte
  have allBytes : (encode prelude).all (fun b => b != Op.JUMPDEST.code) = true := by decide +kernel
  have impossible := (List.all_eq_true.mp allBytes) _ (List.mem_of_getElem? byte)
  cases impossible

/-- This is the actual resolved false target with the actual chosen widths;
subtracting the244-byte combined prefix produces an invalid whole-code PC.
No guessed small coordinate is substituted for the real selected operand. -/
theorem relative_false_target :
    ∃ imm, output.code[payment.length+1]? =
      some (.push (asmWidths 0 (items payment) 0) imm) ∧
      ofBytesBE imm.toList = 244+5+(asmWidths 0 (items payment) 0).val+
        (asmWidths 0 (items payment) 1).val ∧
      validJumpdest (encode output.code) (ofBytesBE imm.toList-244) = false := by
  obtain ⟨_,imm,_,_,push,_,value,_⟩ :=
    assemble_pushTag assembled (show (items payment)[payment.length+1]? = some (.pushTag 0) from rfl)
  have coordinate : ofBytesBE imm.toList = 244+5+(asmWidths 0 (items payment) 0).val+
      (asmWidths 0 (items payment) 1).val := by
    simpa only [Nat.zero_add, false_offset] using value
  refine ⟨imm,push,coordinate,?_⟩
  apply no_prelude_destination
  have first := (asmWidths 0 (items payment) 0).isLt
  have second := (asmWidths 0 (items payment) 1).isLt
  omega

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms available

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assembled

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.prefix_lengths' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_lengths

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.wrong_relative_destination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_relative_destination

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.kernel_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kernel_client

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.destinations_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms destinations_inhabited

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.terminal_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms terminal_control

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.wrong_failure_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_failure_bytes

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.assembled_terminal_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assembled_terminal_control

/-- info: 'Solidity.Backend.Executable.TransferCallChecks.relative_false_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relative_false_target

end Solidity.Backend.Executable.TransferCallChecks

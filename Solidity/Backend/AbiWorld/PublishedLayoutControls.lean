import Solidity.Backend.AbiWorld.PublishedLayout

/-! Empty, mixed, nested-packet, word-boundary and modular-offset controls. -/
namespace Solidity.Backend.AbiWorld.PublishedLayoutControls
open Roadmap PublishedLayout

/-- Empty inputs and empty dynamic tails retain their actual, different encodings. -/
theorem empty_controls : Source.abiLayout [] = [] ∧
    (Source.abiLayout [(true, [])]).length = 64 ∧
    Source.beValue ((Source.abiLayout [(true, [])]).take 32) = 32 := by decide +kernel

/-- Mixed static/dynamic parts advance offsets by padded actual tail lengths. -/
theorem mixed_boundary_offsets :
    let parts := [(false, Source.wordBytes (Source.toWord 7)),
      (true, List.replicate 31 0xa5), (true, List.replicate 33 0x42)]
    (Source.abiLayout parts).length = 256 ∧
    Source.beValue (((Source.abiLayout parts).drop 32).take 32) = 96 ∧
    Source.beValue (((Source.abiLayout parts).drop 64).take 32) = 160 ∧
    Source.beValue (((Source.abiLayout parts).drop 96).take 32) = 31 ∧
    Source.beValue (((Source.abiLayout parts).drop 160).take 32) = 33 := by decide +kernel

/-- A nested already-encoded packet is preserved as the outer dynamic payload. -/
theorem nested_packet_payload :
    let nested := Source.abiLayout [(true, [1, 2])]
    ((Source.abiLayout [(true, nested)]).drop 64).take nested.length = nested := by decide +kernel

/-- The published encoder wraps a nonrepresentable cursor, rather than assuming it fits. -/
theorem cursor_wrap_control :
    Source.beValue ((Source.abiLayout.go [(true, [0x42])] (2 ^ 256)).1.take 32) = 0 := by
  rw [dynamic_offset]

/-- Raw fragments do not imply canonical static head width. -/
theorem missing_static_width_negative :
    headSize [(false, [0x42])] ≠ 32 * ([(false, [0x42])] : List (Bool × Bytes)).length := by decide

private def machine : Failure.Slice.Machine := ⟨[], fun _ => 0xee⟩

/-- Nonzero-address actual emitters observe independent source Error and Panic bytes. -/
theorem source_packet_combination :
    Failure.Slice.checkedRun (emitError 31 [0x42]) machine =
      some ({ machine with memory := Failure.Slice.putBytes machine.memory 31 (Source.errorData [0x42]) },
        some (.revert (Source.errorData [0x42]))) ∧
    Failure.Slice.checkedRun (Failure.emit 160 (sourcePanicInput .alloc)) machine =
      some ({ machine with memory := Failure.Slice.putBytes machine.memory 160 (Source.panicData .alloc) },
        some (.revert (Source.panicData .alloc))) := by
  constructor
  · simpa only [List.append_nil] using execute_source_error 31 [0x42] [] machine
      (by unfold Failure.Fits; decide +kernel) (by decide)
  · simpa only [List.append_nil] using execute_source_panic 160 .alloc [] machine
      (by unfold Failure.Fits; decide +kernel) (by decide)

/-- info: 'Solidity.Backend.AbiWorld.PublishedLayoutControls.source_packet_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_packet_combination

/-- info: 'Solidity.Backend.AbiWorld.PublishedLayoutControls.mixed_boundary_offsets' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms mixed_boundary_offsets
/-- info: 'Solidity.Backend.AbiWorld.PublishedLayoutControls.cursor_wrap_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cursor_wrap_control
end Solidity.Backend.AbiWorld.PublishedLayoutControls

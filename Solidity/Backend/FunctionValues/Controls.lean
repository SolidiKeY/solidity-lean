import Solidity.Backend.FunctionValues.Execution

/-! Inhabited source/compiled value controls. These are values, not a claim
that dynamic external-function call syntax has been lowered. -/
namespace Solidity.Backend.FunctionValues.Controls
open Solidity.Source Solidity.Roadmap Evm

def layout : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
-- Reference-bearing parameters and tuple returns remain in the source index.
def sample : ExternalValue layout [.array .memory .bool none] [.bool, .address false] (some .view) :=
  ⟨⟨7, by decide⟩, [0x12, 0x34, 0x56, 0x78], rfl⟩

def changedSelector : ExternalValue layout [.array .memory .bool none] [.bool, .address false] (some .view) :=
  ⟨⟨7, by decide⟩, [0x12, 0x34, 0x56, 0x79], rfl⟩

def changedAddress : ExternalValue layout [.array .memory .bool none] [.bool, .address false] (some .view) :=
  ⟨⟨8, by decide⟩, [0x12, 0x34, 0x56, 0x78], rfl⟩

theorem observations : sample.number = 0x712345678 ∧
    sample.source.key = some 0x712345678 ∧
    (encode sample.source).val = 0x712345678 ∧
    (encode sample.source).val / 2 ^ 32 = 7 ∧
    Source.beBytes 4 ((encode sample.source).val % 2 ^ 32) = [0x12, 0x34, 0x56, 0x78] := by
  decide

theorem comparison_flags : decide (sample.number = changedSelector.number) = false ∧
    decide (sample.number = changedAddress.number) = false ∧
    decide (sample.number = sample.number) = true := by decide

theorem source_unequal : Source.cmpVal .eq sample.source changedSelector.source = .ok false ∧
    Source.cmpVal .eq sample.source changedAddress.source = .ok false := by
  constructor
  · rw [source_comparison, comparison_flags.1]
  · rw [source_comparison, comparison_flags.2.1]

theorem compiled_unequal :
    run (construct changedSelector.source ++ construct sample.source ++ [.eq]) Machine.init =
      .ok { Machine.init with stack := [.val (bword false)] } 0 :=
  by
    rw [comparison, comparison_flags.1]
    rfl

theorem compiled_equal :
    run (construct sample.source ++ construct sample.source ++ [.eq]) Machine.init =
      .ok { Machine.init with stack := [.val (bword true)] } 0 :=
  by
    rw [comparison, comparison_flags.2.2]
    rfl

theorem roundtrip : decode layout _ _ _ (encode sample.source) = some sample.source :=
  decode_encode sample.source

theorem high_bits_negative : decode layout [] [] none ⟨2 ^ 192, by decide⟩ = none :=
  high_bits_refused _ (by decide)

theorem malformed_selector : ¬ ([0x12, 0x34, 0x56] : List UInt8).length = 4 := by decide

theorem memory_positive :
    run (construct sample.source ++ [.mstore 9, .mload 9]) Machine.init =
      .ok { Machine.init with
        stack := [.val (encode sample.source)]
        mem := upd Machine.init.mem 9 (.val (encode sample.source)) } 0 :=
  memory_roundtrip sample.source Machine.init 9

theorem storage_positive :
    run (construct sample.source ++ [.push (.slot (.root 3)), .sstore, .push (.slot (.root 3)), .sload]) Machine.init =
      .ok { Machine.init with
        stack := [.val (encode sample.source)]
        store := WordStore.write Machine.init.store (.root 3) (encode sample.source).val } 0 :=
  storage_roundtrip sample.source Machine.init (.root 3)

theorem memory_failure : run [.mstore 0] Machine.init = .fault :=
  empty_store_fault Machine.init rfl 0

end Solidity.Backend.FunctionValues.Controls

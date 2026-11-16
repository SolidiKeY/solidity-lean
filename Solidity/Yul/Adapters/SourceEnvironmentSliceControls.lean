import Solidity.Yul.Adapters.SourceEnvironmentSlice
import Solidity.Yul.Views.SourceTargetInputControls
import Solidity.Yul.Views.SourceBalanceOperandControls

/-! Actual Source reads and executed local target slices use distinct sender,
self, full-width value and time. Code-presence/history balance branches and a
wrong target ledger remain observable. This is a gas-free slice, not compiler
or independently deployed world-ledger adequacy. -/
namespace Solidity.Yul.Adapters.SourceEnvironmentSlice.Controls
open Solidity.Yul.Views Solidity.Yul.Views.Controls

/-- Whole target memory and arbitrary stack suffix survive the ordered reads. -/
theorem ordered_target (tail : List Backend.Environment.Word) (memory : Backend.Environment.Memory) :
    Backend.Environment.runSlice tiFrame magicCode ⟨tail,memory⟩=
      some (⟨environmentWord highestUint::environmentWord 88::environmentWord 17::tail,memory⟩ : Backend.Environment.Slice) :=
  magic_target tiGlob tiSource tiFunds tail memory

theorem source_pair (n : Nat) :
    (sourceMagicReads tiGlob tiSource (n+1)).run tiState=
      (.ok (.val (uintValueOfWord Source.SemanticsExamples.E0.layout 17),.val (Source.Val.address tiSource.sender),
        .val (uintValueOfWord Source.SemanticsExamples.E0.layout highestUint)),tiState) :=
  (magic tiGlob tiSource n tiState tiFunds [] (fun _=>0)).1

theorem ordered_values (memory : Backend.Environment.Memory) :
    (Backend.Environment.runSlice tiFrame magicCode ⟨[environmentWord 11,environmentWord 22],memory⟩).map
      (fun result => result.stack.map (fun value=>value.1.toNat))=some [highestUint.val,88,17,11,22] := by
  rw [ordered_target]
  simp only [Option.map_some,List.map_cons,List.map_nil,environmentWord_nat]
  rfl

theorem wrong_sender_and_order (memory : Backend.Environment.Memory) :
    (Backend.Environment.runSlice tiFrame magicCode ⟨[],memory⟩).map
      (fun result => result.stack.map (fun value=>value.1.toNat))≠some [highestUint.val,99,17] ∧
    (Backend.Environment.runSlice tiFrame magicCode ⟨[],memory⟩).map
      (fun result => result.stack.map (fun value=>value.1.toNat))≠some [17,88,highestUint.val] := by
  rw [ordered_target]
  simp only [Option.map_some,List.map_cons,List.map_nil,environmentWord_nat]
  decide +kernel

theorem balance_snapshots (tail : List Backend.Environment.Word) (memory : Backend.Environment.Memory) :
    Backend.Environment.runSlice (sourceEnvironmentFrame sbGlob sbFrame (sourceObservedFunds sbGlob sbExternal)) [.op .BALANCE]
      ⟨environmentWord (addressInputWord sbAddress)::tail,memory⟩=
        some (⟨environmentWord 7::tail,memory⟩ : Backend.Environment.Slice) ∧
    Backend.Environment.runSlice (sourceEnvironmentFrame sbGlob sbFrame (sourceObservedFunds sbGlob sbHistory)) [.op .BALANCE]
      ⟨environmentWord (addressInputWord sbAddress)::tail,memory⟩=
        some (⟨environmentWord 9::tail,memory⟩ : Backend.Environment.Slice) ∧
    Backend.Environment.runSlice (sourceEnvironmentFrame sbGlob sbFrame (sourceObservedFunds sbGlob sbSystem)) [.op .BALANCE]
      ⟨environmentWord (addressInputWord sbAddress)::tail,memory⟩=
        some (⟨environmentWord 77::tail,memory⟩ : Backend.Environment.Slice) :=
  ⟨balance_target sbGlob sbFrame sbExternal sbAddress tail memory,
    balance_target sbGlob sbFrame sbHistory sbAddress tail memory,
    balance_target sbGlob sbFrame sbSystem sbAddress tail memory⟩

/-- A source local-address balance producer inhabits the target correspondence. -/
theorem actual_balance_source (n : Nat) :
    (Source.evalE sbGlob sbFrame (n+2) (sourceBalanceExpr Source.Idx.here)).run sbHistory=
      (.ok (.val (uintValueOfWord Source.SemanticsExamples.E0.layout 9)),sbHistory) :=
  (balance_local sbGlob sbFrame n sbHistory .here sbAddress rfl [] (fun _=>0)).1

/-- A real address assignment changes the operand before BALANCE. The target
slice is parameterized by that actual reached account and snapshot. -/
theorem effectful_operand_slice (n : Nat) (tail : List Backend.Environment.Word) (memory : Backend.Environment.Memory) :
    (Source.evalE sbGlob sbFrame (n+3) (.balance sboAssign)).run sbSystem=
      (.ok (.val (uintValueOfWord Source.SemanticsExamples.E0.layout 9)),sboAfter) ∧
    Backend.Environment.runSlice (sourceEnvironmentFrame sbGlob sbFrame (sourceObservedFunds sbGlob sboAfter)) [.op .BALANCE]
      ⟨environmentWord (addressInputWord sboAddress)::tail,memory⟩=
        some (⟨environmentWord 9::tail,memory⟩ : Backend.Environment.Slice) :=
  balance_operand sbGlob sbFrame (n+2) sboAssign sbSystem sboAfter sboAddress (sbo_actual_operand n) tail memory

/-- Operand failure keeps its actual successful prefix; the balance execution
contract needs a successful operand and does not classify this as a read. -/
theorem operand_late_timeout :
    (Source.evalE sbGlob sbFrame 5 (.balance sboLate)).run sboLateBefore=(.error .timeout,sboLateAfter) ∧
      sboLateAfter≠sboLateBefore := ⟨sbo_late_balance,sbo_wrong_late_prefix⟩

/-- Constructing the Source snapshot does not prove an independent target
ledger correct. This wrong ledger really executes BALANCE to a different word. -/
theorem wrong_ledger (memory : Backend.Environment.Memory) :
    (Backend.Environment.runSlice (sourceEnvironmentFrame sbGlob sbFrame (fun _=>environmentWord 1)) [.op .BALANCE]
      ⟨[environmentWord (addressInputWord sbAddress)],memory⟩).map (fun result=>result.stack)≠
        some [environmentWord (sourceObservedBalance sbGlob sbHistory sbAddress)] := by
  change some [environmentWord 1]≠some [environmentWord 9]
  decide +kernel

/-- Source timeout is retained. The independent target slice has no Source
horizon, so it must not be falsely classified as the same timeout. -/
theorem zero_horizon (tail : List Backend.Environment.Word) (memory : Backend.Environment.Memory) :
    (sourceMagicReads tiGlob tiSource 0).run tiState=(.error .timeout,tiState) ∧
    Backend.Environment.runSlice tiFrame magicCode ⟨tail,memory⟩=
      some (⟨environmentWord highestUint::environmentWord 88::environmentWord 17::tail,memory⟩ : Backend.Environment.Slice) :=
  ⟨sourceMagic_timeout tiGlob tiSource tiState,ordered_target tail memory⟩
end Solidity.Yul.Adapters.SourceEnvironmentSlice.Controls

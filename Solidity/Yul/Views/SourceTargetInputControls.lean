import Solidity.Yul.Views.SourceTargetInputs
import Solidity.Yul.Views.SourceEnvironmentControls
import Solidity.Source.SemanticsExamples

namespace Solidity.Yul.Views.Controls

/-- Concrete owner parameters; API input witnesses, not call reachability. -/
def tiGlob := { Source.SemanticsExamples.G0 .legacy with timestamp := 17 }
def tiSource := { emSourceFrame with static := false, checked := true }
def tiFunds (_ : ContractWorld.Address) := environmentWord 1
def tiFrame := sourceEnvironmentFrame tiGlob tiSource tiFunds
def tiState : Source.EMState Source.SemanticsExamples.E0 [] := ⟨.nil,Source.SemanticsExamples.s0⟩

theorem ti_observations :
    (Backend.Environment.observe tiFrame .timestamp).1.toNat=17 ∧
    (Backend.Environment.observe tiFrame .msgSender).1.toNat=88 ∧
    (Backend.Environment.observe tiFrame .msgValue).1.toNat=highestUint.val ∧
    (Backend.Environment.observe tiFrame .selfAddress).1.toNat=99 := by decide

theorem ti_actual_source_and_target :
    (sourceMagicReads tiGlob tiSource 1).run tiState=
      (.ok (.val (uintValueOfWord Source.SemanticsExamples.E0.layout 17),.val (Source.Val.address tiSource.sender),
        .val (uintValueOfWord Source.SemanticsExamples.E0.layout highestUint)),tiState) ∧
    (uintValueOfWord Source.SemanticsExamples.E0.layout 17).word.map environmentWord=
      some (Backend.Environment.observe tiFrame .timestamp) ∧
    (Source.Val.address (D := Source.SemanticsExamples.E0.layout) (p := false) tiSource.sender).word.map environmentWord=
      some (Backend.Environment.observe tiFrame .msgSender) ∧
    (uintValueOfWord Source.SemanticsExamples.E0.layout highestUint).word.map environmentWord=
      some (Backend.Environment.observe tiFrame .msgValue) :=
  sourceTarget_reads tiGlob tiSource 0 tiState tiFunds

/-- Bounded converter is injective; the underlying unrestricted Nat wrap is
not. No wider total injectivity premise is introduced. -/
theorem ti_unbounded_wrap_collision : Backend.Environment.wrap 0=Backend.Environment.wrap (2^256) := by
  apply Subtype.ext
  change ((0 % 2^256 : Nat) : Int)=((2^256 % 2^256 : Nat) : Int)
  rfl

theorem ti_full_word_distinct : environmentWord 0≠environmentWord highestUint := by
  intro same
  exact (by decide : (0 : Roadmap.Word)≠highestUint) (environmentWord_injective same)

def tiMaximumAddress : Roadmap.Address := ⟨2^160-1,by decide⟩
theorem ti_high_address : ((environmentAddress tiMaximumAddress).1).1.toNat=2^160-1 := by
  rw [environmentAddress_word,environmentWord_nat]
  rfl

/-- Input agreement does not establish ledger equality or whole-frame stability. -/
theorem ti_ledger_boundary :
    Backend.Environment.observe {tiFrame with funds := fun _ => environmentWord 2} .timestamp=
      Backend.Environment.observe tiFrame .timestamp ∧
    Backend.Environment.observe {tiFrame with funds := fun _ => environmentWord 2} .selfBalance≠
      Backend.Environment.observe tiFrame .selfBalance := by decide

end Solidity.Yul.Views.Controls

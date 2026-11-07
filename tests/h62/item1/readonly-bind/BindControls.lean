import Solidity.Source.Hoare
import Solidity.Lowering.Readonly.CaptureFailureControls

/-! Concrete stateful bind controls. These isolate the monad equation; they do
not assert that the synthetic computations are actual external-call phases. -/
namespace Solidity.H62.ReadonlyBind
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly.ReceiverControls

def succeeds : EM EB [.address false] Unit :=
  ExceptT.mk fun _ => (.ok (), after)

def fails : EM EB [.address false] Unit :=
  ExceptT.mk fun _ => (.error .timeout, after)

def continuation (_ : Unit) : EM EB [.address false] Nat := pure 42

theorem changed_state : before ≠ after := by
  intro same
  have localsSame : after.1 = before.1 := (congrArg Prod.fst same).symm
  exact Solidity.Lowering.Readonly.CaptureFailureControls.effect_not_rolled_back.2 localsSame

theorem success_uses_returned_state :
    (succeeds >>= continuation).run before = (.ok 42, after) := by
  rw [Solidity.Source.Hoare.run_bind]
  rfl

theorem error_keeps_returned_state :
    (fails >>= continuation).run before = (.error .timeout, after) := by
  rw [Solidity.Source.Hoare.run_bind]
  rfl

end Solidity.H62.ReadonlyBind

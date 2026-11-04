import Solidity.Yul.World.Lifecycle
import Solidity.Source.StateExamples

/-! H19 exact-money consumer controls. No transaction/world adequacy claim. -/
namespace Solidity.Yul.Composition.MonetaryLifecycleControls
open Solidity.Source Solidity.Source.StateExamples Solidity.Yul.World

def callerPrefix : ExecState D₀ LW LW :=
  s₀.apply (.account (addr 3) fun account => { account with nonce := 7 })

def paid := (destructTransfer callerPrefix false (addr 1) (addr 2)).get (by decide)

theorem full_amount_and_prefix :
    (paid.world.accounts (addr 1)).balance = 0 ∧
    (paid.world.accounts (addr 2)).balance = 100 ∧
    (paid.world.accounts (addr 3)).nonce = 7 ∧ paid.journal.length = 3 := by decide

theorem full_rollback :
    (callerPrefix.enter (addr 1) (addr 3) ⟨0,by decide⟩ [] false).rollback paid = callerPrefix :=
  rollback_destructTransfer callerPrefix paid false (addr 1) (addr 2) (by rfl)
    (addr 1) (addr 3) ⟨0,by decide⟩ [] false

def wideState : ExecState D₀ LW LW :=
  { callerPrefix with world := (callerPrefix.world.set (addr 1)
      ((callerPrefix.world.accounts (addr 1)).withBalance Monetary.wide)) }

/-- Casting the whole balance to Word would turn this refusal into a zero payment. -/
theorem wide_distinct_refused :
    destructTransfer wideState false (addr 1) (addr 2) = none := by rfl

theorem old_self_keeps_exact_wide :
    (destructTransfer wideState false (addr 1) (addr 1)).map
      (fun state => ((state.world.accounts (addr 1)).balance,state.journal.length)) =
      some (2^256,1) := by decide

theorem fresh_self_burns_exact_wide :
    (destructTransfer wideState true (addr 1) (addr 1)).map
      (fun state => ((state.world.accounts (addr 1)).balance,state.journal.length)) =
      some (0,2) := by decide

end Solidity.Yul.Composition.MonetaryLifecycleControls

/-- info: 'Solidity.Yul.Composition.MonetaryLifecycleControls.full_amount_and_prefix' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.MonetaryLifecycleControls.full_amount_and_prefix

/-- info: 'Solidity.Yul.Composition.MonetaryLifecycleControls.full_rollback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.MonetaryLifecycleControls.full_rollback

/-- info: 'Solidity.Yul.Composition.MonetaryLifecycleControls.wide_distinct_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.MonetaryLifecycleControls.wide_distinct_refused

/-- info: 'Solidity.Yul.Composition.MonetaryLifecycleControls.old_self_keeps_exact_wide' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.MonetaryLifecycleControls.old_self_keeps_exact_wide

/-- info: 'Solidity.Yul.Composition.MonetaryLifecycleControls.fresh_self_burns_exact_wide' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.Composition.MonetaryLifecycleControls.fresh_self_burns_exact_wide

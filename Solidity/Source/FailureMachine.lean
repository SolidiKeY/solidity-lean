import Solidity.Source.Eval
import Solidity.Source.FailurePrimitives

/-!
# Explicit-plan Source frame operations (H16 execution leaf)

These operations run in the actual Source EM and use its existing event
emitter. The immutable plan is a parameter, never a mutable St field. None
is the legacy identity even if arbitrary stale cursor metadata is present.
The frame operation owns only cursor entry/pop: it does not perform logical
rollback, select a catch, dispatch a call or finalize a transaction. Those
remain existing Source operations and still require integration at their
real boundaries. Root indexing/funding decisions are not made here.
-/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx}

/-- Execute the existing Source emitter, then account for its actual event.
A zero cut emits nothing. Receipts must be emitted outside active budgets
by the eventual root driver; this helper does not classify receipt events. -/
def emit (plan : RuntimePlan) (event : Roadmap.Event) : EM E Γ Unit :=
  Source.emitEvent event plan

/- BEGIN GENERATED H16 AXIOM PINS -/
/-- info: 'Solidity.Source.FailureExecution.check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.check
/-- info: 'Solidity.Source.FailureExecution.pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.pending
/-- info: 'Solidity.Source.FailureExecution.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.frame
/-- info: 'Solidity.Source.FailureExecution.emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.emit
/- END GENERATED H16 AXIOM PINS -/

end Solidity.Source.FailureExecution

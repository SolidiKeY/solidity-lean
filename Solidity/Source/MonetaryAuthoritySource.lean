import Solidity.Source.MonetaryAuthority
import Solidity.Source.FailureRequest

/-! Actual Source adapters for the H25 authority. This owner-held extension
requires H16 request cursors and H19 natural Source accounts; not standalone
master evidence. Fee settlement and session wiring remain pending G01 review. -/
namespace Solidity.Source.Monetary
open Solidity.Roadmap (Address Word Request)

/-- Exact account bookkeeping via the existing real Source journal operation. -/
def Authority.writeSource {D L T} (authority : Authority) (state : ExecState D L T)
    (address : Address) : ExecState D L T :=
  state.apply (.account address (fun account => account.withBalance (authority.balance address)))

theorem Authority.source_amount {D L T} (authority : Authority) (state : ExecState D L T)
    (address : Address) :
    ((authority.writeSource state address).world.accounts address).balance = authority.balance address := by
  simp only [Authority.writeSource, ExecState.apply, World.set_get, Account.withBalance]

theorem Authority.source_undo {D L T} (authority : Authority) (state : ExecState D L T)
    (address : Address) : (authority.writeSource state address).undo = state :=
  state.undo_apply _

/-- Actual Source request scope transports the entire post-fee Nat into the
authority while preserving every other Source field and the real cursor exit.
This does not claim that session funding/fee settlement already uses it. -/
theorem Authority.request_postFee {E : Env} {Γ : RCtx} (authority : Authority) (sender : Address)
    (amount : Balance) (locals : Locals E.layout Γ) (state : St E) :
    (FailureExecution.requestScope
      (FailureExecution.constantRequestPlan (.runs amount none))
      (fun balance => pure (authority.set sender balance) : Nat → EM E Γ Authority)).run
        (locals,{state with resource := FailureExecution.Cursor.empty}) =
      ((Except.ok (some (authority.set sender amount)) : Except Halt (Option Authority)),
        (locals,{state with resource := FailureExecution.requestFinished})) := rfl

/-- info: 'Solidity.Source.Monetary.Authority.source_amount' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.source_amount

/-- info: 'Solidity.Source.Monetary.Authority.source_undo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.source_undo

/-- info: 'Solidity.Source.Monetary.Authority.request_postFee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.request_postFee

end Solidity.Source.Monetary

import Solidity.Frontend.SolcJson.YulLocalParse
import Solidity.Yul.RawBoundary
/-! H11 actual guarded parser to raw frame beside unchanged Source locals.
Scope/type-context provenance is the same explicit boundary as LocalParse.
No existing typed layer or Source.RStmt constructor is modified. -/
namespace Solidity.Frontend.YulJson.RawParse
open Solidity.Yul

def run {ctx scope outside localNames documentation src}
    (checked : LocalParse.Checked ctx scope outside localNames documentation src)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Option (RawFrame.Outcome ctx ClosedSyntax.rootControl) :=
  RawFrame.run checked.original.prepared.typing.code checked.original.prepared.policy fuel state

theorem projection {ctx scope outside localNames documentation src}
    (checked : LocalParse.Checked ctx scope outside localNames documentation src)
    (fuel : Nat) (state : RawFrame.State ctx) :
    (run checked fuel state).map RawFrame.Outcome.project =
      (LocalParse.run checked fuel (RawFrame.materialize state)).map LocalBlockOutcome.project :=
  RawFrame.local_projection checked.original.prepared.typing.code checked.original.prepared.policy fuel state

theorem preserves {ctx scope outside localNames documentation src}
    (checked : LocalParse.Checked ctx scope outside localNames documentation src)
    (fuel : Nat) (state : RawFrame.State ctx) {result}
    (done : run checked fuel state = some result) :
    result.state.clean = state.clean ∧ result.state.world = state.world :=
  RawFrame.preserves checked.original.prepared.typing.code checked.original.prepared.policy fuel state done

theorem zero {ctx scope outside localNames documentation src}
    (checked : LocalParse.Checked ctx scope outside localNames documentation src)
    (state : RawFrame.State ctx) : run checked 0 state = none := rfl

end Solidity.Frontend.YulJson.RawParse

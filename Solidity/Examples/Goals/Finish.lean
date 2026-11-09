import Solidity.Goals.Finish

/-! The finish line's pinned check. Its `blocked by` list shrinks as each component lane
lands, so it is not pinned here (that would make this a shared pin again); instead the
check fixes what does not move: the six registered dependencies, the statement as their
conjunction, and the status `open` until `Solidity.Finish.project_finished` exists. -/

namespace Solidity.Goals

open Lean Elab Command Meta in
#guard_msgs in
run_cmd liftTermElabM do
  let components := #[``headlineIsNoPaymentRevert, ``compilerEndpointCorrect,
    ``lowerLoopsCorrect, ``compilerCorrectCollisionFree, ``runCarriesPanicCodes,
    ``tacletsPartitioned]
  let es := Solidity.Goal.goalExt.getState (← getEnv)
  let some e := es.find? (·.decl == ``projectFinished) | throwError "projectFinished carries no @[goal]"
  unless e.deps == components do throwError "finish-line dependencies changed: {e.deps}"
  unless e.proof == `Solidity.Finish.project_finished do throwError "finish-line theorem renamed"
  for c in components do
    unless es.any (·.decl == c) do throwError "component {c} carries no @[goal]"
  let conj := components.pop.foldr (fun c acc => mkAnd (mkConst c) acc) (mkConst components.back!)
  unless (← getConstInfo ``projectFinished).value! == conj do
    throwError "projectFinished is not the conjunction of its six components"
  let st ← Solidity.Goal.status e
  unless (← getEnv).contains `Solidity.Finish.project_finished || st == .open do
    throwError "finish line reported {st.label} without its theorem"

end Solidity.Goals

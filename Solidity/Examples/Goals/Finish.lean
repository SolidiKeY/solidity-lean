import Solidity.Goals.Finish

/-! The finish line's pinned check. Its `blocked by` list shrinks as each component lane
lands, so it is not pinned here (that would make this a shared pin again); instead the
check fixes what does not move: the seven registered dependencies, the statement as their
conjunction, and the status `open` until `Solidity.Finish.project_finished` exists. -/

namespace Solidity.Goals

open Lean Elab Command Meta in
#guard_msgs in
run_cmd liftTermElabM do
  let components := #[``headlineIsNoPaymentRevert, ``compilerEndpointCorrect,
    ``lowerLoopsCorrect, ``compilerCorrectCollisionFree, ``runCarriesPanicCodes,
    ``tacletsPartitioned, ``compilerTotal]
  let es := Solidity.Goal.goalExt.getState (← getEnv)
  let some e := es.find? (·.decl == ``projectFinished) | throwError "projectFinished carries no @[goal]"
  unless e.deps == components do throwError "finish-line dependencies changed: {e.deps}"
  unless e.proof == `Solidity.Finish.project_finished do throwError "finish-line theorem renamed"
  for c in components do
    unless es.any (·.decl == c) do throwError "component {c} carries no @[goal]"
  let conj := components.pop.foldr (fun c acc => mkAnd (mkConst c) acc) (mkConst components.back!)
  unless (← getConstInfo ``projectFinished).value! == conj do
    throwError "projectFinished is not the conjunction of its seven components"
  let st ← Solidity.Goal.status e
  if (← getEnv).contains `Solidity.Finish.project_finished then
    -- Once the theorem exists, the finish line counts only when it and every component
    -- are proved (no `sorry`, no axiom).
    unless st == .proved do throwError "finish line theorem is {st.label}"
    for c in components do
      let some ce := es.find? (·.decl == c) | throwError "component {c} lost"
      let cs ← Solidity.Goal.status ce
      unless cs == .proved do throwError "finish line claimed with component {c} {cs.label}"
  else unless st == .open do throwError "finish line reported {st.label} without its theorem"

end Solidity.Goals

import Solidity.Examples.Tactics.CallFunctionShare
import Solidity.Tools.Counterexample
namespace Solidity.Examples.Tactics.CallFunctionShareControls
open Lean Elab Command Meta Tactic
open scoped Solidity.Scoped
local instance : InContract := ⟨Solidity.Examples.Tactics.CallFunctionShare.Affine⟩
/-- Returning input zero falsifies the same source equality in both modes. -/
theorem wrongDiamond : ¬ (⊨ᶠ dl!{ a < 1000 → ⟨ uint y = f6(a); ⟩ y == a }) := by
  sol_refute
theorem wrongBox : ¬ (⊨ᶠ dl!{ a < 1000 → [ uint y = f6(a); ] y == a }) := by
  sol_refute
end Solidity.Examples.Tactics.CallFunctionShareControls

namespace Solidity.Examples.Tactics.CallFunctionShareControls.ConstantFallback
open Lean Elab Command Meta Tactic
open scoped Solidity.Scoped
private def Constant : Contract := contract!{
  function f0(uint x) returns (uint r) { r = x * 0 + 1; }
  function f1(uint x) returns (uint r) { r = f0(f0(x)); }
  function f2(uint x) returns (uint r) { r = f1(f1(x)); }
  function f3(uint x) returns (uint r) { r = f2(f2(x)); }
  function f4(uint x) returns (uint r) { r = f3(f3(x)); }
  function f5(uint x) returns (uint r) { r = f4(f4(x)); }
  function f6(uint x) returns (uint r) { r = f5(f5(x)); }
}
local instance : InContract := ⟨Constant⟩
elab "#call_family_fallback " mode:ident " : " formula:term : command => liftTermElabM do
  let modeId := mode.getId.eraseMacroScopes
  let entered := modeId == Name.mkSimple "unsupported"
  let ty ← Term.withoutErrToSorry <| Term.elabTerm formula none
  let root ← mkFreshExprSyntheticOpaqueMVar ty
  discard <| Tactic.run root.mvarId! (Term.withoutErrToSorry <| withoutRecover do
    setGoals [root.mvarId!]
    evalTactic (← `(tactic| (
      apply Proves.fmlValid
      apply allIntro
      apply update .valueDeclSkip
      apply update .internalCallSummary
      sol_leaf)))
    let g ← getMainGoal
    let before ← instantiateMVars (← g.getType)
    let saved ← saveState
    if entered then
      evalTactic (← `(tactic| sol_share_calls))
      let after ← instantiateMVars (← getMainTarget)
      if after == before then throwError "control did not enter sharing"
      let some leaf := after.find? (fun e => e.isAppOfArity ``CallFunctionLeaf.leaf 11)
        | throwError "no named leaf in entered control"
      let baseText := m!"FALLBACK_ACTUAL_BASE={leaf.getArg! 6}; LEVEL={leaf.getArg! 7}"
      saved.restore
      logInfo baseText
    let failure ← tryCatchRuntimeEx (do
      evalTactic (← `(tactic| sol_close_call_shared))
      pure (none : Option MessageData)) fun ex => pure (some ex.toMessageData)
    let some reason := failure | throwError "unsupported/no-shrink control unexpectedly succeeded"
    let reasonText ← reason.toString
    if entered then
      unless (reasonText.splitOn "application type mismatch").length > 1 do
        throwError "wrong unsupported-profile refusal: {reason}"
    else
      unless (reasonText.splitOn "no smaller checked call leaf").length > 1 do
        throwError "wrong no-shrink refusal: {reason}"
    if ← g.isAssigned then throwError "failure assigned original goal"
    unless (← getMainGoal) == g do throwError "failure changed active goal"
    unless (← instantiateMVars (← g.getType)) == before do throwError "failure changed original type"
    if entered then
      logInfo "CALL_FAMILY_PROFILE_REFUSED: entered=true; exact_goal_restored=true; ordinary_closure_not_claimed=true"
      return
    evalTactic (← `(tactic| sol_close))
    unless (← getGoals).isEmpty do throwError "ordinary fallback did not close"
    let proof ← instantiateMVars root
    if proof.hasSorry || proof.hasMVar then throwError "incomplete ordinary proof"
    let name := (← getCurrNamespace) ++ modeId.appendAfter "Fallback"
    addDecl <| .thmDecl {name := name, levelParams := [], type := (← instantiateMVars ty), value := proof}
    logInfo m!"CALL_FAMILY_FALLBACK {mode.getId}: entered={entered}; restored=true; ordinary_kernel_checked=true")
/-- info: CALL_FAMILY_FALLBACK small: entered=false; restored=true; ordinary_kernel_checked=true -/
#guard_msgs in
#call_family_fallback small : Fml.Valid dl!{ ⟨ uint y = f1(a); ⟩ y == 1 }
#call_family_fallback unsupported : Fml.Valid dl!{ ⟨ uint y = f6(a); ⟩ y == 1 }
end Solidity.Examples.Tactics.CallFunctionShareControls.ConstantFallback

import Solidity.Calculus.AnonLocalCapture
import Solidity.Calculus.Closers
import Solidity.Tools.ProofTree
import Solidity.Tools.Counterexample

namespace Solidity.Examples.Tactics.AnonLocalCapture
open Solidity.AnonLocalCapture
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .bool, .val .uint, .val .int, .val .uint]
private def start : State C Γ :=
  (((({ State.init C with selfBalance := uintOfNat 5 }).push (t := .val .uint) (uintOfNat 7)).push
    (t := .val .int) (CloseS.intOf 2)).push (t := .val .uint) (uintOfNat 13)).push (t := .val .bool) true
private def positions : Positions Γ :=
  [⟨.bool, .here⟩, ⟨.int, .there (.there .here)⟩, ⟨.bool, .here⟩]
private def names (_ : Nat) : Var := .fresh "same" 0
private def post : Fml C Γ :=
  .and (.eq (.pvV (.there .here)) (.app0 (.lit (uintOfNat 13))))
    (.eq (.app0 (.env .selfBalance)) (.app0 (.lit (uintOfNat 5))))

/-- Mixed primitive types, repeated position and colliding display names
preserve an untouched local and a nontrivial global observation. -/
theorem mixedBox : holds start (plan .box names 0 positions post) := by
  dsimp only [plan, positions, CallResultCapture.restore]
  dsimp only [post, start]
  sol_close

/-- The same actual returning copies preserve the diamond observation. -/
theorem mixedDiamond : holds start (plan .diamond names 0 positions post) := by
  dsimp only [plan, positions, CallResultCapture.restore]
  dsimp only [post, start]
  sol_close

/-- The actual original anonymous leaf follows from the proved fresh-local plan. -/
theorem originalMixed : holds start (.anon (keys positions) post) :=
  sound .box names 0 positions post start mixedBox

private def wrong : Fml C Γ :=
  .eq (.pvV (.there .here)) (.app0 (.lit (uintOfNat 14)))
/-- A wrong untouched-local observation has an inhabited countermodel. -/
theorem wrongPost : ¬ holds start (plan .diamond names 0 positions wrong) := by
  intro h
  have ha : holds start (.anon (keys positions) wrong) :=
    sound .diamond names 0 positions wrong start h
  have bad : some (uintOfNat 13) = some (uintOfNat 14) :=
    ha (fun x => TEnv.get x.2 start.env)
  have values : (13 : Int) = 14 := congrArg Subtype.val (Option.some.inj bad)
  omega

/-- Empty positions still check the original postcondition. -/
theorem empty : holds start (plan .box names 0 [] post) := by
  change holds start post
  constructor <;> rfl

/-- All three positions remain in the payload; the postcondition occurs once. -/
theorem actualSize : (plan .box names 0 positions post).tmSize = post.tmSize + 12 := rfl

/-! ## Actual default-route loop and fallback controls -/
local instance : InContract := ⟨StandardExample⟩
open scoped Solidity.Scoped

/-- The measured loop is proved by the scoped walk and ordinary leaf closer. -/
theorem loopBox : ⊢ dl!{ [ uint s = 0;
  /// @custom:key invariant i <= 10 && s <= 1 * i
  for (uint i = 0; i < 10; i++) { if (a == 1) { s = s + 1; } else { s = 0; } }; ] s <= 10 } := by
  sol_prove
  all_goals (sol_leaf; sol_close)

/-- Input a=1 returns s=10, rejecting the false tighter postcondition. -/
theorem loopWrong : ¬ (⊢ dl!{ [ uint s = 0;
  /// @custom:key invariant i <= 10 && s <= 1 * i
  for (uint i = 0; i < 10; i++) { if (a == 1) { s = s + 1; } else { s = 0; } }; ] s <= 9 }) := by
  sol_refute

/-- A non-anon arithmetic leaf retains its original closure path. -/
theorem ordinaryFallback : ⊨ᶠ dl!{ ∀ uint x; x + 0 = x } := by
  fail_if_success sol_close_anon_steps
  sol_close

/-- An empty frame is left to the ordinary closer. -/
theorem emptyFallback : Fml.Valid (.anon [] (.tt : Fml C [])) := by
  fail_if_success sol_close_anon_steps
  sol_close

private def nonprimitive : Fml C [] :=
  .bind .box (.fresh "net" 0) .oldNet
    (.anon [⟨.oldNet, .here⟩]
      (.bind .box (.fresh "x" 0) (.val .uint)
        (.anon [⟨.val .uint, .here⟩] .tt)))
/-- A nonprimitive outer frame keeps its fallback even with a primitive frame inside. -/
theorem nonprimitiveFallback : Fml.Valid nonprimitive := by
  unfold nonprimitive
  fail_if_success sol_close_anon_steps
  sol_close

private def zeroJoin : Fml C [] :=
  .all (.fresh "x" 0) .uint
    (.upd .box (.decl .nil (.fresh "y" 0) (.val (.app0 (.lit (uintOfNat 13)))))
      (.anon [⟨.val .uint, .there .here⟩]
        (.eq (.pvV .here) (.app0 (.lit (uintOfNat 13))))))

/-- Zero-join eligibility refuses the optional route; explicit fresh-local
sharing still proves the nontrivial preserved declaration. -/
theorem zeroJoinExplicit : Fml.Valid zeroJoin := by
  unfold zeroJoin
  fail_if_success sol_close_joined_anon_steps
  sol_close_anon_steps

/-- The identical leaf retains the ordinary default proof. -/
theorem zeroJoinDefault : Fml.Valid zeroJoin := by
  unfold zeroJoin
  sol_close

private def impossibleAnon : Fml C [] :=
  .all (.fresh "x" 0) .uint (.anon [⟨.val .uint, .here⟩] (.not .tt))

open Lean Elab Command Meta Tactic in
elab "#anon_refusal" : command => liftTermElabM do
  let ty ← Term.elabTerm (← `(term| Fml.Valid impossibleAnon)) none
  let root ← mkFreshExprSyntheticOpaqueMVar ty
  discard <| Tactic.run root.mvarId! (Tactic.withoutRecover do
    setGoals [root.mvarId!]
    evalTactic (← `(tactic| unfold impossibleAnon))
    let g ← getMainGoal
    let target ← getMainTarget
    unless ← CloseJ.hasPrimitiveAnon target.appArg! do throwError "negative control did not enter the profile"
    let start ← IO.monoNanosNow
    let hb ← IO.getNumHeartbeats
    let failure ← tryCatchRuntimeEx (do
      evalTactic (← `(tactic| sol_close_anon_steps))
      pure (none : Option MessageData)) fun ex => pure (some ex.toMessageData)
    let some reason := failure | throwError "false anonymous leaf was proved"
    if ← g.isAssigned then throwError "failed proof did not restore the goal"
    unless (← getMainGoal) == g do throwError "failed proof changed the active goal"
    logInfo m!"ANON_REFUSED profile_entered=true; restored=true; ns={(← IO.monoNanosNow)-start}; raw_heartbeats={(← IO.getNumHeartbeats)-hb}; reason={reason}")

#anon_refusal

/-- The refusal is paired with a kernel-checked inhabited countermodel. -/
theorem impossibleCountermodel : ¬ impossibleAnon.Valid := by
  intro h
  have hf : False := h (State.init C) (uintOfNat 0)
    (fun x => TEnv.get x.2 (((State.init C).push (t := .val .uint) (uintOfNat 0)).env)) trivial
  exact hf

end Solidity.Examples.Tactics.AnonLocalCapture

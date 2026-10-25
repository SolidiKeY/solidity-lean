import SolidityBridge.LoomVCGen
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# Loom VCs with the existing dynamic-logic language

The Solidity steps use a fixed deep post, and the Lean bind/if steps use
Loom's own generators. Every Solidity VC comes from the core strategy.
The invariant example uses the core loop taclet, never Loom's loop rule.
-/

namespace Solidity.Bridge.LoomExamples

open Loom

private def Demo : Contract := contract!{
  function seven() returns (uint r) { r = 7; }
}

private def valuePost (n : PrimTy.uint.Denote) : Fml Demo [.val .uint] :=
  .eq (.pvV .here) (.app0 (.lit n))

private def sevenValue : PrimTy.uint.Denote := ⟨7, by decide⟩
private def threeValue : PrimTy.uint.Denote := ⟨3, by decide⟩

private def straight : Prog Demo [] [.val .uint] :=
  sol[Demo]{ uint x = 3; x = x + 4; }

private def callSeven : Prog Demo [] [.val .uint] :=
  sol[Demo]{ uint x = seven(); }

private def countingLoop : Prog Demo [] [.val .uint] := sol[Demo]{
  uint i = 0;
  /// @custom:key invariant i <= 3
  while (i < 3) { i = i + 1; };
}

/-- A real Solidity function call between ordinary Lean binds and a conditional. -/
def mixed (σ : State Demo []) : ExceptT THalt Id Int := do
  let n ← pure 1
  let τ ← runWithPost 200 .box callSeven .nil (valuePost sevenValue) σ
  if τ.env.1.val = 7 then pure (n + τ.env.1.val) else pure 0

/-- The mixed example actually returns: its box specification is not vacuous. -/
theorem mixed_returns : mixed (State.init Demo) = .ok 8 := rfl

noncomputable section

local instance : MAlgOrdered (ExceptT THalt Id) Prop := algebra .box

/--
info: symbolic execution leaves:
    dl{ { x := 3 } { x := x + 4 } x = 7 }
update-free:
    ∀ uint x; true = true → true = true → 7 = 7
-/
#guard_msgs in #wp Fml.modal .box straight .nil (valuePost sevenValue)

/-- Loom's VC generator leaves the ordinary core formula for the closer. -/
theorem straight_via_loom (σ : State Demo []) :
    _root_.triple (m := ExceptT THalt Id) True
      (runWithPost 200 .box straight .nil (valuePost sevenValue) σ) (holds · (valuePost sevenValue)) := by
  mwp
  refine ⟨?_, fun _ h => h⟩
  have leaf : Fml.Valid (symex 200 (.modal .box straight .nil (valuePost sevenValue))) := by
    sol_decide
  exact leaf σ

/-- The VC at the chosen post is exactly the formula computed by `#wp`. -/
theorem straight_vc_is_wp_leaf (σ : State Demo []) :
    (runWithPostGenerator 200 .box straight .nil (valuePost sevenValue) σ).get
      (holds · (valuePost sevenValue)) ↔
      holds σ (symex 200 (.modal .box straight .nil (valuePost sevenValue))) :=
  generator_get .box straight .nil (valuePost sevenValue)
    (symex 200 (.modal .box straight .nil (valuePost sevenValue)))
    (Fml.Steps.ofSymex 200 (.modal .box straight .nil (valuePost sevenValue))).sound σ

/-- The deep post supplies the fact needed by the arbitrary Lean continuation. -/
theorem mixed_via_loom (σ : State Demo []) :
    _root_.triple (m := ExceptT THalt Id) True (mixed σ) (fun n => n = 8) := by
  unfold mixed
  mwp
  refine ⟨?_, ?_⟩
  · have leaf : Fml.Valid (symex 200 (.modal .box callSeven .nil (valuePost sevenValue))) := by
      sol_decide
    exact leaf σ
  · intro τ hτ
    have hx : τ.env.1.val = 7 := congrArg Subtype.val (Option.some.inj hτ)
    constructor <;> intro hc <;> simp only [WithName] at hc <;> omega

/-- Box rejects the actual panic, even with the true deep post. -/
theorem panic_rejected (σ : State Demo []) :
    ¬ loomWp .box (runWithPost 200 .box (sol[Demo]{ assert(false); }) .nil .tt σ)
      (holds · Fml.tt) := by
  intro h
  exact ((loomWp_iff_afterRunTR .box _ _).mp h).2 rfl

/-- Box accepts the actual revert, even with the false deep post. -/
theorem revert_accepted (σ : State Demo []) :
    loomWp .box (runWithPost 200 .box (sol[Demo]{ revert(); }) .nil Fml.ff σ)
      (holds · Fml.ff) := by
  exact (loomWp_iff_afterRunTR .box _ _).mpr ⟨True.intro, nofun⟩

/--
info:   ~[whileInvariantBox]~>
    dl{
  { i := 0 }
    (i <= 3 ∧
        { anon(i) } (i <= 3 → { se1 := i < 3 } ((se1 = true → [ i = i + 1; } ] i <= 3) ∧ (se1 = false → i = 3)))) }
-/
#guard_msgs in #step symex 2 (.modal .box countingLoop .nil (valuePost threeValue))

/-- The loop's annotated invariant is processed by the same translated taclets. -/
theorem invariant_via_loom (σ : State Demo []) :
    _root_.triple (m := ExceptT THalt Id) True
      (runWithPost 200 .box countingLoop .nil (valuePost threeValue) σ) (holds · (valuePost threeValue)) := by
  mwp
  refine ⟨?_, fun _ h => h⟩
  have leaf : Fml.Valid (symex 200 (.modal .box countingLoop .nil (valuePost threeValue))) := by
    conv => arg 1; reduce
    sol_close
  exact leaf σ

end
end Solidity.Bridge.LoomExamples

/-- info: 'Solidity.Bridge.LoomExamples.straight_via_loom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.LoomExamples.straight_via_loom
/-- info: 'Solidity.Bridge.LoomExamples.straight_vc_is_wp_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.LoomExamples.straight_vc_is_wp_leaf
/-- info: 'Solidity.Bridge.LoomExamples.mixed_via_loom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.LoomExamples.mixed_via_loom
/-- info: 'Solidity.Bridge.LoomExamples.panic_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.LoomExamples.panic_rejected
/-- info: 'Solidity.Bridge.LoomExamples.revert_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.LoomExamples.revert_accepted
/-- info: 'Solidity.Bridge.LoomExamples.invariant_via_loom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.LoomExamples.invariant_via_loom

/-- info: 'Solidity.Bridge.LoomExamples.mixed_returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.LoomExamples.mixed_returns

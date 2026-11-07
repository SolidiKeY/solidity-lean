import Solidity.Yul.RawDeclarationFrame
import Solidity.Yul.LocalBoolInitialization

/-! A concrete growing Boolean declaration over the existing certified Boolean
expression evaluator. Both success and error capture its real partial locals;
raw constructors stay raw. Clean Source agreement requires exact input coherence.
This does not supply general declarations or frontend admission. -/
namespace Solidity.Yul.RawControlDeclaration

def run {ctx expr} (name : String)
    (proof : LocalBoolControl.Supported ctx.env ctx.tys expr)
    (fuel : Nat) (state : RawFrame.State ctx) :
    Sum (Solidity.Source.Halt × RawFrame.State ctx)
      (RawFrame.State (ctx.push name .bool)) :=
  match fuel with
  | 0 => .inl (.timeout,state)
  | fuel+1 =>
    let actual := LocalBoolControl.eval proof fuel (RawCoherent.prepare state)
    match actual.1 with
    | .error halt => .inl (halt,RawCoherent.capture state actual.2)
    | .ok value =>
      .inr (RawCoherent.capture
        (RawFrame.ofClean (.cons (.bool false) state.clean) state.world)
        ((value,actual.2.1),actual.2.2))

end Solidity.Yul.RawControlDeclaration

namespace Solidity.Yul.RawControlDeclaration
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys expr)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (match Solidity.Yul.RawControlDeclaration.run name proof fuel state with
 | .inl failure => Solidity.Yul.RawCoherent.coherent failure.2 = true
 | .inr next => Solidity.Yul.RawCoherent.coherent next = true) ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.declInit (E := ctx.env) (R := returns) (M := modifier)
     (k := control) (Γ := ctx.tys) (τ := .bool) expr (by rfl)) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawDeclarationFrame.project
   (Solidity.Yul.RawControlDeclaration.run name proof fuel state) := by
  intro ctx name expr proof returns modifier control glob frame fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have declaration := LocalBoolInitialization.source_agrees ctx.env ctx.tys expr proof
      glob frame (fuel+1) nps ph returns modifier control state.clean state.world
    have agrees := LocalBoolControl.source_agrees proof glob frame fuel (state.clean,state.world)
    cases actual : (Solidity.Source.evalE glob frame fuel expr).run (state.clean,state.world) with
    | mk tag next =>
      rcases next with ⟨locals,world⟩
      rw [actual] at agrees
      cases tag with
      | error halt =>
        change LocalBoolControl.eval proof fuel (LocalState.ofClean (state.clean,state.world)) =
          (.error halt,LocalState.ofClean (locals,world)) at agrees
        simp only [run,RawCoherent.prepare_coherent state same,agrees]
        constructor
        · exact RawCoherent.capture_coherent state locals world
        · simp only [LocalBoolInitialization.run,agrees,LocalBoolInitialization.finish,
            LocalBoolInitialization.project] at declaration
          exact (Option.some.inj declaration).symm
      | ok value =>
        cases value with
        | val value =>
          cases value with
          | bool value =>
            change LocalBoolControl.eval proof fuel (LocalState.ofClean (state.clean,state.world)) =
              (.ok (.clean (.bool value)),LocalState.ofClean (locals,world)) at agrees
            simp only [run,RawCoherent.prepare_coherent state same,agrees]
            constructor
            · exact RawCoherent.capture_coherent (ctx := ctx.push name .bool) _ (.cons (.bool value) locals) world
            · have localRun : LocalBoolInitialization.run proof (fuel+1)
                  (LocalState.ofClean (state.clean,state.world)) =
                  .normal (LocalState.ofClean (.cons (.bool value) locals,world)) := by
                rw [LocalBoolInitialization.run,agrees]
                rfl
              rw [localRun] at declaration
              simp only [LocalBoolInitialization.project,LocalState.ofClean,
                LocalValues.clean_ofClean,Option.map_some] at declaration
              rw [← Option.some.inj declaration]
              have captured := RawCoherent.capture_ofClean (ctx := ctx.push name .bool)
                (RawFrame.ofClean (.cons (.bool false) state.clean) state.world)
                (.cons (.bool value) locals) world
              change RawCoherent.capture (ctx := ctx.push name .bool)
                (RawFrame.ofClean (.cons (.bool false) state.clean) state.world)
                ((.clean (.bool value),(LocalState.ofClean (locals,world)).1),
                  (LocalState.ofClean (locals,world)).2) = _ at captured
              rw [captured]
              rfl
          | memRef impossible _ => cases impossible
          | storRef impossible _ => cases impossible
          | cdRef impossible _ _ => cases impossible
end Solidity.Yul.RawControlDeclaration

import Solidity.Backend.WorldCalls.SourceExpressionIssuer

/-! Exact failing-expression phase classification in the existing Source evaluator.
Capture failure is NOT an issued call and may keep earlier argument writes.
No source-to-Core, whole-body or target/native correspondence is asserted. -/
namespace Solidity.Backend.WorldCalls.SourceExpressionFailure
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceTypedCall
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

theorem classify (G : Glob E) (F : Fr) (n : Nat) (d : Decl)
    (signature : d.fnSig E = some (ps,rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (args : RConvArgs E Γ ps) (before final : Locals E.layout Γ × St E) (halt : Halt)
    (actual : (evalE G F (n+1) (.extCall target d signature value args)).run before =
      (.error halt,final)) :
    (capture G F n target d value args).run before = (.error halt,final) ∨
      ∃ after captured, CapturedAt G F n target d signature value args before after captured ∧
        (resume G F n d rs captured).run after = (.error halt,final) := by
  rw [eval_external, Hoare.run_bind] at actual
  cases captureRun : (capture G F n target d value args).run before with
  | mk outcome after =>
    rw [captureRun] at actual
    cases outcome with
    | error error =>
      cases actual
      exact Or.inl rfl
    | ok captured => exact Or.inr ⟨after,captured,captureRun,actual⟩

/-- Exact capture failure propagates unchanged; it is not a callee revert or
a successful raw return with a failing caller decoder. -/
theorem capture_failure (G : Glob E) (F : Fr) (n : Nat) (d : Decl)
    (signature : d.fnSig E = some (ps,rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (args : RConvArgs E Γ ps) (before final : Locals E.layout Γ × St E) (halt : Halt)
    (actual : (capture G F n target d value args).run before = (.error halt,final)) :
    (evalE G F (n+1) (.extCall target d signature value args)).run before =
      (.error halt,final) := by
  simp only [eval_external, Hoare.run_bind, actual]

/-- Failing caller expressions protect storage only AFTER a successful capture.
The alternative preserves the exact capture error and reached state instead. -/
theorem storage (G : Glob E) (F : Fr) (n : Nat) (d : Decl)
    (declared : E.declOf .function ⟨d.scope,d.name⟩ = some d)
    (signature : d.fnSig E = some (ps,rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (args : RConvArgs E Γ ps) (before final : Locals E.layout Γ × St E) (halt : Halt)
    (actual : (evalE G F (n+1) (.extCall target d signature value args)).run before =
      (.error halt,final))
    (mode : ((d.fnMut == some .view || d.fnMut == some .pure) || F.static) = true) :
    (capture G F n target d value args).run before = (.error halt,final) ∨
      ∃ after captured, CapturedAt G F n target d signature value args before after captured ∧
        (final.2.ex.world.accounts F.this).storage =
          (after.2.ex.world.accounts F.this).storage := by
  rcases classify G F n d signature target value args before final halt actual with failed | resumed
  · exact Or.inl failed
  · obtain ⟨after,captured,captureRun,resumeRun⟩ := resumed
    let i := SourceExpressionIssuer.bind G F n d declared signature target value args
      before after captured captureRun
    have stored := SourceExpressionConsumer.storage i mode
    change (((evalE G F (n+1) (.extCall target d signature value args)).run before).2.2.ex.world.accounts F.this).storage =
      (after.2.ex.world.accounts F.this).storage at stored
    rw [actual] at stored
    exact Or.inr ⟨after,captured,captureRun,stored⟩
end Solidity.Backend.WorldCalls.SourceExpressionFailure

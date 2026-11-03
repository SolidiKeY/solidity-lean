import Solidity.Backend.WorldCalls.SourceExpressionConsumer

/-! Source-local issuance from an actual successful resolved external expression.
Not a whole-body/source-text/target-world or Core adequacy theorem. -/
namespace Solidity.Backend.WorldCalls.SourceExpressionIssuer
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceTypedCall
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}

/-- No metadata-only issuance: this constructor requires the same declaration,
typed signature and actual captured evaluation at the specified source point. -/
def bind (G : Glob E) (F : Fr) (n : Nat) (d : Decl)
    (declared : E.declOf .function ⟨d.scope,d.name⟩ = some d)
    (signature : d.fnSig E = some (ps,rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (args : RConvArgs E Γ ps) (before after : Locals E.layout Γ × St E)
    (captured : Captured E ps)
    (actual : CapturedAt G F n target d signature value args before after captured) :
    InvocationFrame.Invocation E Γ dn ps rs :=
  { global := G, frame := F, horizon := n, declaration := d,
    declared := declared, signature := signature, target := target,
    value := value, arguments := args, before := before, after := after,
    captured := captured, execution := actual }

/-- A successful full expression necessarily crossed an actual successful
capture. Capture failure is not turned into a call or an issued invocation. -/
theorem capture_of_success (G : Glob E) (F : Fr) (n : Nat) (d : Decl)
    (signature : d.fnSig E = some (ps,rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (args : RConvArgs E Γ ps) (before final : Locals E.layout Γ × St E)
    (result : RVal E.layout (STy.ret rs))
    (actual : (evalE G F (n+1) (.extCall target d signature value args)).run before =
      (.ok result, final)) :
    ∃ after captured,
      CapturedAt G F n target d signature value args before after captured ∧
      (resume G F n d rs captured).run after = (.ok result,final) := by
  rw [eval_external, Hoare.run_bind] at actual
  cases captureRun : (capture G F n target d value args).run before with
  | mk outcome after =>
    rw [captureRun] at actual
    cases outcome with
    | error halt => cases actual
    | ok captured => exact ⟨after,captured,captureRun,actual⟩

/-- Requested or inherited static mode protects the successful expression's
caller storage from the actual post-argument checkpoint, not its input state.
Declaration identity is checked; there is no assumed storage frame. -/
theorem storage_of_success (G : Glob E) (F : Fr) (n : Nat) (d : Decl)
    (declared : E.declOf .function ⟨d.scope,d.name⟩ = some d)
    (signature : d.fnSig E = some (ps,rs))
    (target : RExpr E Γ (.contract dn)) (value : RExpr E Γ (.int IntTy.u256))
    (args : RConvArgs E Γ ps) (before final : Locals E.layout Γ × St E)
    (result : RVal E.layout (STy.ret rs))
    (actual : (evalE G F (n+1) (.extCall target d signature value args)).run before =
      (.ok result,final))
    (mode : ((d.fnMut == some .view || d.fnMut == some .pure) || F.static) = true) :
    ∃ after captured, CapturedAt G F n target d signature value args before after captured ∧
      (final.2.ex.world.accounts F.this).storage =
        (after.2.ex.world.accounts F.this).storage := by
  obtain ⟨after,captured,captureRun,resumed⟩ :=
    capture_of_success G F n d signature target value args before final result actual
  let i := bind G F n d declared signature target value args before after captured captureRun
  have stored := SourceExpressionConsumer.storage i mode
  change (((evalE G F (n+1) (.extCall target d signature value args)).run before).2.2.ex.world.accounts F.this).storage =
    (after.2.ex.world.accounts F.this).storage at stored
  rw [actual] at stored
  exact ⟨after,captured,captureRun,stored⟩
end Solidity.Backend.WorldCalls.SourceExpressionIssuer

import Solidity.Yul.Views.RetainedTupleProducers

/-! Capture through actual unary conversion and operator execution. The operand
runs once at the original horizon, with its original state effects. This
boundary collector does not instrument recursive intermediates in the operand. -/
namespace Solidity.Yul.Views

def captureUnaryRun {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.PrefixOp) (operand : Source.RExpr E Γ σ)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.unary op operand)) s
  | n+1 =>
    let first := captureRuntimeRun F prior (Source.evalE G F n operand) s
    match first.1.1 with
    | .error error => ((Except.error error,first.1.2),first.2)
    | .ok value => captureRuntimeRun F first.2 (do
        let x ← Source.getV value
        return .val (← Source.EM.lift (Source.unaryVal F.checked op x))) first.1.2

theorem captureUnaryRun_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.PrefixOp) (operand : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureUnaryRun G F n op operand prior s).1=
      (Source.evalE G F n (.unary op operand)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    change (captureUnaryRun G F (n+1) op operand prior s).1=
      ((Source.evalE G F n operand) >>= fun value => do
        let x ← Source.getV value
        return .val (← Source.EM.lift (Source.unaryVal F.checked op x))).run s
    rw [Source.Hoare.run_bind]
    unfold captureUnaryRun captureRuntimeRun
    cases actual : (Source.evalE G F n operand).run s with
    | mk result after => cases result <;> simp only [actual]

/-- Earlier scopes survive operand failure and subsequent getV/unaryVal failure. -/
theorem captureUnaryRun_keeps_operand {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.PrefixOp) (operand : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ)
    (scope) (member : scope∈(captureRuntimeRun F prior (Source.evalE G F n operand) s).2) :
    scope∈(captureUnaryRun G F (n+1) op operand prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureUnaryRun
  dsimp only
  split
  · exact member
  · exact captureRuntimeRun_prefix F _ _ _ scope member

/-- Constructive capture of any actual successful operand, even if the operator
later halts. This requires an actual run, not RefOK or invented formation. -/
theorem captureUnaryRun_return {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.PrefixOp) (operand : Source.RExpr E Γ σ) (prior) (s after : Source.EMState E Γ)
    (value : Source.RVal E.layout σ)
    (run : (Source.evalE G F n operand).run s=(.ok value,after)) :
    runtimeScope F value∈(captureUnaryRun G F (n+1) op operand prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureUnaryRun_keeps_operand
  exact captureRuntimeRun_return F prior _ s after value run
end Solidity.Yul.Views

import Solidity.Yul.Views.RetainedPairProducers

/-! Operand capture through the actual comparison conversion/operator boundary.
Pairs execute in the owner's pipeline order, then actual getV/cmpVal execute
unchanged. Produced operands remain observed when conversion or ordering fails;
this is not Solidity frontend admission or compiler/operator correspondence. -/
namespace Solidity.Yul.Views

def captureComparisonRun {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.compare op left right)) s
  | n+1 =>
    let operands := capturePairRun G F n left right prior s
    match operands.1.1 with
    | .error error => ((Except.error error,operands.1.2),operands.2)
    | .ok (x,y) => captureRuntimeRun F operands.2 (do
        return .val (.bool (← Source.EM.lift (Source.cmpVal op (← Source.getV x) (← Source.getV y))))) operands.1.2

theorem captureComparisonRun_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureComparisonRun G F n op left right prior s).1=(Source.evalE G F n (.compare op left right)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    change (captureComparisonRun G F (n+1) op left right prior s).1=
      ((Source.evalPair G F n left right) >>= fun (x,y) => do
        return .val (.bool (← Source.EM.lift (Source.cmpVal op (← Source.getV x) (← Source.getV y))))).run s
    rw [Source.Hoare.run_bind]
    unfold captureComparisonRun
    dsimp only
    have actual := capturePairRun_source G F n left right prior s
    cases run : (Source.evalPair G F n left right).run s with
    | mk result after =>
      rw [run] at actual
      rw [actual]
      cases result with
      | error error => rfl
      | ok pair => cases pair;rfl

/-- Conversion/operator failure cannot erase scopes already produced by the
actual operand pair. The comparison's own result/error/store are unchanged. -/
theorem captureComparisonRun_keeps_operands {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) (scope)
    (member : scope∈(capturePairRun G F n left right prior s).2) :
    scope∈(captureComparisonRun G F (n+1) op left right prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureComparisonRun
  dsimp only
  split
  · exact member
  · exact captureRuntimeRun_prefix F _ _ _ scope member

/-- In particular the successful earlier operand survives a later operand or
comparison failure, preserving the actual legacy/viaIR distinction. -/
theorem captureComparisonRun_first {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) (scope)
    (member : scope∈(match G.pipeline with
      | .legacy => (captureRuntimeRun F prior (Source.evalE G F n right) s).2
      | .viaIR => (captureRuntimeRun F prior (Source.evalE G F n left) s).2)) :
    scope∈(captureComparisonRun G F (n+2) op left right prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureComparisonRun_keeps_operands
  exact capturePairRun_first G F n left right prior s scope member
end Solidity.Yul.Views

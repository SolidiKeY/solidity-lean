import Solidity.Yul.Views.RetainedPairProducers

/-! Heterogeneous shift/power capture uses actual evalPair, amount conversion,
getV and checked shiftVal. The intrinsic amount-type certificate is unchanged.
Recursive operand intermediates and physical/compiler adequacy remain open. -/
namespace Solidity.Yul.Views

def captureShiftRun {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left : Source.RExpr E Γ σ) (right : Source.RExpr E Γ τ) (amount : τ.isAmount = true) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.shiftLike op left right amount)) s
  | n+1 =>
    let operands := capturePairRun G F n left right prior s
    match operands.1.1 with
    | .error error => ((Except.error error,operands.1.2),operands.2)
    | .ok (x,y) => captureRuntimeRun F operands.2 (do
        return .val (← Source.EM.lift (Source.shiftVal F.checked op (← Source.EM.lift y.amount) (← Source.getV x)))) operands.1.2

theorem captureShiftRun_source {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left : Source.RExpr E Γ σ) (right : Source.RExpr E Γ τ) (amount : τ.isAmount = true) (prior) (s : Source.EMState E Γ) :
    (captureShiftRun G F n op left right amount prior s).1=(Source.evalE G F n (.shiftLike op left right amount)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    change (captureShiftRun G F (n+1) op left right amount prior s).1=
      ((Source.evalPair G F n left right) >>= fun (x,y) => do
        return .val (← Source.EM.lift (Source.shiftVal F.checked op (← Source.EM.lift y.amount) (← Source.getV x)))).run s
    rw [Source.Hoare.run_bind]
    unfold captureShiftRun
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
actual operand pair. The shift/power operation's own result/error/store are unchanged. -/
theorem captureShiftRun_keeps_operands {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left : Source.RExpr E Γ σ) (right : Source.RExpr E Γ τ) (amount : τ.isAmount = true) (prior) (s : Source.EMState E Γ) (scope)
    (member : scope∈(capturePairRun G F n left right prior s).2) :
    scope∈(captureShiftRun G F (n+1) op left right amount prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureShiftRun
  dsimp only
  split
  · exact member
  · exact captureRuntimeRun_prefix F _ _ _ scope member

/-- In particular the successful earlier operand survives a later operand or
shift/power failure, preserving the actual legacy/viaIR distinction. -/
theorem captureShiftRun_first {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left : Source.RExpr E Γ σ) (right : Source.RExpr E Γ τ) (amount : τ.isAmount = true) (prior) (s : Source.EMState E Γ) (scope)
    (member : scope∈(match G.pipeline with
      | .legacy => (captureRuntimeRun F prior (Source.evalE G F n right) s).2
      | .viaIR => (captureRuntimeRun F prior (Source.evalE G F n left) s).2)) :
    scope∈(captureShiftRun G F (n+2) op left right amount prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureShiftRun_keeps_operands
  exact capturePairRun_first G F n left right prior s scope member
end Solidity.Yul.Views

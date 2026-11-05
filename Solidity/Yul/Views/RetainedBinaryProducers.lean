import Solidity.Yul.Views.RetainedPairProducers

/-! Capture through non-short-circuit binary evaluation. Source evalPair order,
getV and checked binVal are unchanged. The source projection explicitly requires
a nonlogical operator; this does not impose a new Source-language exclusion or
claim coverage of short-circuit evaluation or recursive operand intermediates. -/
namespace Solidity.Yul.Views

def captureBinaryPairRun {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.binary op left right)) s
  | n+1 =>
    let operands := capturePairRun G F n left right prior s
    match operands.1.1 with
    | .error error => ((Except.error error,operands.1.2),operands.2)
    | .ok (x,y) => captureRuntimeRun F operands.2 (do
        return .val (← Source.EM.lift (Source.binVal F.checked op (← Source.getV x) (← Source.getV y)))) operands.1.2

theorem captureBinaryPairRun_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ)
    (nonlogical : (decide (op = .and) || decide (op = .or)) = false) :
    (captureBinaryPairRun G F n op left right prior s).1=(Source.evalE G F n (.binary op left right)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Source.evalE, nonlogical, Bool.false_eq_true, ↓reduceIte]
    change (captureBinaryPairRun G F (n+1) op left right prior s).1=
      ((Source.evalPair G F n left right) >>= fun (x,y) => do
        return .val (← Source.EM.lift (Source.binVal F.checked op (← Source.getV x) (← Source.getV y)))).run s
    rw [Source.Hoare.run_bind]
    unfold captureBinaryPairRun
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
actual operand pair. Source result/error/store agreement additionally requires
the nonlogical premise of captureBinaryPairRun_source; this retention law alone
is about the pair helper, including when given a logical operator. -/
theorem captureBinaryPairRun_keeps_operands {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) (scope)
    (member : scope∈(capturePairRun G F n left right prior s).2) :
    scope∈(captureBinaryPairRun G F (n+1) op left right prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureBinaryPairRun
  dsimp only
  split
  · exact member
  · exact captureRuntimeRun_prefix F _ _ _ scope member

/-- In particular the successful earlier operand survives a later operand or
binary operation failure, preserving the actual legacy/viaIR distinction. -/
theorem captureBinaryPairRun_first {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (op : Source.BinOp)
    (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) (scope)
    (member : scope∈(match G.pipeline with
      | .legacy => (captureRuntimeRun F prior (Source.evalE G F n right) s).2
      | .viaIR => (captureRuntimeRun F prior (Source.evalE G F n left) s).2)) :
    scope∈(captureBinaryPairRun G F (n+2) op left right prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureBinaryPairRun_keeps_operands
  exact capturePairRun_first G F n left right prior s scope member
end Solidity.Yul.Views

import Solidity.Yul.Views.RetainedBinaryProducers
import Solidity.Yul.Views.RetainedLogicalProducers

/-! Total binary-expression boundary capture. The actual owner operator test
selects short-circuit or pipeline-ordered pair capture; no caller-supplied branch
certificate is required. Each path preserves its distinct actual horizon.
Recursive operand intermediates are not implicitly instrumented. -/
namespace Solidity.Yul.Views

def captureBinaryRun {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.BinOp) (left right : Source.RExpr E Γ σ)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  if (decide (op = .and) || decide (op = .or)) = true then
    captureLogicalRun G F n op left right prior s
  else captureBinaryPairRun G F n op left right prior s

/-- Complete Source result/error/state projection, for every binary operator. -/
theorem captureBinaryRun_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.BinOp) (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureBinaryRun G F n op left right prior s).1=(Source.evalE G F n (.binary op left right)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureBinaryRun
  split
  · exact captureLogicalRun_source G F n op left right prior s (by assumption)
  · apply captureBinaryPairRun_source
    cases branch : (decide (op = .and) || decide (op = .or)) <;> simp only [branch] at *
    first | rfl | contradiction

/-- Actual first-stage scopes survive the complete operator. Logical evaluation
uses n+1 for the left operand; pair evaluation uses n for its first operand,
matching the owner's extra evalPair horizon exactly. -/
theorem captureBinaryRun_first {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.BinOp) (left right : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ)
    (scope)
    (member : scope∈(if (decide (op = .and) || decide (op = .or)) = true then
      (captureRuntimeRun F prior (Source.evalE G F (n+1) left) s).2
    else match G.pipeline with
      | .legacy => (captureRuntimeRun F prior (Source.evalE G F n right) s).2
      | .viaIR => (captureRuntimeRun F prior (Source.evalE G F n left) s).2)) :
    scope∈(captureBinaryRun G F (n+2) op left right prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureBinaryRun
  split <;> simp only [*, ↓reduceIte] at member
  · exact captureLogicalRun_keeps_left G F (n+1) op left right prior s scope member
  · exact captureBinaryPairRun_first G F n op left right prior s scope member
end Solidity.Yul.Views

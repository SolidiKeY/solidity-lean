import Solidity.Yul.Views.RetainedTupleProducers

/-! Capture actual operand pairs in the owner's pipeline-specific order.
Legacy evaluates right then left; viaIR evaluates left then right, while both
return (left,right). Earlier runtime values survive later halt. This observes
operand endpoints, not arbitrary recursive intermediates or operator adequacy.
No new Source syntax/state or evaluation-order profile is introduced. -/
namespace Solidity.Yul.Views

def captureRuntimePairRun {E Γ σ τ} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (first : Source.EM E Γ (Source.RVal E.layout σ))
    (second : Source.EM E Γ (Source.RVal E.layout τ)) (s : Source.EMState E Γ) :=
  let head := captureRuntimeRun F prior first s
  match head.1.1 with
  | .error error => ((Except.error error,head.1.2),head.2)
  | .ok value =>
    let tail := captureRuntimeRun F head.2 second head.1.2
    ((tail.1.1.map (fun next=>(value,next)),tail.1.2),tail.2)

theorem captureRuntimePairRun_source {E Γ σ τ} (F : Source.Fr) (prior)
    (first : Source.EM E Γ (Source.RVal E.layout σ))
    (second : Source.EM E Γ (Source.RVal E.layout τ)) (s : Source.EMState E Γ) :
    (captureRuntimePairRun F prior first second s).1=
      (do let x←first;let y←second;pure (x,y)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [Source.Hoare.run_bind]
  unfold captureRuntimePairRun captureRuntimeRun
  cases head : first.run s with
  | mk result after =>
    cases result with
    | error error => simp only []
    | ok value =>
      simp only []
      rw [Source.Hoare.run_bind]
      cases second.run after with
      | mk result final => cases result <;> rfl

theorem captureRuntimePairRun_keeps_first {E Γ σ τ} (F : Source.Fr) (prior)
    (first : Source.EM E Γ (Source.RVal E.layout σ))
    (second : Source.EM E Γ (Source.RVal E.layout τ)) (s : Source.EMState E Γ)
    (scope) (inside : scope∈(captureRuntimeRun F prior first s).2) :
    scope∈(captureRuntimePairRun F prior first second s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureRuntimePairRun
  dsimp only
  split
  · exact inside
  · exact captureRuntimeRun_prefix F _ _ _ scope inside

/-- The successful second operand is captured from its actual reached state. -/
theorem captureRuntimePairRun_second {E Γ σ τ} (F : Source.Fr) (prior)
    (first : Source.EM E Γ (Source.RVal E.layout σ))
    (second : Source.EM E Γ (Source.RVal E.layout τ)) (s middle after : Source.EMState E Γ)
    (one : Source.RVal E.layout σ) (two : Source.RVal E.layout τ)
    (head : first.run s=(.ok one,middle)) (tail : second.run middle=(.ok two,after)) :
    runtimeScope F two∈(captureRuntimePairRun F prior first second s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureRuntimePairRun captureRuntimeRun
  simp only [head,tail]
  exact List.mem_append_right _ List.mem_cons_self

def capturePairRun {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (left : Source.RExpr E Γ σ) (right : Source.RExpr E Γ τ)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 =>
    let result := (Source.evalPair G F 0 left right).run s
    (result,prior++[entryLocalScope F s.1,entryLocalScope F result.2.1])
  | n+1 =>
    match G.pipeline with
    | .legacy =>
      let run := captureRuntimePairRun F prior (Source.evalE G F n right) (Source.evalE G F n left) s
      ((run.1.1.map Prod.swap,run.1.2),run.2)
    | .viaIR => captureRuntimePairRun F prior (Source.evalE G F n left) (Source.evalE G F n right) s

theorem capturePairRun_source {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (left : Source.RExpr E Γ σ) (right : Source.RExpr E Γ τ) (prior) (s : Source.EMState E Γ) :
    (capturePairRun G F n left right prior s).1=(Source.evalPair G F n left right).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    cases pipeline : G.pipeline with
    | viaIR =>
      simp only [capturePairRun,pipeline]
      rw [captureRuntimePairRun_source]
      simp only [Source.evalPair,pipeline]
    | legacy =>
      simp only [capturePairRun,pipeline]
      rw [captureRuntimePairRun_source]
      simp only [Source.evalPair,pipeline,Source.Hoare.run_bind]
      cases head : (Source.evalE G F n right).run s with
      | mk result after =>
        cases result with
        | error error => rfl
        | ok value =>
          simp only []
          cases tail : (Source.evalE G F n left).run after with
          | mk result final => cases result <;> rfl

/-- Capture the actual first-evaluated runtime value before any later halt. -/
theorem capturePairRun_first {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (left : Source.RExpr E Γ σ) (right : Source.RExpr E Γ τ) (prior) (s : Source.EMState E Γ)
    (scope) (inside : scope∈(match G.pipeline with
      | .legacy => (captureRuntimeRun F prior (Source.evalE G F n right) s).2
      | .viaIR => (captureRuntimeRun F prior (Source.evalE G F n left) s).2)) :
    scope∈(capturePairRun G F (n+1) left right prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases pipeline : G.pipeline <;>
    simp only [pipeline] at inside <;>
    simp only [capturePairRun,pipeline] <;>
    exact captureRuntimePairRun_keeps_first F prior _ _ s scope inside
end Solidity.Yul.Views

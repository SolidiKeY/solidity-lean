import Solidity.Yul.Views.RetainedTupleProducers

/-! Capture around actual implicit and explicit conversion producers. Source
conversion bodies, allocations, refusals and horizons remain authoritative.
This observes the operand/result boundary, not recursive conversion internals. -/
namespace Solidity.Yul.Views

def captureConversionRun {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (operand : Source.RExpr E Γ σ) (h : Source.Conv E.isBase E.mapFree σ τ)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.conv operand h)) s
  | n+1 =>
    let first := captureRuntimeRun F prior (Source.evalE G F n operand) s
    match first.1.1 with
    | .error error => ((Except.error error,first.1.2),first.2)
    | .ok value => captureRuntimeRun F first.2 (Source.convRV F n τ value) first.1.2

theorem captureConversionRun_source {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (operand : Source.RExpr E Γ σ) (h : Source.Conv E.isBase E.mapFree σ τ) (prior) (s : Source.EMState E Γ) :
    (captureConversionRun G F n operand h prior s).1=(Source.evalE G F n (.conv operand h)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    change (captureConversionRun G F (n+1) operand h prior s).1=
      ((Source.evalE G F n operand) >>= fun value => Source.convRV F n τ value).run s
    rw [Source.Hoare.run_bind]
    unfold captureConversionRun captureRuntimeRun
    cases actual : (Source.evalE G F n operand).run s with
    | mk result after => cases result <;> simp only [actual]

theorem captureConversionRun_keeps_operand {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (operand : Source.RExpr E Γ σ) (h : Source.Conv E.isBase E.mapFree σ τ) (prior) (s : Source.EMState E Γ)
    (scope) (member : scope∈(captureRuntimeRun F prior (Source.evalE G F n operand) s).2) :
    scope∈(captureConversionRun G F (n+1) operand h prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureConversionRun
  dsimp only
  split
  · exact member
  · exact captureRuntimeRun_prefix F _ _ _ scope member

theorem captureConversionRun_return {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (operand : Source.RExpr E Γ σ) (h : Source.Conv E.isBase E.mapFree σ τ) (prior) (s after : Source.EMState E Γ)
    (value : Source.RVal E.layout σ)
    (run : (Source.evalE G F n operand).run s=(.ok value,after)) :
    runtimeScope F value∈(captureConversionRun G F (n+1) operand h prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureConversionRun_keeps_operand
  exact captureRuntimeRun_return F prior _ s after value run

def captureExplicitConversionRun {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (operand : Source.RExpr E Γ σ) (h : σ.explicit E.isBase E.mapFree τ = true)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.convExplicit operand h)) s
  | n+1 =>
    let first := captureRuntimeRun F prior (Source.evalE G F n operand) s
    match first.1.1 with
    | .error error => ((Except.error error,first.1.2),first.2)
    | .ok value => captureRuntimeRun F first.2 (Source.convExplicitRV F n τ value) first.1.2

theorem captureExplicitConversionRun_source {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (operand : Source.RExpr E Γ σ) (h : σ.explicit E.isBase E.mapFree τ = true) (prior) (s : Source.EMState E Γ) :
    (captureExplicitConversionRun G F n operand h prior s).1=(Source.evalE G F n (.convExplicit operand h)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    change (captureExplicitConversionRun G F (n+1) operand h prior s).1=
      ((Source.evalE G F n operand) >>= fun value => Source.convExplicitRV F n τ value).run s
    rw [Source.Hoare.run_bind]
    unfold captureExplicitConversionRun captureRuntimeRun
    cases actual : (Source.evalE G F n operand).run s with
    | mk result after => cases result <;> simp only [actual]

theorem captureExplicitConversionRun_keeps_operand {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (operand : Source.RExpr E Γ σ) (h : σ.explicit E.isBase E.mapFree τ = true) (prior) (s : Source.EMState E Γ)
    (scope) (member : scope∈(captureRuntimeRun F prior (Source.evalE G F n operand) s).2) :
    scope∈(captureExplicitConversionRun G F (n+1) operand h prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureExplicitConversionRun
  dsimp only
  split
  · exact member
  · exact captureRuntimeRun_prefix F _ _ _ scope member

theorem captureExplicitConversionRun_return {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (operand : Source.RExpr E Γ σ) (h : σ.explicit E.isBase E.mapFree τ = true) (prior) (s after : Source.EMState E Γ)
    (value : Source.RVal E.layout σ)
    (run : (Source.evalE G F n operand).run s=(.ok value,after)) :
    runtimeScope F value∈(captureExplicitConversionRun G F (n+1) operand h prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureExplicitConversionRun_keeps_operand
  exact captureRuntimeRun_return F prior _ s after value run
end Solidity.Yul.Views

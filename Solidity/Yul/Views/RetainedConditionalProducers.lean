import Solidity.Yul.Views.RetainedTupleProducers

/-! Capture for the ACTUAL conditional-expression producer. The condition is
observed before getV; only the selected branch executes, at the owner's exact
horizon. Condition-stage scopes survive later failure, and selected runtime
tuples retain all constituents. Arbitrary recursive intermediates inside the
condition or branches are not implicitly instrumented. No Source AST/state is
added or changed. -/
namespace Solidity.Yul.Views

def captureConditionalRun {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (yes no : Source.RExpr E Γ σ)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.cond condition yes no)) s
  | n+1 =>
    let first := captureRuntimeRun F prior (Source.evalE G F n condition) s
    match first.1.1 with
    | .error error => ((Except.error error,first.1.2),first.2)
    | .ok value => captureRuntimeRun F first.2 (do
        match ← Source.getV value with
        | .bool true => Source.evalE G F n yes
        | _ => Source.evalE G F n no) first.1.2

theorem captureConditionalRun_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (yes no : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureConditionalRun G F n condition yes no prior s).1=(Source.evalE G F n (.cond condition yes no)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    change (captureConditionalRun G F (n+1) condition yes no prior s).1=
      ((Source.evalE G F n condition) >>= fun value => do
        match ← Source.getV value with
        | .bool true => Source.evalE G F n yes
        | _ => Source.evalE G F n no).run s
    rw [Source.Hoare.run_bind]
    unfold captureConditionalRun captureRuntimeRun
    cases actual : (Source.evalE G F n condition).run s with
    | mk result after => cases result <;> simp only [actual]

/-- Retain any condition-stage scope, regardless of selected-branch outcome. -/
theorem captureConditionalRun_keeps_condition {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (yes no : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ)
    (scope) (member : scope∈(captureRuntimeRun F prior (Source.evalE G F n condition) s).2) :
    scope∈(captureConditionalRun G F (n+1) condition yes no prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureConditionalRun
  dsimp only
  split
  · exact member
  · exact captureRuntimeRun_prefix F _ _ _ scope member

theorem captureConditionalRun_prefix {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (yes no : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ)
    (scope) (member : scope∈prior) : scope∈(captureConditionalRun G F n condition yes no prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => exact captureRuntimeRun_prefix F prior _ s scope member
  | succ n =>
    exact captureConditionalRun_keeps_condition G F n condition yes no prior s scope
      (captureRuntimeRun_prefix F prior _ s scope member)

/-- Actual selected-branch success constructs the captured runtime return.
No membership/coverage/inverse result is assumed. -/
theorem captureConditionalRun_selected {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (yes no : Source.RExpr E Γ σ) (prior)
    (s middle after : Source.EMState E Γ) (choice : Bool) (value : Source.RVal E.layout σ)
    (tested : (Source.evalE G F n condition).run s=(.ok (.val (.bool choice)),middle))
    (selected : (Source.evalE G F n (if choice then yes else no)).run middle=(.ok value,after)) :
    runtimeScope F value∈(captureConditionalRun G F (n+1) condition yes no prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureConditionalRun captureRuntimeRun
  simp only [tested]
  cases choice
  all_goals
    simp only [Bool.false_eq_true,if_false,if_true] at selected
    change runtimeScope F value∈(captureRuntimeRun F _ _ middle).2
    apply captureRuntimeRun_return F _ _ middle after value
    exact selected

theorem captureConditionalRun_paths {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (condition : Source.RExpr E Γ .bool) (yes no : Source.RExpr E Γ σ) (prior)
    (s middle after : Source.EMState E Γ) (choice : Bool) (value : Source.RVal E.layout σ)
    (tested : (Source.evalE G F n condition).run s=(.ok (.val (.bool choice)),middle))
    (selected : (Source.evalE G F n (if choice then yes else no)).run middle=(.ok value,after))
    (path) (inside : path∈runtimeStoragePaths value) :
    ∃ scope∈(captureConditionalRun G F (n+1) condition yes no prior s).2,
      scope.account=F.this ∧ path∈scope.paths := by
  first | omega | decide | skip
  exact ⟨runtimeScope F value,captureConditionalRun_selected G F n condition yes no prior s middle after
    choice value tested selected,rfl,inside⟩
end Solidity.Yul.Views

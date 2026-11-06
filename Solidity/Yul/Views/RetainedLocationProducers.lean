import Solidity.Yul.Views.RetainedLocationRun

namespace Solidity.Yul.Views

/-- Observe the actual returned location, before readLoc can replace a scalar
storage path by its scalar value or fail. No inner evalLoc traversal is implied. -/
def captureLocationProducer {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  captureLocationRun F prior (Source.evalLoc G F n loc) s

theorem captureLocationProducer_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureLocationProducer G F n loc prior s).1=(Source.evalLoc G F n loc).run s := rfl

theorem captureLocationProducer_covers {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (prior) (s after : Source.EMState E Γ) (p)
    (run : (Source.evalLoc G F n loc).run s=(.ok (.stor p),after)) :
    ∃ scope ∈ (captureLocationProducer G F n loc prior s).2, scope.account=F.this ∧ p ∈ scope.paths :=
  ⟨locationScope F (Source.Loc.stor (τ := σ) p),captureLocationRun_return F _ _ _ _ _ run,rfl,List.mem_cons_self⟩

theorem captureLocationProducer_timeout {E Γ σ} (G : Source.Glob E) (F : Source.Fr)
    (loc : Source.RLVal E Γ σ) (prior) (s : Source.EMState E Γ) :
    captureLocationProducer G F 0 loc prior s=
      ((Except.error .timeout,s),prior++[entryLocalScope F s.1,entryLocalScope F s.1]) := by
  change (_,(_++_)++[])=_
  rw [List.append_nil]
  rfl

/-- Actual assignment chronology is RHS, location, getV, writeLoc. Capture both
successful RHS runtime values and the resolved target even if getV/write halts.
This is the owner assignment, not an LHS-first replacement evaluator. -/
def captureAssignmentRun {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (rhs : Source.RExpr E Γ σ)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.assign loc rhs)) s
  | n+1 =>
    let first := captureRuntimeRun F prior (Source.evalE G F n rhs) s
    match first.1.1 with
    | .error error => ((Except.error error,first.1.2),first.2)
    | .ok value => captureLocationBindRun F first.2 (Source.evalLoc G F n loc)
        (fun target => do
          let x ← Source.getV value
          Source.writeLoc F n target x
          pure (.val x)) first.1.2

theorem captureAssignmentRun_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (rhs : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureAssignmentRun G F n loc rhs prior s).1=(Source.evalE G F n (.assign loc rhs)).run s := by
  cases n with
  | zero => rfl
  | succ n =>
    change (captureAssignmentRun G F (n+1) loc rhs prior s).1=
      ((Source.evalE G F n rhs) >>= fun v => do
        let target ← Source.evalLoc G F n loc
        let x ← Source.getV v
        Source.writeLoc F n target x
        pure (.val x)).run s
    rw [Source.Hoare.run_bind]
    unfold captureAssignmentRun captureRuntimeRun
    cases first : (Source.evalE G F n rhs).run s with
    | mk result after =>
      cases result with
      | error error => simp only [first]
      | ok value =>
        simp only [first]
        exact captureLocationBindRun_source F _ _ _ after

theorem captureAssignmentRun_target {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (rhs : Source.RExpr E Γ σ) (prior)
    (s mid after : Source.EMState E Γ) (value : Source.RVal E.layout σ) (target)
    (rhsRun : (Source.evalE G F n rhs).run s=(.ok value,mid))
    (locRun : (Source.evalLoc G F n loc).run mid=(.ok target,after)) :
    locationScope F target ∈ (captureAssignmentRun G F (n+1) loc rhs prior s).2 := by
  unfold captureAssignmentRun captureRuntimeRun
  simp only [rhsRun]
  apply captureLocationBindRun_keeps
  exact captureLocationRun_return F _ _ mid after target locRun

theorem captureAssignmentRun_rhs {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (rhs : Source.RExpr E Γ σ) (prior)
    (s mid : Source.EMState E Γ) (value : Source.RVal E.layout σ)
    (run : (Source.evalE G F n rhs).run s=(.ok value,mid)) :
    runtimeScope F value ∈ (captureAssignmentRun G F (n+1) loc rhs prior s).2 := by
  unfold captureAssignmentRun captureRuntimeRun
  simp only [run]
  apply captureLocationBindRun_keeps
  apply captureLocationRun_prefix
  exact List.mem_append_right _ List.mem_cons_self

/-- Actual inc/dec resolves the location once before its read/compute/write.
No assignment ordering is borrowed for this distinct owner constructor. -/
def captureIncDecRun {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (inc pre : Bool) (loc : Source.RLVal E Γ σ)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.incDec inc pre loc)) s
  | n+1 => captureLocationBindRun F prior (Source.evalLoc G F n loc)
      (fun target => do
        let old ← Source.readLoc F target
        let value ← Source.EM.lift (Source.incDecVal F.checked inc old)
        Source.writeLoc F n target value
        pure (.val (if pre then value else old))) s

theorem captureIncDecRun_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (inc pre : Bool) (loc : Source.RLVal E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureIncDecRun G F n inc pre loc prior s).1=(Source.evalE G F n (.incDec inc pre loc)).run s := by
  cases n with
  | zero => rfl
  | succ n => exact captureLocationBindRun_source F prior _ _ s

theorem captureIncDecRun_target {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (inc pre : Bool) (loc : Source.RLVal E Γ σ) (prior)
    (s after : Source.EMState E Γ) (target)
    (run : (Source.evalLoc G F n loc).run s=(.ok target,after)) :
    locationScope F target ∈ (captureIncDecRun G F (n+1) inc pre loc prior s).2 := by
  apply captureLocationBindRun_keeps
  exact captureLocationRun_return F prior _ s after target run

/-- Delete captures its target before the ACTUAL recursive deleteLoc executes.
Intermediate locations formed inside deletion are a separate coverage obligation. -/
def captureDeleteRun {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.delete loc)) s
  | n+1 => captureLocationBindRun F prior (Source.evalLoc G F n loc)
      (fun target => do Source.deleteLoc F n target; pure Source.RVal.unit) s

theorem captureDeleteRun_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureDeleteRun G F n loc prior s).1=(Source.evalE G F n (.delete loc)).run s := by
  cases n with
  | zero => rfl
  | succ n => exact captureLocationBindRun_source F prior _ _ s

theorem captureDeleteRun_target {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (prior) (s after : Source.EMState E Γ) (target)
    (run : (Source.evalLoc G F n loc).run s=(.ok target,after)) :
    locationScope F target ∈ (captureDeleteRun G F (n+1) loc prior s).2 := by
  apply captureLocationBindRun_keeps
  exact captureLocationRun_return F prior _ s after target run

end Solidity.Yul.Views

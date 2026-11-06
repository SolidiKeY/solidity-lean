import Solidity.Yul.Views.RetainedLocationProducers

/-! Actual compound-assignment chronology is RHS, target, old read, checked
operation/conversion, then write. The original fits certificate and Source
operations are retained. Captured RHS/target scopes survive later failure;
recursive conversion/location internals are not implicitly instrumented. -/
namespace Solidity.Yul.Views
def captureCompoundRun {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.AssignOp) (loc : Source.RLVal E Γ τ) (rhs : Source.RExpr E Γ σ)
    (fits : op.fits E.isBase E.mapFree σ τ = true)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.compound op loc rhs fits)) s
  | n+1 =>
    let first := captureRuntimeRun F prior (Source.evalE G F n rhs) s
    match first.1.1 with
    | .error error => ((Except.error error,first.1.2),first.2)
    | .ok value => captureLocationBindRun F first.2 (Source.evalLoc G F n loc)
        (fun target => do
          let old ← Source.readLoc F target
          let new ← match op.kind? with
            | some .shift => Source.EM.lift (Source.shiftVal F.checked
                (if op = Source.AssignOp.shl then .shl else if op = Source.AssignOp.sar then .sar else .shr)
                (← Source.EM.lift value.amount) old)
            | _ => do
              let y ← Source.getV (← Source.convRV F n τ value)
              Source.EM.lift (Source.binVal F.checked (Source.AssignOp.binOp op) old y)
          Source.writeLoc F n target new
          pure (.val new)) first.1.2

theorem captureCompoundRun_source {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.AssignOp) (loc : Source.RLVal E Γ τ) (rhs : Source.RExpr E Γ σ)
    (fits : op.fits E.isBase E.mapFree σ τ = true) (prior) (s : Source.EMState E Γ) :
    (captureCompoundRun G F n op loc rhs fits prior s).1=(Source.evalE G F n (.compound op loc rhs fits)).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => rfl
  | succ n =>
    change (captureCompoundRun G F (n+1) op loc rhs fits prior s).1=
      ((Source.evalE G F n rhs) >>= fun v => do
        let target ← Source.evalLoc G F n loc
        let old ← Source.readLoc F target
        let new ← match op.kind? with
          | some .shift => Source.EM.lift (Source.shiftVal F.checked
              (if op = Source.AssignOp.shl then .shl else if op = Source.AssignOp.sar then .sar else .shr)
              (← Source.EM.lift v.amount) old)
          | _ => do
            let y ← Source.getV (← Source.convRV F n τ v)
            Source.EM.lift (Source.binVal F.checked (Source.AssignOp.binOp op) old y)
        Source.writeLoc F n target new
        pure (.val new)).run s
    rw [Source.Hoare.run_bind]
    unfold captureCompoundRun captureRuntimeRun
    cases first : (Source.evalE G F n rhs).run s with
    | mk result after =>
      cases result with
      | error error => simp only [first]
      | ok value =>
        simp only [first]
        exact captureLocationBindRun_source F _ _ _ after

theorem captureCompoundRun_target {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.AssignOp) (loc : Source.RLVal E Γ τ) (rhs : Source.RExpr E Γ σ)
    (fits : op.fits E.isBase E.mapFree σ τ = true) (prior)
    (s mid after : Source.EMState E Γ) (value : Source.RVal E.layout σ) (target)
    (rhsRun : (Source.evalE G F n rhs).run s=(.ok value,mid))
    (locRun : (Source.evalLoc G F n loc).run mid=(.ok target,after)) :
    locationScope F target ∈ (captureCompoundRun G F (n+1) op loc rhs fits prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureCompoundRun captureRuntimeRun
  simp only [rhsRun]
  apply captureLocationBindRun_keeps
  exact captureLocationRun_return F _ _ mid after target locRun

theorem captureCompoundRun_rhs {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.AssignOp) (loc : Source.RLVal E Γ τ) (rhs : Source.RExpr E Γ σ)
    (fits : op.fits E.isBase E.mapFree σ τ = true) (prior)
    (s mid : Source.EMState E Γ) (value : Source.RVal E.layout σ)
    (run : (Source.evalE G F n rhs).run s=(.ok value,mid)) :
    runtimeScope F value ∈ (captureCompoundRun G F (n+1) op loc rhs fits prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold captureCompoundRun captureRuntimeRun
  simp only [run]
  apply captureLocationBindRun_keeps
  apply captureLocationRun_prefix
  exact List.mem_append_right _ List.mem_cons_self

/-- Earlier observations survive every compound-assignment outcome, including
RHS failure, failed target resolution, arithmetic refusal and failed write. -/
theorem captureCompoundRun_prefix {E Γ σ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (op : Source.AssignOp) (loc : Source.RLVal E Γ τ) (rhs : Source.RExpr E Γ σ)
    (fits : op.fits E.isBase E.mapFree σ τ = true) (prior) (s : Source.EMState E Γ) (scope)
    (member : scope∈prior) : scope∈(captureCompoundRun G F n op loc rhs fits prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases n with
  | zero => exact captureRuntimeRun_prefix F prior _ s scope member
  | succ n =>
    have first : scope∈(captureRuntimeRun F prior (Source.evalE G F n rhs) s).2 :=
      captureRuntimeRun_prefix F prior _ s scope member
    unfold captureCompoundRun
    dsimp only
    split
    · exact first
    · apply captureLocationBindRun_keeps
      apply captureLocationRun_prefix
      exact first
end Solidity.Yul.Views

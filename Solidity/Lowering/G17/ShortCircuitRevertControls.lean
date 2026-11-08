import Solidity.Lowering.G17.ShortCircuitControls
import Solidity.Lowering.V07.ShortCircuitControls
import Solidity.Lowering.V07.IntegerConstants
import Solidity.Lowering.V07.UnsignedQuotRem
import Solidity.Lowering.V08.AbiObservations
import Solidity.Backend.Failure.Observe

/-! A concrete Source RHS-revert producer for the generic lazy condition
constructor. Reuse the published division-by-zero expression; no Source
semantics, value/world relation or admission contract is introduced here.
Only the existing Condition success/revert clauses are exercised: the native
panic at smaller Source horizons does not simulate Source timeout and supplies
no adequacy or backward result. -/
namespace Solidity.Lowering.G17.RevertControls
open V07 V07.P12NextInterface Source.SemanticsExamples
open V07.P12Controls (C E SrcCtx TgtCtx source target mapping)
open V07.P12AssignedConditionControls (values worlds initial)
open V07.MixedAssignmentControls (globals)

private theorem pure_run {α : Type} (v : α) (s : Source.EMState E SrcCtx) :
    (pure v : Source.EM E SrcCtx α).run s = (.ok v,s) := rfl

private theorem locals_run (s : Source.EMState E SrcCtx) :
    (Source.EM.locals : Source.EM E SrcCtx (Source.Locals E.layout SrcCtx)).run s = (.ok s.1,s) := rfl

private theorem lift_run {α : Type} (r : Source.R α) (s : Source.EMState E SrcCtx) :
    (Source.EM.lift r).run s = (r,s) := by
  cases r <;> rfl

/-- Exact division-by-zero fixture, including its smaller timeout horizons. -/
theorem division_source_run (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (s : Source.EMState E SrcCtx) :
    (Source.evalE G F fuel V07.ShortCircuitControls.failure).run s =
      if 6 ≤ fuel then (.error (.revert (Source.panicData .divZero)),s)
      else (.error .timeout,s) := by
  have zero : Source.constVal (Source.Q.ofInt 0) (.int .u8) =
      .ok (.int 0 (by decide) : Source.Val E.layout (.int .u8)) :=
    V07.IntegerConstants.source_value .u8 0 (by decide)
  obtain ⟨env,world⟩ := s
  cases env with
  | cons b env =>
    cases env with
    | cons c env =>
      cases env with
      | cons x env =>
        obtain ⟨x,h,rfl⟩ := Source.Val.eq_int x
        have arithmetic : Source.binVal F.checked .div
            (.int x h : Source.Val E.layout (.int .u8)) (.int 0 (by decide)) =
            .error (.revert (Source.panicData .divZero)) :=
          V07.UnsignedQuotRem.source_zero 8 (by decide) (D := E.layout) F.checked false x h
        rcases fuel with _ | (_ | (_ | (_ | (_ | (_ | fuel)))))
        all_goals cases order : G.pipeline
        all_goals simp only [V07.ShortCircuitControls.failure,Source.evalE,Source.evalPair,order]
        all_goals first | rfl | skip
        all_goals simp only [Source.withLibraryCalldata,reduceCtorEq,decide_false,Bool.false_or,
          Bool.false_eq_true,if_false,Source.Hoare.run_bind,Source.convRV,dite_false,zero]
        all_goals simp only [pure_run,locals_run,lift_run,V07.source_getV_run,Source.Locals.get]
        all_goals simp only [arithmetic]
        all_goals rw [if_pos (by omega)]

private def failingOperand : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,.cons (.revertData [.bytes (Semantics.encodePanic 0x12)]) .nil,.val (.simple (.bool false))⟩

private theorem operand_run (t : State C TgtCtx) :
    failingOperand.run t = .error (THalt.ofData (Source.panicData .divZero)) := by
  unfold failingOperand DeferredSource.Operand.run
  have literal := Backend.Failure.revert_bytes_intrinsic t (Semantics.encodePanic 0x12)
  change (Stmt.revertData [.bytes (Semantics.encodePanic 0x12)] : Stmt C TgtCtx TgtCtx).run t = _ at literal
  rw [V07.singleton_run,literal]
  rw [V08.panicData_transport .divZero]
  rfl

/-- Existing concrete P12 fixture; success/revert only, with no timeout adequacy. -/
def divisionCondition (G : Source.Glob E) (F : Source.Fr) :
    Condition G F mapping values worlds V07.ShortCircuitControls.failure := by
  refine ⟨failingOperand,⟨source,target,initial⟩,?_,?_⟩
  · intro fuel s after t choice aligned run
    rw [division_source_run G F fuel s] at run
    split at run <;> cases run
  · intro fuel s after t data aligned run
    rw [division_source_run G F fuel s] at run
    split at run
    · have same : Source.panicData .divZero = data :=
        Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst run))
      rw [operand_run,← same]
    · cases run

private def producer (p : Roadmap.Pipeline) (checked conj left : Bool) :=
  shortCondition (globals p) {F0 with checked := checked} mapping values worlds conj
    (.bool left) V07.ShortCircuitControls.failure
    (P12AtomicConditions.literal (globals p) {F0 with checked := checked} mapping values worlds
      left ⟨source,target,initial⟩)
    (divisionCondition (globals p) {F0 with checked := checked})

/-- A genuine Source RHS panic reaches the generic condition's revert
clause, with exact data, for both operators, pipelines and checking modes. -/
theorem taken_source_revert_witness (p : Roadmap.Pipeline) (checked conj : Bool) (fuel : Nat) :
    (Source.evalE (globals p) {F0 with checked := checked} (fuel+7)
      (.binary (if conj then .and else .or) (.bool conj) V07.ShortCircuitControls.failure)).run source =
      (.error (.revert (Source.panicData .divZero)),source) ∧
    (producer p checked conj conj).operand.run target = .error (THalt.ofData (Source.panicData .divZero)) := by
  have src := source_short_step (globals p) {F0 with checked := checked} (fuel+6)
    source source conj conj (.bool conj) V07.ShortCircuitControls.failure
    (P12AtomicConditions.literal_source_run (globals p) {F0 with checked := checked} (fuel+5) source conj)
  have run : (Source.evalE (globals p) {F0 with checked := checked} (fuel+7)
      (.binary (if conj then .and else .or) (.bool conj) V07.ShortCircuitControls.failure)).run source =
      (.error (.revert (Source.panicData .divZero)),source) := by
    have take : needsRight conj conj = true := by cases conj <;> rfl
    rw [src,if_pos take,division_source_run,if_pos (show 6 ≤ fuel+6 from by omega)]
  exact ⟨run,(producer p checked conj conj).revert (fuel+7) source source target
    (Source.panicData .divZero) initial run⟩

/-- The same panic-producing RHS is skipped, including at horizons too
small to evaluate it, and cannot turn the successful branch into a failure. -/
theorem skipped_source_revert_witness (p : Roadmap.Pipeline) (checked conj : Bool) (fuel : Nat) :
    (Source.evalE (globals p) {F0 with checked := checked} (fuel+2)
      (.binary (if conj then .and else .or) (.bool (!conj)) V07.ShortCircuitControls.failure)).run source =
      (.ok (.val (.bool (!conj))),source) ∧
    ∃ out : Out C target.H TgtCtx,
      (producer p checked conj (!conj)).operand.run target = .ok (out,.prim (!conj)) ∧
      Aligned mapping values worlds source out.st := by
  have src := source_short_step (globals p) {F0 with checked := checked} (fuel+1)
    source source conj (!conj) (.bool (!conj)) V07.ShortCircuitControls.failure
    (P12AtomicConditions.literal_source_run (globals p) {F0 with checked := checked} fuel source (!conj))
  have run : (Source.evalE (globals p) {F0 with checked := checked} (fuel+2)
      (.binary (if conj then .and else .or) (.bool (!conj)) V07.ShortCircuitControls.failure)).run source =
      (.ok (.val (.bool (!conj))),source) := by
    rw [src]
    cases conj <;> rfl
  exact ⟨run,(producer p checked conj (!conj)).success (fuel+2) source source target (!conj) initial run⟩

#print axioms pure_run
#print axioms locals_run
#print axioms lift_run
#print axioms division_source_run
#print axioms operand_run
#print axioms divisionCondition
#print axioms taken_source_revert_witness
#print axioms skipped_source_revert_witness

end Solidity.Lowering.G17.RevertControls

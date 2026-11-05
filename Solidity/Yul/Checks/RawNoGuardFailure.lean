import Solidity.Yul.RawNoGuardFailure
import Solidity.Yul.Checks.RawInitializedForPostHorizon
/-! Finite noncompletion retains the explicit structural no-break premise.
Break is a witnessed counterexample when omitted. Error classification, general
divergence and admission completeness are not claimed. H30 registration external. -/
namespace Solidity.Yul.Checks.RawNoGuardFailure
namespace Old
export Solidity.Yul.Checks.RawInitializedForPostHorizon
 (ctx env dirty initial flag small skipProof breakProof)
export Solidity.Yul.Checks.RawForPostHorizon (writeFalse continuation)
export Solidity.Yul.Checks.RawControlledWhileHorizon (mutatingContinue)
end Old
export Old (ctx env dirty initial flag small skipProof breakProof writeFalse continuation)
def repeatedStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip .none (.some (.assign (.local .here) (.bool false))) .cont
def conditionalStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip .none (.some (.assign (.local .here) (.bool false)))
 (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont)
def breakStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip .none (.some (.assign (.local .here) (.bool false))) .brk
def repeated : RawSourceAdapter.Adapter ctx [] false false repeatedStmt :=
 RawSourceForPost.Absent.adapter
 (RawSourceForPost.Initialized.adapter (RawSourceAdapter.body skipProof)
 (.base (.literal true)) writeFalse (RawSourceAdapter.body continuation))
def conditional : RawSourceAdapter.Adapter ctx [] false false conditionalStmt :=
 RawSourceForPost.Absent.adapter
 (RawSourceForPost.Initialized.adapter (RawSourceAdapter.body skipProof)
 (.base (.literal true)) writeFalse (RawSourceAdapter.body Old.mutatingContinue))
def broken : RawSourceAdapter.Adapter ctx [] false false breakStmt :=
 RawSourceForPost.Absent.adapter
 (RawSourceForPost.Initialized.adapter (RawSourceAdapter.body skipProof)
 (.base (.literal true)) writeFalse (RawSourceAdapter.body breakProof))
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false repeatedStmt) := ⟨repeated⟩
theorem continueSafe : Solidity.Yul.RawNoGuardFailure.noBreak Solidity.Yul.Checks.RawNoGuardFailure.continuation = true := by
  rfl

theorem conditionalSafe : Solidity.Yul.RawNoGuardFailure.noBreak Solidity.Yul.Checks.RawNoGuardFailure.Old.mutatingContinue = true := by
  rfl

theorem breakUnsafe : Solidity.Yul.RawNoGuardFailure.noBreak Solidity.Yul.Checks.RawNoGuardFailure.breakProof = false := by
  rfl

theorem allFuelNoncompletion : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawNoGuardFailure.ctx), (Solidity.Yul.Checks.RawNoGuardFailure.repeated.run fuel state).1 ≠ .ok .normal := by
  intro fuel state
  exact Solidity.Yul.RawNoGuardFailure.adapter_no_normal Solidity.Yul.Checks.RawNoGuardFailure.ctx [] false false _ Solidity.Yul.Checks.RawNoGuardFailure.continuation (by rfl) _ Solidity.Yul.Checks.RawNoGuardFailure.writeFalse _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoGuardFailure.skipProof) fuel state

theorem conditionalNoncompletion : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawNoGuardFailure.ctx), (Solidity.Yul.Checks.RawNoGuardFailure.conditional.run fuel state).1 ≠ .ok .normal := by
  intro fuel state
  exact Solidity.Yul.RawNoGuardFailure.adapter_no_normal Solidity.Yul.Checks.RawNoGuardFailure.ctx [] false false _ Solidity.Yul.Checks.RawNoGuardFailure.Old.mutatingContinue (by rfl) _ Solidity.Yul.Checks.RawNoGuardFailure.writeFalse _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoGuardFailure.skipProof) fuel state

theorem mutatingPrefix : (Solidity.Yul.Checks.RawNoGuardFailure.repeated.run 4 Solidity.Yul.Checks.RawNoGuardFailure.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawNoGuardFailure.repeated.run 4 Solidity.Yul.Checks.RawNoGuardFailure.dirty).2 Solidity.Yul.Checks.RawNoGuardFailure.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawNoGuardFailure.repeated.run 4 Solidity.Yul.Checks.RawNoGuardFailure.dirty).2 Solidity.Yul.Checks.RawNoGuardFailure.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem breakCounterexample : (Solidity.Yul.Checks.RawNoGuardFailure.broken.run 3 Solidity.Yul.Checks.RawNoGuardFailure.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawNoGuardFailure.broken.run 3 Solidity.Yul.Checks.RawNoGuardFailure.dirty).2 Solidity.Yul.Checks.RawNoGuardFailure.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawNoGuardFailure.broken.run 3 Solidity.Yul.Checks.RawNoGuardFailure.dirty).2 Solidity.Yul.Checks.RawNoGuardFailure.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem earlyTimeout : (Solidity.Yul.Checks.RawNoGuardFailure.repeated.run 2 Solidity.Yul.Checks.RawNoGuardFailure.dirty).1 = .error .timeout := by
  rfl

theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoGuardFailure.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoGuardFailure.env)), Solidity.Yul.RawCoherent.coherent (Solidity.Yul.Checks.RawNoGuardFailure.repeated.run fuel Solidity.Yul.Checks.RawNoGuardFailure.initial).2 = true ∧ (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawNoGuardFailure.repeatedStmt Solidity.Yul.Checks.RawNoGuardFailure.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardFailure.env,Solidity.Yul.Checks.RawNoGuardFailure.initial.world) = Solidity.Yul.RawLoopBody.represented (Solidity.Yul.Checks.RawNoGuardFailure.repeated.run fuel Solidity.Yul.Checks.RawNoGuardFailure.initial) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.Checks.RawNoGuardFailure.repeated.correct glob frame fuel nps ph Solidity.Yul.Checks.RawNoGuardFailure.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

theorem conservativeTest : Solidity.Yul.RawNoGuardFailure.noBreak (Solidity.Yul.RawLoopBody.Supported.ifThen (.base (.literal false)) Solidity.Yul.Checks.RawNoGuardFailure.breakProof) = false := by
  rfl

#print axioms Solidity.Yul.RawNoGuardFailure.run_no_break
#print axioms Solidity.Yul.RawNoGuardFailure.literal_no_false
#print axioms Solidity.Yul.RawNoGuardFailure.run_no_ok
#print axioms Solidity.Yul.RawNoGuardFailure.initialized_no_ok
#print axioms Solidity.Yul.RawNoGuardFailure.adapter_no_normal
#print axioms continueSafe
#print axioms conditionalSafe
#print axioms breakUnsafe
#print axioms allFuelNoncompletion
#print axioms conditionalNoncompletion
#print axioms mutatingPrefix
#print axioms breakCounterexample
#print axioms earlyTimeout
#print axioms cleanSource
#print axioms conservativeTest
end Solidity.Yul.Checks.RawNoGuardFailure

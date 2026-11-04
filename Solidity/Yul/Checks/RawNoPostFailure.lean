import Solidity.Yul.RawNoPostFailure
import Solidity.Yul.Checks.RawNoGuardFailure
/-! Actual no-post raw and Source noncompletion controls. Completing break
demonstrates why the no-break premise remains. Dirty refusal is coherence only,
not admission. No error classification or divergence assertion. H30 registration external. -/
namespace Solidity.Yul.Checks.RawNoPostFailure
namespace Old
export Solidity.Yul.Checks.RawNoGuardFailure
 (ctx env dirty initial flag small skipProof breakProof continuation)
export Solidity.Yul.Checks.RawControlledWhileHorizon (mutatingContinue)
export Solidity.Yul.Checks.RawStatementHorizon (dirtyInput)
end Old
export Old (ctx env dirty initial flag small skipProof breakProof continuation)
def repeatedStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip .none .none .cont
def conditionalStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip .none .none
 (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont)
def breakStmt : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .skip .none .none .brk
def repeated : RawSourceAdapter.Adapter ctx [] false false repeatedStmt :=
 RawSourceForPost.Absent.adapter
 (RawSourceAdapterFor.adapter (RawSourceAdapter.body skipProof)
 (.base (.literal true)) (RawSourceAdapter.body continuation))
def conditional : RawSourceAdapter.Adapter ctx [] false false conditionalStmt :=
 RawSourceForPost.Absent.adapter
 (RawSourceAdapterFor.adapter (RawSourceAdapter.body skipProof)
 (.base (.literal true)) (RawSourceAdapter.body Old.mutatingContinue))
def broken : RawSourceAdapter.Adapter ctx [] false false breakStmt :=
 RawSourceForPost.Absent.adapter
 (RawSourceAdapterFor.adapter (RawSourceAdapter.body skipProof)
 (.base (.literal true)) (RawSourceAdapter.body breakProof))
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false repeatedStmt) := ⟨repeated⟩
theorem rawFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawNoPostFailure.ctx), (Solidity.Yul.Checks.RawNoPostFailure.repeated.run fuel state).1 ≠ .ok .normal := by
  intro fuel state
  exact Solidity.Yul.RawNoPostFailure.adapter_no_normal Solidity.Yul.Checks.RawNoPostFailure.ctx [] false false _ Solidity.Yul.Checks.RawNoPostFailure.continuation (by rfl) _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoPostFailure.skipProof) fuel state

theorem conditionalRawFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawNoPostFailure.ctx), (Solidity.Yul.Checks.RawNoPostFailure.conditional.run fuel state).1 ≠ .ok .normal := by
  intro fuel state
  exact Solidity.Yul.RawNoPostFailure.adapter_no_normal Solidity.Yul.Checks.RawNoPostFailure.ctx [] false false _ Solidity.Yul.Checks.RawNoPostFailure.Old.mutatingContinue (by rfl) _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoPostFailure.skipProof) fuel state

theorem cleanSourceFamily : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoPostFailure.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoPostFailure.env)) (l : Bool) (locals next : Solidity.Source.Locals Solidity.Yul.Checks.RawNoPostFailure.env.layout Solidity.Yul.Checks.RawNoPostFailure.ctx.tys) (world finalWorld : Solidity.Source.St Solidity.Yul.Checks.RawNoPostFailure.env), (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.skip : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoPostFailure.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoPostFailure.ctx.tys Solidity.Yul.Checks.RawNoPostFailure.ctx.tys) .none .none (.cont : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoPostFailure.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoPostFailure.ctx.tys Solidity.Yul.Checks.RawNoPostFailure.ctx.tys)) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoPostFailure.env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoPostFailure.env,finalWorld)) := by
  intro glob frame fuel nps ph l locals next world finalWorld
  exact Solidity.Yul.RawNoPostFailure.source_clean_no_normal Solidity.Yul.Checks.RawNoPostFailure.ctx [] false false _ Solidity.Yul.Checks.RawNoPostFailure.continuation (by rfl) l _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoPostFailure.skipProof) glob frame fuel nps ph locals next world finalWorld

theorem conditionalSourceFamily : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoPostFailure.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoPostFailure.env)) (l : Bool) (locals next : Solidity.Source.Locals Solidity.Yul.Checks.RawNoPostFailure.env.layout Solidity.Yul.Checks.RawNoPostFailure.ctx.tys) (world finalWorld : Solidity.Source.St Solidity.Yul.Checks.RawNoPostFailure.env), (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.skip : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoPostFailure.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoPostFailure.ctx.tys Solidity.Yul.Checks.RawNoPostFailure.ctx.tys) .none .none (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont)) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoPostFailure.env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoPostFailure.env,finalWorld)) := by
  intro glob frame fuel nps ph l locals next world finalWorld
  exact Solidity.Yul.RawNoPostFailure.source_clean_no_normal Solidity.Yul.Checks.RawNoPostFailure.ctx [] false false _ Solidity.Yul.Checks.RawNoPostFailure.Old.mutatingContinue (by rfl) l _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoPostFailure.skipProof) glob frame fuel nps ph locals next world finalWorld

theorem iterationSourceFamily : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoPostFailure.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoPostFailure.env)) (next : Solidity.Source.Locals Solidity.Yul.Checks.RawNoPostFailure.env.layout Solidity.Yul.Checks.RawNoPostFailure.ctx.tys) (finalWorld : Solidity.Source.St Solidity.Yul.Checks.RawNoPostFailure.env), (Solidity.Source.forIter glob frame fuel nps ph .none .none (.cont : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoPostFailure.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoPostFailure.ctx.tys Solidity.Yul.Checks.RawNoPostFailure.ctx.tys) Solidity.Yul.Checks.RawNoPostFailure.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoPostFailure.env,Solidity.Yul.Checks.RawNoPostFailure.initial.world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoPostFailure.env,finalWorld)) := by
  intro glob frame fuel nps ph next finalWorld
  exact Solidity.Yul.RawNoPostFailure.source_iter_no_normal Solidity.Yul.Checks.RawNoPostFailure.ctx [] false false _ Solidity.Yul.Checks.RawNoPostFailure.continuation (by rfl) glob frame fuel nps ph Solidity.Yul.Checks.RawNoPostFailure.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _) next finalWorld

theorem mutatingPrefix : (Solidity.Yul.Checks.RawNoPostFailure.conditional.run 6 Solidity.Yul.Checks.RawNoPostFailure.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawNoPostFailure.conditional.run 6 Solidity.Yul.Checks.RawNoPostFailure.dirty).2 Solidity.Yul.Checks.RawNoPostFailure.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawNoPostFailure.conditional.run 6 Solidity.Yul.Checks.RawNoPostFailure.dirty).2 Solidity.Yul.Checks.RawNoPostFailure.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem sourceBreakCounterexample : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoPostFailure.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoPostFailure.env)), (Solidity.Source.execS glob frame 3 nps ph Solidity.Yul.Checks.RawNoPostFailure.breakStmt Solidity.Yul.Checks.RawNoPostFailure.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoPostFailure.env,Solidity.Yul.Checks.RawNoPostFailure.initial.world) = (.ok (.normal Solidity.Yul.Checks.RawNoPostFailure.initial.clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoPostFailure.env,Solidity.Yul.Checks.RawNoPostFailure.initial.world)) := by
  intro glob frame nps ph
  rfl

theorem rawBreakCounterexample : (Solidity.Yul.Checks.RawNoPostFailure.broken.run 3 Solidity.Yul.Checks.RawNoPostFailure.dirty).1 = .ok .normal ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawNoPostFailure.broken.run 3 Solidity.Yul.Checks.RawNoPostFailure.dirty).2 Solidity.Yul.Checks.RawNoPostFailure.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.Checks.RawNoPostFailure.broken.run 3 Solidity.Yul.Checks.RawNoPostFailure.dirty).2 Solidity.Yul.Checks.RawNoPostFailure.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

theorem dirtyRefusal : Solidity.Yul.RawCoherent.coherent Solidity.Yul.Checks.RawNoPostFailure.dirty = false := by
  exact Solidity.Yul.Checks.RawNoPostFailure.Old.dirtyInput.1

theorem sourceEarlyTimeout : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoPostFailure.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoPostFailure.env)), ((Solidity.Source.execS glob frame 2 nps ph Solidity.Yul.Checks.RawNoPostFailure.repeatedStmt Solidity.Yul.Checks.RawNoPostFailure.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoPostFailure.env,Solidity.Yul.Checks.RawNoPostFailure.initial.world)).1 = .error .timeout := by
  intro glob frame nps ph
  rfl

#print axioms Solidity.Yul.RawNoPostFailure.loop_no_ok
#print axioms Solidity.Yul.RawNoPostFailure.initialized_no_ok
#print axioms Solidity.Yul.RawNoPostFailure.adapter_no_normal
#print axioms Solidity.Yul.RawNoPostFailure.source_iter_no_normal
#print axioms Solidity.Yul.RawNoPostFailure.source_initialized_no_normal
#print axioms Solidity.Yul.RawNoPostFailure.source_clean_no_normal
#print axioms rawFamily
#print axioms conditionalRawFamily
#print axioms cleanSourceFamily
#print axioms conditionalSourceFamily
#print axioms iterationSourceFamily
#print axioms mutatingPrefix
#print axioms sourceBreakCounterexample
#print axioms rawBreakCounterexample
#print axioms dirtyRefusal
#print axioms sourceEarlyTimeout
end Solidity.Yul.Checks.RawNoPostFailure

import Solidity.Yul.RawPureInitTimeout
import Solidity.Yul.Checks.RawSourceLoopTimeout
/-! Actual mutating Boolean block initializer, no-break loop, Source worlds and
firstDone controls. Break completion and arbitrary bad initializer remain
outside the theorem domain. Coherence refusal is not admission. H30 registration external. -/
namespace Solidity.Yul.Checks.RawPureInitTimeout
namespace Old
export Solidity.Yul.Checks.RawSourceLoopTimeout
 (ctx env dirty initial writeFalse continuation conditionalBody invalidInitialized)
export Solidity.Yul.Checks.RawControlledWhileHorizon (mutatingContinue)
export Solidity.Yul.Checks.RawNoGuardFailure (breakProof)
export Solidity.Yul.Checks.RawStatementHorizon (dirtyInput)
end Old
export Old (ctx env dirty initial writeFalse continuation)
def initItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .stmt (.expr (.assign (.local .here) (.bool true))) .nil
def initProof : RawSequence.Supported ctx [] false ⟨true,false⟩ initItems :=
 .cons (.expression (.assign .here (.base (.literal true)))) .nil
def witness : Nonempty (RawSequence.Supported ctx [] false ⟨true,false⟩ initItems) := ⟨initProof⟩

/- The additional dirtyMutatingPrefix fuel-6 conjunction remains an unproved
control obligation; no expected result or proof budget was changed. -/
theorem rawPostFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawPureInitTimeout.ctx), (Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) Solidity.Yul.Checks.RawPureInitTimeout.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue) fuel state).1 = .error .timeout := by
  intro fuel state
  exact Solidity.Yul.RawPureInitTimeout.raw_post_timeout Solidity.Yul.Checks.RawPureInitTimeout.ctx [] false false Solidity.Yul.Checks.RawPureInitTimeout.initItems Solidity.Yul.Checks.RawPureInitTimeout.initProof _ Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue (by rfl) _ Solidity.Yul.Checks.RawPureInitTimeout.writeFalse fuel state

theorem rawNoPostFamily : ∀ (fuel : Nat) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawPureInitTimeout.ctx), (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue) fuel state).1 = .error .timeout := by
  intro fuel state
  exact Solidity.Yul.RawPureInitTimeout.raw_no_post_timeout Solidity.Yul.Checks.RawPureInitTimeout.ctx [] false false Solidity.Yul.Checks.RawPureInitTimeout.initItems Solidity.Yul.Checks.RawPureInitTimeout.initProof _ Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue (by rfl) fuel state

theorem sourcePostWorld : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawPureInitTimeout.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawPureInitTimeout.env)) (l : Bool), (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.block Solidity.Yul.Checks.RawPureInitTimeout.initItems) .none (.some (.assign (.local .here) (.bool false))) Solidity.Yul.Checks.RawPureInitTimeout.Old.conditionalBody) Solidity.Yul.Checks.RawPureInitTimeout.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawPureInitTimeout.env,Solidity.Yul.Checks.RawPureInitTimeout.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.RawPureInitTimeout.env,(Solidity.Yul.RawSourceForPost.Initialized.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) Solidity.Yul.Checks.RawPureInitTimeout.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue) fuel Solidity.Yul.Checks.RawPureInitTimeout.initial).2.world)) := by
  intro glob frame fuel nps ph l
  exact Solidity.Yul.RawPureInitTimeout.source_post_timeout Solidity.Yul.Checks.RawPureInitTimeout.ctx [] false false Solidity.Yul.Checks.RawPureInitTimeout.initItems Solidity.Yul.Checks.RawPureInitTimeout.initProof _ Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue (by rfl) _ Solidity.Yul.Checks.RawPureInitTimeout.writeFalse l glob frame fuel nps ph Solidity.Yul.Checks.RawPureInitTimeout.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

theorem sourceNoPostWorld : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawPureInitTimeout.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawPureInitTimeout.env)) (l : Bool), (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.block Solidity.Yul.Checks.RawPureInitTimeout.initItems) .none .none Solidity.Yul.Checks.RawPureInitTimeout.Old.conditionalBody) Solidity.Yul.Checks.RawPureInitTimeout.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawPureInitTimeout.env,Solidity.Yul.Checks.RawPureInitTimeout.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.RawPureInitTimeout.env,(Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue) fuel Solidity.Yul.Checks.RawPureInitTimeout.initial).2.world)) := by
  intro glob frame fuel nps ph l
  exact Solidity.Yul.RawPureInitTimeout.source_no_post_timeout Solidity.Yul.Checks.RawPureInitTimeout.ctx [] false false Solidity.Yul.Checks.RawPureInitTimeout.initItems Solidity.Yul.Checks.RawPureInitTimeout.initProof _ Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue (by rfl) l glob frame fuel nps ph Solidity.Yul.Checks.RawPureInitTimeout.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

theorem postBounds : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawPureInitTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawPureInitTimeout.env)) (l : Bool) (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawPureInitTimeout.env.layout Solidity.Yul.Checks.RawPureInitTimeout.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawPureInitTimeout.env), ∀ bound, Solidity.Source.firstDone (fun fuel => (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.block Solidity.Yul.Checks.RawPureInitTimeout.initItems) .none (.some (.assign (.local .here) (.bool false))) Solidity.Yul.Checks.RawPureInitTimeout.Old.conditionalBody) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawPureInitTimeout.env,world)) bound = none := by
  intro glob frame nps ph l locals world bound
  exact Solidity.Yul.RawPureInitTimeout.post_firstDone Solidity.Yul.Checks.RawPureInitTimeout.ctx [] false false Solidity.Yul.Checks.RawPureInitTimeout.initItems Solidity.Yul.Checks.RawPureInitTimeout.initProof _ Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue (by rfl) _ Solidity.Yul.Checks.RawPureInitTimeout.writeFalse l glob frame nps ph locals world bound

theorem noPostBounds : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawPureInitTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawPureInitTimeout.env)) (l : Bool) (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawPureInitTimeout.env.layout Solidity.Yul.Checks.RawPureInitTimeout.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawPureInitTimeout.env), ∀ bound, Solidity.Source.firstDone (fun fuel => (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.block Solidity.Yul.Checks.RawPureInitTimeout.initItems) .none .none Solidity.Yul.Checks.RawPureInitTimeout.Old.conditionalBody) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawPureInitTimeout.env,world)) bound = none := by
  intro glob frame nps ph l locals world bound
  exact Solidity.Yul.RawPureInitTimeout.no_post_firstDone Solidity.Yul.Checks.RawPureInitTimeout.ctx [] false false Solidity.Yul.Checks.RawPureInitTimeout.initItems Solidity.Yul.Checks.RawPureInitTimeout.initProof _ Solidity.Yul.Checks.RawPureInitTimeout.Old.mutatingContinue (by rfl) l glob frame nps ph locals world bound

theorem breakCounterexample : (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.breakProof) 6 Solidity.Yul.Checks.RawPureInitTimeout.dirty).1 = .ok () ∧ Solidity.Yul.RawNoGuardFailure.noBreak Solidity.Yul.Checks.RawPureInitTimeout.Old.breakProof = false ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.breakProof) 6 Solidity.Yul.Checks.RawPureInitTimeout.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.flag).val = 1 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceAdapterFor.run (Solidity.Yul.RawSourceAdapter.body (Solidity.Yul.RawLoopBody.Supported.plain Solidity.Yul.Checks.RawPureInitTimeout.initProof)) (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawPureInitTimeout.Old.breakProof) 6 Solidity.Yul.Checks.RawPureInitTimeout.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem initializerCounterexample : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawPureInitTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawPureInitTimeout.env)), Solidity.Source.firstDone (fun fuel => (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawPureInitTimeout.Old.invalidInitialized Solidity.Yul.Checks.RawPureInitTimeout.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawPureInitTimeout.env,Solidity.Yul.Checks.RawPureInitTimeout.initial.world)) 2 ≠ none := by
  intro glob frame nps ph bad
  cases bad

theorem dirtyRefusal : Solidity.Yul.RawCoherent.coherent Solidity.Yul.Checks.RawPureInitTimeout.dirty = false := by
  exact Solidity.Yul.Checks.RawPureInitTimeout.Old.dirtyInput.1

/-- Initializer stage only; the separate full-loop dirty-prefix goal remains open. -/
theorem initializerPrefix : (Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawPureInitTimeout.initProof 5 Solidity.Yul.Checks.RawPureInitTimeout.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawPureInitTimeout.initProof 5 Solidity.Yul.Checks.RawPureInitTimeout.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.flag).val = 1 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawPureInitTimeout.initProof 5 Solidity.Yul.Checks.RawPureInitTimeout.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩

#print axioms initializerPrefix
#print axioms Solidity.Yul.RawPureInitTimeout.raw_post_timeout
#print axioms Solidity.Yul.RawPureInitTimeout.raw_no_post_timeout
#print axioms Solidity.Yul.RawPureInitTimeout.source_post_timeout
#print axioms Solidity.Yul.RawPureInitTimeout.source_no_post_timeout
#print axioms Solidity.Yul.RawPureInitTimeout.post_firstDone
#print axioms Solidity.Yul.RawPureInitTimeout.no_post_firstDone
#print axioms rawPostFamily
#print axioms rawNoPostFamily
#print axioms sourcePostWorld
#print axioms sourceNoPostWorld
#print axioms postBounds
#print axioms noPostBounds
#print axioms breakCounterexample
#print axioms initializerCounterexample
#print axioms dirtyRefusal
end Solidity.Yul.Checks.RawPureInitTimeout

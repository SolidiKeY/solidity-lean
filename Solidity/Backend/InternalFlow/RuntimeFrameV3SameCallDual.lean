import Solidity.Backend.InternalFlow.RuntimeFrameV3SameCallInputs

/-! Real success and bare revert for the exact SAME source call, argument
expression and selected target emission. Only the represented caller changes,
after an actual checked successful rebinding. No approved profile is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.SameCallDual
noncomputable section
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F reference)
open SameCallInputs (caller addresses machine)

def statement (depth : Nat) := RecursiveScopeCompiler.Client.input .uint (.user "sameCall") depth
def selected (depth : Nat) := RecursiveScopeCompiler.Client.selected .uint (.user "sameCall") depth

theorem root (depth : Nat) : RecursiveScopeCompiler.compile 1 5 16 9 8 F (statement depth)=some (selected depth) :=
 RecursiveScopeCompiler.Client.root .uint (.user "sameCall") depth

theorem entry (depth : Nat) : InterfaceV1.Entry (selected depth).plan 1 1 16 F caller addresses machine 10 := by
 have initial := ScalarReentry.entry depth
 refine ⟨SameCallInputs.reached.2.2.1,initial.callerBound,initial.resultBound,initial.workspace,
   initial.pointerAbove,initial.pointerBelow,initial.payloadAbove,?_,?_,.inl (by change (9:Nat)<10;decide),?_,SameCallInputs.cursor,.inl rfl⟩
 · change 10+ScalarDemand.reserve ScalarReentry.count caller≤16
   rw [ScalarDemand.reserve_error _ SameCallInputs.count_fails]
   decide
 · change 5≤ScalarDemand.reserve ScalarReentry.count caller
   rw [ScalarDemand.reserve_error _ SameCallInputs.count_fails]
   decide
 · change 10+ScalarDemand.reserve ScalarReentry.count caller<W
   rw [ScalarDemand.reserve_error _ SameCallInputs.count_fails]
   decide

theorem source_revert (depth : Nat) : (statement depth).run caller=.error .revert :=
 ((selected depth).source_run caller).trans
   (ScalarClaims.source_revert rfl reference ScalarReentry.count .here "scalarCountdown" depth caller SameCallInputs.count_fails)

theorem target_revert (depth : Nat) : run (selected depth).plan.code machine=.revert :=
 (selected depth).bare_revert (by decide) 1 16 caller addresses machine 10 (entry depth) (source_revert depth)

theorem whole_target_revert (depth : Nat) :
 run (SameCallInputs.checked.code++(selected depth).plan.code) SameCallInputs.before=.revert :=
 (run_append_ok SameCallInputs.reached.2.1).trans (target_revert depth)

def sourceProgram (depth : Nat) : Prog SameCallInputs.C Γ Γ :=
 .cons SameCallInputs.preparation (.cons (statement depth) .nil)

theorem whole_source_revert (depth : Nat) : (sourceProgram depth).run SameCallInputs.origin = .error .revert := by
 rw [sourceProgram,Prog.run_cons_ok SameCallInputs.reached.1]
 change (TRun.seq (statement depth).runR TRun.nil caller).map _=_
 simp only [TRun.seq,show (statement depth).runR caller=.error .revert from source_revert depth,Except.map]

theorem good_return : InterfaceV1.Returned (selected 4).plan 1 1 16 ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10
 ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ :=
 RecursiveScopeCompiler.Client.returned .uint (.user "sameCall") 4 (by decide)

/-- One statement/emission has a real successful Entry and a real reverting
Entry. No domain/profile agreement or failed output state is inferred. -/
theorem dual :
 InterfaceV1.Entry (selected 4).plan 1 1 16 F ScalarContinuation.final ScalarContinuation.finalBase ScalarContinuation.target 10 ∧
 (statement 4).run ScalarContinuation.final=.ok ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ ∧
 InterfaceV1.Returned (selected 4).plan 1 1 16 ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10 ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ ∧
 InterfaceV1.Entry (selected 4).plan 1 1 16 F caller addresses machine 10 ∧
 (statement 4).run caller=.error .revert ∧ run (selected 4).plan.code machine=.revert :=
 ⟨ScalarSourceCompiler.Client.entered 4,
  (RecursiveScopeCompiler.Client.source .uint (.user "sameCall") 4).trans (ScalarSourceCompiler.Client.actual_source 4 (by decide)),
  good_return,entry 4,source_revert 4,target_revert 4⟩

/-- Non-vacuity in the existing outcome-linked interface, with no arbitrary
admission predicate chosen to obtain the witnesses. -/
theorem successful_entry : InterfaceV2.SuccessfulEntry 1 F (statement 4) (selected 4).plan :=
 ⟨1,16,ScalarContinuation.final,ScalarContinuation.finalBase,ScalarContinuation.target,10,
  ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩,dual.1,dual.2.1⟩

theorem reverting_entry (depth : Nat) : InterfaceV2.RevertingEntry 1 F (statement depth) (selected depth).plan :=
 ⟨1,16,caller,addresses,machine,10,entry depth,source_revert depth⟩

end
end Solidity.Backend.InternalFlow.RuntimeFrame.SameCallDual

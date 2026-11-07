import Solidity.Backend.InternalFlow.RuntimeFrameV3FrozenScopeCompiler
import Solidity.Backend.InternalFlow.RuntimeFrameV3SameCallControls

/-! Inhabited return/revert witnesses for the EXACT frozen recursiveSource
family. Actual source constructor, selector receipts and code are linked at
every index; approved-domain and general recursive compilation stay open. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeClient
noncomputable section
open Evm Evm.Memory ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F reference)

def statement (depth : Nat) := FrozenScopeCompiler.source rfl reference ScalarReentry.count .here
 "scalarCountdown" .uint (.user "sameCall") depth

def selected (depth : Nat) := FrozenScopeCompiler.selected ScalarReentry.emitted ScalarReentry.selected rfl reference
 (.here : Idx Γ (.val .uint)) "scalarCountdown" .uint (.user "sameCall") depth

theorem root (depth : Nat) : RecursiveScopeCompiler.compile 1 5 16 9 8 F (statement depth)=some (selected depth) :=
 FrozenScopeCompiler.selected_root ScalarReentry.emitted ScalarReentry.selected rfl reference .here
   "scalarCountdown" .uint (.user "sameCall") depth

theorem plan_eq (depth : Nat) : (selected depth).plan=(SameCallDual.selected depth).plan := rfl

theorem same_image (left right : Nat) : (selected left).plan.code=(selected right).plan.code := rfl

/-- Full actual source agreement bridges to the earlier witnessed callers,
not a syntax equality between bare and decorated exhausted bases. -/
theorem source_eq (depth : Nat) (caller : State SameCallInputs.C Γ) :
 (statement depth).run caller=(SameCallDual.statement depth).run caller :=
 ((selected depth).source_run caller).trans ((SameCallDual.selected depth).source_run caller).symm

theorem coherence : InterfaceV1.RecursiveReturnCoherence "scalarCountdown"
 (DisjointScalarEntry.args rfl reference ScalarReentry.count)
 (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint))))
 (FrozenScopeFamily.step CountdownWitness.A rfl .uint (.user "sameCall")) :=
 FrozenScopeFamily.source_coherence rfl .uint (.user "sameCall") "scalarCountdown" _ _

theorem good_entry : InterfaceV1.Entry (selected 4).plan 1 1 16 F ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10 := SameCallDual.dual.1

theorem good_source : (statement 4).run ScalarContinuation.final=
 .ok ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ :=
 (source_eq 4 ScalarContinuation.final).trans SameCallDual.dual.2.1

theorem good_return : InterfaceV1.Returned (selected 4).plan 1 1 16 ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10
 ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ :=
 (selected 4).returns (by decide) 1 16 ScalarContinuation.final ScalarContinuation.finalBase
   ScalarContinuation.target 10 good_entry _ good_source

theorem good_target : run (selected 4).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 :=
 RecursiveScopeCompiler.Client.target .uint (.user "sameCall")

theorem bad_entry (depth : Nat) : InterfaceV1.Entry (selected depth).plan 1 1 16 F
 SameCallInputs.caller SameCallInputs.addresses SameCallInputs.machine 10 := SameCallDual.entry depth

theorem bad_source (depth : Nat) : (statement depth).run SameCallInputs.caller=.error .revert :=
 (source_eq depth SameCallInputs.caller).trans (SameCallDual.source_revert depth)

theorem bad_target (depth : Nat) : run (selected depth).plan.code SameCallInputs.machine=.revert :=
 (selected depth).bare_revert (by decide) 1 16 SameCallInputs.caller SameCallInputs.addresses
   SameCallInputs.machine 10 (bad_entry depth) (bad_source depth)

theorem whole_bad_target (depth : Nat) :
 run (SameCallInputs.checked.code++(selected depth).plan.code) SameCallInputs.before=.revert :=
 (run_append_ok SameCallInputs.reached.2.1).trans (bad_target depth)

theorem successful_entry : InterfaceV2.SuccessfulEntry 1 F (statement 4) (selected 4).plan :=
 ⟨1,16,ScalarContinuation.final,ScalarContinuation.finalBase,ScalarContinuation.target,10,
  ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩,good_entry,good_source⟩

theorem reverting_entry (depth : Nat) : InterfaceV2.RevertingEntry 1 F (statement depth) (selected depth).plan :=
 ⟨1,16,SameCallInputs.caller,SameCallInputs.addresses,SameCallInputs.machine,10,bad_entry depth,bad_source depth⟩

theorem original_base : FrozenScopeFamily.body (C:=SameCallInputs.C) CountdownWitness.A rfl .uint (.user "sameCall") 0=
 (Prog.recBase : Prog SameCallInputs.C (Frame CountdownWitness.A) (Frame CountdownWitness.A)) := rfl

theorem complete_observations :
 run (selected 4).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 ∧
 (List.range 26).map (fun index => ScalarReentry.Endpoint.machine.mem index)=
 [w[26],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],w[16],w[2],w[16],w[1],
  w[2],w[3],w[9],w[0],w[1],w[4],w[3],w[0],w[0],w[0]] ∧
 ScalarReentry.Endpoint.machine.stack=[w[77]] := RecursiveScopeCompiler.Client.complete_observations .uint (.user "sameCall")

theorem native_default_root : RecursiveScopeCompiler.compile 1 5 16 9 8 F (statement recDepth)=some (selected recDepth) := root recDepth

/-- The exact original exhausted base is kept distinct from the common
image execution; no full failure/termination correspondence is asserted. -/
theorem exhaustion_boundary : (statement 0).run ScalarContinuation.final=.error .exhausted ∧
 run (selected 0).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 :=
 ⟨(source_eq 0 ScalarContinuation.final).trans (RecursiveScopeCompiler.Client.exhausted_source .uint (.user "sameCall")),good_target⟩

theorem not_fault (depth : Nat) : run (selected depth).plan.code SameCallInputs.machine≠.fault := by
 rw [bad_target]
 intro wrong
 cases wrong

end
end Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeClient

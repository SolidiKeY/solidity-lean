import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDual

/-! Same-code success/revert nonvacuity and complete observations. The two
represented callers differ in their protected scalar input. Approved-domain
provenance/coverage and general recursive compilation are not supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDual.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

theorem one_image (n k : Nat) : (outputPlan.at n).code=(outputPlan.at k).code := rfl

theorem good_guard : choiceGuard.evalT caller=.ok true := by with_unfolding_all rfl

theorem bad_guard : choiceGuard.evalT rejectedCaller=.ok false := by with_unfolding_all rfl

theorem rejected_reference : TEnv.get reference rejectedCaller.env=some CountdownWitness.P.r0 := by
 with_unfolding_all rfl

theorem bad_branch_reached : badCount.evalT rejectedCaller=.error .revert := by
 with_unfolding_all rfl

theorem skipped_bad_branch : badCount.evalT caller=.error .revert ∧ choice.evalT caller=.ok (countValue 3 (by decide)) :=
 ⟨DisjointScalarReturn.Client.bad_eval,good_eval⟩

theorem source_input_difference : TEnv.get (.there .here : Idx Γ (.val .uint)) caller.env≠
 TEnv.get (.there .here : Idx Γ (.val .uint)) rejectedCaller.env := by
 decide +kernel

theorem complete_observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,
 machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,
 machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],
 w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[0],w[1],w[4]]) := ScalarPlan.Client.complete_observations

theorem target_frame : StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses machine :=
 specification.2.2.1

theorem protected_failure_input :
 (rejectedMachine.stack,rejectedMachine.mem 1,rejectedMachine.mem 2,rejectedMachine.mem 3,rejectedMachine.mem 4,
 rejectedMachine.mem 0,rejectedMachine.mem 9)=(before.stack,before.mem 1,before.mem 2,w[0],before.mem 4,before.mem 0,before.mem 9) := by
 simp only [rejectedMachine,writeMachine,upd]
 rfl

/-- Input allocator evidence only; no allocator is returned by a failed run. -/
theorem rejected_allocator : StructAllocatorRepr rejectedCaller.heap CountdownWitness.P.base 16 ⟨22,by decide⟩ rejectedMachine :=
 initial_owner.localWrite 3 (by decide) (by decide) w[0]

theorem changed_result : machine.mem 4≠before.mem 4 := changed_destination.2.2

theorem wrong_alias : machine.mem 5≠w[20] := DisjointScalarReturn.Client.wrong_alias

theorem wrong_cursor : machine.mem 0≠w[23] := wrong_heap_cursor

theorem failure_not_success (target : Machine) (cost : Nat) : run (outputPlan.at 0).code rejectedMachine≠.ok target cost := by
 rw [bad_execution]
 intro wrong
 cases wrong

theorem failure_not_fault : run (outputPlan.at 0).code rejectedMachine≠.fault := by
 rw [bad_execution]
 intro wrong
 cases wrong

theorem wrong_success_caller : (statement 0).run caller≠.error .revert := by
 have source := ScalarClaims.source_value rfl reference choice .here "scalarCountdown" 0 caller
   CountdownWitness.P.r0 (by with_unfolding_all rfl) (countValue 3 (by decide)) good_eval
 have exhausted : (statement 0).run caller=.error .exhausted := by
   simpa only [Nat.not_lt_zero,if_false] using source
 rw [exhausted]
 intro wrong
 cases wrong

/-- A concrete remaining coverage obstruction: the inherited quotation-based
reserve is conservative even though the SAME code and caller succeed. -/
theorem index_five_source : (statement 5).run caller=.ok ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ := by
 have source := ScalarClaims.source_value rfl reference choice .here "scalarCountdown" 5 caller
   CountdownWitness.P.r0 (by with_unfolding_all rfl) (countValue 3 (by decide)) good_eval
 simpa only [show (countValue 3 (by decide)).word.val=3 from rfl,if_pos (show 3<5 from by decide)] using source

theorem index_five_target : run (outputPlan.at 5).code before=.ok machine 0 := good_execution

theorem index_five_not_entry : ¬InterfaceV1.Entry (outputPlan.at 5) 1 1 16 F caller CountdownWitness.P.base before 10 := by
 intro invalid
 have reserve := invalid.reserve
 change 10+8≤16 at reserve
 omega

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDual.Controls

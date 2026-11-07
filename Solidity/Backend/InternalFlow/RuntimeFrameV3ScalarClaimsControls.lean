import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarClaims
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPlanControls

/-! Inhabited uses of universal frozen claims. The successful caller and
complete physical observation are unchanged; target evidence is obtained from
the actual source success through ReturnClaim. The separate failing-argument
plan exercises BareRevertClaim without a failed-state or rollback inference. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarClaims.Client
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

theorem good_claim (depth : Nat) : InterfaceV1.ReturnClaim 1 F
 (DisjointScalarReturn.call rfl reference count .here "scalarCountdown" depth)
 (ScalarPlan.Client.good.at depth) :=
 returns ScalarEmitter.Client.emitted (by decide) rfl reference .here "scalarCountdown" depth

theorem failing_claim (depth : Nat) : InterfaceV1.BareRevertClaim 1 F
 (DisjointScalarReturn.call rfl reference badCount .here "scalarCountdown" depth)
 (ScalarPlan.Client.bad.at depth) :=
 bare_revert ScalarEmitter.Client.badEmitted (by decide) rfl reference .here "scalarCountdown" depth

theorem returned_via_claim : InterfaceV1.Returned (ScalarPlan.Client.good.at 4) 1 1 16 caller CountdownWitness.P.base before 10
 ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ := by
 have source := (native_and_target 4 (by decide)).1
 rw [←source_identity 4] at source
 exact good_claim 4 1 16 caller CountdownWitness.P.base before 10 ScalarPlan.Client.entry _ source

noncomputable def after : Machine := returned_via_claim.choose
noncomputable def addresses' : Nat → Fin W := returned_via_claim.choose_spec.choose

theorem chosen_execution : run (ScalarPlan.Client.good.at 4).code before=.ok after 0 :=
 returned_via_claim.choose_spec.choose_spec.1

theorem same_endpoint : after=machine := ScalarPlan.Client.same_actual_endpoint chosen_execution

theorem chosen_frame : StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses' after :=
 returned_via_claim.choose_spec.choose_spec.2.1

theorem complete_observations :
 (after.stack,[after.mem 0,after.mem 1,after.mem 2,after.mem 3,after.mem 4,
 after.mem 5,after.mem 6,after.mem 7,after.mem 8,after.mem 9,after.mem 10,
 after.mem 11,after.mem 12,after.mem 13,after.mem 14,after.mem 15,after.mem 16,
 after.mem 17,after.mem 18,after.mem 19,after.mem 20,after.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],
 w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[0],w[1],w[4]]) := by
 rw [same_endpoint]
 exact ScalarPlan.Client.complete_observations

theorem wrong_alias : after.mem 5≠w[20] := by
 rw [same_endpoint]
 exact DisjointScalarReturn.Client.wrong_alias

theorem wrong_cursor : after.mem 0≠w[23] := by
 rw [same_endpoint]
 exact wrong_heap_cursor

theorem actual_revert : run (ScalarPlan.Client.bad.at 0).code before=.revert :=
 failing_claim 0 1 16 caller CountdownWitness.P.base before 10 ScalarPlan.Client.bad_entry (bad_call 0)

theorem failure_not_success (target : Machine) (cost : Nat) :
 run (ScalarPlan.Client.bad.at 0).code before≠.ok target cost := by
 rw [actual_revert]
 intro wrong
 cases wrong

theorem exhaustion_not_revert : (ScalarCallerReturn.invoke 0).run caller≠.error .revert := by
 rw [shallow 0 (by decide)]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarClaims.Client

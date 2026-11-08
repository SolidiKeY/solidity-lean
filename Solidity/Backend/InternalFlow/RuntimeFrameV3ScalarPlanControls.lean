import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPlan
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV2
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarEmitterControls

/-! Real frozen-interface entries and return evidence for the unchanged
populated scalar source caller. Success and revert clients use distinct
argument expressions; no dual-outcome V3 producer or approved domain follows. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPlan.Client
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

def good := plan ScalarEmitter.Client.emitted reference (.here : Idx Γ (.val .uint))
def bad := plan ScalarEmitter.Client.badEmitted reference (.here : Idx Γ (.val .uint))

theorem entry : InterfaceV1.Entry (good.at 4) 1 1 16 F caller CountdownWitness.P.base before 10 where
 represented := initial
 callerBound := by decide
 resultBound := by decide
 workspace := by decide
 pointerAbove := by decide
 pointerBelow := by decide
 payloadAbove := by decide
 reserve := by decide
 controlSpace := by decide
 separate := Or.inl (by decide)
 noWrap := by decide
 cursor := rfl
 capacity := Or.inl rfl

theorem returned : InterfaceV1.Returned (good.at 4) 1 1 16 caller CountdownWitness.P.base before 10
 ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ :=
 returned_of_eval ScalarEmitter.Client.emitted (by decide) rfl reference .here entry 3 (by decide) rfl (by decide)

theorem successful_entry : InterfaceV2.SuccessfulEntry 1 F (ScalarCallerReturn.invoke 4) (good.at 4) := by
 refine ⟨1,16,caller,CountdownWitness.P.base,before,10,⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩,entry,?_⟩
 rw [←source_identity 4]
 simpa only [if_pos (show 3<4 from by decide)] using specification.2.1 "scalarCountdown" 4

theorem same_actual_endpoint {target : Machine}
 (execution : run (good.at 4).code before=.ok target 0) : target=machine := by
 have actual : (.ok target 0 : Evm.Out)=.ok machine 0 := execution.symm.trans ScalarEmitter.Client.target
 cases actual
 rfl

theorem complete_observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,
 machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,
 machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],
 w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[0],w[1],w[4]]) := ScalarEmitter.Client.complete_observations

theorem bad_entry : InterfaceV1.Entry (bad.at 0) 1 1 16 F caller CountdownWitness.P.base before 10 where
 represented := initial
 callerBound := by decide
 resultBound := by decide
 workspace := by decide
 pointerAbove := by decide
 pointerBelow := by decide
 payloadAbove := by decide
 reserve := by decide
 controlSpace := by decide
 separate := Or.inl (by decide)
 noWrap := by decide
 cursor := rfl
 capacity := Or.inl rfl

theorem reverting_entry : InterfaceV2.RevertingEntry 1 F
 (DisjointScalarReturn.call rfl reference badCount .here "scalarCountdown" 0) (bad.at 0) :=
 ⟨1,16,caller,CountdownWitness.P.base,before,10,bad_entry,bad_call 0⟩

theorem bare_target : run (bad.at 0).code before=.revert := by
 simpa only [List.append_nil] using ScalarEmitter.Client.bad_target []

theorem insufficient_frame : ¬InterfaceV1.Entry (good.at 4) 1 1 15 F caller CountdownWitness.P.base before 10 := by
 intro invalid
 have demand := invalid.reserve
 change 10+6≤15 at demand
 omega

theorem omitted_control_space : ¬InterfaceV1.Entry (good.at 0) 1 1 14 F caller CountdownWitness.P.base before 10 := by
 intro invalid
 have demand := invalid.reserve
 change 10+5≤14 at demand
 omega

theorem wrong_cursor : ¬InterfaceV1.Entry (good.at 4) 1 1 16 F caller CountdownWitness.P.base before 11 := by
 intro invalid
 have cursor := invalid.cursor
 change w[10]=w[11] at cursor
 exact (by decide : (w[10] : Word)≠w[11]) cursor

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPlan.Client

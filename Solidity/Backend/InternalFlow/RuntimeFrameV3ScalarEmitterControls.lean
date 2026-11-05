import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarEmitterSound
import Solidity.Backend.InternalFlow.RuntimeFrameV3DisjointScalarControls

/-! Inhabited executable selection uses the unchanged populated scalar source
caller. The actual selected target has the same complete 22-word endpoint,
private-to-caller result change, aliases and stack. Selection refusals are
static layout checks, not new claims about general compiler admission. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarEmitter.Client
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client

def emitted : Emission 1 5 16 9 8 F count := (compile 1 5 16 9 8 F count).get (by rfl)

theorem selected_root : compile 1 5 16 9 8 F count=some emitted := rfl

theorem selected_argument : emitted.value=value := rfl

theorem selected_code : emitted.code reference (.here : Idx Γ (.val .uint))=
 DisjointScalarReturn.code 1 5 reference value .here 9 8 := rfl

theorem available : ∃ (after : Machine) (addresses : Nat → Fin W),
 run (emitted.code reference (.here : Idx Γ (.val .uint))) before=.ok after 0 ∧
 (∀ f depth,(DisjointScalarReturn.call rfl reference count (.here : Idx Γ (.val .uint)) f depth).run caller=
   if 3<depth then .ok ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses after ∧
 after.stack=[w[77]] ∧ BaseExtends caller.H CountdownWitness.P.base addresses ∧
 after.mem 4=w[3] ∧ after.mem 7=w[3] ∧ after.mem 6=w[3] ∧ after.mem 5=w[16] ∧
 after.mem 9=w[10] ∧ after.mem 8=w[10] ∧
 GrowsAllocator 1 16 0 caller CountdownWitness.P.base before (caller.setLocal .here (countValue 3 (by decide))) addresses after ∧
 (∀ x,x≠4 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 16≤x) → after.mem x=before.mem x) ∧
 (∀ j,j<3 → after.mem (10+2*j)=w[16] ∧ after.mem (10+2*j+1)=.val (wmod (3-j))) :=
 ScalarEmitter.endpoint rfl caller reference count emitted .here 3 (by decide) rfl CountdownWitness.P.base before initial
   10 (by decide) (by decide) (by decide) (by decide) (by decide) rfl

theorem target : run (emitted.code reference (.here : Idx Γ (.val .uint))) before=.ok machine 0 := by
 rw [selected_code]
 exact specification.1

theorem complete_observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,
 machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,
 machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],
 w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[0],w[1],w[4]]) := snapshot

theorem restored_caller : StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses machine :=
 specification.2.2.1

theorem wrong_protected_destination : machine.mem 4≠machine.mem 3 := wrong_typed_slot

theorem wrong_alias : machine.mem 5≠w[20] := DisjointScalarReturn.Client.wrong_alias

theorem wrong_cursor : machine.mem 0≠w[23] := wrong_heap_cursor

theorem refuse_overlap : compile 1 4 16 9 8 F count=none := rfl

theorem refuse_control_overlap : compile 1 5 16 9 9 F count=none := rfl

theorem refuse_frame : compile 1 5 8 9 8 F count=none := rfl

def badEmitted : Emission 1 5 16 9 8 F badCount := (compile 1 5 16 9 8 F badCount).get (by rfl)

theorem bad_selected : compile 1 5 16 9 8 F badCount=some badEmitted := rfl

theorem bad_code : badEmitted.code reference (.here : Idx Γ (.val .uint))=
 DisjointScalarReturn.code 1 5 reference badValue .here 9 8 := rfl

theorem bad_target (suffix : List Instr) :
 run (badEmitted.code reference (.here : Idx Γ (.val .uint)) ++ suffix) before=.revert :=
 argument_revert badEmitted rfl caller reference .here bad_eval CountdownWitness.P.base before initial suffix

theorem bad_not_success (after : Machine) (cost : Nat) :
 run (badEmitted.code reference (.here : Idx Γ (.val .uint))) before≠.ok after cost := by
 have failed : run (badEmitted.code reference (.here : Idx Γ (.val .uint))) before=.revert := by
   simpa only [List.append_nil] using bad_target []
 rw [failed]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarEmitter.Client

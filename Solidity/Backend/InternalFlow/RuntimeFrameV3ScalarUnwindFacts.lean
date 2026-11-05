import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarUnwind
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveHistory

/-! Populated scalar unwind: actual native descent supplies all three saved
parent payloads. The public checked increment propagates the live result.
This explicit image is not claimed as a general recursive compiler selection. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.Client
open Evm Evm.Memory RecursiveSource RecursiveActivation CountdownWitness ScalarRecursiveSource
abbrev A := CountdownWitness.A
abbrev F := CountdownWitness.F.push (.val .uint) .ok
def origin := CountdownWitness.callee.setLocal (.here : Idx (Parameters A) (.val .uint)) (countValue 3 (by decide))
def before := writeMachine (writeMachine AllocatorReturn.Checks.input 6 w[2]) 3 w[3]
def entered := writeMachine before 4 w[0]
def state (n : Nat) (bound : n<W) : State P.C (Frame A) :=
 origin.withEnv (Δ:=Frame A) (countValue n bound,(countValue n bound,(some P.r0,())))
def stageCode : List Instr := ScalarUnwind.code (C:=P.C) 2 8 F

theorem initial : StateRepr 1 2 16 CountdownWitness.F origin P.base before :=
 (reserved_write AllocatorReturn.Checks.represented 6 (by decide) (by decide) w[2]).setVal .here (countValue 3 (by decide)) w[3] (ReprV.uint_of rfl)

theorem scalar_entry : origin.push (t:=.val .uint) (PrimTy.dflt .uint)=ScalarRecursiveSource.Controls.entry.st := rfl

theorem entry_repr : StateRepr 1 2 16 F ScalarRecursiveSource.Controls.entry.st P.base entered :=
 initial.consVal (PrimTy.dflt .uint) w[0] (ReprV.dflt_zero .uint) (by decide)

theorem entry_run : run [.push w[0],.mstore 4] before=.ok entered 0 := rfl

theorem available : ∃ (down zero : Machine) (addresses : Nat → Fin W),
 run (descentCode (C:=P.C) 2 CountdownWitness.F 8) entered=.ok down 0 ∧
 run [.push w[0],.mstore 4] down=.ok zero 0 ∧
 StateRepr 1 2 16 F (state 0 W_pos) addresses zero ∧
 zero.stack=[w[77]] ∧ zero.mem 8=w[16] ∧ zero.mem 2=w[16] ∧
 (∀ j,j<3 → zero.mem (10+2*j)=zero.mem 2 ∧ zero.mem (10+2*j+1)=.val (wmod (3-j))) ∧
 (∀ x,x≠8 → x≠3 → x≠4 → (x<10 ∨ 16≤x) → zero.mem x=before.mem x) ∧
 BaseExtends origin.H P.base addresses ∧
 StructAllocatorRepr (state 0 W_pos).heap addresses 16 ⟨22,by decide⟩ zero := by
 have params : StateRepr 1 2 16 CountdownWitness.F origin P.base entered :=
   reserved_write initial 4 (by decide) (by decide) w[0]
 obtain ⟨down,addresses,running,stopped,represented,stack,extended,growth,cursor⟩ :=
   RecursiveDescent.complete rfl 3 (by decide) origin P.r0 rfl rfl P.base entered params
     8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
 obtain ⟨saved,outside⟩ := RecursiveHistory.saved_history rfl 3 (by decide) origin P.r0 rfl rfl
   P.base entered down params 8 8 10 (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) rfl running
 let zero := writeMachine down 4 w[0]
 have repr : StateRepr 1 2 16 F (state 0 W_pos) addresses zero :=
   represented.consVal (PrimTy.dflt .uint) w[0] (ReprV.dflt_zero .uint) (by decide)
 have oldref : down.mem 2=entered.mem 2 := outside 2 (by decide) (by decide) (.inl (by decide))
 have reference : zero.mem 2=w[16] := (upd_other down.mem w[0] (by decide : (2:Nat)≠4)).trans oldref
 have owner0 : StructAllocatorRepr origin.heap P.base 16 ⟨22,by decide⟩ entered :=
   ((AllocatorReturn.Checks.ownership.localWrite 6 (by decide) (by decide) w[2]).localWrite 3 (by decide) (by decide) w[3]).localWrite 4 (by decide) (by decide) w[0]
 have owned := growth ⟨22,by decide⟩ (by decide) owner0 (by decide)
 refine ⟨down,zero,addresses,RecursiveDescent.run_of_stopped stopped,rfl,repr,stack,?_,reference,?_,?_,extended,?_⟩
 · exact (upd_other down.mem w[0] (by decide : (8:Nat)≠4)).trans cursor
 · intro j small
   exact ⟨(upd_other down.mem w[0] (by omega)).trans (((saved j small).1.trans (show entered.mem 2=w[16] from rfl)).trans reference.symm),
     (upd_other down.mem w[0] (by omega)).trans (saved j small).2⟩
 · intro x hp hc hv region
   exact (upd_other _ _ hv).trans ((outside x hp hc region).trans (upd_other _ _ hv))
 · exact owned.localWrite 4 (by decide) (by decide) w[0]

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.Client

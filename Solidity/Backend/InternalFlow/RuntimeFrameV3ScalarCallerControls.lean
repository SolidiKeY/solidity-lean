import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarCallerReturn

/-! Complete ordered observations of the same populated scalar caller endpoint,
derived by projection rather than re-running target programs. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarCallerReturn.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
noncomputable def machine : Machine := endpoint.choose
noncomputable def addresses : Nat → Fin W := endpoint.choose_spec.choose

theorem specification :
 run image before=.ok machine 0 ∧
 StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses machine ∧
 machine.stack=[w[77]] ∧ machine.mem 3=w[2] ∧ machine.mem 4=w[3] ∧
 machine.mem 1=w[16] ∧ machine.mem 2=w[16] ∧ machine.mem 6=w[2] ∧ machine.mem 8=w[10] ∧
 StructAllocatorRepr caller.heap addresses 16 ⟨22,by decide⟩ machine ∧
 BaseExtends caller.H P.base addresses ∧
 (∀ x,16≤x → machine.mem x=before.mem x) ∧
 (∀ x,x<10 → x≠3 → x≠4 → x≠6 → x≠8 → machine.mem x=before.mem x) ∧
 (∀ j,j<3 → machine.mem (10+2*j)=w[16] ∧ machine.mem (10+2*j+1)=.val (wmod (3-j))) := endpoint.choose_spec.choose_spec

theorem snapshot :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,machine.mem 11,
 machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,machine.mem 17,
 machine.mem 18,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[2],w[3],w[2],w[0],w[10],w[99],w[16],w[3],w[16],w[2],
 w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 rcases specification with ⟨executed,represented,stack,count,result,alias1,alias2,saved,cursor,owner,extended,high,low,payload⟩
 have cell0 : machine.mem 0=w[22] := owner.arrays.free.cell
 have cell7 := low 7 (by decide) (by decide) (by decide) (by decide) (by decide)
 have cell9 := low 9 (by decide) (by decide) (by decide) (by decide) (by decide)
 rw [stack,cell0,alias1,alias2,count,result,saved,cell7,cursor,cell9,
   (payload 0 (by decide)).1,(payload 0 (by decide)).2,
   (payload 1 (by decide)).1,(payload 1 (by decide)).2,
   (payload 2 (by decide)).1,(payload 2 (by decide)).2,
   high 16 (by decide),high 17 (by decide),high 18 (by decide),high 20 (by decide),high 21 (by decide)]
 rfl

theorem native_and_target (depth : Nat) (enough : 3<depth) :
 (invoke depth).run caller=.ok ⟨caller.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ ∧
 run image before=.ok machine 0 ∧
 StateRepr 1 1 16 F (caller.setLocal .here (countValue 3 (by decide))) addresses machine :=
 ⟨source depth enough,specification.1,specification.2.1⟩

theorem wrong_result : machine.mem 4≠w[0] := by
 rw [specification.2.2.2.2.1]
 decide

theorem wrong_alias : machine.mem 2≠w[20] := by
 rw [specification.2.2.2.2.2.2.1]
 decide

theorem wrong_order : (machine.mem 3,machine.mem 4)≠(w[3],w[2]) := by
 rw [specification.2.2.2.1,specification.2.2.2.2.1]
 decide

theorem wrong_cursor : machine.mem 0≠w[23] := by
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,owner,_⟩
 rw [owner.arrays.free.cell]
 decide

theorem not_revert : run image before≠.revert := by
 rw [specification.1]
 intro wrong
 cases wrong

theorem shallow (depth : Nat) (short : depth≤3) : (invoke depth).run caller=.error .exhausted := by
 simpa only [if_neg (show ¬(3:Nat)<depth from by omega)] using
   call_all_horizons rfl "scalarCountdown" args .here depth caller 3 (by decide) P.r0 arguments

theorem wrong_stack : machine.stack≠[] := by
 rw [specification.2.2.1]
 decide

theorem shallow_not_revert (depth : Nat) (short : depth≤3) : (invoke depth).run caller≠.error .revert := by
 rw [shallow depth short]
 intro wrong
 cases wrong

/-- Exact zero-allocation transport from the actual caller, not a guessed
frontier for an error-valued result. The initial cursor fixes the same cursor
of the inhabited endpoint. -/
theorem growth : GrowsAllocator 1 16 0 caller P.base before
 (caller.setLocal .here (countValue 3 (by decide))) addresses machine := by
 intro cursor positive owned space
 have inputCell : before.mem 0=w[22] := rfl
 have unique : cursor=(⟨22,by decide⟩ : Fin W) := Word.val.inj (owned.arrays.free.cell.symm.trans inputCell)
 subst cursor
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,result,_⟩
 simpa only [Nat.add_zero] using result

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarCallerReturn.Controls

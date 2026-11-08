import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarUnwindFacts

/-! Three actual scalar-parent returns following the same populated native
descent. Every saved pair comes from that descent; each live result is checked
by the published increment compiler. General recursive selection stays open. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.Client
open Evm Evm.Memory RecursiveSource RecursiveActivation CountdownWitness ScalarRecursiveSource

def unwindCode := stageCode ++ (stageCode ++ stageCode)
def image : List Instr := [.push w[0],.mstore 4] ++
 (descentCode (C:=P.C) 2 CountdownWitness.F 8 ++ ([.push w[0],.mstore 4] ++ unwindCode))

theorem endpoint : ∃ (last : Machine) (addresses : Nat → Fin W),
 run image before=.ok last 0 ∧ StateRepr 1 2 16 F (state 3 (by decide)) addresses last ∧
 last.stack=[w[77]] ∧ last.mem 8=w[10] ∧ last.mem 2=w[16] ∧ last.mem 3=w[3] ∧ last.mem 4=w[3] ∧
 StructAllocatorRepr (state 3 (by decide)).heap addresses 16 ⟨22,by decide⟩ last ∧
 BaseExtends origin.H P.base addresses ∧
 (∀ x,x≠8 → x≠2 → x≠3 → x≠4 → (x<10 ∨ 16≤x) → last.mem x=before.mem x) ∧
 (∀ j,j<3 → last.mem (10+2*j)=w[16] ∧ last.mem (10+2*j+1)=.val (wmod (3-j))) := by
 obtain ⟨down,zero,addresses,descent,baseCase,represented,stack,cursor,reference,saved,outside,extended,owner⟩ := available
 have nearest := saved 2 (by decide)
 obtain ⟨one,run1,repr1,stack1,cursor1,ref1,count1,result1,grow1,out1⟩ :=
   ScalarUnwind.step (state 0 W_pos) addresses zero represented 0 (by decide) rfl
     8 8 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) cursor
     (by simpa only [show 10+2*2=14 from rfl] using nearest.1)
     (by simpa only [show 10+2*2+1=15 from rfl,show 3-2=1 from rfl] using nearest.2)
 have repr1' : StateRepr 1 2 16 F (state 1 (by decide)) addresses one := repr1
 have next := saved 1 (by decide)
 obtain ⟨two,run2,repr2,stack2,cursor2,ref2,count2,result2,grow2,out2⟩ :=
   ScalarUnwind.step (state 1 (by decide)) addresses one repr1' 1 (by decide) rfl
     8 8 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) cursor1
     ((out1 12 (by decide) (by decide) (by decide) (by decide)).trans (next.1.trans ref1.symm))
     ((out1 13 (by decide) (by decide) (by decide) (by decide)).trans next.2)
 have repr2' : StateRepr 1 2 16 F (state 2 (by decide)) addresses two := repr2
 have first := saved 0 (by decide)
 obtain ⟨last,run3,repr3,stack3,cursor3,ref3,count3,result3,grow3,out3⟩ :=
   ScalarUnwind.step (state 2 (by decide)) addresses two repr2' 2 (by decide) rfl
     8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) cursor2
     ((out2 10 (by decide) (by decide) (by decide) (by decide)).trans
       ((out1 10 (by decide) (by decide) (by decide) (by decide)).trans (first.1.trans (ref2.trans ref1).symm)))
     ((out2 11 (by decide) (by decide) (by decide) (by decide)).trans
       ((out1 11 (by decide) (by decide) (by decide) (by decide)).trans first.2))
 have repr3' : StateRepr 1 2 16 F (state 3 (by decide)) addresses last := repr3
 have own1 := grow1 ⟨22,by decide⟩ (by decide) owner (by decide)
 have own2 := grow2 ⟨22,by decide⟩ (by decide) own1 (by decide)
 have own3 := grow3 ⟨22,by decide⟩ (by decide) own2 (by decide)
 refine ⟨last,addresses,?_,repr3',stack3.trans (stack2.trans (stack1.trans stack)),cursor3,
   ref3.trans (ref2.trans (ref1.trans reference)),count3,result3,own3,extended,?_,?_⟩
 · unfold image
   rw [run_append_ok entry_run,run_append_ok descent,run_append_ok baseCase]
   unfold unwindCode stageCode
   rw [run_append_ok run1,run_append_ok run2]
   exact run3
 · intro x hp hr hc hv region
   exact (out3 x hp hr hc hv).trans ((out2 x hp hr hc hv).trans
     ((out1 x hp hr hc hv).trans (outside x hp hc hv region)))

 · intro j small
   have refWord := (saved j small).1.trans reference
   exact ⟨(out3 _ (by omega) (by omega) (by omega) (by omega)).trans
     ((out2 _ (by omega) (by omega) (by omega) (by omega)).trans
       ((out1 _ (by omega) (by omega) (by omega) (by omega)).trans refWord)),
     (out3 _ (by omega) (by omega) (by omega) (by omega)).trans
     ((out2 _ (by omega) (by omega) (by omega) (by omega)).trans
       ((out1 _ (by omega) (by omega) (by omega) (by omega)).trans (saved j small).2))⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarUnwind.Client

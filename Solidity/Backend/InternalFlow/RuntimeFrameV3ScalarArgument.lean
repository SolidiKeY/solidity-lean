import Solidity.Backend.InternalFlow.RuntimeFrameV3CallerReframe

/-! A nonidentity scalar argument uses the real evaluation stack as a caller
save slot. Actual native argument evaluation, allocating body execution and
restoration are linked; no general recursive compiler admission is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarArgument
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes CountdownWitness
abbrev A : RefTy := CountdownWitness.A
abbrev Γ := CallerReframe.Checks.Γ
abbrev F := CallerReframe.Checks.F
def caller := CallerReframe.Checks.caller.setLocal (.here : Idx Γ (.val .uint)) (countValue 9 (by decide))
def input := writeMachine CallerReframe.Checks.before 3 w[9]
def entered := writeMachine (input.push w[9]) 3 w[2]
def entryCode : List Instr := [.mload 3,.push w[2],.mstore 3]

theorem initial : StateRepr 1 1 16 F caller P.base input :=
 CallerReframe.Checks.initial.setVal .here (countValue 9 (by decide)) w[9] (ReprV.uint_of rfl)

theorem ownership : StructAllocatorRepr caller.heap P.base 16 (⟨22,by decide⟩ : Fin W) input :=
 CallerReframe.Checks.ownership.localWrite 3 (by decide) (by decide) w[9]

def args : Args P.C Γ (Parameters A) :=
 .snoc (.snocMemory .nil A (.user "alias") (.var (.there .here) rfl)) .uint (.user "count") (.simple (.lit 2 rfl))

theorem arguments : args.evalT caller=.ok callee.env := by rfl

theorem argument_code : compileSimple 1 (C:=P.C) (.lit 2 rfl : Simple P.C Γ .uint)=[.push w[2]] := by rfl

theorem entry : run entryCode input=.ok entered 0 := by rfl

theorem callee_repr : StateRepr 1 2 16 CountdownWitness.F callee P.base entered :=
 parameter_projection (tail:=[.mem A]) ((initial.push w[9]).setVal .here (countValue 2 (by decide)) w[2] (ReprV.uint_of rfl))

theorem entered_owner : StructAllocatorRepr callee.heap P.base 16 (⟨22,by decide⟩ : Fin W) entered :=
 (ownership.stack (w[9]::input.stack)).localWrite 3 (by decide) (by decide) w[2]

theorem body_available :
 ∃ (out : Solidity.Out P.C callee.H (Parameters A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingActivation.body 3).run callee=.ok out ∧ run (AllocatingReturn.image (C:=P.C) 2 CountdownWitness.F 8 7) entered=.ok last 0 ∧
 StateRepr 1 2 16 CountdownWitness.F out.st addresses last ∧ last.stack=entered.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 8 callee P.base entered out.st addresses last ∧
 last.mem 8=w[10] ∧ last.mem 2=entered.mem 2 ∧
 (∀ j,j<2 → last.mem (10+2*j)=entered.mem 2 ∧ last.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 (∀ x,0<x → x<16 → x≠2 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 14≤x) → last.mem x=entered.mem x) :=
 AllocatingReturn.endpoint 2 (by decide) callee P.r0 rfl rfl AllocatingSource.Checks.read_bound P.base entered callee_repr
   ⟨22,by decide⟩ entered_owner (by decide) (by decide) 8 8 10 (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide) rfl 7 (by decide) (by decide) (by decide) rfl

noncomputable def bodyOut := body_available.choose
noncomputable def bodyMachine : Machine := body_available.choose_spec.choose
noncomputable def addresses : Nat → Fin W := body_available.choose_spec.choose_spec.choose

theorem body_spec :
 (AllocatingActivation.body 3).run callee=.ok bodyOut ∧ run (AllocatingReturn.image (C:=P.C) 2 CountdownWitness.F 8 7) entered=.ok bodyMachine 0 ∧
 StateRepr 1 2 16 CountdownWitness.F bodyOut.st addresses bodyMachine ∧ bodyMachine.stack=entered.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 8 callee P.base entered bodyOut.st addresses bodyMachine ∧
 bodyMachine.mem 8=w[10] ∧ bodyMachine.mem 2=entered.mem 2 ∧
 (∀ j,j<2 → bodyMachine.mem (10+2*j)=entered.mem 2 ∧ bodyMachine.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 (∀ x,0<x → x<16 → x≠2 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 14≤x) → bodyMachine.mem x=entered.mem x) :=
 body_available.choose_spec.choose_spec.choose_spec

noncomputable def output : Solidity.Out P.C caller.H Γ :=
 exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl caller callee.env bodyOut
noncomputable def last : Machine := writeMachine {bodyMachine with stack:=input.stack} 3 w[9]
def call : Stmt P.C Γ Γ := InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step 3
def code : List Instr := entryCode ++ AllocatingReturn.image (C:=P.C) 2 CountdownWitness.F 8 7 ++ [.mstore 3]

theorem source : call.run caller=.ok output :=
 call_return args .none .refl (AllocatingActivation.body 3).runR caller callee.env arguments bodyOut body_spec.1

theorem restore : run [.mstore 3] bodyMachine=.ok last 0 := by
 have stack : bodyMachine.stack=w[9]::input.stack := body_spec.2.2.2.1
 simp only [run,exec_cons_zero,Instr.step,stack,Out.ok_bind,exec_nil]
 rfl

theorem target : run code input=.ok last 0 :=
 (run_append_ok ((run_append_ok entry).trans body_spec.2.1)).trans restore

/-- Reconstruct the saved caller words from the actual body frame and actual
final store. The caller scalar is nine, distinct from the argument two. -/
theorem caller_words : ∀ {t : LTy} (i : Idx Γ t), last.mem (cellOf 1 i)=input.mem (cellOf 1 i) := by
 intro t i
 have aliasWord := body_spec.2.2.2.2.2.2.2.1
 have exterior := body_spec.2.2.2.2.2.2.2.2.2
 cases i with
 | here => rfl
 | there i => cases i with
   | here => exact (upd_other bodyMachine.mem w[9] (by decide : (2:Nat)≠3)).trans aliasWord
   | there i => cases i with
     | here => exact (upd_other bodyMachine.mem w[9] (by decide : (1:Nat)≠3)).trans (exterior 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)))
     | there i => cases i

theorem represented : StateRepr 1 1 16 F output.st addresses last := by
 have restored := (body_spec.2.2.1.stack input.stack).setVal (.here : Idx (Parameters A) (.val .uint))
   (countValue 9 (by decide)) w[9] (ReprV.uint_of rfl)
 exact CallerReframe.reframe caller (bodyOut.st.setLocal .here (countValue 9 (by decide))) bodyOut.ext P.base addresses input last
   initial restored body_spec.2.2.2.2.1 caller_words
   (by intro R i;cases i with | there i => cases i with | there i => cases i with | there i => cases i)

theorem growth : GrowsAllocator 1 16 8 caller P.base input output.st addresses last := by
 intro cursor positive owned room
 have enteredOwned := (owned.stack (w[9]::input.stack)).localWrite 3 (by decide) (by decide) w[2]
 have done := body_spec.2.2.2.2.2.1 cursor (by decide) enteredOwned room
 exact (done.stack input.stack).localWrite 3 (by decide) (by decide) w[9]

theorem endpoint : call.run caller=.ok output ∧ run code input=.ok last 0 ∧
 StateRepr 1 1 16 F output.st addresses last ∧ last.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 8 caller P.base input output.st addresses last :=
 ⟨source,target,represented,rfl,body_spec.2.2.2.2.1,growth⟩


theorem capacity : AllocationInput 1 16 8 caller P.base input :=
 .inr ⟨by decide,⟨22,by decide⟩,ownership,by decide⟩

theorem returned_owner : StructAllocatorRepr output.st.heap addresses 16 (⟨30,by decide⟩ : Fin W) last :=
 growth ⟨22,by decide⟩ (by decide) ownership (by decide)

theorem source_contents : Heap.Keeps output.ext caller.heap output.st.heap := by
 have same : AllocatingReturn.Checks.output=bodyOut := Except.ok.inj (AllocatingReturn.Checks.specification.1.symm.trans body_spec.1)
 change Heap.Keeps bodyOut.ext callee.heap bodyOut.st.heap
 rw [← same]
 exact AllocatingReturn.Checks.source_fields.2

theorem facts :
 last.stack=[w[77]] ∧ last.mem 0=w[30] ∧ last.mem 1=w[16] ∧ last.mem 2=w[16] ∧ last.mem 3=w[9] ∧
 last.mem 7=w[10] ∧ last.mem 8=w[10] ∧ last.mem 9=w[99] ∧ last.mem 10=w[16] ∧ last.mem 11=w[2] ∧
 last.mem 12=w[16] ∧ last.mem 13=w[1] ∧ last.mem 16=w[2] ∧ last.mem 17=w[7] ∧ last.mem 18=w[9] ∧
 last.mem 20=w[1] ∧ last.mem 21=w[4] := by
 have exterior := body_spec.2.2.2.2.2.2.2.2.2
 have saved0 := body_spec.2.2.2.2.2.2.2.2.1 0 (by decide)
 have saved1 := body_spec.2.2.2.2.2.2.2.2.1 1 (by decide)
 have first := AllocatingPrefixes.old_array output.ext source_contents body_spec.2.2.2.2.1 represented.heap P.r0
 have other := AllocatingPrefixes.old_array output.ext source_contents body_spec.2.2.2.2.1 represented.heap Evm.Memory.CompileExamples.r1
 have firstLength := first.length
 have otherLength := other.length
 change last.mem 16=.val (wmod (callee.heap.len P.r0 .dyn)) at firstLength
 change last.mem 20=.val (wmod (callee.heap.len Evm.Memory.CompileExamples.r1 .dyn)) at otherLength
 rw [HeapDomain.Checks.length_zero] at firstLength
 rw [HeapDomain.Checks.length_one] at otherLength
 have seven : last.mem 17=w[7] := Restore.uint_unique
   (first.elements 0 (P.uint 7 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have nine : last.mem 18=w[9] := Restore.uint_unique
   (first.elements 1 (P.uint 9 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have four : last.mem 21=w[4] := Restore.uint_unique
   (other.elements 0 (P.uint 4 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 refine ⟨rfl,returned_owner.arrays.free.cell,caller_words (.there (.there .here)),caller_words (.there .here),rfl,?_,?_,?_,?_,?_,?_,?_,firstLength,seven,nine,otherLength,four⟩
 · exact (upd_other bodyMachine.mem w[9] (by decide : (7:Nat)≠3)).trans
     (exterior 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)))
 · exact (upd_other bodyMachine.mem w[9] (by decide : (8:Nat)≠3)).trans body_spec.2.2.2.2.2.2.1
 · exact (upd_other bodyMachine.mem w[9] (by decide : (9:Nat)≠3)).trans
     (exterior 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)))
 · exact (upd_other bodyMachine.mem w[9] (by decide : (10:Nat)≠3)).trans saved0.1
 · exact (upd_other bodyMachine.mem w[9] (by decide : (11:Nat)≠3)).trans saved0.2
 · exact (upd_other bodyMachine.mem w[9] (by decide : (12:Nat)≠3)).trans saved1.1
 · exact (upd_other bodyMachine.mem w[9] (by decide : (13:Nat)≠3)).trans saved1.2

theorem observations :
 (last.stack,[last.mem 0,last.mem 1,last.mem 2,last.mem 3,last.mem 7,last.mem 8,last.mem 9,last.mem 10,last.mem 11,
 last.mem 12,last.mem 13,last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21])=
 ([w[77]],[w[30],w[16],w[16],w[9],w[10],w[10],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 rcases facts with ⟨stack,cursor,alias,ref,scalar,bottom,pointer,marker,a,b,c,d,len,x,y,len2,z⟩
 rw [stack,cursor,alias,ref,scalar,bottom,pointer,marker,a,b,c,d,len,x,y,len2,z]

theorem wrong_argument : entered.mem 3≠w[9] := by decide

theorem wrong_restore : last.mem 3≠w[2] := by decide

theorem wrong_stack : last.stack≠[w[9],w[77]] := by decide

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarArgument

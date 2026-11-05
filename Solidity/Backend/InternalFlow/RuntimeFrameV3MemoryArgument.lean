import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarArgument

/-! Actual distinct memory argument marshalling with two stack-held caller
save words. This concrete allocating recursive client preserves typed identity;
it is not a general recursive compiler or approved-profile producer. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MemoryArgument
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes CountdownWitness
abbrev A : RefTy := CountdownWitness.A
abbrev Γ := CallerReframe.Checks.Γ
abbrev F := CallerReframe.Checks.F
def caller := (CallerReframe.Checks.caller.setLocal (.there (.there .here) : Idx Γ (.mem A)) (some Evm.Memory.CompileExamples.r1)).setLocal
 (.here : Idx Γ (.val .uint)) (countValue 9 (by decide))
def input := writeMachine (writeMachine CallerReframe.Checks.before 1 w[20]) 3 w[9]
def child := caller.withEnv (Δ:=Parameters A) (countValue 1 (by decide),(some Evm.Memory.CompileExamples.r1,()))
def entered := writeMachine (writeMachine {input with stack:=w[9]::w[16]::input.stack} 2 w[20]) 3 w[1]
def entryCode : List Instr := [.mload 2,.mload 3,.mload 1,.mstore 2,.push w[1],.mstore 3]

theorem initial : StateRepr 1 1 16 F caller P.base input :=
 (CallerReframe.Checks.initial.setMem (.there (.there .here)) Evm.Memory.CompileExamples.r1).setVal
 .here (countValue 9 (by decide)) w[9] (ReprV.uint_of rfl)

theorem ownership : StructAllocatorRepr caller.heap P.base 16 (⟨22,by decide⟩ : Fin W) input :=
 (CallerReframe.Checks.ownership.localWrite 1 (by decide) (by decide) w[20]).localWrite 3 (by decide) (by decide) w[9]

def args : Args P.C Γ (Parameters A) :=
 .snoc (.snocMemory .nil A (.user "alias") (.var (.there (.there .here)) rfl)) .uint (.user "count") (.simple (.lit 1 rfl))

theorem arguments : args.evalT caller=.ok child.env := by rfl

theorem memory_code : (compilePtr 1 (.var (.there (.there .here)) rfl : MPath P.C Γ (.ref A))).map (fun checked => checked.code)=some [.mload 1] := by rfl

theorem scalar_code : compileSimple 1 (C:=P.C) (.lit 1 rfl : Simple P.C Γ .uint)=[.push w[1]] := by rfl

theorem entry : run entryCode input=.ok entered 0 := by rfl

theorem callee_repr : StateRepr 1 2 16 CountdownWitness.F child P.base entered :=
 parameter_projection (tail:=[.mem A])
   ((((initial.push w[16]).push w[9]).setMem (.there .here) Evm.Memory.CompileExamples.r1).setVal
     .here (countValue 1 (by decide)) w[1] (ReprV.uint_of rfl))

theorem entered_owner : StructAllocatorRepr child.heap P.base 16 (⟨22,by decide⟩ : Fin W) entered :=
 ((ownership.stack (w[9]::w[16]::input.stack)).localWrite 2 (by decide) (by decide) w[20]).localWrite 3 (by decide) (by decide) w[1]

theorem read_bound : 1≤child.heap.len Evm.Memory.CompileExamples.r1 .dyn := by
 change 1≤CountdownWitness.callee.heap.len Evm.Memory.CompileExamples.r1 .dyn
 rw [HeapDomain.Checks.length_one]
 decide

theorem available :
 ∃ (out : Solidity.Out P.C child.H (Parameters A)) (m : Machine) (addresses : Nat → Fin W),
 (AllocatingActivation.body 2).run child=.ok out ∧ run (AllocatingReturn.image (C:=P.C) 2 CountdownWitness.F 8 7) entered=.ok m 0 ∧
 StateRepr 1 2 16 CountdownWitness.F out.st addresses m ∧ m.stack=entered.stack ∧
 BaseExtends child.H P.base addresses ∧ GrowsAllocator 2 16 4 child P.base entered out.st addresses m ∧
 m.mem 8=w[10] ∧ m.mem 2=entered.mem 2 ∧
 (∀ j,j<1 → m.mem (10+2*j)=entered.mem 2 ∧ m.mem (10+2*j+1)=.val (wmod (1-j))) ∧
 (∀ x,0<x → x<16 → x≠2 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 12≤x) → m.mem x=entered.mem x) :=
 AllocatingReturn.endpoint 1 (by decide) child Evm.Memory.CompileExamples.r1 rfl rfl read_bound P.base entered callee_repr
   ⟨22,by decide⟩ entered_owner (by decide) (by decide) 8 8 10 (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide) rfl 7 (by decide) (by decide) (by decide) rfl

noncomputable def bodyOut := available.choose
noncomputable def bodyMachine : Machine := available.choose_spec.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose_spec.choose

theorem body_spec :
 (AllocatingActivation.body 2).run child=.ok bodyOut ∧ run (AllocatingReturn.image (C:=P.C) 2 CountdownWitness.F 8 7) entered=.ok bodyMachine 0 ∧
 StateRepr 1 2 16 CountdownWitness.F bodyOut.st addresses bodyMachine ∧ bodyMachine.stack=entered.stack ∧
 BaseExtends child.H P.base addresses ∧ GrowsAllocator 2 16 4 child P.base entered bodyOut.st addresses bodyMachine ∧
 bodyMachine.mem 8=w[10] ∧ bodyMachine.mem 2=entered.mem 2 ∧
 (∀ j,j<1 → bodyMachine.mem (10+2*j)=entered.mem 2 ∧ bodyMachine.mem (10+2*j+1)=.val (wmod (1-j))) ∧
 (∀ x,0<x → x<16 → x≠2 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 12≤x) → bodyMachine.mem x=entered.mem x) :=
 available.choose_spec.choose_spec.choose_spec

noncomputable def output : Solidity.Out P.C caller.H Γ :=
 exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl caller child.env bodyOut
noncomputable def last : Machine := writeMachine (writeMachine {bodyMachine with stack:=input.stack} 3 w[9]) 2 w[16]
def call : Stmt P.C Γ Γ := InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step 2
def code : List Instr := entryCode ++ AllocatingReturn.image (C:=P.C) 2 CountdownWitness.F 8 7 ++ [.mstore 3,.mstore 2]

theorem source : call.run caller=.ok output :=
 call_return args .none .refl (AllocatingActivation.body 2).runR caller child.env arguments bodyOut body_spec.1

theorem restore : run [.mstore 3,.mstore 2] bodyMachine=.ok last 0 := by
 have stack : bodyMachine.stack=w[9]::w[16]::input.stack := body_spec.2.2.2.1
 simp only [run,exec_cons_zero,Instr.step,stack,Out.ok_bind,exec_nil]
 rfl

theorem target : run code input=.ok last 0 :=
 (run_append_ok ((run_append_ok entry).trans body_spec.2.1)).trans restore

theorem caller_words : ∀ {t : LTy} (i : Idx Γ t), last.mem (cellOf 1 i)=input.mem (cellOf 1 i) := by
 intro t i
 have exterior := body_spec.2.2.2.2.2.2.2.2.2
 cases i with
 | here => rfl
 | there i => cases i with
   | here => rfl
   | there i => cases i with
     | here =>
       have low := exterior 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
       exact (upd_other _ w[16] (by decide : (1:Nat)≠2)).trans ((upd_other _ w[9] (by decide : (1:Nat)≠3)).trans low)
     | there i => cases i

theorem represented : StateRepr 1 1 16 F output.st addresses last := by
 have pointer : addresses P.r0.id=P.base P.r0.id := body_spec.2.2.2.2.1 P.r0
 have restored := ((body_spec.2.2.1.stack input.stack).setVal (.here : Idx (Parameters A) (.val .uint))
   (countValue 9 (by decide)) w[9] (ReprV.uint_of rfl)).setMem (.there .here) (P.r0.wk bodyOut.ext)
 change StateRepr 1 2 16 CountdownWitness.F
   ((bodyOut.st.setLocal .here (countValue 9 (by decide))).setLocal (.there .here) (some (P.r0.wk bodyOut.ext))) addresses
   (writeMachine (writeMachine {bodyMachine with stack:=input.stack} 3 w[9]) 2 (.val (addresses P.r0.id))) at restored
 rw [pointer] at restored
 exact CallerReframe.reframe caller ((bodyOut.st.setLocal .here (countValue 9 (by decide))).setLocal (.there .here) (some (P.r0.wk bodyOut.ext))) bodyOut.ext P.base addresses input last initial restored
   body_spec.2.2.2.2.1 caller_words
   (by intro R i;cases i with | there i => cases i with | there i => cases i with | there i => cases i)

theorem growth : GrowsAllocator 1 16 4 caller P.base input output.st addresses last := by
 intro cursor positive owned room
 have enteredOwned := ((owned.stack (w[9]::w[16]::input.stack)).localWrite 2 (by decide) (by decide) w[20]).localWrite 3 (by decide) (by decide) w[1]
 have done := body_spec.2.2.2.2.2.1 cursor (by decide) enteredOwned room
 exact ((done.stack input.stack).localWrite 3 (by decide) (by decide) w[9]).localWrite 2 (by decide) (by decide) w[16]

theorem capacity : AllocationInput 1 16 4 caller P.base input := .inr ⟨by decide,⟨22,by decide⟩,ownership,by decide⟩
theorem returned_owner : StructAllocatorRepr output.st.heap addresses 16 (⟨26,by decide⟩ : Fin W) last :=
 growth ⟨22,by decide⟩ (by decide) ownership (by decide)

theorem endpoint : call.run caller=.ok output ∧ run code input=.ok last 0 ∧
 StateRepr 1 1 16 F output.st addresses last ∧ last.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 4 caller P.base input output.st addresses last :=
 ⟨source,target,represented,rfl,body_spec.2.2.2.2.1,growth⟩


theorem source_contents : Heap.Keeps output.ext caller.heap output.st.heap := by
 obtain ⟨known,actual,size,locals,kept⟩ := AllocatingSource.success 2 child 1 (by decide) Evm.Memory.CompileExamples.r1 rfl rfl read_bound (by decide)
 have same : known=bodyOut := Except.ok.inj (actual.symm.trans body_spec.1)
 change Heap.Keeps bodyOut.ext child.heap bodyOut.st.heap
 rw [← same]
 exact kept

theorem selected_value : ArrayProbe.value.evalT child=.ok (P.uint 4 (by decide)) := by with_unfolding_all rfl

theorem selected_target : run (ArrayProbe.selected (C:=P.C) 2 CountdownWitness.F).code entered=.ok (entered.push w[4]) 0 :=
 ArrayProbe.read_success callee_repr _ _ selected_value (ReprV.uint_of rfl)

theorem source_aliases :
 TEnv.get (.there .here : Idx Γ (.mem A)) output.st.env=some (P.r0.wk output.ext) ∧
 TEnv.get (.there (.there .here) : Idx Γ (.mem A)) output.st.env=some (Evm.Memory.CompileExamples.r1.wk output.ext) := by constructor <;> rfl

theorem facts :
 last.stack=[w[77]] ∧ last.mem 0=w[26] ∧ last.mem 1=w[20] ∧ last.mem 2=w[16] ∧ last.mem 3=w[9] ∧
 last.mem 7=w[10] ∧ last.mem 8=w[10] ∧ last.mem 9=w[99] ∧ last.mem 10=w[20] ∧ last.mem 11=w[1] ∧
 last.mem 16=w[2] ∧ last.mem 17=w[7] ∧ last.mem 18=w[9] ∧ last.mem 20=w[1] ∧ last.mem 21=w[4] := by
 have exterior := body_spec.2.2.2.2.2.2.2.2.2
 have saved := body_spec.2.2.2.2.2.2.2.2.1 0 (by decide)
 have low (x : Nat) (ne2 : x≠2) (ne3 : x≠3) : last.mem x=bodyMachine.mem x :=
   (upd_other _ w[16] ne2).trans (upd_other _ w[9] ne3)
 have first := AllocatingPrefixes.old_array output.ext source_contents body_spec.2.2.2.2.1 represented.heap P.r0
 have other := AllocatingPrefixes.old_array output.ext source_contents body_spec.2.2.2.2.1 represented.heap Evm.Memory.CompileExamples.r1
 have firstLength := first.length
 have otherLength := other.length
 change last.mem 16=.val (wmod (CountdownWitness.callee.heap.len P.r0 .dyn)) at firstLength
 change last.mem 20=.val (wmod (CountdownWitness.callee.heap.len Evm.Memory.CompileExamples.r1 .dyn)) at otherLength
 rw [HeapDomain.Checks.length_zero] at firstLength
 rw [HeapDomain.Checks.length_one] at otherLength
 have seven : last.mem 17=w[7] := Restore.uint_unique (first.elements 0 (P.uint 7 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have nine : last.mem 18=w[9] := Restore.uint_unique (first.elements 1 (P.uint 9 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have four : last.mem 21=w[4] := Restore.uint_unique (other.elements 0 (P.uint 4 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 refine ⟨rfl,returned_owner.arrays.free.cell,caller_words (.there (.there .here)),rfl,rfl,?_,?_,?_,?_,?_,firstLength,seven,nine,otherLength,four⟩
 · exact (low 7 (by decide) (by decide)).trans (exterior 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)))
 · exact (low 8 (by decide) (by decide)).trans body_spec.2.2.2.2.2.2.1
 · exact (low 9 (by decide) (by decide)).trans (exterior 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)))
 · exact (low 10 (by decide) (by decide)).trans saved.1
 · exact (low 11 (by decide) (by decide)).trans saved.2

theorem observations :
 (last.stack,[last.mem 0,last.mem 1,last.mem 2,last.mem 3,last.mem 7,last.mem 8,last.mem 9,last.mem 10,last.mem 11,last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21])=
 ([w[77]],[w[26],w[20],w[16],w[9],w[10],w[10],w[99],w[20],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 rcases facts with ⟨stack,cursor,older,ref,scalar,bottom,pointer,marker,a,b,len,x,y,len2,z⟩
 rw [stack,cursor,older,ref,scalar,bottom,pointer,marker,a,b,len,x,y,len2,z]

theorem wrong_argument : entered.mem 2≠w[16] := by decide

theorem wrong_restore : last.mem 2≠w[20] := by decide

theorem lost_distinct : last.mem 1≠w[16] := by
 have word : last.mem 1=w[20] := caller_words (.there (.there .here))
 rw [word]
 decide

theorem wrong_stack : last.stack≠[w[9],w[16],w[77]] := by decide

theorem wrong_cost : ¬GrowsAllocator 1 16 8 caller P.base input output.st addresses last := by
 intro bad
 have cursor := (bad ⟨22,by decide⟩ (by decide) ownership (by decide)).arrays.free.cell
 rw [facts.2.1] at cursor
 exact (by decide : (w[26] : Word)≠w[30]) cursor

end Solidity.Backend.InternalFlow.RuntimeFrame.MemoryArgument

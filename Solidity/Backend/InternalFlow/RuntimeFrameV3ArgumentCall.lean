import Solidity.Backend.InternalFlow.RuntimeFrameV3ArgumentEntry

/-! Composition of actual public argument compilation with the source-coupled
allocating recursive image. Reached capacity and caller frames are derived;
no midpoint, body simulation, rollback or general compiler claim is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ArgumentCall
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes CountdownWitness
abbrev A : RefTy := CountdownWitness.A
abbrev Γ := MemoryArgument.Γ
abbrev F := MemoryArgument.F
abbrev caller := MemoryArgument.caller
abbrev input := MemoryArgument.input
abbrev child := MemoryArgument.child
abbrev prefixMachine := ArgumentEntry.Checks.target
noncomputable abbrev prefixAddresses := ArgumentEntry.Checks.addresses

theorem total_capacity : AllocationInput 1 16 (ArgumentEntry.Checks.checked.cost caller+4) caller P.base input :=
 .inr ⟨by decide,⟨22,by decide⟩,MemoryArgument.ownership,by rw [ArgumentEntry.Checks.cost_zero];decide⟩

/-- Capacity comes from the actual prefix growth, not an asserted midpoint. -/
theorem reached_capacity : AllocationInput 4 16 4 child prefixAddresses prefixMachine := by
 have next := ArgumentEntry.Checks.specification.2.2.2.2.nextInput total_capacity
 rcases next with zero | ⟨positive,cursor,owned,room⟩
 · exact .inl zero
 · exact .inr ⟨by decide,cursor,owned,room⟩

theorem prefix_scratch : Footprint.Words 6 16 input prefixMachine :=
 ArgumentEntry.Checks.safe MemoryArgument.initial
   (by change 1+ArgumentEntry.Checks.checked.need≤6;rw [ArgumentEntry.Checks.need_eq];decide)
   (by decide) ArgumentEntry.Checks.capacity ArgumentEntry.Checks.target_run

theorem reached_cursor : prefixMachine.mem 8=w[10] := (prefix_scratch 8 (by decide) (by decide)).trans rfl

theorem reached_bottom : prefixMachine.mem 7=w[10] := (prefix_scratch 7 (by decide) (by decide)).trans rfl

theorem available :
 ∃ (out : Solidity.Out P.C child.H (Parameters A)) (m : Machine) (addresses : Nat → Fin W),
 (AllocatingActivation.body 2).run child=.ok out ∧ run (AllocatingReturn.image (C:=P.C) 4 CountdownWitness.F 8 7) prefixMachine=.ok m 0 ∧
 StateRepr 1 4 16 CountdownWitness.F out.st addresses m ∧ m.stack=prefixMachine.stack ∧
 BaseExtends child.H prefixAddresses addresses ∧ GrowsAllocator 4 16 4 child prefixAddresses prefixMachine out.st addresses m ∧
 m.mem 8=w[10] ∧ m.mem 4=prefixMachine.mem 4 ∧
 (∀ j,j<1 → m.mem (10+2*j)=prefixMachine.mem 4 ∧ m.mem (10+2*j+1)=.val (wmod (1-j))) ∧
 (∀ x,0<x → x<16 → x≠4 → x≠5 → x≠6 → x≠8 → (x<10 ∨ 12≤x) → m.mem x=prefixMachine.mem x) := by
 rcases reached_capacity with zero | ⟨positive,cursor,owned,room⟩
 · omega
 · exact AllocatingReturn.endpoint 1 (by decide) child Evm.Memory.CompileExamples.r1 rfl rfl MemoryArgument.read_bound
     prefixAddresses prefixMachine ArgumentEntry.Checks.parameter_frame cursor owned (by decide) room 8 8 10
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) reached_cursor 7
     (by decide) (by decide) (by decide) reached_bottom

noncomputable def bodyOut := available.choose
noncomputable def last : Machine := available.choose_spec.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose_spec.choose

theorem body_spec :
 (AllocatingActivation.body 2).run child=.ok bodyOut ∧ run (AllocatingReturn.image (C:=P.C) 4 CountdownWitness.F 8 7) prefixMachine=.ok last 0 ∧
 StateRepr 1 4 16 CountdownWitness.F bodyOut.st addresses last ∧ last.stack=prefixMachine.stack ∧
 BaseExtends child.H prefixAddresses addresses ∧ GrowsAllocator 4 16 4 child prefixAddresses prefixMachine bodyOut.st addresses last ∧
 last.mem 8=w[10] ∧ last.mem 4=prefixMachine.mem 4 ∧
 (∀ j,j<1 → last.mem (10+2*j)=prefixMachine.mem 4 ∧ last.mem (10+2*j+1)=.val (wmod (1-j))) ∧
 (∀ x,0<x → x<16 → x≠4 → x≠5 → x≠6 → x≠8 → (x<10 ∨ 12≤x) → last.mem x=prefixMachine.mem x) :=
 available.choose_spec.choose_spec.choose_spec

noncomputable def output : Solidity.Out P.C caller.H Γ :=
 exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl caller child.env bodyOut

def call : Stmt P.C Γ Γ := InterfaceV1.recursiveSource "allocatingCountdown" MemoryArgument.args .none AllocatingActivation.step 2
def code : List Instr := ArgumentEntry.Checks.checked.code ++ AllocatingReturn.image (C:=P.C) 4 CountdownWitness.F 8 7

theorem entry_agreement :
 ((CallRet.none : CallRet Γ [] Γ).enterT (caller.withEnv child.env)).st=child := by rfl

theorem source : call.run caller=.ok output :=
 call_return MemoryArgument.args .none .refl (AllocatingActivation.body 2).runR caller child.env MemoryArgument.arguments bodyOut body_spec.1

theorem target : run code input=.ok last 0 :=
 (run_append_ok ArgumentEntry.Checks.target_run).trans body_spec.2.1

theorem caller_fragment : ArgumentEntry.Checks.checked.frag.restrict Γ=F := by rfl

theorem caller_words : ∀ {t : LTy} (i : Idx Γ t), last.mem (cellOf 1 i)=prefixMachine.mem (cellOf 1 i) := by
 intro t i
 have exterior := body_spec.2.2.2.2.2.2.2.2.2
 cases i with
 | here => exact exterior 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
 | there i => cases i with
   | here => exact exterior 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
   | there i => cases i with
     | here => exact exterior 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
     | there i => cases i

theorem represented : StateRepr 1 1 16 F output.st addresses last := by
 have initial := ArgumentEntry.Checks.specification.2.1
 rw [caller_fragment] at initial
 exact CallerReframe.reframe caller bodyOut.st bodyOut.ext prefixAddresses addresses prefixMachine last initial
   body_spec.2.2.1 body_spec.2.2.2.2.1 caller_words
   (by intro R i;cases i with | there i => cases i with | there i => cases i with | there i => cases i)

theorem extended : BaseExtends caller.H P.base addresses :=
 BaseExtends.trans (List.prefix_refl caller.H) ArgumentEntry.Checks.specification.2.2.2.1 body_spec.2.2.2.2.1

/-- Compose real prefix growth with the actual reached body growth. -/
theorem growth : GrowsAllocator 1 16 4 caller P.base input output.st addresses last := by
 intro cursor positive owned room
 have prefixOwner := ArgumentEntry.Checks.specification.2.2.2.2 cursor positive owned
   (by rw [ArgumentEntry.Checks.cost_zero];omega)
 have reached : StructAllocatorRepr child.heap prefixAddresses 16 cursor prefixMachine := by
   simpa only [ArgumentEntry.Checks.cost_zero,Nat.add_zero] using prefixOwner
 exact body_spec.2.2.2.2.2.1 cursor (by decide) reached room

theorem returned_owner : StructAllocatorRepr output.st.heap addresses 16 (⟨26,by decide⟩ : Fin W) last :=
 growth ⟨22,by decide⟩ (by decide) MemoryArgument.ownership (by decide)

theorem endpoint : call.run caller=.ok output ∧ run code input=.ok last 0 ∧
 StateRepr 1 1 16 F output.st addresses last ∧ last.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 4 caller P.base input output.st addresses last :=
 ⟨source,target,represented,body_spec.2.2.2.1.trans ArgumentEntry.Checks.specification.2.2.1,extended,growth⟩


theorem body_fields : bodyOut.st.env=TEnv.wk bodyOut.ext (Parameters A) child.env ∧
 Heap.Keeps bodyOut.ext child.heap bodyOut.st.heap := by
 obtain ⟨known,actual,size,locals,kept⟩ := AllocatingSource.success 2 child 1 (by decide) Evm.Memory.CompileExamples.r1 rfl rfl MemoryArgument.read_bound (by decide)
 have same : known=bodyOut := Except.ok.inj (actual.symm.trans body_spec.1)
 cases same
 exact ⟨locals,kept⟩

theorem source_contents : Heap.Keeps output.ext caller.heap output.st.heap := by
 change Heap.Keeps bodyOut.ext child.heap bodyOut.st.heap
 exact body_fields.2

theorem source_aliases :
 TEnv.get (.there .here : Idx Γ (.mem A)) output.st.env=some (P.r0.wk output.ext) ∧
 TEnv.get (.there (.there .here) : Idx Γ (.mem A)) output.st.env=some (Evm.Memory.CompileExamples.r1.wk output.ext) := by constructor <;> rfl

theorem facts :
 last.stack=[w[77]] ∧ last.mem 0=w[26] ∧ last.mem 1=w[20] ∧ last.mem 2=w[16] ∧ last.mem 3=w[9] ∧
 last.mem 4=w[20] ∧ last.mem 5=w[1] ∧ last.mem 7=w[10] ∧ last.mem 8=w[10] ∧ last.mem 9=w[99] ∧
 last.mem 10=w[20] ∧ last.mem 11=w[1] ∧ last.mem 12=w[0] ∧ last.mem 13=w[0] ∧
 last.mem 16=w[2] ∧ last.mem 17=w[7] ∧ last.mem 18=w[9] ∧ last.mem 20=w[1] ∧ last.mem 21=w[4] := by
 have exterior := body_spec.2.2.2.2.2.2.2.2.2
 have saved := body_spec.2.2.2.2.2.2.2.2.1 0 (by decide)
 have count : TEnv.get (.here : Idx (Parameters A) (.val .uint)) bodyOut.st.env=countValue 1 (by decide) := by
   rw [body_fields.1]
   rfl
 have counterWord : last.mem 5=w[1] := RecursiveHistory.counter_word bodyOut.st 1 (by decide) count addresses last body_spec.2.2.1
 have first := AllocatingPrefixes.old_array output.ext source_contents extended represented.heap P.r0
 have other := AllocatingPrefixes.old_array output.ext source_contents extended represented.heap Evm.Memory.CompileExamples.r1
 have firstLength := first.length
 have otherLength := other.length
 change last.mem 16=.val (wmod (CountdownWitness.callee.heap.len P.r0 .dyn)) at firstLength
 change last.mem 20=.val (wmod (CountdownWitness.callee.heap.len Evm.Memory.CompileExamples.r1 .dyn)) at otherLength
 rw [HeapDomain.Checks.length_zero] at firstLength
 rw [HeapDomain.Checks.length_one] at otherLength
 have seven : last.mem 17=w[7] := Restore.uint_unique (first.elements 0 (P.uint 7 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have nine : last.mem 18=w[9] := Restore.uint_unique (first.elements 1 (P.uint 9 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have four : last.mem 21=w[4] := Restore.uint_unique (other.elements 0 (P.uint 4 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 refine ⟨body_spec.2.2.2.1,returned_owner.arrays.free.cell,caller_words (.there (.there .here)),caller_words (.there .here),caller_words .here,
   body_spec.2.2.2.2.2.2.2.1,counterWord,?_,body_spec.2.2.2.2.2.2.1,?_,saved.1,saved.2,?_,?_,firstLength,seven,nine,otherLength,four⟩
 · exact exterior 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
 · exact exterior 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
 · exact exterior 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))
 · exact exterior 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))

theorem observations :
 (last.stack,[last.mem 0,last.mem 1,last.mem 2,last.mem 3,last.mem 4,last.mem 5,last.mem 7,last.mem 8,last.mem 9,
 last.mem 10,last.mem 11,last.mem 12,last.mem 13,last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21])=
 ([w[77]],[w[26],w[20],w[16],w[9],w[20],w[1],w[10],w[10],w[99],w[20],w[1],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]) := by
 rcases facts with ⟨stack,cursor,older,ref,scalar,param,count,bottom,pointer,marker,a,b,c,d,len,x,y,len2,z⟩
 rw [stack,cursor,older,ref,scalar,param,count,bottom,pointer,marker,a,b,c,d,len,x,y,len2,z]

theorem wrong_caller_alias : last.mem 2≠w[20] := by
 have word : last.mem 2=w[16] := caller_words (.there .here)
 rw [word]
 decide

theorem wrong_parameter_alias : last.mem 4≠w[16] := by
 have word : last.mem 4=w[20] := body_spec.2.2.2.2.2.2.2.1
 rw [word]
 decide

theorem wrong_cost : ¬GrowsAllocator 1 16 8 caller P.base input output.st addresses last := by
 intro bad
 have cursor := (bad ⟨22,by decide⟩ (by decide) MemoryArgument.ownership (by decide)).arrays.free.cell
 rw [facts.2.1] at cursor
 exact (by decide : (w[26] : Word)≠w[30]) cursor

theorem omitted_allocation : last.mem 0≠w[22] := by
 rw [facts.2.1]
 decide

theorem shallow :
 (InterfaceV1.recursiveSource "allocatingCountdown" MemoryArgument.args .none AllocatingActivation.step 1).run caller=.error .exhausted :=
 AllocatingSource.call_exhaustion "allocatingCountdown" MemoryArgument.args 1 caller 1 (by decide) Evm.Memory.CompileExamples.r1
   MemoryArgument.arguments MemoryArgument.read_bound (by decide)


theorem shallow_unmatched :
 ¬GrowingResult 1 1 16 4 F caller P.base input
   ((InterfaceV1.recursiveSource "allocatingCountdown" MemoryArgument.args .none AllocatingActivation.step 1).run caller)
   (run code input) := by
 rw [shallow]
 intro same
 rcases same with ⟨out,m,base,source,rest⟩ | ⟨source,rest⟩
 · cases source
 · cases source

def badCall : Stmt P.C Γ Γ := InterfaceV1.recursiveSource "allocatingCountdown" ArgumentEntry.Checks.badArgs .none AllocatingActivation.step 2
def badCode : List Instr := ArgumentEntry.Checks.badChecked.code ++ AllocatingReturn.image (C:=P.C) 4 CountdownWitness.F 8 7

theorem bad_source : badCall.run caller=.error .revert := by
 change TRun.call ArgumentEntry.Checks.badArgs .none .refl (AllocatingActivation.body 2).runR caller=_
 simp only [TRun.call,ArgumentEntry.Checks.bad_evaluated,error_bind]

theorem bad_target : run badCode input=.revert := ArgumentEntry.Checks.bad_suffix _

theorem bad_not_fault : run badCode input≠.fault := by
 rw [bad_target]
 intro wrong
 cases wrong


/-- Every sufficient source quotation agrees with the actual output already
represented by this one fixed target image. -/
theorem source_all (depth : Nat) (enough : 1<depth) :
 (InterfaceV1.recursiveSource "allocatingCountdown" MemoryArgument.args .none AllocatingActivation.step depth).run caller=.ok output := by
 obtain ⟨known,executed,size,locals,kept⟩ := AllocatingSource.success depth child 1 (by decide) Evm.Memory.CompileExamples.r1 rfl rfl MemoryArgument.read_bound enough
 have same : known=bodyOut := AllocatingCoherence.bodies depth 2 child known bodyOut executed body_spec.1
 rw [same] at executed
 exact call_return MemoryArgument.args .none .refl (AllocatingActivation.body depth).runR caller child.env MemoryArgument.arguments bodyOut executed

/-- Insufficient source quotation remains exhausted, with no successful
failed state or claim that target success implements exhaustion. -/
theorem source_indices (depth : Nat) :
 (InterfaceV1.recursiveSource "allocatingCountdown" MemoryArgument.args .none AllocatingActivation.step depth).run caller=
 if 1<depth then .ok output else .error .exhausted := by
 by_cases enough : 1<depth
 · simpa only [if_pos enough] using source_all depth enough
 · simpa only [if_neg enough] using AllocatingSource.call_exhaustion "allocatingCountdown" MemoryArgument.args depth caller 1
     (by decide) Evm.Memory.CompileExamples.r1 MemoryArgument.arguments MemoryArgument.read_bound (by omega)

theorem indexed_endpoint (depth : Nat) (enough : 1<depth) :
 (InterfaceV1.recursiveSource "allocatingCountdown" MemoryArgument.args .none AllocatingActivation.step depth).run caller=.ok output ∧
 run code input=.ok last 0 ∧ StateRepr 1 1 16 F output.st addresses last :=
 ⟨source_all depth enough,target,represented⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ArgumentCall

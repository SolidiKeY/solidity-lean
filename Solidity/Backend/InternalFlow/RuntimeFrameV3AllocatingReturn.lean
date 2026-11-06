import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingHistory

/-! Matched allocating countdown returns from actual source continuation,
derived saved-parent history and the existing checked paired unwind. This is
not public recursive compiler or approved-domain coverage. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingReturn
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

def image {C : Contract} (b : Nat) (F : Frag (Parameters A)) (pointer bottom : Nat) : List Instr :=
 [.loop (guardCompiled (C:=C) b F).code (AllocatingActivation.code (C:=C) b F pointer)] ++ PairedUnwind.code b pointer bottom A

theorem endpoint {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (count : Nat) (bound : count<W)
 (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor before)
 (positive : 0<b) (heapSpace : cursor.val+4*count<W)
 (lo pointer start : Nat) (localBound : b+2<lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) (bottom : Nat) (bottomAbove : b+2<bottom) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (bottomValue : before.mem bottom=.val (wmod start)) :
 ∃ (out : Solidity.Out C σ.H (Parameters A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingActivation.body (count+1)).run σ=.ok out ∧ run (image (C:=C) b F pointer bottom) before=.ok last 0 ∧
 StateRepr L b frame F out.st addresses last ∧ last.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator b frame (4*count) σ base before out.st addresses last ∧
 last.mem pointer=.val (wmod start) ∧ last.mem b=before.mem b ∧
 (∀ j,j<count → last.mem (start+2*j)=before.mem b ∧ last.mem (start+2*j+1)=.val (wmod (count-j))) ∧
 (∀ x,0<x → x<frame → x≠b → x≠b+1 → x≠b+2 → x≠pointer →
   (x<start ∨ start+2*count≤x) → last.mem x=before.mem x) := by
 obtain ⟨τ,e,down,addresses,running,reprDown,env,size,kept,stack,extended,growth,owned,currentDown,resume⟩ :=
   AllocatingResume.coupled count count (by omega) bound σ ref counter alias reads base before repr cursor owner positive heapSpace
     lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current
 have zeroEnv : τ.env=(countValue 0 W_pos,(some (ref.wk e),())) := by simpa only [Nat.sub_self] using env
 have zeroCounter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [zeroEnv];rfl
 let returned : Solidity.Out C σ.H (Parameters A) := AllocatingResume.reexport σ e ⟨τ,List.prefix_refl _⟩
 have source : (AllocatingActivation.body (count+1)).run σ=.ok returned :=
   AllocatingResume.finish σ τ e count zeroCounter resume
 have callerEnv : σ.env=(countValue count bound,(some ref,())) :=
   Prod.ext counter (Prod.ext alias (by cases σ.env.2.2;rfl))
 have returnEnv : returned.st.env=(countValue count bound,(some (ref.wk e),())) := by
   change TEnv.wk e (Parameters A) σ.env=_
   rw [callerEnv]
   rfl
 have zeroAt : ParentPrefixes.sourceAt returned.st 0 W_pos=τ := by
   change τ.withEnv (Δ:=Parameters A) (countValue 0 W_pos,(TEnv.wk e (Parameters A) σ.env).2)=τ
   have data : (countValue 0 W_pos,(TEnv.wk e (Parameters A) σ.env).2)=τ.env := by
     rw [callerEnv]
     exact zeroEnv.symm
   exact (congrArg (fun locals => τ.withEnv (Δ:=Parameters A) locals) data).trans rfl
 have fullAt : ParentPrefixes.sourceAt returned.st count bound=returned.st := by
   change returned.st.withEnv (Δ:=Parameters A) (countValue count bound,returned.st.env.2)=returned.st
   have data : (countValue count bound,returned.st.env.2)=returned.st.env := by rw [returnEnv]
   exact (congrArg (fun locals => returned.st.withEnv (Δ:=Parameters A) locals) data).trans rfl
 have parentInput : StateRepr L b frame F (ParentPrefixes.sourceAt returned.st (count-count) (by omega)) addresses down := by
   simpa only [Nat.sub_self,zeroAt] using reprDown
 obtain ⟨saved,exterior,reference⟩ :=
   AllocatingHistory.history count count (by omega) bound σ ref counter alias reads base before repr cursor owner positive heapSpace
     lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current down running
 have savedHere : ∀ j,j<count → down.mem (start+2*j)=down.mem b ∧
     down.mem (start+2*j+1)=.val (wmod (count-j)) := by
   intro j small
   exact ⟨(saved j small).1.trans reference.symm,(saved j small).2⟩
 have bottomDown : down.mem bottom=.val (wmod start) :=
   (exterior bottom (by omega) (by omega) (by omega) (by omega) bottomSeparate (.inl bottomBefore)).trans bottomValue
 obtain ⟨last,unwinding,parentRepr,unwindStack,unwindCursor,unwindRef,unwindGrowth,high,outside⟩ :=
   ParentPrefixes.running_prefix returned.st addresses count count count (by omega) (by omega) bound down parentInput
     lo pointer bottom start (by omega) pointerAbove pointerBelow payloadAbove pointerBefore
     (by omega) bottomBefore bottomSeparate fits currentDown bottomDown savedHere
 have finalRepr : StateRepr L b frame F returned.st addresses last := by
   simpa only [Nat.sub_self,Nat.zero_add,fullAt] using parentRepr
 have finalGrowth : GrowsAllocator b frame 0 τ addresses down returned.st addresses last := by
   simpa only [Nat.sub_self,Nat.zero_add,zeroAt,fullAt] using unwindGrowth
 have finalCursor : last.mem pointer=.val (wmod start) := by
   simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using unwindCursor
 have finalBottom : last.mem bottom=.val (wmod start) :=
   (outside bottom bottomSeparate (by omega) (by omega)).trans bottomDown
 have finished := ParentStop.stop_after_running unwinding finalCursor finalBottom
 have restoreRun := PairedUnwind.run_of_stopped finished
 have guard := guard_run τ 0 W_pos zeroCounter addresses down reprDown
 have stopped := GuardedPrefixes.finish_prefix _ _ count _ _ _ running
   (empty_turn _ (run (AllocatingActivation.code (C:=C) b F pointer)) _ guard)
 have descent := successful_loop _ _ _ _ _ stopped
 have combined := growth.comp finalGrowth
 refine ⟨returned,last,addresses,source,(run_append_ok descent).trans restoreRun,finalRepr,
   unwindStack.trans stack,extended,?_,finalCursor,unwindRef.trans reference,?_,?_⟩
 · simpa only [Nat.add_zero] using combined
 · intro j small
   exact ⟨(outside _ (by omega) (by omega) (by omega)).trans (saved j small).1,
     (outside _ (by omega) (by omega) (by omega)).trans (saved j small).2⟩
 · intro x hp hf hr hc ht hx ho
   exact (outside x hx hr hc).trans (exterior x hp hf hc ht hx ho)

/-- A genuine matched growing result, not a supplied simulation field. -/
theorem growing_result {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (count : Nat) (bound : count<W)
 (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor before)
 (positive : 0<b) (heapSpace : cursor.val+4*count<W)
 (lo pointer start : Nat) (localBound : b+2<lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) (bottom : Nat) (bottomAbove : b+2<bottom) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (bottomValue : before.mem bottom=.val (wmod start)) :
 GrowingResult L b frame (4*count) F σ base before ((AllocatingActivation.body (count+1)).run σ)
   (run (image (C:=C) b F pointer bottom) before) := by
 obtain ⟨out,last,addresses,source,target,represented,stack,extended,growth,rest⟩ :=
   endpoint count bound σ ref counter alias reads base before repr cursor owner positive heapSpace lo pointer start localBound
     pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current bottom bottomAbove bottomBefore bottomSeparate bottomValue
 exact .inl ⟨out,last,addresses,source,target,represented,stack,extended,growth⟩

namespace Checks
open CountdownWitness

theorem available :
 ∃ (out : Solidity.Out P.C callee.H (Parameters CountdownWitness.A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingActivation.body 3).run callee=.ok out ∧ run (image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧ last.stack=ParentPrefixes.Checks.input.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input out.st addresses last ∧
 last.mem 8=w[10] ∧ last.mem 2=ParentPrefixes.Checks.input.mem 2 ∧
 (∀ j,j<2 → last.mem (10+2*j)=ParentPrefixes.Checks.input.mem 2 ∧ last.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 (∀ x,0<x → x<16 → x≠2 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 14≤x) → last.mem x=ParentPrefixes.Checks.input.mem x) :=
 endpoint 2 (by decide) callee P.r0 rfl rfl AllocatingSource.Checks.read_bound
   P.base ParentPrefixes.Checks.input ParentPrefixes.Checks.initial ⟨22,by decide⟩ ParentPrefixes.Checks.ownership
   (by decide) (by decide) 8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) rfl 7 (by decide) (by decide) (by decide) rfl

noncomputable def output := available.choose
noncomputable def machine : Machine := available.choose_spec.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose_spec.choose

theorem specification :
 (AllocatingActivation.body 3).run callee=.ok output ∧ run (image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input=.ok machine 0 ∧
 StateRepr 1 2 16 F output.st addresses machine ∧ machine.stack=ParentPrefixes.Checks.input.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input output.st addresses machine ∧
 machine.mem 8=w[10] ∧ machine.mem 2=ParentPrefixes.Checks.input.mem 2 ∧
 (∀ j,j<2 → machine.mem (10+2*j)=ParentPrefixes.Checks.input.mem 2 ∧ machine.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 (∀ x,0<x → x<16 → x≠2 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 14≤x) → machine.mem x=ParentPrefixes.Checks.input.mem x) :=
 available.choose_spec.choose_spec.choose_spec

theorem source_fields : output.st.env=TEnv.wk output.ext (Parameters CountdownWitness.A) callee.env ∧
 Heap.Keeps output.ext callee.heap output.st.heap := by
 obtain ⟨known,actual,size,locals,kept⟩ := AllocatingSource.success 3 callee 2 (by decide) P.r0 rfl rfl
   AllocatingSource.Checks.read_bound (by decide)
 have same : known=output := Except.ok.inj (actual.symm.trans specification.1)
 rw [same] at locals kept
 exact ⟨locals,kept⟩

theorem facts :
 machine.stack=[w[77]] ∧ machine.mem 0=w[30] ∧ machine.mem 1=w[16] ∧ machine.mem 2=w[16] ∧
 machine.mem 3=w[2] ∧ machine.mem 7=w[10] ∧ machine.mem 8=w[10] ∧ machine.mem 9=w[99] ∧
 machine.mem 10=w[16] ∧ machine.mem 11=w[2] ∧ machine.mem 12=w[16] ∧ machine.mem 13=w[1] ∧
 machine.mem 16=w[2] ∧ machine.mem 17=w[7] ∧ machine.mem 18=w[9] ∧ machine.mem 20=w[1] ∧ machine.mem 21=w[4] := by
 rcases specification with ⟨source,target,repr,stack,extended,growth,cursor,reference,saved,exterior⟩
 have owned := growth ⟨22,by decide⟩ (by decide) ParentPrefixes.Checks.ownership (by decide)
 have freeWord : machine.mem 0=w[30] := owned.arrays.free.cell
 have counter : TEnv.get (.here : Idx (Parameters CountdownWitness.A) (.val .uint)) output.st.env=countValue 2 (by decide) := by
   rw [source_fields.1]
   rfl
 have counterWord : machine.mem 3=w[2] := RecursiveHistory.counter_word output.st 2 (by decide) counter addresses machine repr
 have first := AllocatingPrefixes.old_array output.ext source_fields.2 extended repr.heap P.r0
 have other := AllocatingPrefixes.old_array output.ext source_fields.2 extended repr.heap Evm.Memory.CompileExamples.r1
 have firstLength := first.length
 have otherLength := other.length
 rw [HeapDomain.Checks.length_zero] at firstLength
 rw [HeapDomain.Checks.length_one] at otherLength
 have word7 : machine.mem 17=w[7] := Restore.uint_unique
   (first.elements 0 (P.uint 7 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have word9 : machine.mem 18=w[9] := Restore.uint_unique
   (first.elements 1 (P.uint 9 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have word4 : machine.mem 21=w[4] := Restore.uint_unique
   (other.elements 0 (P.uint 4 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have saved0 := saved 0 (by decide)
 have saved1 := saved 1 (by decide)
 exact ⟨stack,freeWord,exterior 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   reference,counterWord,exterior 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   cursor,exterior 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   saved0.1,saved0.2,saved1.1,saved1.2,firstLength,word7,word9,otherLength,word4⟩

theorem observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 7,machine.mem 8,machine.mem 9,
 machine.mem 10,machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[30],w[16],w[16],w[2],w[10],w[10],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 rcases facts with ⟨stack,cursor,alias,reference,counter,bottom,pointer,marker,saved0,saved1,saved2,saved3,len0,old0,old1,len1,other0⟩
 rw [stack,cursor,alias,reference,counter,bottom,pointer,marker,saved0,saved1,saved2,saved3,len0,old0,old1,len1,other0]

theorem wrong_saved_order : machine.mem 11≠w[1] ∧ machine.mem 13≠w[2] := by
 rcases facts with ⟨stack,cursor,alias,reference,counter,bottom,pointer,marker,saved0,saved1,saved2,saved3,rest⟩
 rw [saved1,saved3]
 constructor <;> decide

theorem wrong_phase : machine.mem 8≠w[14] := by
 rw [facts.2.2.2.2.2.2.1]
 decide

theorem wrong_cost : ¬GrowsAllocator 2 16 4 callee P.base ParentPrefixes.Checks.input output.st addresses machine := by
 intro bad
 have owned := bad ⟨22,by decide⟩ (by decide) ParentPrefixes.Checks.ownership (by decide)
 have cursor := owned.arrays.free.cell
 rw [facts.2.1] at cursor
 exact (by decide : (w[30] : Word)≠w[26]) cursor

theorem shallow : (AllocatingActivation.body 2).run callee=.error .exhausted :=
 AllocatingSource.exhaustion 2 callee 2 (by decide) P.r0 rfl rfl AllocatingSource.Checks.read_bound (by decide)

theorem shallow_unmatched : ¬GrowingResult 1 2 16 8 F callee P.base ParentPrefixes.Checks.input
 ((AllocatingActivation.body 2).run callee) (run (image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input) := by
 rw [shallow]
 intro same
 rcases same with ⟨out,target,addresses,source,rest⟩ | ⟨source,rest⟩
 · cases source
 · cases source

theorem target_not_revert : run (image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input≠.revert := by
 rw [specification.2.1]
 intro wrong
 cases wrong

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingReturn

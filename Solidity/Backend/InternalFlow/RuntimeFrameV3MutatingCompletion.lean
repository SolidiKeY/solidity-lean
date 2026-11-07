import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingHistory
import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingReturn

/-! Matched mutating countdown returns from actual source continuation,
derived saved-parent history and the existing checked paired unwind. This is
not public recursive compiler or approved-domain coverage. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingCompletion
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

def image {C : Contract} (b : Nat) (F : Frag (Parameters A)) (pointer bottom : Nat) : List Instr :=
 [.loop (guardCompiled (C:=C) b F).code (MutatingActivation.code (C:=C) b F pointer)] ++ PairedUnwind.code b pointer bottom A

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
 (MutatingActivation.body (count+1)).run σ=.ok out ∧ run (image (C:=C) b F pointer bottom) before=.ok last 0 ∧
 StateRepr L b frame F out.st addresses last ∧ last.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator b frame (4*count) σ base before out.st addresses last ∧
 last.mem pointer=.val (wmod start) ∧ last.mem b=before.mem b ∧
 (∀ j,j<count → last.mem (start+2*j)=before.mem b ∧ last.mem (start+2*j+1)=.val (wmod (count-j))) ∧
 (∀ x,0<x → x<frame → x≠b → x≠b+1 → x≠b+2 → x≠pointer →
   (x<start ∨ start+2*count≤x) → last.mem x=before.mem x) := by
 obtain ⟨τ,e,down,addresses,running,reprDown,env,size,kept,stack,extended,growth,owned,currentDown,resume⟩ :=
   MutatingResume.coupled count count (by omega) bound σ ref counter alias reads base before repr cursor owner positive heapSpace
     lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current
 have zeroEnv : τ.env=(countValue 0 W_pos,(some (ref.wk e),())) := by simpa only [Nat.sub_self] using env
 have zeroCounter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [zeroEnv];rfl
 let returned : Solidity.Out C σ.H (Parameters A) := AllocatingResume.reexport σ e ⟨τ,List.prefix_refl _⟩
 have source : (MutatingActivation.body (count+1)).run σ=.ok returned :=
   MutatingResume.finish σ τ e count zeroCounter resume
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
   MutatingHistory.history count count (by omega) bound σ ref counter alias reads base before repr cursor owner positive heapSpace
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
   (empty_turn _ (run (MutatingActivation.code (C:=C) b F pointer)) _ guard)
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
 GrowingResult L b frame (4*count) F σ base before ((MutatingActivation.body (count+1)).run σ)
   (run (image (C:=C) b F pointer bottom) before) := by
 obtain ⟨out,last,addresses,source,target,represented,stack,extended,growth,rest⟩ :=
   endpoint count bound σ ref counter alias reads base before repr cursor owner positive heapSpace lo pointer start localBound
     pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current bottom bottomAbove bottomBefore bottomSeparate bottomValue
 exact .inl ⟨out,last,addresses,source,target,represented,stack,extended,growth⟩


/-- One target image agrees with every actually sufficient source index. -/
theorem growing_at {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (depth count : Nat) (bound : count<W)
 (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn) (enough : count<depth)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor before)
 (positive : 0<b) (heapSpace : cursor.val+4*count<W)
 (lo pointer start : Nat) (localBound : b+2<lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) (bottom : Nat) (bottomAbove : b+2<bottom) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (bottomValue : before.mem bottom=.val (wmod start)) :
 GrowingResult L b frame (4*count) F σ base before ((MutatingActivation.body depth).run σ)
   (run (image (C:=C) b F pointer bottom) before) := by
 obtain ⟨out,last,addresses,source,target,represented,stack,extended,growth,rest⟩ :=
   endpoint count bound σ ref counter alias reads base before repr cursor owner positive heapSpace lo pointer start localBound
     pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current bottom bottomAbove bottomBefore bottomSeparate bottomValue
 obtain ⟨other,actual,size,locals,lengths⟩ := MutatingSource.success depth σ count bound ref counter alias reads enough
 have same := MutatingSource.bodies depth (count+1) σ other out actual source
 rw [same] at actual
 exact .inl ⟨out,last,addresses,actual,target,represented,stack,extended,growth⟩

namespace Checks
open CountdownWitness
abbrev A := CountdownWitness.A

theorem available :
 ∃ (out : Solidity.Out P.C callee.H (Parameters CountdownWitness.A)) (last : Machine) (addresses : Nat → Fin W),
 (MutatingActivation.body 3).run callee=.ok out ∧ run (image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧ last.stack=ParentPrefixes.Checks.input.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input out.st addresses last ∧
 last.mem 8=w[10] ∧ last.mem 2=ParentPrefixes.Checks.input.mem 2 ∧
 (∀ j,j<2 → last.mem (10+2*j)=ParentPrefixes.Checks.input.mem 2 ∧ last.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 (∀ x,0<x → x<16 → x≠2 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 14≤x) → last.mem x=ParentPrefixes.Checks.input.mem x) :=
 endpoint 2 (by decide) callee P.r0 rfl rfl MutatingSource.Checks.read_bound
   P.base ParentPrefixes.Checks.input ParentPrefixes.Checks.initial ⟨22,by decide⟩ ParentPrefixes.Checks.ownership
   (by decide) (by decide) 8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) rfl 7 (by decide) (by decide) (by decide) rfl

noncomputable def output := available.choose
noncomputable def machine : Machine := available.choose_spec.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose_spec.choose

theorem specification :
 (MutatingActivation.body 3).run callee=.ok output ∧ run (image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input=.ok machine 0 ∧
 StateRepr 1 2 16 F output.st addresses machine ∧ machine.stack=ParentPrefixes.Checks.input.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input output.st addresses machine ∧
 machine.mem 8=w[10] ∧ machine.mem 2=ParentPrefixes.Checks.input.mem 2 ∧
 (∀ j,j<2 → machine.mem (10+2*j)=ParentPrefixes.Checks.input.mem 2 ∧ machine.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 (∀ x,0<x → x<16 → x≠2 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 14≤x) → machine.mem x=ParentPrefixes.Checks.input.mem x) :=
 available.choose_spec.choose_spec.choose_spec

theorem source_identity : output=MutatingSource.Checks.rootOut :=
 Except.ok.inj (specification.1.symm.trans MutatingSource.Checks.root)

theorem same_machine : machine=MutatingReturn.Checks.machine :=
 (Out.ok.inj (specification.2.1.symm.trans MutatingReturn.Checks.specification.1)).1

theorem all_indices (depth : Nat) (enough : 2<depth) :
 GrowingResult 1 2 16 8 F callee P.base ParentPrefixes.Checks.input
   ((MutatingActivation.body depth).run callee) (run (image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input) :=
 growing_at depth 2 (by decide) callee P.r0 rfl rfl MutatingSource.Checks.read_bound enough
   P.base ParentPrefixes.Checks.input ParentPrefixes.Checks.initial ⟨22,by decide⟩ ParentPrefixes.Checks.ownership
   (by decide) (by decide) 8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) rfl 7 (by decide) (by decide) (by decide) rfl

theorem observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,machine.mem 11,machine.mem 12,machine.mem 13,
 machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 20,machine.mem 21,
 machine.mem 22,machine.mem 23,machine.mem 24,machine.mem 25,
 machine.mem 26,machine.mem 27,machine.mem 28,machine.mem 29])=
 ([w[77]],[w[30],w[16],w[16],w[2],w[26],w[10],w[10],w[99],w[16],w[2],w[16],w[1],
 w[2],w[1],w[2],w[1],w[4],w[3],w[0],w[0],w[0],w[3],w[0],w[0],w[0]]) := by
 rw [same_machine]
 exact MutatingReturn.Checks.observations

theorem wrong_cost : ¬GrowsAllocator 2 16 4 callee P.base ParentPrefixes.Checks.input
 output.st addresses machine := by
 intro wrong
 have wrongOwner := wrong (⟨22,by decide⟩ : Fin W) (by decide) ParentPrefixes.Checks.ownership (by decide)
 have goodGrowth := specification.2.2.2.2.2.1
 have goodOwner := goodGrowth (⟨22,by decide⟩ : Fin W) (by decide) ParentPrefixes.Checks.ownership (by decide)
 have badCursor := wrongOwner.arrays.free.cell
 have goodCursor := goodOwner.arrays.free.cell
 change machine.mem 0=w[26] at badCursor
 change machine.mem 0=w[30] at goodCursor
 rw [goodCursor] at badCursor
 cases badCursor

theorem unfinished_pointer : machine.mem 8≠w[14] := by
 rw [same_machine]
 exact MutatingReturn.Checks.unfinished_pointer

theorem missing_mutation : machine.mem 17≠w[7] := by
 rw [same_machine]
 exact MutatingReturn.Checks.missing_mutation

end Checks

namespace Zero
open CountdownWitness
abbrev A := CountdownWitness.A

def source := callee.setLocal (.here : Idx (Parameters A) (.val .uint)) (countValue 0 W_pos)
def input := writeMachine ParentPrefixes.Checks.input 3 w[0]

theorem source_prefix :
 (Stmt.assignLocal (.here : Idx (Parameters A) (.val .uint)) (.simple (.lit 0 rfl))).run callee=
 .ok ⟨source,List.prefix_refl _⟩ := rfl

theorem target_prefix : run [.push w[0],.mstore 3] ParentPrefixes.Checks.input=.ok input 0 := rfl

theorem public_selection :
 (compileStmt 2 F (Stmt.assignLocal (.here : Idx (Parameters A) (.val .uint)) (.simple (.lit 0 rfl)) :
   Stmt P.C (Parameters A) (Parameters A))).map (fun checked => checked.code)=some [.push w[0],.mstore 3] := rfl

theorem represented : StateRepr 1 2 16 F source P.base input :=
 ParentPrefixes.Checks.initial.setVal .here (countValue 0 W_pos) w[0] (ReprV.uint_of rfl)

theorem ownership : StructAllocatorRepr source.heap P.base 16 (⟨22,by decide⟩ : Fin W) input :=
 ParentPrefixes.Checks.ownership.localWrite 3 (by decide) (by decide) w[0]

theorem available : ∃ (out : Solidity.Out P.C source.H (Parameters A)) (last : Machine) (addresses : Nat → Fin W),
 (MutatingActivation.body 1).run source=.ok out ∧
 run (image (C:=P.C) 2 F 8 7) input=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧ last.stack=input.stack ∧
 BaseExtends source.H P.base addresses ∧
 GrowsAllocator 2 16 0 source P.base input out.st addresses last ∧
 last.mem 8=w[10] ∧ last.mem 2=input.mem 2 ∧
 (∀ j,j<0 → last.mem (10+2*j)=input.mem 2 ∧ last.mem (10+2*j+1)=.val (wmod (0-j))) ∧
 (∀ x,0<x → x<16 → x≠2 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 10≤x) → last.mem x=input.mem x) :=
 endpoint 0 W_pos source P.r0 rfl rfl (by omega) P.base input represented ⟨22,by decide⟩ ownership
   (by decide) (by decide) 8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) rfl 7 (by decide) (by decide) (by decide) rfl

/-- The zero branch actually skips every allocation and saved-parent turn. -/
theorem unchanged : run (image (C:=P.C) 2 F 8 7) input=.ok input 0 := by
 have guard := guard_run source 0 W_pos rfl P.base input represented
 have turn := empty_turn (run (guardCompiled (C:=P.C) 2 F).code)
   (run (MutatingActivation.code (C:=P.C) 2 F 8)) input guard
 have down : run [.loop (guardCompiled (C:=P.C) 2 F).code (MutatingActivation.code (C:=P.C) 2 F 8)] input=.ok input 0 :=
   successful_loop _ _ _ _ 1 (by simp only [loopIterN,turn])
 have back := PairedUnwind.turn_done input 2 8 7 10 A rfl rfl
 have unwind : run (PairedUnwind.code 2 8 7 A) input=.ok input 0 :=
   PairedUnwind.run_of_stopped (horizon:=1) (by simp only [loopIterN,back])
 exact (run_append_ok down).trans unwind

theorem observations :
 (input.stack,[input.mem 0,input.mem 1,input.mem 2,input.mem 3,input.mem 7,input.mem 8,input.mem 9,
 input.mem 16,input.mem 17,input.mem 18,input.mem 20,input.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[0],w[10],w[10],w[99],w[2],w[7],w[9],w[1],w[4]]) := rfl

theorem no_allocation_charge : ¬GrowsAllocator 2 16 4 source P.base input source P.base input := by
 intro wrong
 have owner := wrong (⟨22,by decide⟩ : Fin W) (by decide) ownership (by decide)
 have cursor := owner.arrays.free.cell
 change w[22]=w[26] at cursor
 cases cursor

end Zero

end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingCompletion

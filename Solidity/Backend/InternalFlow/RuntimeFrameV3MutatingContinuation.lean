import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingCompletion
import Solidity.Evm.MemoryCalls

/-! Checked continuation after actual mutating recursive completion. Initial
capacity is split by reached source cost and the prefix's genuine growth.
This does not supply a general recursive compiler or approved-domain proof. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingContinuation
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Consume the completed recursive construction, not a supplied midpoint or
simulation. The suffix retains its real code, fragment, need and reached cost. -/
theorem after_return {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
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
 (bottomSeparate : bottom≠pointer) (bottomValue : before.mem bottom=.val (wmod start))
 {Δ : Ctx} (suffix : Prog C (Parameters A) Δ) (checked : Calls.Program b F suffix) (budget : Nat)
 (suffixRoom : b+checked.need≤frame)
 (suffixCost : ∀ out, (MutatingActivation.body (count+1)).run σ=.ok out → checked.cost out.st≤budget)
 (totalRoom : AllocationInput b frame (4*count+budget) σ base before) :
 ∃ out, (MutatingActivation.body (count+1)).run σ=.ok out ∧
 GrowingResult L b frame (4*count+checked.cost out.st) checked.frag σ base before
   ((.cons (.block (MutatingActivation.body (count+1))) suffix : Prog C (Parameters A) Δ).run σ)
   (run (MutatingCompletion.image (C:=C) b F pointer bottom ++ checked.code) before) := by
 obtain ⟨out,mid,addresses,source,target,represented,stack,extended,growth,rest⟩ :=
   MutatingCompletion.endpoint count bound σ ref counter alias reads base before repr cursor owner positive heapSpace
     lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current
     bottom bottomAbove bottomBefore bottomSeparate bottomValue
 have split : AllocationInput b frame (4*count+checked.cost out.st) σ base before :=
   totalRoom.of_le (Nat.add_le_add_left (suffixCost out source) _)
 have reached := growth.nextInput split
 have blockSource : (.block (MutatingActivation.body (count+1)) : Stmt C (Parameters A) (Parameters A)).run σ=.ok out := by
   change TRun.block (MutatingActivation.body (count+1)).ext (MutatingActivation.body (count+1)).runR σ=_
   unfold TRun.block
   change (MutatingActivation.body (count+1)).runR σ=.ok out at source
   rw [source]
   have scope : (MutatingActivation.body (C:=C) (count+1)).ext=Ext.refl := Subsingleton.elim _ _
   simp only [Except.map,scope]
   rfl
 have suffixResult := checked.sound represented suffixRoom reached
 refine ⟨out,source,?_⟩
 rcases suffixResult with ⟨last,final,finalBase,suffixSource,suffixTarget,suffixRepr,suffixStack,suffixBase,suffixGrowth⟩ |
   ⟨suffixSource,suffixTarget⟩
 · refine .inl ⟨⟨last.st,out.ext.trans last.ext⟩,final,finalBase,?_,?_,suffixRepr,
     suffixStack.trans stack,BaseExtends.trans out.ext extended suffixBase,growth.comp suffixGrowth⟩
   · rw [Prog.run_cons_ok blockSource,suffixSource]
     rfl
   · exact (run_append_ok target).trans suffixTarget
 · refine .inr ⟨?_,(run_append_ok target).trans suffixTarget⟩
   rw [Prog.run_cons_ok blockSource,suffixSource]
   rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingContinuation

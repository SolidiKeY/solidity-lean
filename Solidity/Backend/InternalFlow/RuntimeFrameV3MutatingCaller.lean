import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingArguments
import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingCompletion

/-! Mutating recursive body transport through checked argument entry and
caller restoration. Reached ownership/capacity and caller words are derived.
Old heap contents may change; fragile caller aliases are explicitly excluded.
No general selector, source-profile or physical-world closure is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingCaller
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
abbrev A : RefTy := CountdownWitness.A

/-- Arbitrary caller-context export, with explicit non-fragile caller restriction.
Body execution, low-word framing and reached allocation cost are derived from
the actual mutating return image, not supplied as simulation premises. -/
theorem after_arguments {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 (name : Name) (args : Args C Γ (Parameters A))
 (compiled : Composition.Program b F (args.declsThen .nil))
 (σ : State C Γ) (a : TEnv C σ.H (Parameters A)) (evaluated : args.evalT σ=.ok a)
 (count : Nat) (positive : 0<count) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) a=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) a=some ref)
 (reads : count≤σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (initial : StateRepr L b frame F σ base before)
 (lo pointer bottom start : Nat) (room : b+compiled.checked.need≤lo) (boundary : lo≤frame)
 (localBound : b+Γ.length+2<lo) (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame)
 (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (savedRoom : start+2*count≤frame) (savedFits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start))
 (bottomAbove : b+Γ.length+2<bottom) (bottomBelow : bottom<frame)
 (bottomBefore : bottom<start) (bottomSeparate : bottom≠pointer)
 (bottomValue : before.mem bottom=.val (wmod start))
 (bottomScratch : lo≤bottom)
 (capacity : AllocationInput b frame (compiled.checked.cost σ+4*count) σ base before)
 (notFragile : ∀ {R : RefTy} (i : Idx Γ (.alias R)), (compiled.checked.frag.restrict Γ).get i≠.fragile) :
 ∃ (out : Solidity.Out C σ.H Γ) (target : Machine) (addresses : Nat → Fin W) (mid : Machine),
 run compiled.checked.code before=.ok mid 0 ∧
 (InterfaceV1.recursiveSource name args .none MutatingActivation.step (count+1)).run σ=.ok out ∧
 run (compiled.checked.code++MutatingCompletion.image (C:=C) (b+Γ.length) (Frag.init (Parameters A)) pointer bottom) before=.ok target 0 ∧
 StateRepr L b frame (compiled.checked.frag.restrict Γ) out.st addresses target ∧ target.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (compiled.checked.cost σ+4*count) σ base before out.st addresses target ∧
 (∀ {t : LTy} (i : Idx Γ t), target.mem (cellOf b i)=mid.mem (cellOf b i)) ∧
 target.mem pointer=.val (wmod start) ∧
 (∀ j,j<count → target.mem (start+2*j)=.val (base ref.id) ∧ target.mem (start+2*j+1)=.val (wmod (count-j))) := by
 have prefixCapacity := AllocatingArguments.prefix_input capacity
 obtain ⟨mid,middle,executed,full,caller,stack,extended,prefixGrowth⟩ :=
   ArgumentEntry.endpoint args compiled.checked σ a evaluated base before initial (by omega) prefixCapacity
 have parameters := parameter_projection (tail:=Γ) full
 change StateRepr L (b+Γ.length) frame (Frag.init (Parameters A))
   (σ.withEnv (TEnv.take (Parameters A) (TEnv.append (Parameters A) a σ.env))) middle mid at parameters
 rw [AllocatingZero.take_parameters] at parameters
 have scratch := compiled.safe initial room boundary prefixCapacity executed
 have reached := prefixGrowth.nextInput capacity
 rcases reached with zero | ⟨hb,cursor,owner,space⟩
 · omega
 · have childOwner : StructAllocatorRepr (σ.withEnv a).heap middle frame cursor mid := owner
   obtain ⟨body,last,addresses,source,target,represented,bodyStack,bodyExtended,bodyGrowth,pointerValue,reference,saved,outside⟩ :=
     MutatingCompletion.endpoint count bound (σ.withEnv a) ref counter alias reads middle mid parameters cursor childOwner
       (by omega) space lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore savedRoom savedFits
       ((scratch pointer pointerAbove pointerBelow).trans current) bottom bottomAbove bottomBefore bottomSeparate
       ((scratch bottom bottomScratch bottomBelow).trans bottomValue)
   let out : Solidity.Out C σ.H Γ := exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl σ a body
   have midWords {t : LTy} (i : Idx Γ t) : last.mem (cellOf b i)=mid.mem (cellOf b i) := by
     have lower := le_lvl b i
     have upper := lvl_lt b i
     exact outside (lvl b i) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (.inl (by omega))
   have callerRepr := CallerReframe.reframe σ body.st body.ext middle addresses mid last caller represented bodyExtended midWords notFragile
   have totalGrowth : GrowsAllocator b frame (compiled.checked.cost σ+4*count) σ base before out.st addresses last := by
     intro cursor hb owned totalSpace
     have leftSpace : cursor.val+compiled.checked.cost σ<W := by omega
     have reachedOwner := prefixGrowth cursor hb owned leftSpace
     have afterSpace : (cursor.val+compiled.checked.cost σ)+4*count<W := by omega
     have grown := bodyGrowth ⟨cursor.val+compiled.checked.cost σ,leftSpace⟩ (by omega) reachedOwner afterSpace
     simpa only [Nat.add_assoc] using grown
   have refWord : mid.mem (b+Γ.length)=.val (base ref.id) := by
     obtain ⟨r,value,word⟩ := parameters.pointers (.there .here)
     have same : r=ref := Option.some.inj (value.symm.trans alias)
     subst r
     exact word.trans (congrArg Word.val (extended ref))
   refine ⟨out,last,addresses,mid,executed,call_return args .none .refl (MutatingActivation.body (count+1)).runR σ a evaluated body source,
     (run_append_ok executed).trans target,callerRepr,bodyStack.trans stack,
     BaseExtends.trans (List.prefix_refl σ.H) extended bodyExtended,totalGrowth,?_,pointerValue,?_⟩
   · intro t i
     exact midWords i
   · intro j small
     exact ⟨((saved j small).1).trans refWord,(saved j small).2⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingCaller

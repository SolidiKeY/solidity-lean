import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeHeapProfile
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarAllocatingDescent

/-! Actual native recursive output and actual target descent have the same
complete dependent heap. Their local environments differ at this boundary:
parent-return transport remains necessary for native-output StateRepr. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeDescentHeap
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent TypedHeapExtensionality

theorem heap_matches (depth n : Nat) {L frame : Nat} (σ : State C (Frame A))
 (fit : n<W) (ref : HRef σ.H A)
 (result : TEnv.get (.here : Idx (Frame A) (.val .uint)) σ.env=PrimTy.dflt .uint)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue (n) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L 2 frame F σ base before)
 (cursor : Fin W) (owned : StructAllocatorRepr σ.heap base frame cursor before)
 (heapSpace : cursor.val+4*n<W) (lo pointer start : Nat)
 (privateBelow : 5<lo) (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame)
 (payloadAbove : lo≤start) (payloadBelow : start+3*n≤frame) (pointerBefore : pointer<start)
 (fits : start+3*n<W) (current : before.mem pointer=.val (wmod start))
 (enough : n<depth) :
 ∃ (out : Solidity.Out C σ.H (Frame A)) (τ : State C (Frame A)) (e : σ.H <+: τ.H)
   (after : Machine) (addresses : Nat → Fin W),
 (AllocatingScalarSource.body A (by rfl) depth).run σ=.ok out ∧
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code pointer)) n before=.inl after ∧
 StateRepr L 2 frame F τ addresses after ∧
 out.st.H=τ.H ∧ HEq out.st.heap τ.heap ∧
 ScalarAllocationInventory.Holds σ.H.length n cursor.val τ addresses ∧
 Heap.Keeps e σ.heap τ.heap ∧
 TEnv.get (.here : Idx (Frame A) (.val .uint)) out.st.env=countValue n fit := by
 obtain ⟨out,source,value,sourceSize,sourceKeeps,sourceDefaults⟩ :=
   NativeHeapProfile.success (by rfl) depth σ n fit ref counter alias enough
 obtain ⟨τ,e,after,addresses,actual,represented,env,size,kept,owner,extension,growth,stack,position,history,words,inventory⟩ :=
   running_with_inventory n 0 σ (by omega) ref result (by simpa only [Nat.zero_add] using counter) alias base before repr cursor owned heapSpace
     lo pointer start privateBelow pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore fits current
 have targetDefaults : Defaults σ.H.length τ.heap := of_inventory inventory size
 obtain ⟨sameTyping,sameHeap⟩ := profiles_heq σ.heap out.ext e out.st.heap τ.heap n sourceSize size sourceKeeps kept sourceDefaults targetDefaults
 exact ⟨out,τ,e,after,addresses,source,actual,represented,sameTyping,sameHeap,inventory,kept,value⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.NativeDescentHeap
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeDescentHeap.heap_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeDescentHeap.heap_matches

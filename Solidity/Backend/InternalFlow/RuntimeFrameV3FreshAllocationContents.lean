import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarAllocatingDescent
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingPrefixes
import Solidity.Semantics.AllocBytes

/-! Exact contents of a genuinely fresh private array after arbitrary further
allocating descent. The object is constructed by State.alloc, then preserved
by the actual tail and read from that same reached represented target heap.
This is not full native-output heap equality or general recursive selection. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FreshAllocationContents
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem reached (steps remaining : Nat) {L frame : Nat} (σ : State C (Frame A))
 (fit : remaining+steps+1<W) (ref : HRef σ.H A)
 (_result : TEnv.get (.here : Idx (Frame A) (.val .uint)) σ.env=PrimTy.dflt .uint)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue (remaining+steps+1) fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L 2 frame F σ base before)
 (cursor : Fin W) (owned : StructAllocatorRepr σ.heap base frame cursor before)
 (heapSpace : cursor.val+4*(steps+1)<W) (lo pointer start : Nat)
 (privateBelow : 5<lo) (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame)
 (payloadAbove : lo≤start) (payloadBelow : start+3*(steps+1)≤frame) (pointerBefore : pointer<start)
 (fits : start+3*(steps+1)<W) (current : before.mem pointer=.val (wmod start)) :
 let first := AllocatingScalarSource.allocated σ
 let fresh : HRef first.H (.array (.prim .bool)) := (σ.alloc (defaultArray .bool AllocatingScalarSource.size)).2
 ∃ (τ : State C (Frame A)) (e : first.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code pointer)) (steps+1) before=.inl after ∧
 StateRepr L 2 frame F τ addresses after ∧
 Heap.Keeps e first.heap τ.heap ∧
 τ.heap.get (fresh.wk e)=defaultArray .bool AllocatingScalarSource.size ∧
 addresses (fresh.wk e).id=cursor ∧
 [after.mem cursor.val,after.mem (cursor.val+1),after.mem (cursor.val+2),after.mem (cursor.val+3)]=
 [w[3],w[0],w[0],w[0]] := by
 simp only []
 let first := AllocatingScalarSource.allocated σ
 let fresh : HRef first.H (.array (.prim .bool)) := (σ.alloc (defaultArray .bool AllocatingScalarSource.size)).2
 let child := entered first (remaining+steps) (by omega) (ref.wk (AllocatingScalarSource.extension σ))
 let nextBase := upd base σ.H.length cursor
 have space : cursor.val+4<W := by omega
 obtain ⟨next,source,actual,nextRepr,nextOwner,extended,stack,position,rest⟩ :=
   AllocatingScalarTurn.turn σ (remaining+steps) fit ref counter alias base before repr cursor owned space
     lo pointer start privateBelow pointerAbove pointerBelow payloadAbove (by omega) pointerBefore (by omega) current
 obtain ⟨τ,e,after,addresses,running,finalRepr,env,size,kept,owner,extension,growth,finalStack,finalPointer,history,words⟩ :=
   ScalarAllocatingDescent.running steps remaining child (by omega) (ref.wk (AllocatingScalarSource.extension σ))
     rfl rfl rfl nextBase next nextRepr (⟨cursor.val+4,space⟩ : Fin W) nextOwner (by change cursor.val+4+4*steps<W;omega)
     lo pointer (start+3) privateBelow pointerAbove pointerBelow (by omega) (by omega) (by omega) (by omega) position
 have turn := positive_turn σ (remaining+steps) fit counter base before next repr pointer actual
 have freshGet : first.heap.get fresh=defaultArray .bool AllocatingScalarSource.size := by
   exact Heap.get_alloc_self σ.heap (defaultArray .bool AllocatingScalarSource.size)
 have contents : τ.heap.get (fresh.wk e)=defaultArray .bool AllocatingScalarSource.size := by
   rw [kept fresh]
   change MObj.wk e (.array (.prim .bool)) (first.heap.get fresh)=_
   rw [freshGet]
   simp only [MObj.wk,defaultArray,List.map_replicate,MVal.wk]
 have address : addresses (fresh.wk e).id=cursor := (extension fresh).trans (upd_same base σ.H.length cursor)
 have array := AllocatingPrefixes.old_array e kept extension finalRepr.heap fresh
 have initialAddress : nextBase fresh.id=cursor := upd_same base σ.H.length cursor
 rw [initialAddress] at array
 change ArrayRepr first.heap fresh cursor after at array
 have length : first.heap.len fresh .dyn=3 := by
   simp only [Heap.len,MObj.elems_dyn,freshGet,defaultArray,List.length_replicate,AllocatingScalarSource.size]
 have header := array.length
 rw [length] at header
 have zero := array.elements 0 false (by rw [freshGet];simp only [MObj.elems_dyn,defaultArray,AllocatingScalarSource.size];rfl)
 have one := array.elements 1 false (by rw [freshGet];simp only [MObj.elems_dyn,defaultArray,AllocatingScalarSource.size];rfl)
 have two := array.elements 2 false (by rw [freshGet];simp only [MObj.elems_dyn,defaultArray,AllocatingScalarSource.size];rfl)
 change after.mem (cursor.val+1)=w[0] at zero
 change after.mem (cursor.val+2)=w[0] at one
 change after.mem (cursor.val+3)=w[0] at two
 refine ⟨τ,e,after,addresses,?_,finalRepr,kept,contents,address,?_⟩
 · simpa only [loopIterN,turn] using running
 · rw [header,zero,one,two]
   rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.FreshAllocationContents

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FreshAllocationContents.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FreshAllocationContents.reached

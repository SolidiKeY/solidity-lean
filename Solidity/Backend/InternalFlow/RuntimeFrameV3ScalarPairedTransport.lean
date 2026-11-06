import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentInterfaceV1
import Solidity.Backend.InternalFlow.RuntimeFrameV3FullScalarLoop

/-! A single target image composes allocating descent and full scalar returns
for every finite admitted count. Return history is derived from the frozen
descent contract at the same reached machine. Native recursive compilation and
approved-domain provenance are separate obligations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedTransport
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarDescentInterfaceV1

def image (selected : CompiledVal 2 F (guard (C:=C) (R:=A))) (pointer bottom : Nat) : List Instr :=
 [.loop selected.code (AllocatingScalarTurn.code pointer)] ++ FullScalarLoop.code (C:=C) 2 pointer bottom F

theorem complete (selected : CompiledVal 2 F (guard (C:=C) (R:=A)))
 (producer : Producer selected) (n : Nat) {L frame : Nat} (σ : State C (Frame A))
 (fit : n<W) (ref : HRef σ.H A)
 (result : TEnv.get (.here : Idx (Frame A) (.val .uint)) σ.env=PrimTy.dflt .uint)
 (counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) σ.env=countValue n fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L 2 frame F σ base before)
 (cursor : Fin W) (owned : StructAllocatorRepr σ.heap base frame cursor before)
 (heapSpace : cursor.val+4*n<W) (lo pointer bottom start : Nat)
 (privateBelow : 5<lo) (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame)
 (payloadAbove : lo≤start) (payloadBelow : start+3*n≤frame) (pointerBefore : pointer<start)
 (fits : start+3*n<W) (current : before.mem pointer=.val (wmod start))
 (bottomAbove : 6≤bottom) (bottomBefore : bottom<start) (bottomSeparate : bottom≠pointer)
 (bottomValue : before.mem bottom=.val (wmod start)) :
 ∃ (τ : State C (Frame A)) (e : σ.H <+: τ.H) (down last : Machine) (addresses : Nat → Fin W),
 Memory.compileVal 2 F (guard (C:=C) (R:=A))=some selected ∧
 run (image selected pointer bottom) before=.ok last 0 ∧
 loopIterN (run selected.code) (run (AllocatingScalarTurn.code pointer)) n before=.inl down ∧
 loopIterN (run (FullScalarLoop.condition pointer bottom))
   (run (FullScalarUnwind.code (C:=C) 2 pointer F)) (n+1) down=.inr (.ok last 0) ∧
 StateRepr L 2 frame F (FullScalarLoop.returned τ 0 n (by omega)) addresses last ∧
 τ.H.length=σ.H.length+n ∧ Heap.Keeps e σ.heap τ.heap ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator 2 frame (4*n) σ base before (FullScalarLoop.returned τ 0 n (by omega)) addresses last ∧
 StructAllocatorRepr (FullScalarLoop.returned τ 0 n (by omega)).heap addresses frame
   (⟨cursor.val+4*n,heapSpace⟩ : Fin W) last ∧
 last.stack=before.stack ∧ last.mem pointer=.val (wmod start) ∧ last.mem 2=.val (base ref.id) := by
 obtain ⟨τ,e,down,addresses,running,downRepr,env,size,kept,downOwner,extended,descentGrowth,stack,position,history,words⟩ :=
   producer.running n 0 σ (by omega) ref result (by simpa only [Nat.zero_add] using counter) alias base before repr cursor owned heapSpace
     lo pointer start privateBelow pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore fits current
 have zeroCounter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [env];rfl
 have zeroResult : TEnv.get (.here : Idx (Frame A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [env];rfl
 have stopped := GuardedPrefixes.finish_prefix _ _ n before down (.ok down 0) running
   (producer.zero_turn τ zeroCounter addresses down downRepr pointer)
 have descend : run [.loop selected.code (AllocatingScalarTurn.code pointer)] before=.ok down 0 :=
   GuardedRecursion.successful_loop selected.code (AllocatingScalarTurn.code pointer) before down (n+1) stopped
 obtain ⟨reference,binding,referenceWord⟩ := downRepr.pointers (.there (.there .here) : Idx (Frame A) (.mem A))
 have expected : TEnv.get (.there (.there .here) : Idx (Frame A) (.mem A)) τ.env=some (ref.wk e) := by rw [env];rfl
 have same : reference=ref.wk e := Option.some.inj (binding.symm.trans expected)
 subst reference
 change down.mem 2=.val (addresses ref.id) at referenceWord
 rw [extended ref] at referenceWord
 have saved : ∀ j,j<n → down.mem (start+3*j)=down.mem 2 ∧
     down.mem (start+3*j+1)=.val (wmod (0+n-j)) := by
   intro j small
   exact ⟨(history j small).1.trans referenceWord.symm,(history j small).2.1⟩
 have downBottom := (words bottom bottomAbove (by omega) bottomSeparate (.inl bottomBefore)).trans bottomValue
 obtain ⟨last,returns,done,lastRepr,growth,lastStack,lastPointer,lastRef,outside⟩ :=
   FullScalarLoop.iter n 0 τ addresses down downRepr (by omega) zeroResult lo pointer bottom start
     (by omega) pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore (by omega)
     bottomSeparate fits position downBottom saved
 have actual : run (image selected pointer bottom) before=.ok last 0 :=
   (run_append_ok descend).trans (FullScalarLoop.run_of_stopped done)
 have total : GrowsAllocator 2 frame (4*n) σ base before
     (FullScalarLoop.returned τ 0 n (by omega)) addresses last := by
   simpa only [Nat.add_zero] using descentGrowth.comp growth
 have finalOwner := growth (⟨cursor.val+4*n,heapSpace⟩ : Fin W) (by omega) downOwner (by omega)
 exact ⟨τ,e,down,last,addresses,producer.public_guard,actual,running,done,lastRepr,size,kept,extended,total,
   finalOwner,lastStack.trans stack,lastPointer,lastRef.trans referenceWord⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedTransport

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedTransport.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedTransport.complete

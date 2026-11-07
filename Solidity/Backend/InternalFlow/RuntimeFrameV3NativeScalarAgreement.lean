import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPairedTransport
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarOutcomes

/-! Scalar observation agreement between the actual native allocating-recursive
source run and the single paired target image. Counts quantify all admitted
finite executions. Full new-heap identity, native compiler selection and
approved-domain provenance are not supplied by this observation theorem. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeScalarAgreement
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarDescentInterfaceV1

theorem agreement (selected : CompiledVal 2 F (guard (C:=C) (R:=A)))
 (producer : Producer selected) (depth n : Nat) {L frame : Nat} (σ : State C (Frame A))
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
 (bottomValue : before.mem bottom=.val (wmod start))
 (enough : n<depth) :
 ∃ (out : Solidity.Out C σ.H (Frame A)) (last : Machine),
 (AllocatingScalarSource.body A (by rfl) depth).run σ=.ok out ∧
 run (ScalarPairedTransport.image selected pointer bottom) before=.ok last 0 ∧
 TEnv.get (.here : Idx (Frame A) (.val .uint)) out.st.env=countValue n fit ∧
 ReprV .uint (TEnv.get (.here : Idx (Frame A) (.val .uint)) out.st.env) (last.mem 4) ∧
 out.st.H.length=σ.H.length+n ∧
 last.stack=before.stack ∧ last.mem pointer=.val (wmod start) ∧ last.mem 2=.val (base ref.id) := by
 obtain ⟨out,source,size,environment,kept⟩ :=
   AllocatingScalarSource.success (by rfl) depth σ n fit ref counter alias enough
 have sourceValue : TEnv.get (.here : Idx (Frame A) (.val .uint)) out.st.env=countValue n fit := by
   rw [environment,TEnv.get_set]
 obtain ⟨τ,e,down,last,addresses,selection,target,running,done,lastRepr,targetSize,targetKept,extended,growth,owner,stack,position,reference⟩ :=
   ScalarPairedTransport.complete selected producer n σ fit ref result counter alias base before repr cursor owned heapSpace
     lo pointer bottom start privateBelow pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore fits current
     bottomAbove bottomBefore bottomSeparate bottomValue
 have observed : ReprV .uint (countValue n fit) (last.mem 4) := by
   cases n with
   | zero =>
     have beforeDown : before=down := Sum.inl.inj running
     subst down
     have turn := FullScalarLoop.turn_done (C:=C) (R:=A) (b:=2) (F:=F) before current bottomValue
     have halted : Evm.Out.ok before 0=Evm.Out.ok last 0 := Sum.inr.inj (by simpa only [loopIterN,turn] using done)
     have same : before=last := by injection halted
     rw [←same]
     have cell := repr.core.vals (.here : Idx (Frame A) (.val .uint))
     change ReprV .uint (TEnv.get (.here : Idx (Frame A) (.val .uint)) σ.env) (before.mem 4) at cell
     rw [result] at cell
     exact cell
   | succ k =>
     have cell := lastRepr.core.vals (.here : Idx (Frame A) (.val .uint))
     simp only [FullScalarLoop.returned] at cell
     change ReprV .uint (countValue (0+(k+1)) _) (last.mem 4) at cell
     simpa only [Nat.zero_add] using cell
 refine ⟨out,last,source,target,sourceValue,?_,size,stack,position,reference⟩
 rw [sourceValue]
 exact observed

end Solidity.Backend.InternalFlow.RuntimeFrame.NativeScalarAgreement

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeScalarAgreement.agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeScalarAgreement.agreement

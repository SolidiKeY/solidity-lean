import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescent

/-! One scalar runtime image connects arbitrary-count actual native descent,
all-parent return and every successful source quotation. The image has no
count or quotation argument. General public compiler/profile closure is not
asserted, and shallow source exhaustion is kept distinct. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarReturn
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def image {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Parameters R)) (pointer bottom : Nat) : List Instr :=
 ScalarDescent.image (C:=C) b F pointer bottom ++
 ScalarPrefixes.image (C:=C) b pointer bottom (F.push (.val .uint) .ok)

theorem endpoint {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (count : Nat) (bound : count<W)
 (σ : State C (Frame R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine)
 (repr : StateRepr L b frame (F.push (.val .uint) .ok) σ base before)
 (lo pointer bottom start : Nat) (locals : b+3≤lo) (above : lo≤pointer)
 (below : pointer<frame) (payload : lo≤start) (separate : pointer<start)
 (bottomAbove : b+3≤bottom) (bottomBelow : bottom<frame) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) :
 ∃ after addresses,
 run (image (C:=C) b F pointer bottom) before=.ok after 0 ∧
 (∀ depth,(ScalarRecursiveSource.body R hm depth).run σ=
   if count<depth then .ok ⟨finished σ count bound,List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr L b frame (F.push (.val .uint) .ok) (finished σ count bound) addresses after ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 after.mem pointer=.val (wmod start) ∧ after.mem bottom=.val (wmod start) ∧ after.mem b=before.mem b ∧
 GrowsAllocator b frame 0 σ base before (finished σ count bound) addresses after ∧
 (∀ x,x≠pointer → x≠bottom → x≠b → x≠b+1 → x≠b+2 →
   (x<start ∨ start+2*count≤x) → after.mem x=before.mem x) ∧
 (∀ j,j<count → after.mem (start+2*j)=before.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (count-j))) := by
 obtain ⟨down,addresses,descent,zero,stack,extended,currentDown,bottomDown,reference,saved,growth,outside⟩ :=
   ScalarDescent.reached hm count bound σ ref counter alias base before repr lo pointer bottom start
     locals above below payload separate bottomAbove bottomBelow bottomBefore bottomSeparate capacity fits current
 have initial : StateRepr L b frame (F.push (.val .uint) .ok)
     (ScalarPrefixes.sourceAt σ (count-count) (by omega)) addresses down := by
   simpa only [Nat.sub_self] using zero
 obtain ⟨after,unwind,stable,reached,lastStack,lastCursor,lastRef,lastGrowth,lastOutside⟩ :=
   ScalarPrefixes.complete σ addresses count count (Nat.le_refl _) bound down initial lo pointer bottom start
     locals above below payload separate bottomAbove bottomBefore bottomSeparate fits currentDown bottomDown saved
 have oldEnv : σ.env.2=(countValue count bound,σ.env.2.2) := Prod.ext counter rfl
 have sameSource : ScalarPrefixes.sourceAt σ count bound=finished σ count bound := by
   change σ.withEnv (Δ:=Frame R) (countValue count bound,(countValue count bound,σ.env.2.2))=
     σ.withEnv (Δ:=Frame R) (countValue count bound,σ.env.2)
   rw [←oldEnv]
 rw [sameSource] at reached lastGrowth
 refine ⟨after,addresses,?_,?_,reached,lastStack.trans stack,extended,lastCursor,?_,lastRef.trans reference,?_,?_,?_⟩
 · unfold image
   rw [run_append_ok descent]
   exact unwind
 · intro depth
   exact ScalarRecursiveSource.all_horizons hm depth σ count bound ref counter alias
 · exact (lastOutside bottom bottomSeparate (by omega) (by omega) (by omega)).trans bottomDown
 · have actual : GrowsAllocator b frame 0 (ScalarPrefixes.sourceAt σ 0 W_pos) addresses down
       (finished σ count bound) addresses after := by
     simpa only [Nat.sub_self] using lastGrowth
   simpa only [Nat.add_zero] using growth.comp actual
 · intro x hp hb hr hc hv region
   exact (lastOutside x hp hr hc hv).trans (outside x hp hb hc hv region)
 · intro j small
   have low : b+2<start := by omega
   exact ⟨(lastOutside _ (by omega) (by omega) (by omega) (by omega)).trans ((saved j small).1.trans reference),
     (lastOutside _ (by omega) (by omega) (by omega) (by omega)).trans (saved j small).2⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarReturn

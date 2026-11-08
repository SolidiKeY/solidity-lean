import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarReturn
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveCall
import Solidity.Backend.InternalFlow.RuntimeFrameResult

/-! Actual recursive argument/default entry, one arbitrary-count scalar image
and nonidentity private-result export. This is the typed countdown family,
not an ordinary-call producer or a general public recursive compiler selector. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarCallReturn
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def args {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) : Args C (Parameters R) (Parameters R) :=
 entryArgs R hm (.there .here) .here

def call {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (f : Name) (depth : Nat) :
 Stmt C (Parameters R) (Parameters R) :=
 InterfaceV1.recursiveSource f (args hm) (.val .uint (.user "result") (some .here)) (ScalarRecursiveSource.step R hm) depth

def image {C : Contract} {R : RefTy} (b : Nat) (F : Frag (Parameters R)) (pointer bottom : Nat) : List Instr :=
 [.push w[0],.mstore (b+2)] ++
 (ScalarReturn.image (C:=C) b F pointer bottom ++
 Result.code b (.push .refl : Ext (Parameters R) (Frame R)) .here .here)

theorem arguments {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Parameters R)) (count : Nat) (bound : count<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref) :
 (args hm).evalT σ=.ok (countValue count bound,(some ref,())) := by
 simp only [args,entryArgs,Args.evalT,MPath.mvalT,alias,Val.evalT,Simple.evalT,counter,ok_bind]
 rfl

theorem source {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Parameters R)) (count : Nat) (bound : count<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (f : Name) (depth : Nat) :
 (call hm f depth).run σ=if count<depth then
   .ok ⟨σ.setLocal .here (countValue count bound),List.prefix_refl _⟩ else .error .exhausted :=
 ScalarRecursiveSource.call_all_horizons hm f (args hm) .here depth σ count bound ref
   (arguments hm σ count bound ref counter alias)

/-- The source caller supplies the only initial representation. Private
entry, both runtime loops and the physically distinct result copy all execute;
no callee midpoint, result value or whole-call simulation is assumed. -/
theorem endpoint {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (count : Nat) (bound : count<W)
 (σ : State C (Parameters R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer bottom start : Nat) (locals : b+3≤lo) (above : lo≤pointer)
 (below : pointer<frame) (payload : lo≤start) (separate : pointer<start)
 (bottomAbove : b+3≤bottom) (bottomBelow : bottom<frame) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) :
 ∃ after addresses,
 run (image (C:=C) b F pointer bottom) before=.ok after 0 ∧
 (∀ f depth,(call hm f depth).run σ=if count<depth then
   .ok ⟨σ.setLocal .here (countValue count bound),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr L b frame F (σ.setLocal .here (countValue count bound)) addresses after ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 after.mem pointer=.val (wmod start) ∧ after.mem bottom=.val (wmod start) ∧ after.mem b=before.mem b ∧
 after.mem (b+1)=.val (wmod count) ∧ after.mem (b+2)=.val (wmod count) ∧
 GrowsAllocator b frame 0 σ base before (σ.setLocal .here (countValue count bound)) addresses after ∧
 (∀ x,x≠pointer → x≠bottom → x≠b → x≠b+1 → x≠b+2 →
   (x<start ∨ start+2*count≤x) → after.mem x=before.mem x) ∧
 (∀ j,j<count → after.mem (start+2*j)=before.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (count-j))) := by
 let entered := writeMachine before (b+2) w[0]
 let child := σ.push (t:=.val .uint) (PrimTy.dflt .uint)
 have childRepr := repr.consVal (PrimTy.dflt .uint) w[0] (ReprV.dflt_zero .uint)
   (by change b+3≤frame;omega)
 obtain ⟨last,addresses,body,sourceBody,reached,stack,extended,cursor,bottomWord,reference,growth,outside,saved⟩ :=
   ScalarReturn.endpoint hm count bound child ref counter alias base entered childRepr lo pointer bottom start
     locals above below payload separate bottomAbove bottomBelow bottomBefore bottomSeparate capacity fits
       ((upd_other before.mem w[0] (by omega)).trans current)
 have exported :=  Result.export_result reached (.push .refl : Ext (Parameters R) (Frame R)) .here .here
 have exportGrowth := Result.allocator reached (.push .refl : Ext (Parameters R) (Frame R)) .here .here
 let after := writeMachine last (b+1) (last.mem (b+2))
 have word : last.mem (b+2)=.val (wmod count) := by
   have represented := reached.core.vals (.here : Idx (Frame R) (.val .uint))
   have encoded : ReprV .uint (countValue count bound) (.val (wmod count)) := by
     have same : wmod count=(⟨count,bound⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bound)
     rw [same]
     exact ReprV.uint_of rfl
   exact Restored.value_unique represented encoded
 have unchanged : ∀ x,x≠b+1 → after.mem x=last.mem x := fun x different => upd_other _ _ different
 refine ⟨after,addresses,?_,?_,exported.2,stack,extended,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · unfold image
   have entry : run [.push w[0],.mstore (b+2)] before=.ok entered 0 := rfl
   rw [run_append_ok entry,run_append_ok body]
   exact exported.1
 · intro f depth
   exact source hm σ count bound ref counter alias f depth
 · exact (unchanged pointer (by omega)).trans cursor
 · exact (unchanged bottom (by omega)).trans bottomWord
 · exact (unchanged b (by omega)).trans (reference.trans (upd_other before.mem w[0] (by omega)))
 · exact (upd_same _ _ _).trans word
 · exact (unchanged (b+2) (by omega)).trans word
 · intro allocation positive initial space
   have privateOwner := initial.localWrite (b+2) (by omega) (by omega) w[0]
   have bodyOwner := growth allocation positive privateOwner space
   simpa only [Nat.add_zero] using exportGrowth allocation positive bodyOwner space
 · intro x hp hb hr hc hv region
   exact (unchanged x hc).trans ((outside x hp hb hr hc hv region).trans (upd_other before.mem w[0] hv))
 · intro j small
   have oldRef : entered.mem b=before.mem b := upd_other before.mem w[0] (by omega)
   exact ⟨(unchanged _ (by omega)).trans (((saved j small).1.trans oldRef)),
     (unchanged _ (by omega)).trans (saved j small).2⟩

theorem export_distinct {R : RefTy} (b : Nat) :
 cellOf b (.here : Idx (Parameters R) (.val .uint))≠cellOf b (.here : Idx (Frame R) (.val .uint)) := by
 change b+1≠b+2
 omega

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarCallReturn

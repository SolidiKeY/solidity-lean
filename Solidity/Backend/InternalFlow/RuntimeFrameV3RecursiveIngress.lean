import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOutcome

/-! Actual runtime cursor-to-bottom setup for recursive descent/unwind.
The bottom sentinel is emitted, not supplied as an initial-memory oracle.
Generic frozen Entry transport preserves all represented fields and capacity;
this is not a whole general recursive compiler or approved-domain producer. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveIngress
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

def code (pointer bottom : Nat) : List Instr := [.mload pointer,.mstore bottom]
def prepared (before : Machine) (pointer bottom : Nat) : Machine := writeMachine before bottom (before.mem pointer)

theorem executed (before : Machine) (pointer bottom : Nat) :
 run (code pointer bottom) before=.ok (prepared before pointer bottom) 0 := rfl

/-- Actual workspace writes preserve the existing allocator, not a new owner. -/
theorem growth {C : Contract} {Γ : Ctx} {b frame : Nat}
 (σ : State C Γ) (base : Nat → Fin W) (before : Machine) (pointer bottom : Nat)
 (positive : 0<bottom) (below : bottom<frame) :
 GrowsAllocator b frame 0 σ base before σ base (prepared before pointer bottom) := by
 intro cursor basePositive owner room
 simpa only [Nat.add_zero,prepared] using owner.localWrite bottom positive below (before.mem pointer)

/-- The frozen Entry's workspace establishes a private bottom cell one word
below localLimit. No bottom-value or target-execution premise is added. -/
theorem entry_prepared {C : Contract} {Γ Δ : Ctx}
 (plan : InterfaceV1.Emission C Γ Δ) {L b frame : Nat} {F : Frag Γ} {σ : State C Γ}
 {base : Nat → Fin W} {before : Machine} {start : Nat}
 (entry : InterfaceV1.Entry plan L b frame F σ base before start)
 (workspace : Γ.length+2≤plan.need) (pointer : plan.pointerCell=plan.localLimit) :
 run (code plan.pointerCell (plan.localLimit-1)) before=.ok (prepared before plan.pointerCell (plan.localLimit-1)) 0 ∧
 InterfaceV1.Entry plan L b frame F σ base (prepared before plan.pointerCell (plan.localLimit-1)) start ∧
 (prepared before plan.pointerCell (plan.localLimit-1)).mem (plan.localLimit-1)=.val (wmod start) ∧
 Footprint.Words plan.localLimit start before (prepared before plan.pointerCell (plan.localLimit-1)) ∧
 GrowsAllocator b frame 0 σ base before σ base (prepared before plan.pointerCell (plan.localLimit-1)) := by
 have workspaceBound := entry.workspace
 have pointerBound := entry.pointerBelow
 rw [pointer] at pointerBound
 have positive : 0<plan.localLimit-1 := by omega
 have bottomBound : b+Γ.length≤plan.localLimit-1 := by omega
 have below : plan.localLimit-1<frame := by omega
 have represented := reserved_write entry.represented (plan.localLimit-1) bottomBound below (before.mem plan.pointerCell)
 have grows := growth (b:=b) σ base before plan.pointerCell (plan.localLimit-1) positive below
 have capacity : AllocationInput b frame (plan.heapCost σ) σ base (prepared before plan.pointerCell (plan.localLimit-1)) :=
   grows.nextInput (by simpa only [Nat.zero_add] using entry.capacity)
 have cursor : (prepared before plan.pointerCell (plan.localLimit-1)).mem plan.pointerCell=.val (wmod start) :=
   (upd_other _ _ (by omega)).trans entry.cursor
 refine ⟨executed before _ _,?_,?_,?_,grows⟩
 · exact ⟨represented,entry.callerBound,entry.resultBound,entry.workspace,entry.pointerAbove,entry.pointerBelow,
     entry.payloadAbove,entry.reserve,entry.controlSpace,entry.separate,entry.noWrap,cursor,capacity⟩
 · exact (upd_same _ _ _).trans entry.cursor
 · exact Footprint.write_below before _ _ (by omega)

theorem after_setup {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
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
 (bottomSeparate : bottom≠pointer) (bottomPrivate : bottom<lo) :
 ∃ (out : Solidity.Out C σ.H (Parameters A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingActivation.body (count+1)).run σ=.ok out ∧ run (code pointer bottom++AllocatingReturn.image (C:=C) b F pointer bottom) before=.ok last 0 ∧
 StateRepr L b frame F out.st addresses last ∧ last.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator b frame (4*count) σ base before out.st addresses last ∧
 last.mem pointer=.val (wmod start) ∧ last.mem b=before.mem b ∧
 (∀ j,j<count → last.mem (start+2*j)=before.mem b ∧ last.mem (start+2*j+1)=.val (wmod (count-j))) ∧
 Footprint.Words lo start before last := by
 have below : bottom<frame := by omega
 have initial := reserved_write repr bottom (by change b+(Parameters A).length≤bottom;change b+2≤bottom;omega) below (before.mem pointer)
 have owned := owner.localWrite bottom (by omega) below (before.mem pointer)
 have pointerValue : (prepared before pointer bottom).mem pointer=.val (wmod start) :=
   (upd_other _ _ bottomSeparate.symm).trans current
 have bottomValue : (prepared before pointer bottom).mem bottom=.val (wmod start) :=
   (upd_same _ _ _).trans current
 obtain ⟨out,last,addresses,source,target,represented,stack,extended,bodyGrowth,cursor,reference,saved,outside⟩ :=
   AllocatingReturn.endpoint count bound σ ref counter alias reads base (prepared before pointer bottom) initial
     cursor owned positive heapSpace lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits
     pointerValue bottom bottomAbove bottomBefore bottomSeparate bottomValue
 have grow := (growth σ base before pointer bottom (by omega) below).comp bodyGrowth
 refine ⟨out,last,addresses,source,(run_append_ok (executed before pointer bottom)).trans target,represented,stack,extended,?_,
   cursor,?_,?_,?_⟩
 · simpa only [Nat.zero_add] using grow
 · exact reference.trans (upd_other _ _ (by omega))
 · intro j small
   exact ⟨(saved j small).1.trans (upd_other _ _ (by omega)),(saved j small).2⟩
 · intro x lower upper
   by_cases same : x=pointer
   · subst x
     exact cursor.trans current.symm
   · exact (outside x (by omega) (by omega) (by omega) (by omega) (by omega) same (.inl upper)).trans
       (upd_other _ _ (by omega))

namespace Checks
open CountdownWitness
abbrev before := AllocatorReturn.Checks.input

def plan : InterfaceV1.Emission P.C (Parameters CountdownWitness.A) (Parameters CountdownWitness.A) :=
 ⟨code 8 7++AllocatingReturn.image (C:=P.C) 2 F 8 7,F,4,8,8,(fun _ => 6),(fun _ => 8)⟩

/-- This is the concrete count-two entry witness, not a universal profile or
ReturnClaim for the demonstration's fixed metadata. -/
theorem entry : InterfaceV1.Entry plan 1 2 16 F callee P.base before 10 where
 represented := AllocatorReturn.Checks.represented
 callerBound := by decide
 resultBound := by decide
 workspace := by decide
 pointerAbove := by decide
 pointerBelow := by decide
 payloadAbove := by decide
 reserve := by decide
 controlSpace := by decide
 separate := .inl (by decide)
 noWrap := by decide
 cursor := rfl
 capacity := .inr ⟨by decide,⟨22,by decide⟩,AllocatorReturn.Checks.ownership,by decide⟩

theorem initialized :
 run (code 8 7) before=.ok (prepared before 8 7) 0 ∧
 InterfaceV1.Entry plan 1 2 16 F callee P.base (prepared before 8 7) 10 ∧
 (prepared before 8 7).mem 7=w[10] ∧ Footprint.Words 8 10 before (prepared before 8 7) ∧
 GrowsAllocator 2 16 0 callee P.base before callee P.base (prepared before 8 7) :=
 entry_prepared plan entry (by decide) rfl

theorem initialized_eq : prepared before 8 7=ParentPrefixes.Checks.input := rfl

theorem missing_setup : before.mem 7≠w[10] := by decide

theorem available :
 ∃ (out : Solidity.Out P.C callee.H (Parameters CountdownWitness.A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingActivation.body 3).run callee=.ok out ∧ run plan.code before=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧ last.stack=before.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 8 callee P.base before out.st addresses last ∧
 last.mem 8=w[10] ∧ last.mem 2=before.mem 2 ∧
 (∀ j,j<2 → last.mem (10+2*j)=before.mem 2 ∧ last.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 Footprint.Words 8 10 before last :=
 after_setup 2 (by decide) callee P.r0 rfl rfl AllocatingSource.Checks.read_bound P.base before
   AllocatorReturn.Checks.represented ⟨22,by decide⟩ AllocatorReturn.Checks.ownership (by decide) (by decide)
   8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
   7 (by decide) (by decide) (by decide) (by decide)

noncomputable def output := available.choose
noncomputable def target := available.choose_spec.choose
noncomputable def addresses := available.choose_spec.choose_spec.choose

theorem specification :
 (AllocatingActivation.body 3).run callee=.ok output ∧ run plan.code before=.ok target 0 ∧
 StateRepr 1 2 16 F output.st addresses target ∧ target.stack=before.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 8 callee P.base before output.st addresses target ∧
 target.mem 8=w[10] ∧ target.mem 2=before.mem 2 ∧
 (∀ j,j<2 → target.mem (10+2*j)=before.mem 2 ∧ target.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 Footprint.Words 8 10 before target := available.choose_spec.choose_spec.choose_spec

/-- The actual emitted prologue reaches the same already checked body input. -/
theorem prior_target : run plan.code before=.ok AllocatingReturn.Checks.machine 0 :=
 (run_append_ok (executed before 8 7)).trans (by rw [initialized_eq];exact AllocatingReturn.Checks.specification.2.1)

theorem same : output=AllocatingReturn.Checks.output ∧ target=AllocatingReturn.Checks.machine :=
 ⟨Except.ok.inj (specification.1.symm.trans AllocatingReturn.Checks.specification.1),
   (Evm.Out.ok.inj (specification.2.1.symm.trans prior_target)).1⟩

/-- A genuine inhabitant of the frozen Returned relation for this entry. -/
theorem returned : InterfaceV1.Returned plan 1 2 16 callee P.base before 10 output := by
 rcases specification with ⟨source,targetRun,repr,stack,extended,growth,cursor,reference,saved,words⟩
 exact ⟨target,addresses,targetRun,repr,stack,extended,growth,cursor,words⟩

theorem observations :
 (target.stack,[target.mem 0,target.mem 1,target.mem 2,target.mem 3,target.mem 7,target.mem 8,target.mem 9,
 target.mem 10,target.mem 11,target.mem 12,target.mem 13,target.mem 16,target.mem 17,target.mem 18,target.mem 20,target.mem 21])=
 ([w[77]],[w[30],w[16],w[16],w[2],w[10],w[10],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 rw [same.2]
 exact AllocatingReturn.Checks.observations

theorem wrong_source : (prepared before 9 7).mem 7≠w[10] := by decide

/-- A successful machine write to a caller cell is not preservation of its
source representation. This is a failed frame premise, not runtime rejection. -/
theorem overlap_not_represented : ¬StateRepr 1 2 16 F callee P.base (prepared before 8 3) := by
 intro bad
 have word := bad.core.vals (.here : Idx (Parameters CountdownWitness.A) (.val .uint))
 change ReprV .uint (countValue 2 (by decide)) w[10] at word
 exact (by decide : (w[10] : Word)≠w[2]) (Restore.uint_unique word (ReprV.uint_of rfl))

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveIngress

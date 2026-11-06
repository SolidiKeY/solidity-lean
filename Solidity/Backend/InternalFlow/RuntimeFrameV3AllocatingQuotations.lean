import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingArguments

/-! The same actual allocating target image is matched to all sufficient native
quotation indices. Shallow quotations remain exhausted; no target failure or
failed state is inferred. This is the countdown family, not arbitrary recursive
compiler admission or source-approved-domain provenance. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingQuotations
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
abbrev A : RefTy := CountdownWitness.A

/-- A known actual return fixes the full dependent output at every sufficient
index. The valid-read domain is necessary for the exhaustion classification. -/
theorem source_classification {C : Contract} {Γ : Ctx} (name : Name) (args : Args C Γ (Parameters A))
 (σ : State C Γ) (a : TEnv C σ.H (Parameters A)) (evaluated : args.evalT σ=.ok a)
 (count : Nat) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) a=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) a=some ref)
 (reads : count≤σ.heap.len ref .dyn) (known : Nat) (out : Solidity.Out C σ.H Γ)
 (actual : (InterfaceV1.recursiveSource name args .none AllocatingActivation.step known).run σ=.ok out)
 (depth : Nat) :
 (InterfaceV1.recursiveSource name args .none AllocatingActivation.step depth).run σ=
   if count<depth then .ok out else .error .exhausted := by
 have values : a=(countValue count bound,(some ref,())) :=
   Prod.ext counter (Prod.ext alias (by cases a.2.2;rfl))
 have arguments : args.evalT σ=.ok (countValue count bound,(some ref,())) := evaluated.trans (congrArg Except.ok values)
 by_cases enough : count<depth
 · obtain ⟨candidate,returned,rest⟩ := AllocatingSource.call_success name args depth σ count bound ref arguments reads enough
   have same := AllocatingCoherence.source_coherence name args σ depth known candidate out returned actual
   rw [same] at returned
   simpa only [if_pos enough] using returned
 · simpa only [if_neg enough] using AllocatingSource.call_exhaustion name args depth σ count bound ref arguments reads (by omega)

/-- Uniform source-index coverage for the actual checked-prefix/body endpoint.
The target image and all allocation/frame premises are independent of depth. -/
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
 (∀ depth, (InterfaceV1.recursiveSource name args .none AllocatingActivation.step depth).run σ=
   if count<depth then .ok out else .error .exhausted) ∧
 run (compiled.checked.code++AllocatingReturn.image (C:=C) (b+Γ.length) (Frag.init (Parameters A)) pointer bottom) before=.ok target 0 ∧
 StateRepr L b frame (compiled.checked.frag.restrict Γ) out.st addresses target ∧ target.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (compiled.checked.cost σ+4*count) σ base before out.st addresses target ∧
 (∀ {t : LTy} (i : Idx Γ t), target.mem (cellOf b i)=mid.mem (cellOf b i)) ∧
 target.mem pointer=.val (wmod start) ∧
 (∀ j,j<count → target.mem (start+2*j)=.val (base ref.id) ∧ target.mem (start+2*j+1)=.val (wmod (count-j))) := by
 obtain ⟨out,target,addresses,mid,prefixRun,source,executed,represented,stack,extended,growth,words,pointerValue,saved⟩ :=
   AllocatingArguments.after_arguments name args compiled σ a evaluated count positive bound ref counter alias reads
     base before initial lo pointer bottom start room boundary localBound pointerAbove pointerBelow payloadAbove pointerBefore
     savedRoom savedFits current bottomAbove bottomBelow bottomBefore bottomSeparate bottomValue bottomScratch capacity notFragile
 exact ⟨out,target,addresses,mid,prefixRun,source_classification name args σ a evaluated count bound ref counter alias reads
   (count+1) out source,executed,represented,stack,extended,growth,words,pointerValue,saved⟩

namespace Checks
open CountdownWitness
abbrev Γ := MemoryArgument.Γ
abbrev F := MemoryArgument.F
abbrev caller := MemoryArgument.caller
abbrev input := MemoryArgument.input
abbrev args := MemoryArgument.args
abbrev child := MemoryArgument.child
abbrev checked := ArgumentEntry.Checks.checked
abbrev code := ArgumentCall.code

theorem available :
 ∃ (out : Solidity.Out P.C caller.H Γ) (target : Machine) (addresses : Nat → Fin W) (mid : Machine),
 run checked.code input=.ok mid 0 ∧ (∀ depth,(InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step depth).run caller=
   if 1<depth then .ok out else .error .exhausted) ∧ run code input=.ok target 0 ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) out.st addresses target ∧ target.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 (checked.cost caller+4*1) caller P.base input out.st addresses target ∧
 (∀ {t : LTy} (i : Idx Γ t),target.mem (cellOf 1 i)=mid.mem (cellOf 1 i)) ∧ target.mem 8=w[10] ∧
 (∀ j,j<1 → target.mem (10+2*j)=.val (P.base Evm.Memory.CompileExamples.r1.id) ∧ target.mem (10+2*j+1)=.val (wmod (1-j))) :=
 after_arguments "allocatingCountdown" args ArgumentEntry.Checks.prepared caller child.env MemoryArgument.arguments
   1 (by decide) (by decide) Evm.Memory.CompileExamples.r1 rfl rfl MemoryArgument.read_bound
   P.base input MemoryArgument.initial 7 8 7 10
   (by change 1+checked.need≤7;rw [ArgumentEntry.Checks.need_eq];decide) (by decide)
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
   (by decide) (by decide) (by decide) (by decide) rfl (by decide) ArgumentCall.total_capacity
   (by intro R i;cases i with | there i => cases i with | there i => cases i with | there i => cases i)


noncomputable def output := available.choose
noncomputable def target := available.choose_spec.choose
noncomputable def addresses := available.choose_spec.choose_spec.choose
noncomputable def midpoint := available.choose_spec.choose_spec.choose_spec.choose

theorem specification :
 run checked.code input=.ok midpoint 0 ∧
 (∀ depth,(InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step depth).run caller=
   if 1<depth then .ok output else .error .exhausted) ∧ run code input=.ok target 0 ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) output.st addresses target ∧ target.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 (checked.cost caller+4*1) caller P.base input output.st addresses target ∧
 (∀ {t : LTy} (i : Idx Γ t),target.mem (cellOf 1 i)=midpoint.mem (cellOf 1 i)) ∧ target.mem 8=w[10] ∧
 (∀ j,j<1 → target.mem (10+2*j)=.val (P.base Evm.Memory.CompileExamples.r1.id) ∧ target.mem (10+2*j+1)=.val (wmod (1-j))) :=
 available.choose_spec.choose_spec.choose_spec.choose_spec

theorem all_source (depth : Nat) :
 (InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step depth).run caller=
   if 1<depth then .ok output else .error .exhausted := specification.2.1 depth

theorem sufficient (depth : Nat) (enough : 1<depth) :
 (InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step depth).run caller=.ok output := by
 rw [all_source,if_pos enough]

theorem shallow (depth : Nat) (short : depth≤1) :
 (InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step depth).run caller=.error .exhausted := by
 rw [all_source,if_neg (by omega)]

/-- Source and target uniqueness pin the same complete previous endpoint. -/
theorem same : output=AllocatingArguments.Checks.output ∧ target=AllocatingArguments.Checks.target :=
 ⟨Except.ok.inj ((sufficient 2 (by decide)).symm.trans AllocatingArguments.Checks.specification.2.1),
   (Evm.Out.ok.inj (specification.2.2.1.symm.trans AllocatingArguments.Checks.specification.2.2.1)).1⟩

theorem target_run : run code input=.ok target 0 := specification.2.2.1

theorem observations :
 (target.stack,[target.mem 0,target.mem 1,target.mem 2,target.mem 3,target.mem 4,target.mem 5,target.mem 7,target.mem 8,target.mem 9,
 target.mem 10,target.mem 11,target.mem 12,target.mem 13,target.mem 16,target.mem 17,target.mem 18,target.mem 20,target.mem 21])=
 ([w[77]],[w[26],w[20],w[16],w[9],w[20],w[1],w[10],w[10],w[99],w[20],w[1],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]) := by
 rw [same.2]
 exact AllocatingArguments.Checks.observations

theorem source_not_revert (depth : Nat) :
 (InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step depth).run caller≠.error .revert := by
 rw [all_source]
 split <;> intro wrong <;> cases wrong

theorem success_iff (depth : Nat) :
 (InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step depth).run caller=.ok output ↔ 1<depth := by
 constructor
 · intro actual
   by_cases enough : 1<depth
   · exact enough
   · have failed := shallow depth (by omega)
     rw [failed] at actual
     cases actual
 · exact sufficient depth

/-- The fixed target succeeds even for a shallow source quotation. Thus no
all-index simulation or target failure is claimed for exhausted source runs. -/
theorem shallow_mismatch :
 (InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step 1).run caller=.error .exhausted ∧
 run code input=.ok target 0 := ⟨shallow 1 (by decide),target_run⟩

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingQuotations

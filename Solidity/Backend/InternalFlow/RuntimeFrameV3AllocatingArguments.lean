import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingZero

/-! Positive allocating countdown calls after checked argument declarations.
The reached owner and parameter frame come from actual prefix execution.
This composes the existing recursive image; it is not compiler admission for
arbitrary recursion or approved-domain provenance. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingArguments
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
abbrev A : RefTy := CountdownWitness.A

/-- The actual summed input supplies prefix room without a midpoint oracle. -/
theorem prefix_input {C : Contract} {Γ : Ctx} {b frame head tail : Nat}
 {σ : State C Γ} {base : Nat → Fin W} {before : Machine}
 (capacity : AllocationInput b frame (head+tail) σ base before) :
 AllocationInput b frame head σ base before := capacity.of_le (by omega)

/-- Arbitrary caller-context export, with explicit non-fragile caller restriction.
Body execution, low-word framing and reached allocation cost are derived from
the existing allocating return image, not supplied as simulation premises. -/
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
 (InterfaceV1.recursiveSource name args .none AllocatingActivation.step (count+1)).run σ=.ok out ∧
 run (compiled.checked.code++AllocatingReturn.image (C:=C) (b+Γ.length) (Frag.init (Parameters A)) pointer bottom) before=.ok target 0 ∧
 StateRepr L b frame (compiled.checked.frag.restrict Γ) out.st addresses target ∧ target.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (compiled.checked.cost σ+4*count) σ base before out.st addresses target ∧
 (∀ {t : LTy} (i : Idx Γ t), target.mem (cellOf b i)=mid.mem (cellOf b i)) ∧
 target.mem pointer=.val (wmod start) ∧
 (∀ j,j<count → target.mem (start+2*j)=.val (base ref.id) ∧ target.mem (start+2*j+1)=.val (wmod (count-j))) := by
 have prefixCapacity := prefix_input capacity
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
     AllocatingReturn.endpoint count bound (σ.withEnv a) ref counter alias reads middle mid parameters cursor childOwner
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
     simpa only [Nat.add_assoc,out,exported,State.withEnv] using grown
   have refWord : mid.mem (b+Γ.length)=.val (base ref.id) := by
     obtain ⟨r,value,word⟩ := parameters.pointers (.there .here)
     have same : r=ref := Option.some.inj (value.symm.trans alias)
     subst r
     exact word.trans (congrArg Word.val (extended ref))
   refine ⟨out,last,addresses,mid,executed,call_return args .none .refl (AllocatingActivation.body (count+1)).runR σ a evaluated body source,
     (run_append_ok executed).trans target,callerRepr,bodyStack.trans stack,
     BaseExtends.trans (List.prefix_refl σ.H) extended bodyExtended,totalGrowth,?_,pointerValue,?_⟩
   · intro t i
     exact midWords i
   · intro j small
     exact ⟨((saved j small).1).trans refWord,(saved j small).2⟩

/-- Exact source extension and old contents for this allocating/read-only body.
This is body-specific, not a Heap.Keeps consequence of generic call frames. -/
theorem source_fields {C : Contract} {Γ : Ctx} (name : Name) (args : Args C Γ (Parameters A))
 (σ : State C Γ) (a : TEnv C σ.H (Parameters A)) (evaluated : args.evalT σ=.ok a)
 (count depth : Nat) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) a=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) a=some ref)
 (reads : count≤σ.heap.len ref .dyn) (enough : count<depth)
 (out : Solidity.Out C σ.H Γ)
 (actual : (InterfaceV1.recursiveSource name args .none AllocatingActivation.step depth).run σ=.ok out) :
 out.st.H.length=σ.H.length+count ∧ out.st.env=TEnv.wk out.ext Γ σ.env ∧ Heap.Keeps out.ext σ.heap out.st.heap := by
 obtain ⟨body,bodyRun,size,locals,kept⟩ := AllocatingSource.success depth (σ.withEnv a) count bound ref counter alias reads enough
 have called := call_return args .none .refl (AllocatingActivation.body depth).runR σ a evaluated body bodyRun
 have same : out=exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl σ a body :=
   Except.ok.inj (actual.symm.trans called)
 subst out
 exact ⟨size,rfl,kept⟩

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
 run checked.code input=.ok mid 0 ∧ ArgumentCall.call.run caller=.ok out ∧ run code input=.ok target 0 ∧
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
 run checked.code input=.ok midpoint 0 ∧ ArgumentCall.call.run caller=.ok output ∧ run code input=.ok target 0 ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) output.st addresses target ∧ target.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 (checked.cost caller+4*1) caller P.base input output.st addresses target ∧
 (∀ {t : LTy} (i : Idx Γ t),target.mem (cellOf 1 i)=midpoint.mem (cellOf 1 i)) ∧ target.mem 8=w[10] ∧
 (∀ j,j<1 → target.mem (10+2*j)=.val (P.base Evm.Memory.CompileExamples.r1.id) ∧ target.mem (10+2*j+1)=.val (wmod (1-j))) :=
 available.choose_spec.choose_spec.choose_spec.choose_spec

/-- Uniqueness ties the new generic instance to the existing complete endpoint. -/
theorem same : output=ArgumentCall.output ∧ target=ArgumentCall.last ∧ midpoint=ArgumentEntry.Checks.target :=
 ⟨Except.ok.inj (specification.2.1.symm.trans ArgumentCall.source),
  (Evm.Out.ok.inj (specification.2.2.1.symm.trans ArgumentCall.target)).1,
  (Evm.Out.ok.inj (specification.1.symm.trans ArgumentEntry.Checks.target_run)).1⟩

theorem represented : StateRepr 1 1 16 F output.st addresses target := by
 have repr := specification.2.2.2.1
 rw [ArgumentCall.caller_fragment] at repr
 exact repr

theorem returned_owner : StructAllocatorRepr output.st.heap addresses 16 (⟨26,by decide⟩ : Fin W) target := by
 have grown := specification.2.2.2.2.2.2.1
 have owner := grown ⟨22,by decide⟩ (by decide) MemoryArgument.ownership (by rw [ArgumentEntry.Checks.cost_zero];decide)
 simpa only [ArgumentEntry.Checks.cost_zero,Nat.zero_add] using owner

theorem source_extension : output.st.H.length=caller.H.length+1 ∧
 output.st.env=TEnv.wk output.ext Γ caller.env ∧ Heap.Keeps output.ext caller.heap output.st.heap :=
 source_fields "allocatingCountdown" args caller child.env MemoryArgument.arguments 1 2 (by decide)
   Evm.Memory.CompileExamples.r1 rfl rfl MemoryArgument.read_bound (by decide) output specification.2.1

theorem observations :
 (target.stack,[target.mem 0,target.mem 1,target.mem 2,target.mem 3,target.mem 4,target.mem 5,target.mem 7,target.mem 8,target.mem 9,
 target.mem 10,target.mem 11,target.mem 12,target.mem 13,target.mem 16,target.mem 17,target.mem 18,target.mem 20,target.mem 21])=
 ([w[77]],[w[26],w[20],w[16],w[9],w[20],w[1],w[10],w[10],w[99],w[20],w[1],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]) := by
 rw [same.2.1]
 exact ArgumentCall.observations

theorem wrong_alias : target.mem 2≠w[20] := by
 rw [same.2.1]
 exact ArgumentCall.wrong_caller_alias

theorem omitted_allocation : target.mem 0≠w[22] := by
 rw [same.2.1]
 exact ArgumentCall.omitted_allocation

theorem wrong_cost : ¬GrowsAllocator 1 16 8 caller P.base input output.st addresses target := by
 intro bad
 have cursor := (bad ⟨22,by decide⟩ (by decide) MemoryArgument.ownership (by decide)).arrays.free.cell
 have actual := returned_owner.arrays.free.cell
 have unequal : (w[26] : Word)≠w[30] := by decide
 exact unequal (actual.symm.trans cursor)

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingArguments

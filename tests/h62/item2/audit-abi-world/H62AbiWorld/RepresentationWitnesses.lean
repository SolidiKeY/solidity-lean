import H62AbiWorld.WitnessSchema
import Solidity.Backend.AbiWorld.PanicCallFrameControls
import Solidity.Backend.AbiWorld.CallerWordBytesControls
import Solidity.Backend.AbiWorld.NativeParentWordControls
import Solidity.Backend.AbiWorld.MutatingEntryWordsControls
import Solidity.Backend.AbiWorld.MutatingWritePhysicalControls

/-! The nine remaining packages. Representation, oracle compatibility, byte
images, stack contents, heap objects and layout bounds hold of the SAME actual
installed fixtures; no separately inhabited global structure is substituted. -/
namespace H62.AbiWorld.RepresentationWitnesses
open Solidity Evm Evm.Memory Solidity.Backend.AbiWorld

namespace Panic
open PanicCallFrameControls

theorem PanicCallFrame_selected_hypotheses : hypotheses% Solidity.Backend.AbiWorld.PanicCallFrame.selected :=
  ⟨contract,_,_,_,_,_,_,caller,call 7,by decide,rfl,300,by decide,[17],
    branch 10 (by decide),branch 20 (by decide),.some (.user "panicCode"),
    panicBranch,branch 30 (by decide),True.intro⟩
#print axioms PanicCallFrame_selected_hypotheses
end Panic

namespace Caller
open CallerWordBytesControls
private abbrev saved : Fin W := ⟨300,by decide⟩

theorem CallerWordBytes_recovered_hypotheses : hypotheses% Solidity.Backend.AbiWorld.CallerWordBytes.recovered :=
  ⟨loaded saved,initialBytes saved,live,image saved,cell,temporary,saved,rfl,
    [w[77]],[lenU 77 (by decide)],rfl,rfl,True.intro⟩
#print axioms CallerWordBytes_recovered_hypotheses

theorem CallerWordBytes_typed_hypotheses : hypotheses% Solidity.Backend.AbiWorld.CallerWordBytes.typed :=
  ⟨P.C,1,0,6,P.Γ,P.F,caller saved,P.base,loaded saved,loaded_repr saved,
    .here,cell,temporary,saved,rfl,initialBytes saved,live,image saved,rfl,
    [w[77]],[lenU 77 (by decide)],rfl,ReprV.uint_of rfl,True.intro⟩
#print axioms CallerWordBytes_typed_hypotheses
end Caller

namespace Native
open Solidity.Backend.InternalFlow.RuntimeFrame
open RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes AllocatingEmission
open CountdownWitness

theorem NativeParentWord_represented_counter_hypotheses : hypotheses% Solidity.Backend.AbiWorld.NativeParentWord.represented_counter :=
  ⟨P.C,1,2,16,F,callee,P.base,ParentPrefixes.Checks.input,2,by decide,
    ParentPrefixes.Checks.initial,rfl,True.intro⟩
#print axioms NativeParentWord_represented_counter_hypotheses

theorem NativeParentWord_native_parent_hypotheses : hypotheses% Solidity.Backend.AbiWorld.NativeParentWord.native_parent := by
  refine ⟨P.C,2,8,1,16,F,callee,P.base,EmissionPrefixes.Checks.before,10,[17],
    AllocatingEmission.Checks.entry,?_,1,?_,True.intro⟩
  · rw [AllocatingEmission.Checks.counter_two,AllocatingEmission.Checks.length_two]
    decide
  · rw [AllocatingEmission.Checks.counter_two]
    decide
#print axioms NativeParentWord_native_parent_hypotheses

theorem MutatingEntryWords_allocated_read_hypotheses : hypotheses% Solidity.Backend.AbiWorld.MutatingEntryWords.allocated_read := by
  refine ⟨P.C,callee,1,by decide,P.r0,?_,True.intro⟩
  rw [HeapDomain.Checks.length_zero]
  decide
#print axioms MutatingEntryWords_allocated_read_hypotheses

theorem MutatingEntryWords_represented_element_hypotheses : hypotheses% Solidity.Backend.AbiWorld.MutatingEntryWords.represented_element :=
  ⟨P.C,1,2,16,F,callee,P.base,ParentPrefixes.Checks.input,P.r0,1,9,
    by decide,by decide,ParentPrefixes.Checks.initial,by with_unfolding_all rfl,True.intro⟩
#print axioms MutatingEntryWords_represented_element_hypotheses

theorem MutatingEntryWords_observed_activation_hypotheses : hypotheses% Solidity.Backend.AbiWorld.MutatingEntryWords.observed_activation := by
  refine ⟨P.C,1,2,16,F,callee,1,by decide,P.r0,rfl,rfl,?_,P.base,
    ParentPrefixes.Checks.input,ParentPrefixes.Checks.initial,⟨22,by decide⟩,
    ParentPrefixes.Checks.ownership,by decide,by decide,8,8,10,
    by decide,by decide,by decide,by decide,by decide,by decide,by decide,[17],rfl,True.intro⟩
  rw [HeapDomain.Checks.length_zero]
  decide
#print axioms MutatingEntryWords_observed_activation_hypotheses

theorem MutatingWritePhysical_write_prefix_hypotheses : hypotheses% Solidity.Backend.AbiWorld.MutatingWritePhysical.write_prefix := by
  refine ⟨P.C,1,2,16,F,callee,1,by decide,P.r0,rfl,rfl,?_,P.base,
    MutatingWritePhysicalControls.before,ParentPrefixes.Checks.initial,
    MutatingWritePhysicalControls.bytes,MutatingWritePhysicalControls.live,
    MutatingWritePhysicalControls.initial,by decide,[lenU 77 (by decide)],True.intro⟩
  rw [HeapDomain.Checks.length_zero]
  decide
#print axioms MutatingWritePhysical_write_prefix_hypotheses
end Native
end H62.AbiWorld.RepresentationWitnesses

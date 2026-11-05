import Solidity.Yul.Views.MixedNominalAllocation
import Solidity.Yul.Views.MixedNominalGeneratedControls

/-! Actual allocation of a second mixed fixed/nominal struct computes its raw
image and allocated heap roundtrip. Initial image reads are derived from encoding
its genuine generated inventory, not assumed final allocation agreement. -/
namespace Solidity.Yul.Views.MixedNominalInventory.AllocationControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalMember.StructControls

def newData : Source.Data env.layout ty := .struct newFields
theorem prepared : ComputedPlacement.prepare heap=.ok placement :=
  ComputedPlacement.prepare_success heap (by decide) (by decide)
theorem bound : placement.free.val+max 1 (MemoryShape.strct 3).size<2^256 := by decide

def allocatedPlacement := ComputedAllocationWrite.placement heap placement prepared newData (.strct 3) rfl bound
def after := objectAllocatedState state newData

theorem allocation_constructed (residual : ByteView) : ∃ raw,
    ComputedAllocationWrite.prepare heap placement prepared newData (.strct 3) rfl bound
      (encodeMixedHeap placement (generatedHeapEntries placement) residual)=some raw ∧
    (Source.allocRef newData).run state=(.ok (.memRef rfl 1),after) ∧
    Source.MemOK env heap.ty after ∧
    prepareHeapInventory allocatedPlacement=.ok (generatedHeapEntries allocatedPlacement) ∧
    encodeMixedHeap allocatedPlacement (generatedHeapEntries allocatedPlacement) raw=raw ∧
    writeback after allocatedPlacement allocatedPlacement .initial (generatedHeapEntries allocatedPlacement) raw=some (.ok (),after) := by
  first | solve | simp only
        | have supported : TypeSupported env ty := profile
          have inner : Source.Data.Inner (E:=env) newData :=
            ⟨⟨_,rfl⟩,⟨⟨_,rfl⟩,⟨⟨_,rfl⟩,trivial⟩⟩⟩
          have valid : Source.DataOK env heap.ty newData := .struct new_repr.dataOK
          obtain ⟨raw,step⟩ := Option.isSome_iff_exists.mp
            (computed_allocation_complete heap placement prepared newData (.strct 3) rfl bound _ supported inner valid)
          have ready := owner_prepares heap.ty state placement GeneratedControls.actual_MemOK GeneratedControls.heap_profile
          obtain ⟨_,_,distinct⟩ := prepareHeapInventory_ok placement _ ready
          have facts := computed_allocation_sound heap.ty state placement prepared newData (.strct 3) rfl bound
            _ raw step GeneratedControls.actual_MemOK inner valid supported GeneratedControls.heap_profile
            (encodeMixedHeap_reads placement (generatedHeapEntries placement) distinct residual)
          exact ⟨raw,step,facts⟩

theorem fresh_and_old : after.2.heap.next=2 ∧
    after.2.heap.get 0=some ⟨ty,Source.Data.struct oldFields⟩ ∧
    after.2.heap.get 1=some ⟨ty,newData⟩ ∧ after.1=state.1 := by
  first | solve | rfl
        | exact ⟨rfl,rfl,rfl,rfl⟩

theorem old_profile_insufficient : ¬ InventoryTypeSupported env ty := by
  intro support
  have impossible : ExtendedMemberType env.layout (.fixed Solidity.Yul.Views.Controls.scaled16) :=
    support _ List.mem_cons_self
  simp only [ExtendedMemberType,OrdinaryMemberType,CanonicalScalarType,Source.STy.loc?,reduceCtorEq,or_self] at impossible

end Solidity.Yul.Views.MixedNominalInventory.AllocationControls

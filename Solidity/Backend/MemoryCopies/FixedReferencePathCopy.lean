import Solidity.Backend.MemoryCopies.FixedReferencePathCopyInterface
import Solidity.Backend.MemoryCopies.NestedStorageHeader

/-! Actual selected storage values retain arbitrary shadows. A proved intrinsic
count equality aligns their canonical rows with the existing parent kernel. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_reference_path_copy_correct {C : Contract} {Γ : Ctx} {primitive : PrimTy} {count L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (reference : SRef C (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count)))
    (represented : Sim C L b frag state machine) (allocator : Objects.AllocatorRepr state.heap base frame cursor machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some value) :
    (∃ fits, FixedReferencePathCopyResult b frame state base cursor machine path value fits) ∨
    (¬ cursor.val + fixedReferenceStorageParentDemand (fixedReferenceLiveRows value) < W ∧
      run (fixedReferencePathCopyCode b path) machine = .revert) := by
  obtain ⟨source,pathRun,originalRepr,canonicalRepr⟩ :=
    fixed_reference_path_select state machine path reference value represented supported resolved found
  simp only [FixedReferencePathCopyResult]
  have countEq : (fixedReferenceLiveRows value).length = count := fixed_reference_live_count value
  generalize rowsEq : fixedReferenceLiveRows value = rows at *
  subst count
  have canonical : fixedReferenceLiveCanonical value = fixedReferenceStorageValue primitive rows := by
    apply congrArg SVal.fixed
    apply SVec.eq_of_toList_eq
    change (fixedReferenceLiveCanonical value).view.toList = (nestedStorageValues primitive rows).toList
    rw [fixed_reference_live_rows,rowsEq,nested_storage_header_values]
  have sourceRepr : ReprAt machine.store L (.ref (.fixed (.ref (.array (.prim primitive))) rows.length)) source
      (fixedReferenceStorageValue primitive rows) := by
    rw [← canonical]
    exact canonicalRepr
  have copying : value.copyStToM state.heap rfl = (fixedReferenceStorageValue primitive rows).copyStToM state.heap rfl := by
    rw [fixed_reference_live_copy,canonical]
  rcases fixed_reference_storage_parent_correct state.heap primitive rows base frame cursor machine source L allocator sourceRepr with success | refusal
  · obtain ⟨fits,base',target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,growth⟩ := success
    left
    refine ⟨fits,base',target,?_,?_,?_,extension,shape,below,?_,?_,?_,?_,?_,?_⟩
    · rw [fixedReferencePathCopyCode,run_append_ok pathRun]
      exact ran
    · rw [copying]
      exact allocated
    · rw [copying]
      exact root
    · rw [copying]
      exact gaps
    · exact SVal.keeps_copyStToM value rfl state.heap
    · rw [copying]
      exact fresh
    · rw [copying]
      exact length
    · exact (storageHeapContents value rfl).contents state.heap
    · rw [copying]
      exact growth
  · right
    refine ⟨refusal.1,?_⟩
    rw [fixedReferencePathCopyCode,run_append_ok pathRun]
    exact refusal.2

def fixedReferencePathCopy : FixedReferencePathCopyCertificate := ⟨fixed_reference_path_copy_correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_path_copy_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_path_copy_correct
/--
info: 'Solidity.Backend.MemoryCopies.fixedReferencePathCopy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixedReferencePathCopy
end Solidity.Backend.MemoryCopies

import Solidity.Theorems
import Solidity.Semantics.Termination
import Solidity.Semantics.LexMetrics
import Solidity.Examples.LexMetrics
import Solidity.Examples.Tactics.LexAnnotations
import Solidity.Calculus.LexVariantSound
import Solidity.Calculus.Sound.LoopLexDiamond
import Solidity.Examples.LexDiamond
import Solidity.Examples.Tactics.LexDiamond
import Solidity.Calculus.FiniteMembership
import Solidity.Calculus.FilteredMembership
import Solidity.Calculus.MemoryWitness
import Solidity.Examples.DecisionMemory
import Solidity.Examples.Tactics.FilteredSets
import Solidity.Calculus.Preconditions
import Solidity.Examples.SourceCounterexample
import Solidity.Evm.Memory
import Solidity.Evm.MemoryStructExamples
import Solidity.Evm.MemoryStructDefaultExamples
import Solidity.Evm.MemoryStructCopyExamples
import Solidity.Evm.MemoryPathExamples
import Solidity.Evm.MemoryRefArrayExamples
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Evm.MemoryFixedChildArrayExamples
import Solidity.Evm.MemoryPrimitiveStructArrayDefaultExamples
import Solidity.Evm.MemoryFixedDefaultExamples
import Solidity.Evm.MemoryDynamicFixedDefaultExamples
import Solidity.Evm.MemoryNestedFixedDefaultExamples
import Solidity.Evm.MemoryReferenceArrayRebindExamples
import Solidity.Evm.MemoryFixedDynamicDefaultExamples
import Solidity.Evm.MemoryObjectConstructionExamples
import Solidity.Evm.MemoryStructArrayInputExamples
import Solidity.Evm.MemoryObjectEmpty
import Solidity.Evm.MemoryAllocExamples
import Solidity.Evm.MemoryAllocSourceExamples
import Solidity.Evm.MemoryExamples
import Solidity.Evm.MemoryCompileExamples
import Solidity.Evm.MemoryExprExamples
import Solidity.Examples.Tactics.Nonvacuity
import Solidity.Examples.Tactics.AllLeftLater
import Solidity.Examples.Tactics.Nonlinear
import Solidity.Examples.Tactics.ArrayScans
import Solidity.Examples.Tactics.OpenLoops
import Solidity.Examples.Tactics.ComputedRevert
import Solidity.Examples.Tactics.Decide
import Solidity.Examples.Tactics.Rigid
import Solidity.Roadmap.Controls
import Solidity.Source.TypingExamples
import Solidity.Frontend.Static.UnitsExamples
import Solidity.Frontend.Static.Certificates
import Solidity.Frontend.Static.InferExamples
import Solidity.Frontend.Static.InheritanceExamples
import Solidity.Source.StateExamples
import Solidity.Frontend.Checked.LexExamples
import Solidity.Frontend.Checked.TypeExamples
import Solidity.Frontend.Checked.ExprExamples
import Solidity.Frontend.Checked.UnitExamples
import Solidity.Source.SemanticsExamples
import Solidity.Source.Unique
import Solidity.Source.Horizon
import Solidity.Source.Session
import Solidity.Source.SoundnessExamples

/-! Local and CI gate for the transitive axioms of the public proof bridges.
Unlike a source scan, this follows dependencies through every imported module.
The normal build also pins their printed axiom sets in `Solidity.Theorems`.
-/
open Lean Elab Command

run_cmd do
  let headlines : List Name := [
    ``Solidity.MemoryWitness.bind_exact,
    ``Solidity.MemoryWitness.heap_get,
    ``Solidity.MemoryWitness.reference_eq_iff,
    ``Solidity.MemoryWitness.Checked.refutes,
    ``Solidity.Fml.checkMemoryAt_eq_checkMemoryAtM,
    ``Solidity.Decide.decideMem_sound,
    ``Solidity.Decide.decideMem_refutes,
    ``Solidity.Examples.Decision.gapMemParam_countermodel,
    ``Solidity.Examples.Decision.gapMemParam_verdict,
    ``Solidity.Examples.Decision.gapMemParam_empty,
    ``Solidity.Examples.Decision.memParamSame_valid,
    ``Solidity.Examples.Decision.memParamAliasBad_countermodel,
    ``Solidity.Examples.Decision.memoryAlias_equalContents,
    ``Solidity.Examples.Decision.memoryAlias_differentContents,
    ``Solidity.Examples.Decision.memoryParameter_emptyDomains,
    ``Solidity.Evm.Memory.Objects.DefaultBuilder.empty,
    ``Solidity.Evm.Memory.Objects.DefaultBuilder.primitiveStruct,
    ``Solidity.Evm.Memory.Objects.DefaultBuilder.fixedPrimitive,
    ``Solidity.Evm.Memory.Objects.DefaultBuilder.fixedReference,
    ``Solidity.Evm.Memory.Objects.defaultChildrenCopy_succ,
    ``Solidity.Evm.Memory.Objects.defaultChildren_sim,
    ``Solidity.Evm.Memory.Objects.referenceArrayCopy_source,
    ``Solidity.Evm.Memory.Objects.referenceFixedCopy_source,
    ``Solidity.Evm.Memory.Objects.referenceArray_correct,
    ``Solidity.Evm.Memory.Objects.defaultDeclare_correct,
    ``Solidity.Evm.Memory.Objects.referenceDeclare_correct,
    ``Solidity.Evm.Memory.Objects.referenceRebind_correct,
    ``Solidity.Evm.Memory.Objects.HeapRepr.setStruct,
    ``Solidity.Evm.Memory.Objects.AllocatorRepr.setStruct,
    ``Solidity.Evm.Memory.Objects.PtrFrag.writeField,
    ``Solidity.Evm.Memory.ReferenceDefaults.compileDefault_correct,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.initial_repr,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.initial_allocator,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.source_cost,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.compiled_input,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.compiled_agrees,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.source_result,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.target_result,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.failed_input,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.failed_agrees,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.source_bounds,
    ``Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.target_bounds,
    ``Solidity.Evm.Memory.FixedDefaultExamples.initial_repr,
    ``Solidity.Evm.Memory.FixedDefaultExamples.initial_allocator,
    ``Solidity.Evm.Memory.FixedDefaultExamples.source_cost,
    ``Solidity.Evm.Memory.FixedDefaultExamples.compiled_input,
    ``Solidity.Evm.Memory.FixedDefaultExamples.compiled_agrees,
    ``Solidity.Evm.Memory.FixedDefaultExamples.source_result,
    ``Solidity.Evm.Memory.FixedDefaultExamples.target_result,
    ``Solidity.Evm.Memory.FixedDefaultExamples.failed_input,
    ``Solidity.Evm.Memory.FixedDefaultExamples.failed_agrees,
    ``Solidity.Evm.Memory.FixedDefaultExamples.source_bounds,
    ``Solidity.Evm.Memory.FixedDefaultExamples.target_bounds,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.initial_repr,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.initial_allocator,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.source_cost,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.compiled_input,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.compiled_agrees,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.source_result,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.target_result,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.failed_input,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.failed_agrees,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.source_bounds,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.target_bounds,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.initial_repr,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.initial_allocator,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.source_cost,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.compiled_input,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.compiled_agrees,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.source_result,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.target_result,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.failed_input,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.failed_agrees,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.source_bounds,
    ``Solidity.Evm.Memory.NestedFixedDefaultExamples.target_bounds,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.initial_repr,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.initial_allocator,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.source_cost,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.compiled_input,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.compiled_agrees,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.source_result,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.target_result,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.failed_input,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.failed_agrees,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.source_bounds,
    ``Solidity.Evm.Memory.ReferenceArrayRebindExamples.target_bounds,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.initial_repr,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.initial_allocator,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.source_cost,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.compiled_input,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.compiled_agrees,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.source_result,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.target_result,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.failed_input,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.failed_agrees,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.source_bounds,
    ``Solidity.Evm.Memory.FixedDynamicDefaultExamples.target_bounds,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.exact_capacity_input,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.exact_capacity_agrees,
    ``Solidity.Evm.Memory.DynamicFixedDefaultExamples.insufficient_capacity_refuted,
    ``Solidity.Evm.Memory.Objects.AllocatorRepr.reserveArray,
    ``Solidity.Evm.Memory.Objects.AllocatorRepr.writeGap,
    ``Solidity.Evm.Memory.Objects.Gap.allocateEmpty,
    ``Solidity.Evm.Memory.Objects.AllocatorRepr.adoptReservedArray,
    ``Solidity.Evm.Memory.Objects.childrenCopy_ids,
    ``Solidity.Evm.Memory.Objects.children_sim,
    ``Solidity.Evm.Memory.Objects.nestedCopy_source,
    ``Solidity.Evm.Memory.Objects.nested_correct,
    ``Solidity.Evm.Memory.Objects.StateRepr.adopt,
    ``Solidity.Evm.Memory.Objects.nestedDeclare_correct,
    ``Solidity.Evm.Memory.Objects.nestedRebind_correct,
    ``Solidity.Evm.Memory.Objects.AllocatorRepr.allocatePrimitive,
    ``Solidity.Evm.Memory.Objects.primitiveDeclare_correct,
    ``Solidity.Evm.Memory.Objects.primitiveRebind_correct,
    ``Solidity.Evm.Memory.Objects.newEmpty_correct,
    ``Solidity.Evm.Memory.Objects.rebindEmpty_correct,
    ``Solidity.Evm.Memory.Construction.StmtFrag.correct,
    ``Solidity.Evm.Memory.Construction.ProgFrag.correct,
    ``Solidity.Evm.Memory.ConstructionExamples.initial_repr,
    ``Solidity.Evm.Memory.ConstructionExamples.initial_allocator,
    ``Solidity.Evm.Memory.ConstructionExamples.source_cost,
    ``Solidity.Evm.Memory.ConstructionExamples.compiled_input,
    ``Solidity.Evm.Memory.ConstructionExamples.compiled_agrees,
    ``Solidity.Evm.Memory.ConstructionExamples.source_result,
    ``Solidity.Evm.Memory.ConstructionExamples.target_result,
    ``Solidity.Evm.Memory.ConstructionExamples.failed_input,
    ``Solidity.Evm.Memory.ConstructionExamples.failed_agrees,
    ``Solidity.Evm.Memory.ConstructionExamples.source_bounds,
    ``Solidity.Evm.Memory.ConstructionExamples.target_bounds,
    ``Solidity.Evm.Memory.ConstructionExamples.source_default_identities,
    ``Solidity.Evm.Memory.ConstructionExamples.target_default_identities,
    ``Solidity.Evm.Memory.ConstructionExamples.exact_capacity_input,
    ``Solidity.Evm.Memory.ConstructionExamples.exact_capacity_agrees,
    ``Solidity.Evm.Memory.ConstructionExamples.insufficient_capacity_refuted,
    ``Solidity.Evm.Memory.ConstructionExamples.unreachable_cost,
    ``Solidity.Evm.Memory.ConstructionExamples.unreachable_input,
    ``Solidity.Evm.Memory.ConstructionExamples.unreachable_source,
    ``Solidity.Evm.Memory.ConstructionExamples.unreachable_target,
    ``Solidity.Evm.Memory.ConstructionExamples.zero_source_length,
    ``Solidity.Evm.Memory.ConstructionExamples.zero_target_allocation,
    ``Solidity.Evm.Memory.ConstructionExamples.zero_public_input,
    ``Solidity.Evm.Memory.ConstructionExamples.zero_public_agrees,
    ``Solidity.Evm.Memory.ConstructionExamples.zero_public_source,
    ``Solidity.Evm.Memory.ConstructionExamples.fixed_zero_input,
    ``Solidity.Evm.Memory.ConstructionExamples.fixed_zero_agrees,
    ``Solidity.Evm.Memory.ConstructionExamples.fixed_zero_source,
    ``Solidity.Evm.Memory.ConstructionExamples.fixed_zero_target,
    ``Solidity.Evm.Memory.ConstructionExamples.fixed_child_nonempty_allocation_registered,
    ``Solidity.Evm.Memory.ConstructionExamples.fixed_parent_default_registered,
    ``Solidity.Evm.Memory.StructArrayInputExamples.initial_repr,
    ``Solidity.Evm.Memory.StructArrayInputExamples.compiled_input,
    ``Solidity.Evm.Memory.StructArrayInputExamples.compiled_agrees,
    ``Solidity.Evm.Memory.StructArrayInputExamples.source_observation,
    ``Solidity.Evm.Memory.StructArrayInputExamples.target_observation,
    ``Solidity.Evm.Memory.StructArrayInputExamples.wrong_reference_field_refuted,
    ``Solidity.Evm.Memory.StructArrayInputExamples.reference_struct_construction_refused,
    ``Solidity.Evm.Memory.StructArrayInputExamples.failed_input,
    ``Solidity.Evm.Memory.StructArrayInputExamples.failed_agrees,
    ``Solidity.Evm.Memory.StructArrayInputExamples.source_bounds,
    ``Solidity.Evm.Memory.StructArrayInputExamples.target_bounds,

    ``Solidity.Evm.Memory.ObjectArrayExamples.empty_default_simulation,
    ``Solidity.Evm.Memory.ObjectArrayExamples.empty_source_observation,
    ``Solidity.Evm.Memory.ObjectArrayExamples.empty_target_observation,
    ``Solidity.Evm.Memory.ObjectArrayExamples.empty_cursor_advanced,

    ``Solidity.Evm.Memory.Objects.emptyArray_copy,
    ``Solidity.Evm.Memory.Objects.newEmptyArray_copy,
    ``Solidity.Evm.Memory.Objects.AllocatorRepr.allocateEmpty,
    ``Solidity.Evm.Memory.Objects.defaultEmpty_correct,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.initial_repr,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.initial_allocator,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.allocator_preserved,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.allocator_overlap_refuted,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.compiled_input,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.compiled_agrees,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.source_observation,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.target_observation,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.failed_input,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.failed_agrees,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.source_bounds,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.target_bounds,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.read_input,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.read_agrees,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.source_read,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.target_read,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.alias_input,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.alias_agrees,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.source_alias,
    ``Solidity.Evm.Memory.FixedChildArrayExamples.target_alias,

    ``Solidity.Evm.Memory.Objects.Ownership.base_injective,
    ``Solidity.Evm.Memory.Objects.ArrayRepr.read,
    ``Solidity.Evm.Memory.Objects.ArrayRepr.write,
    ``Solidity.Evm.Memory.Objects.HeapRepr.setArray,
    ``Solidity.Evm.Memory.Objects.AllocatorRepr.setArray,
    ``Solidity.Evm.Memory.Objects.HeapRepr.adoptArray,
    ``Solidity.Evm.Memory.Objects.ProgFrag.correct,
    ``Solidity.Evm.Memory.ObjectArrayExamples.initial_repr,
    ``Solidity.Evm.Memory.ObjectArrayExamples.initial_allocator,
    ``Solidity.Evm.Memory.ObjectArrayExamples.allocator_overlap_refuted,
    ``Solidity.Evm.Memory.ObjectArrayExamples.allocator_preserved,
    ``Solidity.Evm.Memory.ObjectArrayExamples.compiled_input,
    ``Solidity.Evm.Memory.ObjectArrayExamples.compiled_agrees,
    ``Solidity.Evm.Memory.ObjectArrayExamples.source_observation,
    ``Solidity.Evm.Memory.ObjectArrayExamples.target_observation,
    ``Solidity.Evm.Memory.ObjectArrayExamples.wrong_pointer_refuted,
    ``Solidity.Evm.Memory.ObjectArrayExamples.failed_input,
    ``Solidity.Evm.Memory.ObjectArrayExamples.failed_agrees,
    ``Solidity.Evm.Memory.ObjectArrayExamples.source_bounds,
    ``Solidity.Evm.Memory.ObjectArrayExamples.target_bounds,
    ``Solidity.Evm.Memory.ObjectArrayExamples.read_input,
    ``Solidity.Evm.Memory.ObjectArrayExamples.read_agrees,
    ``Solidity.Evm.Memory.ObjectArrayExamples.source_read,
    ``Solidity.Evm.Memory.ObjectArrayExamples.target_read,
    ``Solidity.Evm.Memory.ObjectArrayExamples.alias_input,
    ``Solidity.Evm.Memory.ObjectArrayExamples.alias_agrees,
    ``Solidity.Evm.Memory.ObjectArrayExamples.source_alias,
    ``Solidity.Evm.Memory.ObjectArrayExamples.target_alias,

    ``Solidity.Evm.Memory.RefArrayRepr.read,
    ``Solidity.Evm.Memory.RefArrayRepr.write,
    ``Solidity.Evm.Memory.ReferenceArrays.ProgFrag.correct,
    ``Solidity.Evm.Memory.RefArrayExamples.initial_repr,
    ``Solidity.Evm.Memory.RefArrayExamples.compiled_input,
    ``Solidity.Evm.Memory.RefArrayExamples.compiled_agrees,
    ``Solidity.Evm.Memory.RefArrayExamples.source_observation,
    ``Solidity.Evm.Memory.RefArrayExamples.target_observation,
    ``Solidity.Evm.Memory.RefArrayExamples.retained_stack,
    ``Solidity.Evm.Memory.RefArrayExamples.wrong_pointer_refuted,
    ``Solidity.Evm.Memory.RefArrayExamples.failed_input,
    ``Solidity.Evm.Memory.RefArrayExamples.failed_agrees,
    ``Solidity.Evm.Memory.RefArrayExamples.source_bounds,
    ``Solidity.Evm.Memory.RefArrayExamples.target_bounds,
    ``Solidity.Evm.Memory.RefArrayExamples.allocation_supported,
    ``Solidity.Evm.Memory.RefArrayExamples.default_declaration_supported,
    ``Solidity.Evm.Memory.RefArrayExamples.fixed_index_supported,
    ``Solidity.Evm.Memory.copiedFields_copy,
    ``Solidity.Evm.Memory.copiedStruct_alloc,
    ``Solidity.Evm.Memory.copiedFields_get,
    ``Solidity.Evm.Memory.copiedStruct_rhs,
    ``Solidity.Evm.Memory.copiedStruct_decl,
    ``Solidity.Evm.Memory.copiedStruct_rebind,
    ``Solidity.Evm.Memory.copiedStruct_keeps,
    ``Solidity.Evm.Memory.copiedStruct_fresh,
    ``Solidity.Evm.Memory.copyMember_eval,
    ``Solidity.Evm.Memory.CopyLoads.member,
    ``Solidity.Evm.Memory.CopyLoads.correct,
    ``Solidity.Evm.Memory.copyStore_run,
    ``Solidity.Evm.Memory.copyStore_other,
    ``Solidity.Evm.Memory.copyStore_shape,
    ``Solidity.Evm.Memory.copyStore_preserves,
    ``Solidity.Evm.Memory.copyStore_written,
    ``Solidity.Evm.Memory.copyStore_fields,
    ``Solidity.Evm.Memory.StateRepr.reserveFilledStruct,
    ``Solidity.Evm.Memory.copiedStruct_body_correct,
    ``Solidity.Evm.Memory.copiedStruct_correct,
    ``Solidity.Evm.Memory.copiedStruct_rebind_correct,
    ``Solidity.Evm.Memory.StructCopyExamples.initial_repr,
    ``Solidity.Evm.Memory.StructCopyExamples.program_cost,
    ``Solidity.Evm.Memory.StructCopyExamples.compiled_input,
    ``Solidity.Evm.Memory.StructCopyExamples.compiled_agrees,
    ``Solidity.Evm.Memory.StructCopyExamples.target_observation,
    ``Solidity.Evm.Memory.StructCopyExamples.source_observation,
    ``Solidity.Evm.Memory.StructCopyExamples.capacity_invalid,
    ``Solidity.Evm.Memory.StructCopyExamples.unreached_cost,
    ``Solidity.Evm.Memory.StructCopyExamples.unreached_input,
    ``Solidity.Evm.Memory.StructCopyExamples.unreached_agrees,
    ``Solidity.Evm.Memory.StructCopyExamples.unreached_reverts,
    ``Solidity.Evm.Memory.clearStructField,
    ``Solidity.Evm.Memory.defaultArray_alloc,
    ``Solidity.Evm.Memory.clearArrayField,
    ``Solidity.Evm.Memory.clearReference_run,
    ``Solidity.Evm.Memory.deleteStructField_correct,
    ``Solidity.Evm.Memory.deleteArrayField_correct,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.program_cost,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.compiled_input,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.compiled_agrees,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.target_observation,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.source_observation,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.capacity_invalid,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.unset_cost,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.unset_reverts,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.unset_input_refuted,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.unreached_cost,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.unreached_input,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.unreached_agrees,
    ``Solidity.Evm.Memory.PathExamples.ReferenceDelete.unreached_reverts,
    ``Solidity.Evm.Memory.arrayLen_setRefField,
    ``Solidity.Evm.Memory.StructRepr.setReference,
    ``Solidity.Evm.Memory.StructHeapRepr.setReference,
    ``Solidity.Evm.Memory.RefFieldsRepr.setReference,
    ``Solidity.Evm.Memory.ArrayRepr.structRefWrite,
    ``Solidity.Evm.Memory.HeapRepr.structRefWrite,
    ``Solidity.Evm.Memory.StructArraySeparated.setReference,
    ``Solidity.Evm.Memory.StructAllocatorRepr.setReference,
    ``Solidity.Evm.Memory.StateRepr.setReference,
    ``Solidity.Evm.Memory.writeFieldWord_run,
    ``Solidity.Evm.Memory.writeReference_correct,
    ``Solidity.Evm.Memory.PathExamples.ReferenceWrite.program_cost,
    ``Solidity.Evm.Memory.PathExamples.ReferenceWrite.compiled_input,
    ``Solidity.Evm.Memory.PathExamples.ReferenceWrite.compiled_agrees,
    ``Solidity.Evm.Memory.PathExamples.ReferenceWrite.target_observation,
    ``Solidity.Evm.Memory.PathExamples.ReferenceWrite.source_observation,
    ``Solidity.Evm.Memory.PtrFrag.run_of_eval,
    ``Solidity.Evm.Memory.PtrFrag.writePrimitive,
    ``Solidity.Evm.Memory.PtrFrag.writeArray,
    ``Solidity.Evm.Memory.PathExamples.Direct.program_cost,
    ``Solidity.Evm.Memory.PathExamples.Direct.compiled_input,
    ``Solidity.Evm.Memory.PathExamples.Direct.compiled_agrees,
    ``Solidity.Evm.Memory.PathExamples.Direct.target_observation,
    ``Solidity.Evm.Memory.PathExamples.Direct.source_observation,
    ``Solidity.Evm.Memory.PathExamples.Direct.failure_inputs,
    ``Solidity.Evm.Memory.PathExamples.Direct.failure_agrees,
    ``Solidity.Evm.Memory.PathExamples.Direct.failures_revert,
    ``Solidity.Evm.Memory.RefFieldsRepr.withoutStructs,
    ``Solidity.Evm.Memory.RefFieldsRepr.mem_eq,
    ``Solidity.Evm.Memory.RefFieldsRepr.localWrite,
    ``Solidity.Evm.Memory.primitive_reference_fields_ne,
    ``Solidity.Evm.Memory.refField_setPrimitive,
    ``Solidity.Evm.Memory.RefFieldsRepr.setPrimitive,
    ``Solidity.Evm.Memory.RefFieldsRepr.arraySet,
    ``Solidity.Evm.Memory.RefFieldsRepr.readField,
    ``Solidity.Evm.Memory.RefFieldsRepr.alloc,
    ``Solidity.Evm.Memory.RefFieldsRepr.allocateArray,
    ``Solidity.Evm.Memory.RefFieldsRepr.allocateStruct,
    ``Solidity.Evm.Memory.primitiveMembers_noRef,
    ``Solidity.Evm.Memory.PtrFrag.correct,
    ``Solidity.Evm.Memory.PtrFrag.readPrimitive,
    ``Solidity.Evm.Memory.PtrFrag.length,
    ``Solidity.Evm.Memory.PtrFrag.readArray,
    ``Solidity.Evm.Memory.PtrFrag.rebind,
    ``Solidity.Evm.Memory.PtrFrag.declareAlias,
    ``Solidity.Evm.Memory.PathExamples.reference_words,
    ``Solidity.Evm.Memory.PathExamples.fixture,
    ``Solidity.Evm.Memory.PathExamples.wrong_pointer_refuted,
    ``Solidity.Evm.Memory.PathExamples.program_cost,
    ``Solidity.Evm.Memory.PathExamples.compiled_input,
    ``Solidity.Evm.Memory.PathExamples.compiled_agrees,
    ``Solidity.Evm.Memory.PathExamples.target_observation,
    ``Solidity.Evm.Memory.PathExamples.source_observation,
    ``Solidity.Evm.Memory.PathExamples.bad_input,
    ``Solidity.Evm.Memory.PathExamples.bad_agrees,
    ``Solidity.Evm.Memory.PathExamples.bad_reverts,
    ``Solidity.Evm.Memory.defaultArray_eq_allocate,
    ``Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.program_cost,
    ``Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.compiled_input,
    ``Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.compiled_agrees,
    ``Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.target_observation,
    ``Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.source_observation,
    ``Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.capacity_invalid,
    ``Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.unreached_cost,
    ``Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.unreached_input,
    ``Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.unreached_agrees,
    ``Solidity.Evm.Memory.defaultStruct_delete,
    ``Solidity.Evm.Memory.deleteStruct_correct,
    ``Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.program_cost,
    ``Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.compiled_input,
    ``Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.compiled_agrees,
    ``Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.target_observation,
    ``Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.source_observation,
    ``Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.capacity_invalid,
    ``Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.unreached_cost,
    ``Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.unreached_input,
    ``Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.unreached_agrees,
    ``Solidity.Evm.Memory.compoundField_eq_write,
    ``Solidity.Evm.Memory.incrementField_eq_compound,
    ``Solidity.Evm.Memory.captureField_eq,
    ``Solidity.Evm.Memory.StructDefaultExamples.Fields.compiled_input,
    ``Solidity.Evm.Memory.StructDefaultExamples.Fields.compiled_agrees,
    ``Solidity.Evm.Memory.StructDefaultExamples.Fields.failure_inputs,
    ``Solidity.Evm.Memory.StructDefaultExamples.Fields.failure_agrees,
    ``Solidity.Evm.Memory.StructDefaultExamples.Fields.failures_revert,
    ``Solidity.Evm.Memory.StructAllocatorRepr.advance,
    ``Solidity.Evm.Memory.StructAllocatorRepr.reserveStruct,
    ``Solidity.Evm.Memory.defaultFields_defaults,
    ``Solidity.Evm.Memory.defaultStruct_alloc,
    ``Solidity.Evm.Memory.defaultStruct_decl,
    ``Solidity.Evm.Memory.StateRepr.allocateStruct,
    ``Solidity.Evm.Memory.defaultStruct_correct,
    ``Solidity.Evm.Memory.StructDefaultExamples.initial_repr,
    ``Solidity.Evm.Memory.StructDefaultExamples.surface_cost,
    ``Solidity.Evm.Memory.StructDefaultExamples.compiled_input,
    ``Solidity.Evm.Memory.StructDefaultExamples.compiled_agrees,
    ``Solidity.Evm.Memory.StructDefaultExamples.capacity_invalid,
    ``Solidity.Evm.Memory.StructDefaultExamples.failed_input,
    ``Solidity.Evm.Memory.StructDefaultExamples.failed_agrees,
    ``Solidity.Evm.Memory.StructDefaultExamples.unreached_input,
    ``Solidity.Evm.Memory.StructDefaultExamples.unreached_agrees,
    ``Solidity.Evm.Memory.StructDefaultExamples.empty_input,
    ``Solidity.Evm.Memory.StructDefaultExamples.empty_agrees,
    ``Solidity.Evm.Memory.StructAllocatorRepr.mem_eq,
    ``Solidity.Evm.Memory.AllocatorRepr.withoutStructs,
    ``Solidity.Evm.Memory.StateRepr.consMem,
    ``Solidity.Evm.Memory.aliasLocal_correct,
    ``Solidity.Evm.Memory.StateRepr.setStruct,
    ``Solidity.Evm.Memory.readLocalField_correct,
    ``Solidity.Evm.Memory.writeLocalField_correct,
    ``Solidity.Evm.Memory.StructExamples.Public.fixture,
    ``Solidity.Evm.Memory.StructExamples.Public.compiled_input,
    ``Solidity.Evm.Memory.StructExamples.Public.compiled_agrees,
    ``Solidity.Evm.Memory.StructExamples.Public.bad_input,
    ``Solidity.Evm.Memory.StructExamples.Public.bad_agrees,
    ``Solidity.Evm.Memory.StructRepr.keeps,
    ``Solidity.Evm.Memory.StructHeapRepr.allocateArray,
    ``Solidity.Evm.Memory.StructHeapRepr.allocArray,
    ``Solidity.Evm.Memory.StructArraySeparated.allocArray,
    ``Solidity.Evm.Memory.StructAllocatorRepr.allocateArray,
    ``Solidity.Evm.Memory.allocateStruct_run,
    ``Solidity.Evm.Memory.allocateStructMachine_other,
    ``Solidity.Evm.Memory.FreeMemory.allocateStruct,
    ``Solidity.Evm.Memory.FreeMemory.struct,
    ``Solidity.Evm.Memory.HeapRepr.allocStruct,
    ``Solidity.Evm.Memory.StructHeapRepr.allocStruct,
    ``Solidity.Evm.Memory.StructArraySeparated.allocStruct,
    ``Solidity.Evm.Memory.StructAllocatorRepr.allocateStruct,
    ``Solidity.Evm.Memory.StructExamples.array_allocated_repr,
    ``Solidity.Evm.Memory.StructExamples.struct_allocated_repr,
    ``Solidity.Evm.Memory.StructExamples.allocated_written_repr,
    ``Solidity.Evm.Memory.StructExamples.allocated_old_array_written_repr,
    ``Solidity.Evm.Memory.StructExamples.repeated_array_allocated_repr,
    ``Solidity.Evm.Memory.fieldOffset_bound,
    ``Solidity.Evm.Memory.fieldOffset_ne,
    ``Solidity.Evm.Memory.StructRepr.stack,
    ``Solidity.Evm.Memory.fieldAddr_run,
    ``Solidity.Evm.Memory.readField_correct,
    ``Solidity.Evm.Memory.StructRepr.set,
    ``Solidity.Evm.Memory.writeField_correct,
    ``Solidity.Evm.Memory.StructHeapRepr.stack,
    ``Solidity.Evm.Memory.StructHeapRepr.write_below,
    ``Solidity.Evm.Memory.StructHeapRepr.localWrite,
    ``Solidity.Evm.Memory.StructHeapRepr.set,
    ``Solidity.Evm.Memory.ArrayRepr.structWrite,
    ``Solidity.Evm.Memory.StructRepr.arrayWrite,
    ``Solidity.Evm.Memory.arrayLen_setField,
    ``Solidity.Evm.Memory.HeapRepr.structWrite,
    ``Solidity.Evm.Memory.StructHeapRepr.arraySet,
    ``Solidity.Evm.Memory.StructArraySeparated.setStruct,
    ``Solidity.Evm.Memory.StructArraySeparated.setArray,
    ``Solidity.Evm.Memory.StructAllocatorRepr.stack,
    ``Solidity.Evm.Memory.StructAllocatorRepr.localWrite,
    ``Solidity.Evm.Memory.StructAllocatorRepr.setStruct,
    ``Solidity.Evm.Memory.StructAllocatorRepr.setArray,
    ``Solidity.Evm.Memory.StructExamples.fixture_repr,
    ``Solidity.Evm.Memory.StructExamples.written_repr,
    ``Solidity.Evm.Memory.StructExamples.array_written_repr,
    ``Solidity.Evm.Memory.StructExamples.wrapping_invalid,
    ``Solidity.Evm.Memory.StructExamples.signed_repr,
    ``Solidity.Evm.Memory.StructExamples.signed_read_correct,
    ``Solidity.Evm.Memory.StructExamples.legacy_allocator,
    ``Solidity.Evm.Memory.StructExamples.legacy_struct_repr,
    ``Solidity.Evm.Memory.StructExamples.legacy_write_breaks_allocator,
    ``Solidity.Evm.Memory.StructExamples.misplaced_invalid,
    ``Solidity.Hyps.rigid_eq_rigidM,
    ``Solidity.Hyps.rigid_lift,
    ``Solidity.Seq.refuteLanded_sound,
    ``Solidity.Examples.Tactics.Rigid.memoryLoop,
    ``Solidity.Examples.Tactics.Rigid.stopped_invalid,
    ``Solidity.Evm.Memory.bumpResultValue_eval,
    ``Solidity.Evm.Memory.captureMemory_eq,
    ``Solidity.Evm.Memory.captureLocal_eq,
    ``Solidity.Evm.Memory.captureStep_correct,
    ``Solidity.Evm.Memory.ExprExamples.CaptureCase.simulates,
    ``Solidity.Evm.Memory.ExprExamples.CaptureCase.source,
    ``Solidity.Evm.Memory.ExprExamples.CaptureCase.target,
    ``Solidity.Evm.Memory.ExprExamples.CaptureCase.self_simulates,
    ``Solidity.Evm.Memory.ExprExamples.CaptureCase.self_source,
    ``Solidity.Evm.Memory.ExprExamples.CaptureCase.self_target,
    ``Solidity.Evm.Memory.ExprExamples.CaptureCase.failure_simulates,
    ``Solidity.Evm.Memory.ExprExamples.CaptureCase.failure_source,
    ``Solidity.Evm.Memory.ExprExamples.CaptureCase.failure_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.captured_memory_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.captured_memory_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.captured_memory_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.capture_sum_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.capture_sum_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.capture_sum_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_capture_failure_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_capture_failure_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_capture_failure_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.failed_capture_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.failed_capture_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.failed_capture_target,
    ``Solidity.Evm.Memory.incrementMemory_eq_compound,
    ``Solidity.Evm.Memory.incrementLocal_eq_compound,
    ``Solidity.Evm.Memory.ExprExamples.IncrementCase.simulates,
    ``Solidity.Evm.Memory.ExprExamples.IncrementCase.source,
    ``Solidity.Evm.Memory.ExprExamples.IncrementCase.target,
    ``Solidity.Evm.Memory.ExprExamples.IncrementCase.failure_simulates,
    ``Solidity.Evm.Memory.ExprExamples.IncrementCase.failure_source,
    ``Solidity.Evm.Memory.ExprExamples.IncrementCase.failure_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.increments_simulate,
    ``Solidity.Evm.Memory.AllocSourceExamples.increments_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.increments_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_increments_simulate,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_increments_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_increments_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_bump_failure_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_bump_failure_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_bump_failure_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.failed_increment_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.failed_increment_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.failed_increment_target,
    ``Solidity.Evm.Memory.compoundValue_eval,
    ``Solidity.Evm.Memory.compoundMemT_eq_assign,
    ``Solidity.Evm.Memory.compoundAssign_eq_write,
    ``Solidity.Evm.Memory.compoundLocal_eq_assign,
    ``Solidity.Evm.Memory.ExprExamples.CompoundCase.simulates,
    ``Solidity.Evm.Memory.ExprExamples.CompoundCase.source,
    ``Solidity.Evm.Memory.ExprExamples.CompoundCase.target,
    ``Solidity.Evm.Memory.ExprExamples.CompoundCase.failure_simulates,
    ``Solidity.Evm.Memory.ExprExamples.CompoundCase.failure_source,
    ``Solidity.Evm.Memory.ExprExamples.CompoundCase.failure_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.compound_signed_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.compound_signed_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.compound_signed_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_compound_failure_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_compound_failure_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.signed_compound_failure_target,
    ``Solidity.Evm.Memory.deleteDefaultValue_eval,
    ``Solidity.Evm.Memory.deleteMem_primitive_eq_assign,
    ``Solidity.Evm.Memory.deleteLocalValue_correct,
    ``Solidity.Evm.Memory.deleteMem_array_eq_reallocate,
    ``Solidity.Evm.Memory.AllocSourceExamples.deletions_cost,
    ``Solidity.Evm.Memory.AllocSourceExamples.deletions_simulate,
    ``Solidity.Evm.Memory.AllocSourceExamples.deletions_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.deletions_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.typed_deletions_simulate,
    ``Solidity.Evm.Memory.AllocSourceExamples.typed_deletions_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.typed_deletions_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.failed_deletion_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.failed_deletion_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.failed_deletion_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.boundary_deletion_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.boundary_deletion_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.boundary_deletion_target,
    ``Solidity.RevPart.evalT_mem,
    ``Solidity.RevPart.evalT_mem_unset,
    ``Solidity.TRun.revertData_mem,
    ``Solidity.TRes.Approx.halt_eq,
    ``Solidity.TRes.Approx.returned,
    ``Solidity.Prog.run_halt_of_runF,
    ``Solidity.Examples.Tactics.ComputedRevert.computed_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.eager_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.raw_alias_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.empty_raw_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.empty_reason_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.condition_captured,
    ``Solidity.Examples.Tactics.ComputedRevert.renamed_buffer_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.cast_reason_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.failed_concat_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.eager_failure_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.runtime_bytes_reason_exact,
    ``Solidity.Examples.Tactics.ComputedRevert.unicode_hex_reason_exact,
    ``Solidity.Decide.foldMem2_eval,
    ``Solidity.Decide.foldRead2_eval,
    ``Solidity.Examples.Tactics.OpenLoops.binomialFaithfulRowsSmall,
    ``Solidity.Examples.Tactics.OpenLoops.binomialRowsNine,
    ``Solidity.Decide.copyRes_eval,
    ``Solidity.Decide.LTm.stripW_eval,
    ``Solidity.Decide.LTm.read_unstrip,
    ``Solidity.Proves.of_cutWithin,
    ``Solidity.Evm.loop_sim,
    ``Solidity.Evm.compile_correct,
    ``Solidity.Examples.Tactics.Decide.memoryRepeatedDoubling,
    ``Solidity.Evm.Memory.StateRepr.drop,
    ``Solidity.Evm.Memory.StateRepr.meet,
    ``Solidity.Evm.Memory.StateRepr.meetRight,
    ``Solidity.Evm.Memory.frameNeedStmt_end,
    ``Solidity.Evm.Memory.allocationCostStmt_block,
    ``Solidity.Evm.Memory.allocationCostStmt_ite,
    ``Solidity.Evm.Compiler.Compilation.memory_input,
    ``Solidity.Evm.Memory.AllocSourceExamples.scopes_simulate,
    ``Solidity.Evm.Memory.AllocSourceExamples.scopes_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.scopes_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.scopes_frame_rejected,
    ``Solidity.Evm.Memory.AllocSourceExamples.branches_simulate,
    ``Solidity.Evm.Memory.AllocSourceExamples.branches_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.branches_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.else_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.else_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.branch_revert_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.branch_revert_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.branch_revert_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.bad_condition_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.bad_condition_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.bad_condition_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.surface_accepted,
    ``Solidity.Evm.Memory.newArray_rebind,
    ``Solidity.Evm.Memory.rebindNew_correct,
    ``Solidity.Evm.Memory.AllocSourceExamples.rebindings_simulate,
    ``Solidity.Evm.Memory.AllocSourceExamples.rebindings_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.rebindings_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.rebindings_old_read,
    ``Solidity.Evm.Memory.AllocSourceExamples.rebindings_empty,
    ``Solidity.Evm.Memory.AllocSourceExamples.rebindings_retained_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.rebindings_retained_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.maximal_rebind_rejected,
    ``Solidity.Evm.Memory.allocationCostProg_zero,
    ``Solidity.Evm.Memory.allocationCostProg_cons,
    ``Solidity.Evm.Memory.AllocSourceExamples.whole_space_rejected,
    ``Solidity.Evm.Memory.AllocSourceExamples.maximal_input_rejected,
    ``Solidity.Evm.Memory.AllocatorRepr.mem_eq,
    ``Solidity.Evm.Memory.BaseExtends.trans,
    ``Solidity.Evm.Memory.AllocationInput.of_le,
    ``Solidity.Evm.Memory.GrowsAllocator.comp,
    ``Solidity.Evm.Memory.GrowsAllocator.nextInput,
    ``Solidity.Evm.Memory.ResultRepr.growing,
    ``Solidity.Evm.Memory.StmtFrag.correct,
    ``Solidity.Evm.Memory.AllocSourceExamples.compiled_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.mixed_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.mixed_source,
    ``Solidity.Evm.Memory.AllocSourceExamples.mixed_target,
    ``Solidity.Evm.Memory.AllocSourceExamples.mixed_default,
    ``Solidity.Evm.Memory.AllocSourceExamples.skipped_simulates,
    ``Solidity.Evm.Memory.AllocSourceExamples.skipped_target,
    ``Solidity.Evm.Memory.AllocatorRepr.localWrite,
    ``Solidity.Evm.Memory.newArray_copy,
    ``Solidity.Evm.Memory.newArray_decl,
    ``Solidity.Evm.Memory.StateRepr.allocate,
    ``Solidity.Evm.Memory.newArray_correct,
    ``Solidity.Evm.Memory.AllocSourceExamples.initial_repr,
    ``Solidity.Evm.Memory.AllocSourceExamples.first_repr,
    ``Solidity.Evm.Memory.AllocSourceExamples.second_repr,
    ``Solidity.Evm.Memory.AllocSourceExamples.source_run,
    ``Solidity.Evm.Memory.AllocSourceExamples.target_run,
    ``Solidity.Evm.Memory.AllocSourceExamples.default_read,
    ``Solidity.Evm.Memory.AllocSourceExamples.empty_reverts,
    ``Solidity.Main.soundness, ``Solidity.Main.soundness',
    ``Solidity.Main.callback_soundness, ``Solidity.Main.symex_sound,
    ``Solidity.Main.compiler_correct, ``Solidity.Main.compiler_net,
    ``Solidity.Spec.sat_iff_holds, ``Solidity.Spec.valid_iff,
    ``Solidity.Proves.valid, ``Solidity.ProvesC.valid,
    ``Solidity.Examples.Tactics.Nonvacuity.good_provable,
    ``Solidity.Examples.Tactics.Nonvacuity.good_valid,
    ``Solidity.Examples.Tactics.Nonvacuity.bad_at_init,
    ``Solidity.Examples.Tactics.Nonvacuity.bad_unprovable,
    ``Solidity.Evm.Memory.readArray_correct,
    ``Solidity.Evm.Memory.ArrayRepr.set,
    ``Solidity.Evm.Memory.writeArray_correct,
    ``Solidity.Evm.Memory.Examples.fixture_repr,
    ``Solidity.Evm.Memory.HeapRepr.set,
    ``Solidity.Evm.Memory.StateRepr.set,
    ``Solidity.Evm.Memory.readLocal_correct,
    ``Solidity.Evm.Memory.writeLocal_correct,
    ``Solidity.Evm.Memory.ProgFrag.correct,
    ``Solidity.Evm.Memory.compile_correct,
    ``Solidity.Evm.Memory.CompileExamples.fixture_repr,
    ``Solidity.Evm.Memory.CompileExamples.compiled_simulates,
    ``Solidity.Evm.Memory.lengthLocal_correct,
    ``Solidity.Evm.Memory.StateRepr.setMem,
    ``Solidity.Evm.Memory.declareAlias_correct,
    ``Solidity.Evm.Memory.declareValue_correct,
    ``Solidity.Evm.Compiler.Compilation.correct,
    ``Solidity.Main.compiler_checked,
    ``Solidity.Evm.Memory.CompileExamples.locals_simulate,
    ``Solidity.Evm.Memory.CompileExamples.checked_locals_simulate,
    ``Solidity.Evm.Memory.CompileExamples.checked_core_simulates,
    ``Solidity.Evm.Memory.readLocalValue_correct,
    ``Solidity.Evm.Memory.writeLocalValue_correct,
    ``Solidity.Evm.Memory.declareDefault_correct,
    ``Solidity.Evm.Memory.CompileExamples.indirect_simulates,
    ``Solidity.Evm.Memory.binaryValue_correct,
    ``Solidity.Evm.Memory.unaryValue_correct,
    ``Solidity.Evm.Memory.conditionalValue_correct,
    ``Solidity.Evm.Memory.StateRepr.store,
    ``Solidity.Evm.Memory.storageAssign_correct,
    ``Solidity.Evm.Memory.requireValue_correct,
    ``Solidity.Evm.Memory.ExprExamples.arithmetic_simulates,
    ``Solidity.Evm.Memory.ExprExamples.guard_simulates,
    ``Solidity.Evm.Memory.ExprExamples.StorageCase.fixture,
    ``Solidity.Evm.Memory.ExprExamples.StorageCase.storage_memory_simulate,
    ``Solidity.Examples.Tactics.AllLeftLater.laterIndex,
    ``Solidity.Examples.Tactics.AllLeftLater.laterLocal,
    ``Solidity.Examples.Tactics.AllLeftLater.loopCounter,
    ``Solidity.Close.square_nonneg,
    ``Solidity.Close.multiply_inEq0,
    ``Solidity.Examples.Tactics.Nonlinear.positiveScale,
    ``Solidity.Examples.Tactics.Nonlinear.negativeScale,
    ``Solidity.Examples.Tactics.Nonlinear.strictScale,
    ``Solidity.Examples.Tactics.Nonlinear.coefficientScale,
    ``Solidity.Examples.Tactics.Nonlinear.coefficientNegative,
    ``Solidity.Examples.Tactics.Nonlinear.orderedProduct,
    ``Solidity.Examples.Tactics.Nonlinear.compoundSquare,
    ``Solidity.Examples.Tactics.Nonlinear.crossProduct,
    ``Solidity.Examples.Tactics.Nonlinear.checkedProducts,
    ``Solidity.CloseS.exists_val_eq,
    ``Solidity.CloseS.index_uint_eta,
    ``Solidity.Examples.Tactics.ArrayScans.unsignedScan,
    ``Solidity.Examples.Tactics.ArrayScans.signedScan,
    ``Solidity.Examples.Tactics.ArrayScans.signedUpperScan,
    ``Solidity.Evm.Memory.allocateArray_run,
    ``Solidity.Evm.Memory.FreeMemory.array,
    ``Solidity.Evm.Memory.HeapRepr.alloc,
    ``Solidity.Evm.Memory.AllocatorRepr.allocate,
    ``Solidity.Evm.Memory.AllocatorRepr.set,
    ``Solidity.Evm.Memory.ArrayRepr.keeps,
    ``Solidity.Evm.Memory.AllocExamples.initial_repr,
    ``Solidity.Evm.Memory.AllocExamples.written_repr,
    ``Solidity.Evm.Memory.AllocExamples.twoArrays_repr,
    ``Solidity.TLoop.finite_of_wellFounded,
    ``Solidity.TLoop.run_measure,
    ``Solidity.TLoop.run_lex,
    ``Solidity.Stmt.loop_terminates_of_wellFounded,
    ``Solidity.holds_finiteMember,
    ``Solidity.Fml.EntryNegative.holds_source,
    ``Solidity.Fml.EntryNegative.unique,
    ``Solidity.Fml.PreconditionsImpossible.valid,
    ``Solidity.Fml.PreconditionsImpossible.not_possible,
    ``Solidity.Examples.SourceCounterexample.badRefuted,
    ``Solidity.Examples.SourceCounterexample.wideRefuted,
    ``Solidity.LoopMetrics.NatTuple.wellFounded,
    ``Solidity.LoopMetrics.Certificate.valid,
    ``Solidity.LoopMetrics.SourceCertificate.valid,
    ``Solidity.LoopMetrics.SourceCertificate.checks,
    ``Solidity.Examples.LexMetrics.sourceProgram_success,
    ``Solidity.Examples.LexMetrics.equal_source_rejected,
    ``Solidity.Examples.LexMetrics.increasing_source_rejected,
    ``Solidity.Examples.LexMetrics.undefined_source_rejected,
    ``Solidity.Premise.sound_loopAnnotation,
    ``Solidity.CallbackCapture.loop_ann_all,
    ``Solidity.Stmt.CapturesAs.loopAnnotation,
    ``Solidity.LoopAnn.lex_erasure_size,
    ``Solidity.Examples.Tactics.LexAnnotations.ordinaryBox,
    ``Solidity.LoopLex.snapshot_globT_iff_eval,
    ``Solidity.LoopLex.snapshot_fails_of_undefined,
    ``Solidity.LoopLex.snapshot_pushFree,
    ``Solidity.LoopLex.snapshot_exh,
    ``Solidity.LoopLex.snapshot_lands,
    ``Solidity.LoopLex.snapshot_lands_eq,
    ``Solidity.LoopLex.saveState_drop,
    ``Solidity.LoopLex.metrics_eval_wk,
    ``Solidity.LoopLex.metrics_eval_saved,
    ``Solidity.LoopLex.lexFml_holds,
    ``Solidity.LoopLex.snapshotsDecrease_holds,
    ``Solidity.LoopLex.run_lex_or,
    ``Solidity.LoopLex.diamondPremise_sound,
    ``Solidity.LoopLex.diamondStep_sound,
    ``Solidity.Stmt.step_upds_le,
    ``Solidity.Stmt.step_upds_le_two,
    ``Solidity.Stmt.step_tmSize_le,
    ``Solidity.Examples.LexDiamond.exiting_source_diamond,
    ``Solidity.Examples.LexDiamond.exhausting_source_diamond,
    ``Solidity.Examples.LexDiamond.exhausting_not_strict,
    ``Solidity.Examples.LexDiamond.return_flag_loop_succeeds,
    ``Solidity.Examples.Tactics.LexDiamond.pairCountdown,
    ``Solidity.Examples.Tactics.LexDiamond.tripleCountdown,
    ``Solidity.Examples.Tactics.LexDiamond.pairReset,
    ``Solidity.Examples.Tactics.LexDiamond.tripleReset,
    ``Solidity.Examples.Tactics.LexDiamond.scalarCountdown,
    ``Solidity.holds_finiteValues,
    ``Solidity.holds_filteredMember,
    ``Solidity.holds_filteredMember_rename,
    ``Solidity.holds_filteredMember_domain,
    ``Solidity.not_holds_filteredMember_nil,
    ``Solidity.not_holds_filteredMember_undefined,
    ``Solidity.Examples.Tactics.FilteredSets.one_correct,
    ``Solidity.Examples.Tactics.FilteredSets.echo_correct,
    ``Solidity.Examples.Tactics.FilteredSets.empty_correct,
    ``Solidity.Examples.Tactics.FilteredSets.undefined_key_correct,
    ``Solidity.Examples.Tactics.FilteredSets.theory_guard_correct]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} headline theorems use only the standard axioms"

#print axioms Solidity.Evm.Memory.RefArrayRepr.read
#print axioms Solidity.Evm.Memory.RefArrayRepr.write
#print axioms Solidity.Evm.Memory.ReferenceArrays.ProgFrag.correct
#print axioms Solidity.Evm.Memory.RefArrayExamples.compiled_agrees
#print axioms Solidity.Evm.Memory.RefArrayExamples.failed_agrees

#print axioms Solidity.Evm.Memory.Objects.ProgFrag.correct
#print axioms Solidity.Evm.Memory.Objects.defaultEmpty_correct
#print axioms Solidity.Evm.Memory.ObjectArrayExamples.allocator_preserved
#print axioms Solidity.Evm.Memory.FixedChildArrayExamples.compiled_agrees

#print axioms Solidity.Evm.Memory.Objects.nested_correct
#print axioms Solidity.Evm.Memory.Construction.ProgFrag.correct
#print axioms Solidity.Evm.Memory.ConstructionExamples.target_result
#print axioms Solidity.Evm.Memory.ConstructionExamples.unreachable_target
#print axioms Solidity.Evm.Memory.StructArrayInputExamples.compiled_agrees

#print axioms Solidity.Evm.Memory.Objects.DefaultBuilder.fixedReference
#print axioms Solidity.Evm.Memory.Objects.referenceArray_correct
#print axioms Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.target_result

/-! Roadmap G07: the inhabited and negative controls of the G01 contracts
(`Solidity/Roadmap/Controls.lean`, `docs/feature-work/roadmap-g07-gates.md`). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Roadmap.PublicCorrectness.transfer,
    ``Solidity.Roadmap.PublicCorrectness.not_alwaysRevert,
    ``Solidity.Roadmap.PublicCorrectness.observes,
    ``Solidity.Roadmap.PublicCorrectness.rejects,
    ``Solidity.Roadmap.SourceSpec.not_nonVacuous_of_no_parse,
    ``Solidity.Roadmap.Admission.rejects,
    ``Solidity.Roadmap.Controls.toy_publicCorrectness,
    ``Solidity.Roadmap.Controls.toySource_nonVacuous,
    ``Solidity.Roadmap.Controls.toySource_approved,
    ``Solidity.Roadmap.Controls.toyEvm_approved,
    ``Solidity.Roadmap.Controls.not_publicCorrectness_revertCompiler,
    ``Solidity.Roadmap.Controls.not_publicCorrectness_alteredCompiler,
    ``Solidity.Roadmap.Controls.not_publicCorrectness_erasingCompiler,
    ``Solidity.Roadmap.Controls.not_publicCorrectness_sloppyCompiler,
    ``Solidity.Roadmap.Controls.not_admission_sloppy,
    ``Solidity.Roadmap.Controls.not_nonVacuous_emptySource,
    ``Solidity.Roadmap.PublicCorrectness.observedBySource,
    ``Solidity.Roadmap.SourceSpec.NonVacuous.admits,
    ``Solidity.Roadmap.HashPremise.not_of_rootSlots,
    ``Solidity.Roadmap.Controls.toy_publicCorrectness_loopReverts,
    ``Solidity.Roadmap.Controls.not_publicCorrectness_loopToSucceed,
    ``Solidity.Roadmap.Controls.not_publicCorrectness_linkBlindCompiler,
    ``Solidity.Roadmap.Controls.not_publicCorrectness_hashRevertCompiler,
    ``Solidity.Roadmap.Fixed.Sane.rootSlots_lt,
    ``Solidity.Roadmap.Controls.toyFixed_keccak]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} roadmap control theorems use only the standard axioms"

/-! Roadmap S00/S01: the source syntax, its rejection and mapping, and static
typing (`Solidity/Source/`, `docs/feature-work/source-s00-s01.md`). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.Ctor.mem_all,
    ``Solidity.Source.Syn.nodes_eq,
    ``Solidity.Source.Syn.rejections_of_sub,
    ``Solidity.Source.Syn.rejections_witnessed,
    ``Solidity.Source.Syn.excl_ctor,
    ``Solidity.Source.Excl.mapped,
    ``Solidity.Source.Ctor.grammar_covers,
    ``Solidity.Source.Syn.decls_ctor,
    ``Solidity.Source.Examples.no_break_outside_loop,
    ``Solidity.Source.Examples.no_nested_unchecked,
    ``Solidity.Source.implicit_int_range,
    ``Solidity.Source.FixTy.subsumes_inRange,
    ``Solidity.Source.Q.toFixedExplicit?_of_toFixed?,
    ``Solidity.Source.resolve_iff,
    ``Solidity.Source.Resolves.unique,
    ``Solidity.Source.StmtD.locals_suffix,
    ``Solidity.Source.HasType.resolved,
    ``Solidity.Source.ItemsOK.resolved,
    ``Solidity.Source.TypingExamples.shl18_folded,
    ``Solidity.Source.TypingExamples.shlTooBig_illTyped,
    ``Solidity.Source.TypingExamples.bareReturn_refused,
    ``Solidity.Source.TypingExamples.twoCtors_illFormed,
    ``Solidity.Source.TypingExamples.noVisibility_illFormed,
    ``Solidity.Source.TypingExamples.exprCoverage_total,
    ``Solidity.Source.TypingExamples.stmtCoverage_total,
    ``Solidity.Source.TypingExamples.msgValue_refused,
    ``Solidity.Source.TypingExamples.sameSig_illFormed,
    ``Solidity.Source.TypingExamples.ifaceBody_illFormed,
    ``Solidity.Source.TypingExamples.unknownPragma_illFormed,
    ``Solidity.Source.TypingExamples.exprCoverage_typed,
    ``Solidity.Source.TypingExamples.counter_wellFormed,
    ``Solidity.Source.TypingExamples.tooBig_illTyped,
    ``Solidity.Source.TypingExamples.clashing_illFormed,
    ``Solidity.Source.TypingExamples.gasleft_untyped]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} source-definition theorems use only the standard axioms"

/-! Roadmap S04.01–S04.03: source state, observations and world
(`Solidity/Source/{State,Observe,World}.lean`,
`docs/feature-work/source-s04-state.md`). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.Heap.copy_get,
    ``Solidity.Source.Heap.copy_independent,
    ``Solidity.Source.Heap.write_get,
    ``Solidity.Source.Heap.write_ty,
    ``Solidity.Source.Storage.write_read,
    ``Solidity.Source.Storage.set_restore,
    ``Solidity.Source.wordBytes_value,
    ``Solidity.Source.Val.word_int,
    ``Solidity.Source.readInt_reject,
    ``Solidity.Source.panicData_code,
    ``Solidity.Source.panic_distinct,
    ``Solidity.Source.ExecState.undoN_run,
    ``Solidity.Source.rollback_run,
    ``Solidity.Source.rollback_inner,
    ``Solidity.Source.rollback_outer_after_commit,
    ``Solidity.Source.rollback_transfer,
    ``Solidity.Source.transfer_none_iff,
    ``Solidity.Source.StateExamples.alias_seen,
    ``Solidity.Source.StateExamples.revert_undoes,
    ``Solidity.Source.StateExamples.transfers]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} source-state theorems use only the standard axioms"

/-! Roadmap G12: the import resolver, declaration identities and overloads
across bases (`Solidity/Frontend/Static/`, `docs/feature-work/frontend-static.md`). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Static.iter_sound,
    ``Solidity.Frontend.Static.iter_complete,
    ``Solidity.Frontend.Static.globals_sound,
    ``Solidity.Frontend.Static.globals_complete,
    ``Solidity.Frontend.Static.unitsOK_iff,
    ``Solidity.Frontend.Static.globals_lookup,
    ``Solidity.Source.Sees.decl_exists,
    ``Solidity.Frontend.Static.mem_inheritedFns,
    ``Solidity.Frontend.Static.lookup_sub_inheritedFns,
    ``Solidity.Frontend.Static.selectOverload_unique,
    ``Solidity.Frontend.Static.unitsChecker_complete,
    ``Solidity.Frontend.Static.UnitsExamples.cycle_resolves,
    ``Solidity.Frontend.Static.UnitsExamples.cycle_ok,
    ``Solidity.Frontend.Static.UnitsExamples.diamond_one_identity,
    ``Solidity.Frontend.Static.UnitsExamples.clash_refused,
    ``Solidity.Frontend.Static.UnitsExamples.missing_refused,
    ``Solidity.Frontend.Static.UnitsExamples.alias_hides_original,
    ``Solidity.Frontend.Static.UnitsExamples.shadowed_member,
    ``Solidity.Frontend.Static.UnitsExamples.ambiguous_refused,
    ``Solidity.Frontend.Static.UnitsExamples.exact_selected,
    ``Solidity.Frontend.Static.UnitsExamples.crossBase_merged,
    ``Solidity.Frontend.Static.UnitsExamples.override_hides,
    ``Solidity.Frontend.Static.lookup_sub_globals,
    ``Solidity.Frontend.Static.UnitsExamples.missingSym_refused,
    ``Solidity.Frontend.Static.UnitsExamples.aliasCycle_refused,
    ``Solidity.Frontend.Static.UnitsExamples.fnEvent_refused,
    ``Solidity.Frontend.Static.UnitsExamples.freeOverloads_ok,
    ``Solidity.Frontend.Static.UnitsExamples.namespace_binds]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} G12 resolver theorems use only the standard axioms"

/-! Roadmap G13: type inference and statement checking for S01, its
well-formedness decided, compile-time constants and user-defined value type
operations (`Solidity/Frontend/Static/`, `docs/feature-work/frontend-static.md`). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Static.typed_complete,
    ``Solidity.Frontend.Static.lval_complete,
    ``Solidity.Frontend.Static.args_complete,
    ``Solidity.Frontend.Static.slots_complete,
    ``Solidity.Frontend.Static.stmt_complete,
    ``Solidity.Frontend.Static.items_complete,
    ``Solidity.Frontend.Static.stmtOK_iff,
    ``Solidity.Frontend.Static.itemsOK_iff,
    ``Solidity.Frontend.Static.wellFormed_iff,
    ``Solidity.Frontend.Static.inProfileSyntaxB_iff,
    ``Solidity.Frontend.Static.pureB_iff,
    ``Solidity.Frontend.Static.constInitsB_iff,
    ``Solidity.Frontend.Static.teval_complete,
    ``Solidity.Frontend.Static.nconst_complete,
    ``Solidity.Frontend.Static.acyclic_iff,
    ``Solidity.Frontend.Static.usingOpsB_iff,
    ``Solidity.Frontend.Static.hasType_iff,
    ``Solidity.Frontend.Static.evalConst_sound,
    
    ``Solidity.Frontend.Static.arrayLenB_sound,
    ``Solidity.Frontend.Static.udvt_iff,
    ``Solidity.Frontend.Static.metadataChecker_complete,
    ``Solidity.Frontend.Static.InferExamples.counter_checked,
    ``Solidity.Frontend.Static.InferExamples.clashing_checked,
    ``Solidity.Frontend.Static.InferExamples.sameSig_checked,
    ``Solidity.Frontend.Static.InferExamples.twoCtors_checked,
    ``Solidity.Frontend.Static.InferExamples.tooBig_checked,
    ``Solidity.Frontend.Static.InferExamples.gasleft_checked,
    ``Solidity.Frontend.Static.InferExamples.msgValue_checked,
    ``Solidity.Frontend.Static.InferExamples.zero_types,
    ``Solidity.Frontend.Static.InferExamples.named_length,
    ``Solidity.Frontend.Static.InferExamples.cyclic_refused,
    ``Solidity.Frontend.Static.InferExamples.cyclic_noValue,
    ``Solidity.Frontend.Static.InferExamples.typed_division,
    ``Solidity.Frontend.Static.InferExamples.overflow_length,
    ``Solidity.Frontend.Static.InferExamples.badBinding_refused,
    ``Solidity.Frontend.Static.InferExamples.hexCall_typed,
    ``Solidity.Frontend.Static.InferExamples.timestamp_refused,
    ``Solidity.Frontend.Static.InferExamples.keccak_pure,
    ``Solidity.Frontend.Static.InferExamples.udvt_add,
    ``Solidity.Frontend.Static.InferExamples.udvt_noBinding,
    ``Solidity.Frontend.Static.InferExamples.udvt_wrap,
    ``Solidity.Frontend.Static.InferExamples.udvt_unwrap]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} G13 checker theorems use only the standard axioms"

/-! Roadmap G14: inheritance checks (overrides, implementations, base
constructors, modifiers, `using for`), C3 linearization soundness and
callable identity (`Solidity/Frontend/Static/`, `docs/feature-work/frontend-static.md`). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Static.fnOverrideB_iff,
    ``Solidity.Frontend.Static.overridesB_iff,
    ``Solidity.Frontend.Static.mustOverrideB_iff,
    ``Solidity.Frontend.Static.implB_iff,
    ``Solidity.Frontend.Static.ctorArgsB_iff,
    ``Solidity.Frontend.Static.modInvsB_iff,
    ``Solidity.Frontend.Static.usingLibB_iff,
    ``Solidity.Frontend.Static.inheritance_iff,
    ``Solidity.Frontend.Static.callable_unique,
    ``Solidity.Frontend.Static.merge_sub,
    ``Solidity.Frontend.Static.merge_nodup,
    ``Solidity.Frontend.Static.merge_sublist,
    ``Solidity.Frontend.Static.linearize_sound,
    ``Solidity.Frontend.Static.ctorOrder_spec,
    ``Solidity.Frontend.Static.InheritanceExamples.missingVirtual_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.override_ok,
    ``Solidity.Frontend.Static.InheritanceExamples.lessStrict_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.stricter_ok,
    ``Solidity.Frontend.Static.InheritanceExamples.noCommonBase_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.sharedBase_ok,
    ``Solidity.Frontend.Static.InheritanceExamples.sharedBase_override_ok,
    ``Solidity.Frontend.Static.InheritanceExamples.sharedBase_unlisted_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.externalPublic_ok,
    ``Solidity.Frontend.Static.InheritanceExamples.unimplementedNonVirtual_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.abstractNeeded_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.argsTwice_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.argsMissing_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.argsCount_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.nonBaseCtor_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.ctorModifiers_ok,
    ``Solidity.Frontend.Static.InheritanceExamples.usingNotLibrary_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.diamond_c3,
    ``Solidity.Frontend.Static.InheritanceExamples.diamond_ctorOrder]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} G14 inheritance theorems use only the standard axioms"

/-! Roadmap G14 review fixes: `virtual` declarations, the checker's
completeness and the controls added after the finder and skeptic reviews. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Static.virtualDeclB_iff,
    ``Solidity.Frontend.Static.inheritanceChecker_complete,
    ``Solidity.Frontend.Static.InheritanceExamples.dupList_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.dupListFixed_ok,
    ``Solidity.Frontend.Static.InheritanceExamples.argsTwice_paths_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.modStyleBare_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.modArgs_count,
    ``Solidity.Frontend.Static.InheritanceExamples.calldataMemory_ok,
    ``Solidity.Frontend.Static.InheritanceExamples.overridesSingle_ok,
    ``Solidity.Frontend.Static.InheritanceExamples.implThenUnimpl_refused,
    ``Solidity.Frontend.Static.InheritanceExamples.virtualDecl_refused]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} G14 review-fix theorems use only the standard axioms"

/-! Backfill item 5: standalone fractional constants at their mobile
fixed-point types, also as ABI arguments (`Solidity/Language/FixedPoint/Literals.lean`,
`Solidity/Frontend/Static/Standalone.lean`, `docs/feature-work/frontend-static.md`). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Language.FixedPoint.Fx.mobileConst?_eq,
    ``Solidity.Language.FixedPoint.Fx.mobileConst?_trunc,
    ``Solidity.Language.FixedPoint.Fx.mobileConst?_exact,
    ``Solidity.Language.FixedPoint.Fx.abiConst?_decode,
    ``Solidity.Language.FixedPoint.Fx.abiConst?_eq_none,
    ``Solidity.Frontend.Static.standalone_iff,
    ``Solidity.Frontend.Static.abiArg_iff,
    ``Solidity.Frontend.Static.standalone_value,
    ``Solidity.Frontend.Static.InferExamples.oneThird_standalone,
    ``Solidity.Frontend.Static.InferExamples.tooBigFrac_refused,
    ``Solidity.Frontend.Static.InferExamples.oneThird_value]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} standalone-constant theorems use only the standard axioms"

/-! Backfill item 5 review fixes: S01's explicit value and the ABI word of a
standalone constant, and the unreduced-constant control. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Static.standalone_toFixedExplicit,
    ``Solidity.Frontend.Static.standalone_abi,
    ``Solidity.Frontend.Static.InferExamples.unreduced_standalone]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} standalone-constant review theorems use only the standard axioms"


-- G08 (`docs/feature-work/frontend-parse.md`): the checked lexer's headline
-- theorems use only the standard axioms.
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Checked.lex_sound,
    ``Solidity.Frontend.Checked.lex_reprint,
    ``Solidity.Frontend.Checked.lex_locate,
    ``Solidity.Frontend.Checked.lex_error_pos,
    ``Solidity.Frontend.Checked.lexRules_classified,
    ``Solidity.Frontend.Checked.lexRules_cover,
    ``Solidity.Frontend.Checked.classify_reserved]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} checked-lexer theorems use only the standard axioms"

-- G09 (`docs/feature-work/frontend-parse.md`): checked parsing of types and
-- declarations.
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Checked.parse_sound,
    ``Solidity.Frontend.Checked.parse_derives,
    ``Solidity.Frontend.Checked.parseType_derives,
    ``Solidity.Frontend.Checked.declCtors_covered,
    ``Solidity.Frontend.Checked.recursive_struct,
    ``Solidity.Frontend.Checked.print_roundtrip,
    ``Solidity.Frontend.Checked.strBody_sound]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} checked-parse (G09) theorems use only the standard axioms"

-- G10 (`docs/feature-work/frontend-parse.md`): checked expressions.
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Checked.parseExpr_derives,
    ``Solidity.Frontend.Checked.parseExpr_prec_root,
    ``Solidity.Frontend.Checked.binary_levels,
    ``Solidity.Frontend.Checked.every_operator,
    ``Solidity.Frontend.Checked.exprCtors_covered,
    ``Solidity.Frontend.Checked.expr_out_of_profile,
    ``Solidity.Frontend.Checked.parseInProfile_sound]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} checked-expression (G10) theorems use only the standard axioms"

-- G11 (`docs/feature-work/frontend-parse.md`): whole-unit parsing, the G05
-- parse stage and constructor coverage.
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Checked.checkUnits_sound,
    ``Solidity.Frontend.Checked.produce_accepted,
    ``Solidity.Frontend.Checked.allCtors_covered,
    ``Solidity.Frontend.Checked.profileCtors_covered,
    ``Solidity.Frontend.Checked.demo_parses,
    ``Solidity.Frontend.Checked.unit_out_of_profile]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} checked-unit (G11) theorems use only the standard axioms"

run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.wrapBits_mem,
    ``Solidity.Source.Env.fieldTy?_of_fieldAt,
    ``Solidity.Source.firstDone_mono,
    ``Solidity.Source.firstDone_none_iff,
    ``Solidity.Source.sessionAt_consistent,
    ``Solidity.Source.Ledger.semExprCoverage_of_typed,
    ``Solidity.Source.Ledger.semStmtCoverage_of_typed,
    ``Solidity.Source.Ledger.semExprGaps_spec,
    ``Solidity.Source.SemanticsExamples.add_overflow_checked,
    ``Solidity.Source.SemanticsExamples.order_legacy,
    ``Solidity.Source.SemanticsExamples.order_viaIR,
    ``Solidity.Source.SemanticsExamples.modifier_twice_legacy,
    ``Solidity.Source.SemanticsExamples.modifier_twice_viaIR,
    ``Solidity.Source.SemanticsExamples.revert_rolls_back,
    ``Solidity.Source.SemanticsExamples.transient_cleared,
    ``Solidity.Source.SemanticsExamples.reentrant_callback,
    ``Solidity.Source.SemanticsExamples.ctor_order_legacy,
    ``Solidity.Source.SemanticsExamples.ctor_order_viaIR,
    ``Solidity.Source.SemanticsExamples.outside_revert_rolls_back,
    ``Solidity.Source.SemanticsExamples.static_callback_refused,
    ``Solidity.Source.SemanticsExamples.session_runs,
    ``Solidity.Source.Typed.constShape,
    ``Solidity.Source.Syn.const_binOp,
    ``Solidity.Source.zeroLength_illTyped, ``Solidity.Source.Typed.unique,
    ``Solidity.Source.StmtD.unique, ``Solidity.Source.ItemsD.unique,
    ``Solidity.Source.RBody.ofDerivation_unique,
    ``Solidity.Source.belowAt, ``Solidity.Source.runTx_stable, ``Solidity.Source.deploy_stable,
    ``Solidity.Source.firstDone_runTx, ``Solidity.Source.runTx_stuck_stable,
    ``Solidity.Source.growAt, ``Solidity.Source.approxAt, ``Solidity.Source.runTx_events_mono,
    ``Solidity.Source.sessionAtEvents_consistent, ``Solidity.Source.stuck_not_diverges,
    ``Solidity.Source.stuck_stable, ``Solidity.Source.txFate_mono,
    ``Solidity.Source.stuck_eventually, ``Solidity.Source.deploy_events_mono]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} source-semantics theorems use only the standard axioms"

/-! Lane V04b checkpoint 1: G13's checker on the S02 typing rules
(`Solidity/Frontend/Static/`, `docs/feature-work/source-soundness.md`). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Static.hasType_iff,
    ``Solidity.Frontend.Static.stmtOK_iff,
    ``Solidity.Frontend.Static.itemsOK_iff,
    ``Solidity.Frontend.Static.wellFormed_iff,
    ``Solidity.Frontend.Static.InferExamples.member_checked,
    ``Solidity.Frontend.Static.InferExamples.structNew_checked,
    ``Solidity.Frontend.Static.InferExamples.extCall_checked,
    ``Solidity.Frontend.Static.InferExamples.extCallValue_checked,
    ``Solidity.Frontend.Static.InferExamples.pay_checked,
    ``Solidity.Frontend.Static.InferExamples.abiEncode_checked]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} checkpoint-1 checker theorems use only the standard axioms"

/-! Lane V04b checkpoints 2-3: preservation of the heap typing, the value
layer and value-fragment progress, the integration fixes (EIP-214, local
storage pointers, string byte writes; `docs/feature-work/source-soundness.md`). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.binVal_ok,
    ``Solidity.Source.cmpVal_ok,
    ``Solidity.Source.shiftVal_ok,
    ``Solidity.Source.unaryVal_ok,
    ``Solidity.Source.incDecVal_ok,
    ``Solidity.Source.amount_ok,
    ``Solidity.Source.convVal_ok,
    ``Solidity.Source.constVal_ok,
    ``Solidity.Source.Typed.toR_opsOK,
    ``Solidity.Source.StmtD.toR_opsOK,
    ``Solidity.Source.Elaborated.body_opsOK,
    ``Solidity.Source.Elaborated.inits_opsOK,
    ``Solidity.Source.convRV_ns,
    ``Solidity.Source.readAt_ns,
    ``Solidity.Source.writeAt_ns,
    ``Solidity.Source.keyStep_nsp,
    ``Solidity.Source.exprNSAt,
    ``Solidity.Source.evalE_valFrag_ns,
    ``Solidity.Source.stmtNSAt,
    ``Solidity.Source.stmtNS,
    ``Solidity.Source.itemsNS,
    ``Solidity.Source.ItemsD.toR_ns,
    ``Solidity.Source.alloc_ok,
    ``Solidity.Source.allocRef_ok,
    ``Solidity.Source.heapPut_ok,
    ``Solidity.Source.heapAt_ok,
    ``Solidity.Source.HeapOK.alloc,
    ``Solidity.Source.HeapOK.write,
    ``Solidity.Source.SoundnessExamples.add_value,
    ``Solidity.Source.SoundnessExamples.add_bool_stuck,
    ``Solidity.Source.SoundnessExamples.badBinary_not_opsOK,
    ``Solidity.Source.SoundnessExamples.badBinary_stuck,
    ``Solidity.Source.SoundnessExamples.cond_value,
    ``Solidity.Source.SoundnessExamples.loop_ns,
    ``Solidity.Source.SoundnessExamples.loop_value,
    ``Solidity.Source.SoundnessExamples.cb_ns,
    ``Solidity.Source.SoundnessExamples.cb_value,
    ``Solidity.Source.SoundnessExamples.ret_unframed_stuck,
    ``Solidity.Source.SoundnessExamples.ret_framed_ns,
    ``Solidity.Source.SoundnessExamples.stringByte_write,
    ``Solidity.Source.SemanticsExamples.static_value_call_halts,
    ``Solidity.Frontend.Static.InferExamples.ptrCopy_refused,
    ``Solidity.Frontend.Static.InferExamples.ptrDelete_refused]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} lane V04b checkpoint 2-3 theorems use only the standard axioms"

/-! Lane V04b typing decisions of 2026-10-30 (`docs/feature-work/source-s02.md`,
"Typing decisions"). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Frontend.Static.InferExamples.mapAssign_refused,
    ``Solidity.Frontend.Static.InferExamples.cdDelete_refused]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} typing-decision controls use only the standard axioms"

/-! Lane V04b: elaborated witnesses of the value fragment. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.SoundnessExamples.indexMapping_ns,
    ``Solidity.Source.SoundnessExamples.incBody_ns]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} elaborated fragment witnesses use only the standard axioms"

/-! Lane V04b: the function level (internal calls without modifiers). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.itemsNSP,
    ``Solidity.Source.runMods_nil_ns,
    ``Solidity.Source.callInternal_ns,
    ``Solidity.Source.SoundnessExamples.callRetOne_ns,
    ``Solidity.Source.SoundnessExamples.callBadFrame_stuck]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} function-level theorems use only the standard axioms"

/-! Lane V04b: elaborated bodies are in the frame internal calls build. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.Decl.frame?_lengths,
    ``Solidity.Source.Elaborated.body_locals,
    ``Solidity.Source.Elaborated.callInternal_ns]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} elaborated-frame theorems use only the standard axioms"

/-! Lane V04b: `return (a, b)` in the statement fragment. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.evalConvArgs_ns,
    ``Solidity.Source.setRets_ok,
    ``Solidity.Source.SoundnessExamples.retPair_ns,
    ``Solidity.Source.SoundnessExamples.retPair_unframed_stuck]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} return-tuple theorems use only the standard axioms"

/-! Lane V04b: dispatch coherence by signature. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.Decl.frame?_fnSig,
    ``Solidity.Source.Elaborated.body_sig,
    ``Solidity.Source.Elaborated.callInternal_sig_ns]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} signature-coherence theorems use only the standard axioms"

/-! Lane V04b: dispatch keeps the parameter types. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.Glob.dispatchFn_params,
    ``Solidity.Source.Elaborated.callInternal_call_ns]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} dispatch-parameter theorems use only the standard axioms"

/-! Lane V04b: internal calls inside expressions (the joint induction). -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.fragAt,
    ``Solidity.Source.evalE_callFrag_ns,
    ``Solidity.Source.stmt_callFrag_ns,
    ``Solidity.Source.callInternal_callFrag_ns,
    ``Solidity.Source.SoundnessExamples.callF_ns,
    ``Solidity.Source.SoundnessExamples.callF_value,
    ``Solidity.Source.SoundnessExamples.callF_badFrame_stuck]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} call-fragment theorems use only the standard axioms"

/-! Lane V04b: recursion through calls inside expressions; `return (x, x)`. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.SoundnessExamples.recF_ns,
    ``Solidity.Source.SoundnessExamples.recF_timeout,
    ``Solidity.Source.SoundnessExamples.retLocalPair_ns]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} recursion and return-tuple witnesses use only the standard axioms"

/-! Lane V04b: a call through a body that calls, with distinct bodies. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.SoundnessExamples.callG_ns,
    ``Solidity.Source.SoundnessExamples.callG_value]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} two-body call witnesses use only the standard axioms"

/-! Lane V04b: preservation of location reads and writes; the object-shape control. -/
run_cmd do
  let headlines : List Name := [
    ``Solidity.Source.memSet_pres,
    ``Solidity.Source.writeLoc_mem_pres,
    ``Solidity.Source.writeLoc_memByte_pres,
    ``Solidity.Source.writeLoc_local_pres,
    ``Solidity.Source.memElem_pres,
    ``Solidity.Source.readLoc_local_pres,
    ``Solidity.Source.readLoc_mem_pres,
    ``Solidity.Source.readLoc_memByte_pres,
    ``Solidity.Source.SoundnessExamples.ptrHeap_ok,
    ``Solidity.Source.SoundnessExamples.ptrHeap_byte_stuck]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"trust: {headlines.length} location read/write preservation theorems use only the standard axioms"

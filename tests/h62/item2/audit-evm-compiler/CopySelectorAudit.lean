import tests.h62.item2.«audit-evm-compiler».InputFixture
import tests.h62.item2.«audit-evm-compiler».JointWitness
import Solidity.Evm.MemoryStorageCopyExamples
import Solidity.Evm.MemoryFixedMixedExamples
import Solidity.Evm.MemoryStorageLifecycleExamples
import Solidity.Evm.MemoryObjectArrayExamples

/-! Joint premise satisfiability for five unchanged equivalence interfaces.
The output-relation equivalence does not assume either side holds: its chosen
output state/machine are ordinary data, not a successful execution witness.
The copy-free fixture admits a real program whose destination check reverts;
its Input certificate and both selector/copy-free guards hold together. -/
namespace Solidity.H62.EvmCompilerAudit.CopySelectors
#audit_input_fixture "Solidity.Evm.Memory.StorageCopyExamples.compiled_input" as Solidity.H62.EvmCompilerAudit.CopySelectors.storage_copy
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.memory_copy_input" as Solidity.H62.EvmCompilerAudit.CopySelectors.storage_copy_joint := by
  exact ⟨storage_copy.C, storage_copy.b, storage_copy.Γ, storage_copy.Δ, storage_copy.F, storage_copy.P, storage_copy.result, by decide +kernel, storage_copy.L, storage_copy.frame, storage_copy.base, storage_copy.σ, storage_copy.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.CopySelectors.storage_copy_joint

#audit_input_fixture "Solidity.Evm.Memory.FixedMixedExamples.compiled_input" as Solidity.H62.EvmCompilerAudit.CopySelectors.fixed_memory
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.fixed_input" as Solidity.H62.EvmCompilerAudit.CopySelectors.fixed_memory_joint := by
  exact ⟨fixed_memory.C, fixed_memory.b, fixed_memory.Γ, fixed_memory.Δ, fixed_memory.F, fixed_memory.P, fixed_memory.result, by decide +kernel, fixed_memory.L, fixed_memory.frame, fixed_memory.base, fixed_memory.σ, fixed_memory.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.CopySelectors.fixed_memory_joint

#audit_input_fixture "Solidity.Evm.Memory.StorageLifecycleExamples.compiled_input" as Solidity.H62.EvmCompilerAudit.CopySelectors.copy_construction
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.copyConstruction_input" as Solidity.H62.EvmCompilerAudit.CopySelectors.copy_construction_joint := by
  exact ⟨copy_construction.C, copy_construction.b, copy_construction.Γ, copy_construction.Δ, copy_construction.F, copy_construction.P, copy_construction.result, by decide +kernel, copy_construction.L, copy_construction.frame, copy_construction.base, copy_construction.σ, copy_construction.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.CopySelectors.copy_construction_joint

#audit_input_fixture "Solidity.Evm.Memory.StorageCopyExamples.bad_input" as Solidity.H62.EvmCompilerAudit.CopySelectors.copy_free
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.memory_copy_free_input" as Solidity.H62.EvmCompilerAudit.CopySelectors.copy_free_joint := by
  exact ⟨copy_free.C, copy_free.b, copy_free.Γ, copy_free.Δ, copy_free.F, copy_free.P, copy_free.result, by decide +kernel, copy_free.L, copy_free.frame, copy_free.base, copy_free.σ, copy_free.m, by decide +kernel, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.CopySelectors.copy_free_joint

#audit_input_fixture "Solidity.Evm.Memory.ObjectArrayExamples.compiled_input" as Solidity.H62.EvmCompilerAudit.CopySelectors.object_output
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.object_rep" as Solidity.H62.EvmCompilerAudit.CopySelectors.object_output_joint := by
  exact ⟨object_output.C, object_output.b, object_output.Γ, object_output.Δ, object_output.F, object_output.P, object_output.result, by decide +kernel, object_output.L, object_output.frame, object_output.base, object_output.σ, object_output.m, object_output.σ, object_output.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.CopySelectors.object_output_joint

end Solidity.H62.EvmCompilerAudit.CopySelectors

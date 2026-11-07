import tests.h62.item2.«audit-evm-compiler».InputFixture
import tests.h62.item2.«audit-evm-compiler».JointWitness
import Solidity.Evm.MemoryStructExamples
import Solidity.Evm.MemoryRefArrayExamples
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Evm.MemoryObjectConstructionExamples
import Solidity.Evm.MemoryCallExamples

/-! Five ordinary selector interfaces. Each existential tuple uses one actual
inhabited public Input fixture, including the correct backend selector.
The originals are equivalences, not totality statements. -/
namespace Solidity.H62.EvmCompilerAudit.Selectors
open Solidity.H62.EvmCompilerAudit.Fixtures
#audit_input_fixture "Solidity.Evm.Memory.StructExamples.Public.compiled_input" as Solidity.H62.EvmCompilerAudit.Selectors.memory
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.memory_input" as Solidity.H62.EvmCompilerAudit.Selectors.memory_joint := by
  exact ⟨memory.C, memory.b, memory.Γ, memory.Δ, memory.F, memory.P, memory.result, by decide +kernel, memory.L, memory.frame, memory.base, memory.σ, memory.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Selectors.memory_joint

#audit_input_fixture "Solidity.Evm.Memory.RefArrayExamples.compiled_input" as Solidity.H62.EvmCompilerAudit.Selectors.references
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.referenceArray_input" as Solidity.H62.EvmCompilerAudit.Selectors.references_joint := by
  exact ⟨references.C, references.b, references.Γ, references.Δ, references.F, references.P, references.result, by decide +kernel, references.L, references.frame, references.base, references.σ, references.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Selectors.references_joint

#audit_input_fixture "Solidity.Evm.Memory.ObjectArrayExamples.compiled_input" as Solidity.H62.EvmCompilerAudit.Selectors.objects
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.object_input" as Solidity.H62.EvmCompilerAudit.Selectors.objects_joint := by
  exact ⟨objects.C, objects.b, objects.Γ, objects.Δ, objects.F, objects.P, objects.result, by decide +kernel, objects.L, objects.frame, objects.base, objects.σ, objects.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Selectors.objects_joint

#audit_input_fixture "Solidity.Evm.Memory.ConstructionExamples.compiled_input" as Solidity.H62.EvmCompilerAudit.Selectors.construction
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.construction_input" as Solidity.H62.EvmCompilerAudit.Selectors.construction_joint := by
  exact ⟨construction.C, construction.b, construction.Γ, construction.Δ, construction.F, construction.P, construction.result, by decide +kernel, construction.L, construction.frame, construction.base, construction.σ, construction.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Selectors.construction_joint

#audit_input_fixture "Solidity.Evm.Memory.CallExamples.mutation_input" as Solidity.H62.EvmCompilerAudit.Selectors.calls
#audit_joint_witness "Solidity.Evm.Compiler.Compilation.memoryCalls_input" as Solidity.H62.EvmCompilerAudit.Selectors.calls_joint := by
  exact ⟨calls.C, calls.b, calls.Γ, calls.Δ, calls.F, calls.P, calls.result, by decide +kernel, calls.L, calls.frame, calls.base, calls.σ, calls.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.Selectors.calls_joint

end Solidity.H62.EvmCompilerAudit.Selectors

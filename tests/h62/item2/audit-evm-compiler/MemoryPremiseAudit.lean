import tests.h62.item2.«audit-evm-compiler».JointWitness
import Solidity.Evm.MemoryCompileExamples

/-! Complete premise packages for five original memory-compiler statements.
The unchanged populated fixture compiles a nonempty write-through-alias/read
program. Representation, frame capacity and allocation input are proved for
that same tuple. These packages establish premise satisfiability; the original
GrowingResult conclusions remain conditional simulation, not total success. -/
namespace Solidity.H62.EvmCompilerAudit.MemoryPremises
open Evm Evm.Memory Evm.Memory.CompileExamples

#audit_joint_witness "Solidity.Evm.Memory.compile_correct" as Solidity.H62.EvmCompilerAudit.MemoryPremises.compile_joint := by
  exact ⟨Evm.Memory.CompileExamples.C, 0, 1, 4, Evm.Memory.CompileExamples.Γ, Evm.Memory.CompileExamples.Γ,
    Frag.init Evm.Memory.CompileExamples.Γ, writeAndRead, compiled, rfl,
    Evm.Memory.CompileExamples.σ, Evm.Memory.CompileExamples.base, Evm.Memory.CompileExamples.machine,
    fixture_repr, by decide +kernel, .inl (by decide +kernel), True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.MemoryPremises.compile_joint

#audit_joint_witness "Solidity.Evm.Memory.ProgFrag.correct" as Solidity.H62.EvmCompilerAudit.MemoryPremises.program_joint := by
  exact ⟨Evm.Memory.CompileExamples.C, 0, 1, 4, Evm.Memory.CompileExamples.Γ, Evm.Memory.CompileExamples.Γ,
    Frag.init Evm.Memory.CompileExamples.Γ, compiled.frag, writeAndRead, compiled.code,
    compiled.cert, Evm.Memory.CompileExamples.σ, Evm.Memory.CompileExamples.base, Evm.Memory.CompileExamples.machine,
    fixture_repr, by decide +kernel,
    .inl (by decide +kernel), True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.MemoryPremises.program_joint

#audit_joint_witness "Solidity.Evm.Memory.ProgFrag.length_mono" as Solidity.H62.EvmCompilerAudit.MemoryPremises.length_joint := by
  exact ⟨Evm.Memory.CompileExamples.C, 0, Evm.Memory.CompileExamples.Γ, Evm.Memory.CompileExamples.Γ,
    Frag.init Evm.Memory.CompileExamples.Γ, compiled.frag, writeAndRead, compiled.code,
    compiled.cert, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.MemoryPremises.length_joint

#audit_joint_witness "Solidity.Evm.Memory.ProgFrag.pushes_zero" as Solidity.H62.EvmCompilerAudit.MemoryPremises.pushes_joint := by
  exact ⟨Evm.Memory.CompileExamples.C, 0, Evm.Memory.CompileExamples.Γ, Evm.Memory.CompileExamples.Γ,
    Frag.init Evm.Memory.CompileExamples.Γ, compiled.frag, writeAndRead, compiled.code,
    compiled.cert, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.MemoryPremises.pushes_joint

#audit_joint_witness "Solidity.Evm.Memory.allocationCostProg_zero" as Solidity.H62.EvmCompilerAudit.MemoryPremises.cost_joint := by
  exact ⟨Evm.Memory.CompileExamples.C, Evm.Memory.CompileExamples.Γ, Evm.Memory.CompileExamples.Γ, writeAndRead, by decide +kernel,
    Evm.Memory.CompileExamples.σ, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.MemoryPremises.cost_joint
end Solidity.H62.EvmCompilerAudit.MemoryPremises

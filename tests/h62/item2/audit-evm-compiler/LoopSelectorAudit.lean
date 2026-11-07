import tests.h62.item2.«audit-evm-compiler».SelectorAudit
import Solidity.Evm.MemoryCompileExamples

/-! Binder-level satisfiability only for five unchanged Compiler interfaces.
The nonempty loop fixtures are compiled by the unchanged lower compilers.
All original binders are jointly instantiated. This does not show that Input,
Room or Rep is satisfiable; they occur in equivalence conclusions. The
construction output is merely typed data, not a source-success witness. -/
namespace Solidity.H62.EvmCompilerAudit.LoopSelectors
open Evm
open Evm.Memory.CompileExamples

private def loopCondition : Val C Γ .bool :=
  .binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 3 rfl))
private def loopProgram : Solidity.Prog C Γ Γ :=
  .cons (.loop .auto loopCondition writeAndRead) .nil
private def scopedProgram : Solidity.Prog C Γ Γ :=
  .cons (.block loopProgram) .nil
private def loopCompiled : Memory.Loops.CompiledProg 0 (Frag.init Γ) loopProgram :=
  (Memory.Loops.compileProg 0 (Frag.init Γ) loopProgram).get (by decide +kernel)
private def scopedCompiled : Memory.LoopScopes.CompiledProg 0 (Frag.init Γ) scopedProgram :=
  (Memory.LoopScopes.compileProg 0 scopedProgram (Frag.init Γ)).get (by decide +kernel)
private def loopResult : Compiler.Compilation 0 (Frag.init Γ) loopProgram :=
  .memoryLoops loopCompiled
private def scopedResult : Compiler.Compilation 0 (Frag.init Γ) scopedProgram :=
  .memoryLoopScopes scopedCompiled

#audit_joint_witness "Solidity.Evm.Compiler.Compilation.memoryLoops_input_of" as Solidity.H62.EvmCompilerAudit.LoopSelectors.loops_of_joint := by
  exact ⟨Evm.Memory.CompileExamples.C, 0, Evm.Memory.CompileExamples.Γ, Evm.Memory.CompileExamples.Γ, Frag.init Evm.Memory.CompileExamples.Γ, loopProgram, loopCompiled, 1, 4, Evm.Memory.CompileExamples.base, Evm.Memory.CompileExamples.σ, Evm.Memory.CompileExamples.machine, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.LoopSelectors.loops_of_joint

#audit_joint_witness "Solidity.Evm.Compiler.Compilation.memoryLoops_input" as Solidity.H62.EvmCompilerAudit.LoopSelectors.loops_joint := by
  exact ⟨Evm.Memory.CompileExamples.C, 0, Evm.Memory.CompileExamples.Γ, Evm.Memory.CompileExamples.Γ, Frag.init Evm.Memory.CompileExamples.Γ, loopProgram, loopResult, rfl, 1, 4, Evm.Memory.CompileExamples.base, Evm.Memory.CompileExamples.σ, Evm.Memory.CompileExamples.machine, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.LoopSelectors.loops_joint

#audit_joint_witness "Solidity.Evm.Compiler.Compilation.memoryLoopScopes_input_of" as Solidity.H62.EvmCompilerAudit.LoopSelectors.scopes_of_joint := by
  exact ⟨Evm.Memory.CompileExamples.C, 0, Evm.Memory.CompileExamples.Γ, Evm.Memory.CompileExamples.Γ, Frag.init Evm.Memory.CompileExamples.Γ, scopedProgram, scopedCompiled, 1, 4, Evm.Memory.CompileExamples.base, Evm.Memory.CompileExamples.σ, Evm.Memory.CompileExamples.machine, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.LoopSelectors.scopes_of_joint

#audit_joint_witness "Solidity.Evm.Compiler.Compilation.memoryLoopScopes_input" as Solidity.H62.EvmCompilerAudit.LoopSelectors.scopes_joint := by
  exact ⟨Evm.Memory.CompileExamples.C, 0, Evm.Memory.CompileExamples.Γ, Evm.Memory.CompileExamples.Γ, Frag.init Evm.Memory.CompileExamples.Γ, scopedProgram, scopedResult, rfl, 1, 4, Evm.Memory.CompileExamples.base, Evm.Memory.CompileExamples.σ, Evm.Memory.CompileExamples.machine, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.LoopSelectors.scopes_joint

private noncomputable def constructionOutput : State Selectors.construction.C Selectors.construction.Δ :=
  { storage := Storage.init Selectors.construction.C
    H := []
    heap := Heap.empty
    env := (PrimTy.dflt .uint, none, none, none, none, PrimTy.dflt .uint, none, ()) }

#audit_joint_witness "Solidity.Evm.Compiler.Compilation.construction_rep" as Solidity.H62.EvmCompilerAudit.LoopSelectors.construction_output_joint := by
  exact ⟨Selectors.construction.C, Selectors.construction.b, Selectors.construction.Γ, Selectors.construction.Δ, Selectors.construction.F, Selectors.construction.P, Selectors.construction.result, by decide +kernel, Selectors.construction.L, Selectors.construction.frame, Selectors.construction.base, Selectors.construction.σ, Selectors.construction.m, constructionOutput, Selectors.construction.m, True.intro⟩
#print axioms Solidity.H62.EvmCompilerAudit.LoopSelectors.construction_output_joint
end Solidity.H62.EvmCompilerAudit.LoopSelectors

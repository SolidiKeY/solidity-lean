import tests.h62.item2.«audit-compiler-transport».Audit

/-! One simultaneous witness for original generic compiler boundary statements.
No global producer inhabitation follows. The selected concrete contract, program,
input, source output, target output and map occur in the same dependent tuple.
-/
namespace H62.CompilerTransport
open Solidity Solidity.Evm Solidity.Evm.Compiler Solidity.Backend.Passes
open MemoryCallControls (initial base machine)

/-- Witnesses the original premises of compilation_exact, compilation_success,
compilation_reflect_success, compilation_revert_iff and compilation_input_stack,
using the same nonempty allocating supported program. -/
theorem boundary_joint_witness :
    ∃ (canonical : Machine) (selected : Nat → Fin W),
      Compiler.compile 1 (Frag.init []) CompilerWholeScope.program = some CompilerWholeScope.actual ∧
      CompilerWholeScope.actual.Input 1 128 base initial machine ∧
      Evm.Prog.pays CompilerWholeScope.program = false ∧
      CompilerWholeScope.program.run initial = .ok CompilerWholeScope.result ∧
      canonical.stack = [] ∧
      ∀ (tail : List Word),
        CompilerWholeScope.actual.Input 1 128 base initial {machine with stack := tail} ∧
        run CompilerWholeScope.actual.code {machine with stack := tail} =
          .ok {canonical with stack := tail} 0 ∧
        MappedOutput CompilerWholeScope.actual 1 128 base initial {machine with stack := tail}
          CompilerWholeScope.result.st {canonical with stack := tail} selected := by
  obtain ⟨canonical,selected,empty,runs⟩ := CompilerWholeScope.shared
  refine ⟨canonical,selected,CompilerWholeScope.accepted,CompilerWholeScope.initial_input,
    ?_,CompilerWholeScope.source_run,empty,?_⟩
  · decide +kernel
  · intro tail
    exact ⟨compilation_input_stack CompilerWholeScope.actual CompilerWholeScope.initial_input tail,
      (runs tail).1,(runs tail).2⟩

#print axioms boundary_joint_witness
end H62.CompilerTransport

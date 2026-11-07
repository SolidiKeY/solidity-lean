import tests.h62.item2.«audit-evm-compiler».JointFromCertificate
import Solidity.Evm.MemoryCallExamples

/-! Joint input for the unified compiler agreement interface. The original
closed mutation_input certificate determines every actual program, state,
machine, allocation/frame bound and representation argument together. Its
nonempty allocation/internal-call program is unchanged. -/
#audit_joint_from "Solidity.Evm.Compiler.Compilation.correct" using "Solidity.Evm.Memory.CallExamples.mutation_input" as Solidity.H62.EvmCompilerAudit.Entry.compilation_correct_joint
#print axioms Solidity.H62.EvmCompilerAudit.Entry.compilation_correct_joint

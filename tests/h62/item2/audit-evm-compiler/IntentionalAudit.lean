import tests.h62.item2.«audit-evm-compiler».JointImpossible
import Solidity.Evm.Correct
import Solidity.Evm.MemoryCallExamples
import Solidity.Evm.MemoryCompileExamples
import Solidity.Evm.MemoryDynamicFixedDefaultExamples
import Solidity.Evm.MemoryFixedDefaultExamples
import Solidity.Evm.MemoryFixedDynamicDefaultExamples
import Solidity.Evm.MemoryNestedFixedDefaultExamples
import Solidity.Evm.MemoryObjectConstructionExamples
import Solidity.Evm.MemoryPrimitiveStructArrayDefaultExamples
import Solidity.Evm.MemoryRefArrayExamples
import Solidity.Evm.MemoryReferenceArrayRebindExamples
import Solidity.Evm.MemoryStructCopyExamples
import Solidity.Evm.MemoryStructDefault
import Solidity.Evm.MemoryStructDefaultExamples
import Solidity.Evm.MemoryStructReferenceDefaultExamples
import Solidity.Evm.MemoryStructReferenceDefaultModes
import Solidity.Evm.Repr

/-! H69 intentional refutations. Every package includes every original forall binder.
Names, reasons and exact frozen signature bindings are recorded in coverage.json. -/

-- Solidity.Evm.Memory.RefArrayExamples.noStructs: Array-only fixture cannot contain a struct reference
#audit_joint_impossible "Solidity.Evm.Memory.RefArrayExamples.noStructs" as Solidity.H62.EvmCompilerAudit.Intentional.case00
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case00

-- Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.noRefs: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.PrimitiveStructArrayDefaultExamples.noRefs" as Solidity.H62.EvmCompilerAudit.Intentional.case01
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case01

-- Solidity.Evm.Memory.FixedDefaultExamples.noRefs: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.FixedDefaultExamples.noRefs" as Solidity.H62.EvmCompilerAudit.Intentional.case02
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case02

-- Solidity.Evm.Memory.DynamicFixedDefaultExamples.noRefs: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.DynamicFixedDefaultExamples.noRefs" as Solidity.H62.EvmCompilerAudit.Intentional.case03
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case03

-- Solidity.Evm.Memory.NestedFixedDefaultExamples.noRefs: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.NestedFixedDefaultExamples.noRefs" as Solidity.H62.EvmCompilerAudit.Intentional.case04
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case04

-- Solidity.Evm.Memory.ReferenceArrayRebindExamples.noRefs: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.ReferenceArrayRebindExamples.noRefs" as Solidity.H62.EvmCompilerAudit.Intentional.case05
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case05

-- Solidity.Evm.Memory.FixedDynamicDefaultExamples.noRefs: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.FixedDynamicDefaultExamples.noRefs" as Solidity.H62.EvmCompilerAudit.Intentional.case06
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case06

-- Solidity.Evm.Memory.ConstructionExamples.noRefs: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.ConstructionExamples.noRefs" as Solidity.H62.EvmCompilerAudit.Intentional.case07
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case07

-- Solidity.Evm.Memory.primitiveMembers_noRef: Primitive-only members cannot contain a reference member
#audit_joint_impossible "Solidity.Evm.Memory.primitiveMembers_noRef" as Solidity.H62.EvmCompilerAudit.Intentional.case08
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case08

-- Solidity.Evm.Memory.StructDefaultExamples.noRef: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.StructDefaultExamples.noRef" as Solidity.H62.EvmCompilerAudit.Intentional.case09
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case09

-- Solidity.Evm.Memory.StructCopyExamples.noRef: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.StructCopyExamples.noRef" as Solidity.H62.EvmCompilerAudit.Intentional.case10
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case10

-- Solidity.Evm.Memory.StructReferenceDefaultExamples.noRef: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.StructReferenceDefaultExamples.noRef" as Solidity.H62.EvmCompilerAudit.Intentional.case11
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case11

-- Solidity.Evm.Memory.StructReferenceDefaultModes.noRef: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.StructReferenceDefaultModes.noRef" as Solidity.H62.EvmCompilerAudit.Intentional.case12
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case12

-- Solidity.Evm.Memory.CallExamples.noRef: Empty-heap reference refutation
#audit_joint_impossible "Solidity.Evm.Memory.CallExamples.noRef" as Solidity.H62.EvmCompilerAudit.Intentional.case13
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case13

-- Solidity.Evm.Memory.CompileExamples.noStructs: Array-only fixture cannot contain a struct reference
#audit_joint_impossible "Solidity.Evm.Memory.CompileExamples.noStructs" as Solidity.H62.EvmCompilerAudit.Intentional.case14
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case14

-- Solidity.Evm.OccAt.kind_unique: Length and primitive roles of one typed layout cell are disjoint
#audit_joint_impossible "Solidity.Evm.OccAt.kind_unique" as Solidity.H62.EvmCompilerAudit.Intentional.case15
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case15

-- Solidity.Evm.len_prim_disjoint: A contract storage slot cannot simultaneously be a length slot and a primitive slot
#audit_joint_impossible "Solidity.Evm.len_prim_disjoint" as Solidity.H62.EvmCompilerAudit.Intentional.case16
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case16

-- Solidity.Evm.Args.noAlias: Admitted compiler argument contexts cannot contain an alias parameter index
#audit_joint_impossible "Solidity.Evm.Args.noAlias" as Solidity.H62.EvmCompilerAudit.Intentional.case17
#print axioms Solidity.H62.EvmCompilerAudit.Intentional.case17

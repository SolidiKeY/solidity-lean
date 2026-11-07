import tests.h62.item2.«audit-evm-compiler».JointRefutation
import Solidity.Evm.MemoryAllocSourceExamples
import Solidity.Evm.MemoryCallExamples
import Solidity.Evm.MemoryDynamicFixedDefaultExamples
import Solidity.Evm.MemoryFixedChildArrayExamples
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Evm.MemoryObjectConstructionExamples
import Solidity.Evm.MemoryPathExamples
import Solidity.Evm.MemoryRefArrayExamples
import Solidity.Evm.MemoryStructArrayInputExamples
import Solidity.Evm.MemoryStructCopyExamples
import Solidity.Evm.MemoryStructDefaultExamples
import Solidity.Evm.MemoryStructExamples
import Solidity.Evm.MemoryStructReferenceDefaultBoundaries
import Solidity.Evm.MemoryStructReferenceDefaultExamples

/-! Intentional negative controls under H69. Each proof negates the complete
joint package of the original hypotheses, including those hidden by Not.
These refutations are not ordinary success witnesses or compiler defects. -/
namespace Solidity.H62.EvmCompilerAudit.Refutations

-- Solidity/Evm/MemoryStructExamples.lean:269
-- Intentional: Two-cell struct at W-1 violates the no-wrap bound.
#audit_refutation "Solidity.Evm.Memory.StructExamples.wrapping_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case00
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case00

-- Solidity/Evm/MemoryStructExamples.lean:340
-- Intentional: A live write makes a required free-tail zero cell equal one.
#audit_refutation "Solidity.Evm.Memory.StructExamples.legacy_write_breaks_allocator" as Solidity.H62.EvmCompilerAudit.Refutations.case01
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case01

-- Solidity/Evm/MemoryStructExamples.lean:349
-- Intentional: The live struct ends at 18 beyond allocator cursor 8.
#audit_refutation "Solidity.Evm.Memory.StructExamples.misplaced_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case02
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case02

-- Solidity/Evm/MemoryAllocSourceExamples.lean:199
-- Intentional: Reached allocation cost W cannot fit its header and payload.
#audit_refutation "Solidity.Evm.Memory.AllocSourceExamples.whole_space_rejected" as Solidity.H62.EvmCompilerAudit.Refutations.case03
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case03

-- Solidity/Evm/MemoryAllocSourceExamples.lean:209
-- Intentional: Public input entails an impossible whole-address-space allocation.
#audit_refutation "Solidity.Evm.Memory.AllocSourceExamples.maximal_input_rejected" as Solidity.H62.EvmCompilerAudit.Refutations.case04
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case04

-- Solidity/Evm/MemoryAllocSourceExamples.lean:301
-- Intentional: Rebinding length plus header costs W and cannot fit.
#audit_refutation "Solidity.Evm.Memory.AllocSourceExamples.maximal_rebind_rejected" as Solidity.H62.EvmCompilerAudit.Refutations.case05
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case05

-- Solidity/Evm/MemoryAllocSourceExamples.lean:366
-- Intentional: Temporary block locals exceed the reserved frame.
#audit_refutation "Solidity.Evm.Memory.AllocSourceExamples.scopes_frame_rejected" as Solidity.H62.EvmCompilerAudit.Refutations.case06
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case06

-- Solidity/Evm/MemoryRefArrayExamples.lean:181
-- Intentional: Child pointer 24 contradicts the expected pointer 16.
#audit_refutation "Solidity.Evm.Memory.RefArrayExamples.wrong_pointer_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case07
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case07

-- Solidity/Evm/MemoryObjectArrayExamples.lean:104
-- Intentional: Cursor 33 overlaps the live fixed parent.
#audit_refutation "Solidity.Evm.Memory.ObjectArrayExamples.allocator_overlap_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case08
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case08

-- Solidity/Evm/MemoryObjectArrayExamples.lean:180
-- Intentional: Child pointer 24 contradicts the expected pointer 16.
#audit_refutation "Solidity.Evm.Memory.ObjectArrayExamples.wrong_pointer_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case09
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case09

-- Solidity/Evm/MemoryFixedChildArrayExamples.lean:103
-- Intentional: Cursor 33 overlaps the live fixed parent.
#audit_refutation "Solidity.Evm.Memory.FixedChildArrayExamples.allocator_overlap_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case10
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case10

-- Solidity/Evm/MemoryFixedChildArrayExamples.lean:179
-- Intentional: Child pointer 24 contradicts the expected pointer 16.
#audit_refutation "Solidity.Evm.Memory.FixedChildArrayExamples.wrong_pointer_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case11
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case11

-- Solidity/Evm/MemoryDynamicFixedDefaultExamples.lean:160
-- Intentional: Cursor W-5 plus allocation cost 5 violates strict capacity.
#audit_refutation "Solidity.Evm.Memory.DynamicFixedDefaultExamples.insufficient_capacity_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case12
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case12

-- Solidity/Evm/MemoryObjectConstructionExamples.lean:221
-- Intentional: Cursor W-15 plus allocation cost 15 violates strict capacity.
#audit_refutation "Solidity.Evm.Memory.ConstructionExamples.insufficient_capacity_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case13
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case13

-- Solidity/Evm/MemoryStructArrayInputExamples.lean:158
-- Intentional: Reference field 24 contradicts the expected reference 16.
#audit_refutation "Solidity.Evm.Memory.StructArrayInputExamples.wrong_reference_field_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case14
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case14

-- Solidity/Evm/MemoryPathExamples.lean:189
-- Intentional: Leaf pointer 40 contradicts the expected pointer 32.
#audit_refutation "Solidity.Evm.Memory.PathExamples.wrong_pointer_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case15
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case15

-- Solidity/Evm/MemoryPathExamples.lean:589
-- Intentional: Cursor W-10 plus cost 11 cannot fit.
#audit_refutation "Solidity.Evm.Memory.PathExamples.ReferenceDelete.capacity_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case16
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case16

-- Solidity/Evm/MemoryPathExamples.lean:612
-- Intentional: Required initialized pointer would equate none with some reference.
#audit_refutation "Solidity.Evm.Memory.PathExamples.ReferenceDelete.unset_input_refuted" as Solidity.H62.EvmCompilerAudit.Refutations.case17
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case17

-- Solidity/Evm/MemoryStructDefaultExamples.lean:118
-- Intentional: Cursor W-10 plus cost 12 cannot fit.
#audit_refutation "Solidity.Evm.Memory.StructDefaultExamples.capacity_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case18
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case18

-- Solidity/Evm/MemoryStructDefaultExamples.lean:433
-- Intentional: Cursor W-10 plus cost 20 cannot fit.
#audit_refutation "Solidity.Evm.Memory.StructDefaultExamples.WholeDelete.capacity_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case19
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case19

-- Solidity/Evm/MemoryStructDefaultExamples.lean:528
-- Intentional: Cursor W-10 plus cost 14 cannot fit.
#audit_refutation "Solidity.Evm.Memory.StructDefaultExamples.DefaultArrays.capacity_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case20
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case20

-- Solidity/Evm/MemoryStructCopyExamples.lean:131
-- Intentional: Cursor W-10 plus cost 20 cannot fit.
#audit_refutation "Solidity.Evm.Memory.StructCopyExamples.capacity_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case21
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case21

-- Solidity/Evm/MemoryStructReferenceDefaultExamples.lean:114
-- Intentional: Cursor W-10 plus cost 22 cannot fit.
#audit_refutation "Solidity.Evm.Memory.StructReferenceDefaultExamples.capacity_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case22
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case22

-- Solidity/Evm/MemoryStructReferenceDefaultBoundaries.lean:73
-- Intentional: Zero child pointer contradicts required nonzero pointer 128.
#audit_refutation "Solidity.Evm.Memory.StructReferenceDefaultBoundaries.zero_pointer_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case23
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case23

-- Solidity/Evm/MemoryStructReferenceDefaultBoundaries.lean:86
-- Intentional: Cursor W-3 plus cost 4 cannot fit.
#audit_refutation "Solidity.Evm.Memory.StructReferenceDefaultBoundaries.empty_capacity_invalid" as Solidity.H62.EvmCompilerAudit.Refutations.case24
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case24

-- Solidity/Evm/MemoryCallExamples.lean:250
-- Intentional: Cursor W-4 plus allocation cost 5 cannot fit.
#audit_refutation "Solidity.Evm.Memory.CallExamples.capacity_refused" as Solidity.H62.EvmCompilerAudit.Refutations.case25
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case25

-- Solidity/Evm/MemoryCallExamples.lean:262
-- Intentional: No available frame cannot hold the positive required frame.
#audit_refutation "Solidity.Evm.Memory.CallExamples.frame_refused" as Solidity.H62.EvmCompilerAudit.Refutations.case26
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case26

-- Solidity/Evm/MemoryCallExamples.lean:507
-- Intentional: Caller-only frame omits required callee-private capacity.
#audit_refutation "Solidity.Evm.Memory.CallExamples.privateFrame_refused" as Solidity.H62.EvmCompilerAudit.Refutations.case27
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case27

-- Solidity/Evm/MemoryCallExamples.lean:574
-- Intentional: Observed empty reversion excludes the panic-1 payload; observation separation.
#audit_refutation "Solidity.Evm.Memory.CallExamples.calleeFailure_not_panic" as Solidity.H62.EvmCompilerAudit.Refutations.case28
#print axioms Solidity.H62.EvmCompilerAudit.Refutations.case28

end Solidity.H62.EvmCompilerAudit.Refutations

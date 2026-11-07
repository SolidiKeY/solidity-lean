import Solidity.Assurance.NonVacuityH28.AllocatorGrowth
import Solidity.Assurance.NonVacuityH28.Calculus
import Solidity.Assurance.NonVacuityH28.CallbackFrames
import Solidity.Assurance.NonVacuityH28.Callbacks
import Solidity.Assurance.NonVacuityH28.CheckedFamilies
import Solidity.Assurance.NonVacuityH28.CheckedObjects
import Solidity.Assurance.NonVacuityH28.Environments
import Solidity.Assurance.NonVacuityH28.Families
import Solidity.Assurance.NonVacuityH28.Fragile
import Solidity.Assurance.NonVacuityH28.HeapQueries
import Solidity.Assurance.NonVacuityH28.JointWorld
import Solidity.Assurance.NonVacuityH28.Locals
import Solidity.Assurance.NonVacuityH28.LogicalGates
import Solidity.Assurance.NonVacuityH28.LoopContracts
import Solidity.Assurance.NonVacuityH28.MemoryControls
import Solidity.Assurance.NonVacuityH28.MemoryInputs
import Solidity.Assurance.NonVacuityH28.Originals
import Solidity.Assurance.NonVacuityH28.Outcomes
import Solidity.Assurance.NonVacuityH28.Preconditions
import Solidity.Assurance.NonVacuityH28.PrimitiveFamilies
import Solidity.Assurance.NonVacuityH28.ScalarPremises
import Solidity.Assurance.NonVacuityH28.Storage
import Solidity.Assurance.NonVacuityH28.TailSensitive
import Solidity.Assurance.NonVacuityH28.VacuityControls

/-! Exact kernel signatures and measured axiom sets; no semantic witness. -/
set_option pp.explicit true
set_option pp.universes true

#check @Solidity.Main.rule_sound
#print axioms Solidity.Main.rule_sound
#check @Solidity.Main.rule_unique
#print axioms Solidity.Main.rule_unique
#check @Solidity.Main.rule_is_step
#print axioms Solidity.Main.rule_is_step
#check @Solidity.Main.rule_exists
#print axioms Solidity.Main.rule_exists
#check @Solidity.Main.rule_of_step
#print axioms Solidity.Main.rule_of_step
#check @Solidity.Main.solkey_rule_exists
#print axioms Solidity.Main.solkey_rule_exists
#check @Solidity.Main.solkey_rule_lt_calculus
#print axioms Solidity.Main.solkey_rule_lt_calculus
#check @Solidity.Main.solkey_step_taclet
#print axioms Solidity.Main.solkey_step_taclet
#check @Solidity.Main.solkey_eq_calculus
#print axioms Solidity.Main.solkey_eq_calculus
#check @Solidity.Main.solkey_lt_calculus
#print axioms Solidity.Main.solkey_lt_calculus
#check @Solidity.Main.soundness
#print axioms Solidity.Main.soundness
#check @Solidity.Main.soundness'
#print axioms Solidity.Main.soundness'
#check @Solidity.Main.solkey_soundness
#print axioms Solidity.Main.solkey_soundness
#check @Solidity.Main.callback_soundness
#print axioms Solidity.Main.callback_soundness
#check @Solidity.Main.noCallback_soundness
#print axioms Solidity.Main.noCallback_soundness
#check @Solidity.Main.noCallback_iff
#print axioms Solidity.Main.noCallback_iff
#check @Solidity.Main.cleanTail_holds
#print axioms Solidity.Main.cleanTail_holds
#check @Solidity.Main.symex_sound
#print axioms Solidity.Main.symex_sound
#check @Solidity.Main.compiler_correct
#print axioms Solidity.Main.compiler_correct
#check @Solidity.Main.compiler_net
#print axioms Solidity.Main.compiler_net
#check @Solidity.Main.compiler_checked
#print axioms Solidity.Main.compiler_checked
#check @Solidity.Stmt.sound
#print axioms Solidity.Stmt.sound
#check @Solidity.Rule.premise_unique
#print axioms Solidity.Rule.premise_unique
#check @Solidity.Rule.toStep
#print axioms Solidity.Rule.toStep
#check @Solidity.Stmt.rule_exists
#print axioms Solidity.Stmt.rule_exists
#check @Solidity.Rule.ofStep
#print axioms Solidity.Rule.ofStep
#check @Solidity.Stmt.step_taclet
#print axioms Solidity.Stmt.step_taclet
#check @Solidity.Stmt.solkey_lt_calculus
#print axioms Solidity.Stmt.solkey_lt_calculus
#check @Solidity.Stmt.taclet_of_admits
#print axioms Solidity.Stmt.taclet_of_admits
#check @Solidity.Proves.solkey_iff
#print axioms Solidity.Proves.solkey_iff
#check @Solidity.Proves.solkey_lt_calculus
#print axioms Solidity.Proves.solkey_lt_calculus
#check @Solidity.Proves.sound
#print axioms Solidity.Proves.sound
#check @Solidity.Proves.valid
#print axioms Solidity.Proves.valid
#check @Solidity.ProvesC.valid
#print axioms Solidity.ProvesC.valid
#check @Solidity.validC_false_iff
#print axioms Solidity.validC_false_iff
#check @Solidity.ValidTail.holds_of_clean
#print axioms Solidity.ValidTail.holds_of_clean
#check @Solidity.symex_sound
#print axioms Solidity.symex_sound
#check @Solidity.Evm.compile_correct
#print axioms Solidity.Evm.compile_correct
#check @Solidity.Evm.compile_net
#print axioms Solidity.Evm.compile_net
#check @Solidity.Evm.Compiler.Compilation.correct
#print axioms Solidity.Evm.Compiler.Compilation.correct
#check @Solidity.Proves.sound_of
#print axioms Solidity.Proves.sound_of
#check @Solidity.ProvesC.fmlValid
#print axioms Solidity.ProvesC.fmlValid
#check @Solidity.Evm.Sim.init
#print axioms Solidity.Evm.Sim.init
#check @Solidity.Main.ValidUnder
#print axioms Solidity.Main.ValidUnder
#check @Solidity.Main.Derives
#print axioms Solidity.Main.Derives
#check @Solidity.Main.DerivesK
#print axioms Solidity.Main.DerivesK
#check @Solidity.Main.Rewrites
#print axioms Solidity.Main.Rewrites
#check @Solidity.Main.RewritesK
#print axioms Solidity.Main.RewritesK
#check @Solidity.Main.DoesAs
#print axioms Solidity.Main.DoesAs
#check @Solidity.Main.Runs
#print axioms Solidity.Main.Runs
#check @Solidity.Main.MRuns
#print axioms Solidity.Main.MRuns
#check @Solidity.Main.MReverts
#print axioms Solidity.Main.MReverts
#check @Solidity.Main.Compiles
#print axioms Solidity.Main.Compiles
#check @Solidity.Main.Represents
#print axioms Solidity.Main.Represents
#check @Solidity.Evm.Frag
#print axioms Solidity.Evm.Frag
#check @Solidity.Evm.inFrag
#print axioms Solidity.Evm.inFrag
#check @Solidity.Evm.inFragP
#print axioms Solidity.Evm.inFragP
#check @Solidity.Evm.SimL
#print axioms Solidity.Evm.SimL
#check @Solidity.Evm.Sim
#print axioms Solidity.Evm.Sim
#check @Solidity.Evm.ReprV
#print axioms Solidity.Evm.ReprV
#check @Solidity.Evm.ReprAt
#print axioms Solidity.Evm.ReprAt
#check @Solidity.Evm.ReprStore
#print axioms Solidity.Evm.ReprStore
#check @Solidity.Evm.PathAt
#print axioms Solidity.Evm.PathAt
#check @Solidity.Evm.PathSlot
#print axioms Solidity.Evm.PathSlot
#check @Solidity.Evm.EnvSim
#print axioms Solidity.Evm.EnvSim
#check @Solidity.Evm.Compiler.Compilation.Input
#print axioms Solidity.Evm.Compiler.Compilation.Input
#check @Solidity.Evm.Compiler.Compilation.Rep
#print axioms Solidity.Evm.Compiler.Compilation.Rep
#check @Solidity.Evm.Compiler.Compilation.Agrees
#print axioms Solidity.Evm.Compiler.Compilation.Agrees
#check @Solidity.Premise.Sound
#print axioms Solidity.Premise.Sound
#check @Solidity.Stmt.Sound
#print axioms Solidity.Stmt.Sound
#check @Solidity.Premise.fml
#print axioms Solidity.Premise.fml
#check @Solidity.Modality.forallB
#print axioms Solidity.Modality.forallB
#check @Solidity.Hyps.wrap
#print axioms Solidity.Hyps.wrap
#check @Solidity.RuleSet.admits
#print axioms Solidity.RuleSet.admits
#check @Solidity.holds
#print axioms Solidity.holds
#check @Solidity.Modality.afterRunTR
#print axioms Solidity.Modality.afterRunTR
#check @Solidity.Fml.Valid
#print axioms Solidity.Fml.Valid
#check @Solidity.Spec.sat
#print axioms Solidity.Spec.sat
#check @Solidity.Spec.Valid
#print axioms Solidity.Spec.Valid
#check @Solidity.Spec.toFml
#print axioms Solidity.Spec.toFml
#check @Solidity.Spec.satC
#print axioms Solidity.Spec.satC
#check @Solidity.Spec.ValidC
#print axioms Solidity.Spec.ValidC
#check @Solidity.Fml.stateInv
#print axioms Solidity.Fml.stateInv
#check @Solidity.COut.thenF
#print axioms Solidity.COut.thenF
#check @Solidity.holdsC
#print axioms Solidity.holdsC
#check @Solidity.Invariant
#print axioms Solidity.Invariant
#check @Solidity.ValidC
#print axioms Solidity.ValidC
#check @Solidity.StateInv
#print axioms Solidity.StateInv
#check @Solidity.Stmt.callsBack
#print axioms Solidity.Stmt.callsBack
#check @Solidity.Prog.callsBack
#print axioms Solidity.Prog.callsBack
#check @Solidity.Frames.callsBack
#print axioms Solidity.Frames.callsBack
#check @Solidity.Fml.callsBack
#print axioms Solidity.Fml.callsBack
#check @Solidity.COut.after
#print axioms Solidity.COut.after
#check @Solidity.Fml.FO
#print axioms Solidity.Fml.FO
#check @Solidity.Stmt.inSolkey
#print axioms Solidity.Stmt.inSolkey
#check @Solidity.Fml.inSolkey
#print axioms Solidity.Fml.inSolkey
#check @Solidity.ValidTail
#print axioms Solidity.ValidTail
#check @Solidity.ordinaryDefaultFold
#print axioms Solidity.ordinaryDefaultFold
#check @Solidity.SVal.OrdinaryDefault
#print axioms Solidity.SVal.OrdinaryDefault
#check @Solidity.SFields.OrdinaryDefault
#print axioms Solidity.SFields.OrdinaryDefault
#check @Solidity.SList.OrdinaryDefault
#print axioms Solidity.SList.OrdinaryDefault
#check @Solidity.SVec.OrdinaryDefault
#print axioms Solidity.SVec.OrdinaryDefault
#check @Solidity.cleanTailH
#print axioms Solidity.cleanTailH
#check @Solidity.SVal.CleanTail
#print axioms Solidity.SVal.CleanTail
#check @Solidity.SFields.CleanTail
#print axioms Solidity.SFields.CleanTail
#check @Solidity.Storage.CleanTail
#print axioms Solidity.Storage.CleanTail
#check @Solidity.Modality.onTHalt
#print axioms Solidity.Modality.onTHalt
#check @Solidity.Modality.onHalt
#print axioms Solidity.Modality.onHalt
#check @Solidity.Evm.Memory.PointerRepr
#print axioms Solidity.Evm.Memory.PointerRepr
#check @Solidity.Evm.Memory.StateRepr
#print axioms Solidity.Evm.Memory.StateRepr
#check @Solidity.Evm.Memory.ArrayRepr
#print axioms Solidity.Evm.Memory.ArrayRepr
#check @Solidity.Evm.Memory.HeapRepr
#print axioms Solidity.Evm.Memory.HeapRepr
#check @Solidity.Evm.Memory.StructRepr
#print axioms Solidity.Evm.Memory.StructRepr
#check @Solidity.Evm.Memory.StructHeapRepr
#print axioms Solidity.Evm.Memory.StructHeapRepr
#check @Solidity.Evm.Memory.StructArraySeparated
#print axioms Solidity.Evm.Memory.StructArraySeparated
#check @Solidity.Evm.Memory.RefFieldsRepr
#print axioms Solidity.Evm.Memory.RefFieldsRepr
#check @Solidity.Evm.Memory.FreeMemory
#print axioms Solidity.Evm.Memory.FreeMemory
#check @Solidity.Evm.Memory.AllocatorRepr
#print axioms Solidity.Evm.Memory.AllocatorRepr
#check @Solidity.Evm.Memory.StructAllocatorRepr
#print axioms Solidity.Evm.Memory.StructAllocatorRepr
#check @Solidity.Evm.Memory.Objects.ValueRepr
#print axioms Solidity.Evm.Memory.Objects.ValueRepr
#check @Solidity.Evm.Memory.Objects.header
#print axioms Solidity.Evm.Memory.Objects.header
#check @Solidity.Evm.Memory.Objects.cells
#print axioms Solidity.Evm.Memory.Objects.cells
#check @Solidity.Evm.Memory.Objects.Ownership
#print axioms Solidity.Evm.Memory.Objects.Ownership
#check @Solidity.Evm.Memory.Objects.ArrayRepr
#print axioms Solidity.Evm.Memory.Objects.ArrayRepr
#check @Solidity.Evm.Memory.Objects.HeapRepr
#print axioms Solidity.Evm.Memory.Objects.HeapRepr
#check @Solidity.Evm.Memory.Objects.StateRepr
#print axioms Solidity.Evm.Memory.Objects.StateRepr
#check @Solidity.Evm.Memory.Objects.AllocatorRepr
#print axioms Solidity.Evm.Memory.Objects.AllocatorRepr
#check @Solidity.Evm.Memory.Objects.AllocationInput
#print axioms Solidity.Evm.Memory.Objects.AllocationInput
#check @Solidity.Evm.Memory.Objects.GrowsAllocator
#print axioms Solidity.Evm.Memory.Objects.GrowsAllocator
#check @Solidity.Evm.Memory.Objects.KeepsAllocator
#print axioms Solidity.Evm.Memory.Objects.KeepsAllocator
#check @Solidity.Evm.Memory.BaseExtends
#print axioms Solidity.Evm.Memory.BaseExtends
#check @Solidity.Evm.Memory.GrowsAllocator
#print axioms Solidity.Evm.Memory.GrowsAllocator
#check @Solidity.Evm.Memory.AllocationInput
#print axioms Solidity.Evm.Memory.AllocationInput
#check @Solidity.Evm.Memory.RefArrayRepr
#print axioms Solidity.Evm.Memory.RefArrayRepr
#check @Solidity.Evm.Memory.RefArrayHeapRepr
#print axioms Solidity.Evm.Memory.RefArrayHeapRepr
#check @Solidity.Evm.Memory.RefArrayStateRepr
#print axioms Solidity.Evm.Memory.RefArrayStateRepr
#check @Solidity.Evm.Memory.FixedArrayRepr
#print axioms Solidity.Evm.Memory.FixedArrayRepr
#check @Solidity.Evm.Memory.FixedHeapRepr
#print axioms Solidity.Evm.Memory.FixedHeapRepr
#check @Solidity.Evm.Memory.FixedStateRepr
#print axioms Solidity.Evm.Memory.FixedStateRepr
#check @Solidity.Evm.Memory.Loops.StmtCert.Cost
#print axioms Solidity.Evm.Memory.Loops.StmtCert.Cost
#check @Solidity.Evm.Memory.Loops.Cost
#print axioms Solidity.Evm.Memory.Loops.Cost
#check @Solidity.Evm.Memory.Loops.StmtCert.Demand
#print axioms Solidity.Evm.Memory.Loops.StmtCert.Demand
#check @Solidity.Evm.Memory.Loops.Demand
#print axioms Solidity.Evm.Memory.Loops.Demand
#check @Solidity.Evm.Memory.Loops.Room
#print axioms Solidity.Evm.Memory.Loops.Room
#check @Solidity.Evm.Memory.LoopScopes.StmtCost
#print axioms Solidity.Evm.Memory.LoopScopes.StmtCost
#check @Solidity.Evm.Memory.LoopScopes.Cost
#print axioms Solidity.Evm.Memory.LoopScopes.Cost
#check @Solidity.Evm.Memory.LoopScopes.StmtDemand
#print axioms Solidity.Evm.Memory.LoopScopes.StmtDemand
#check @Solidity.Evm.Memory.LoopScopes.Demand
#print axioms Solidity.Evm.Memory.LoopScopes.Demand
#check @Solidity.Evm.Memory.LoopScopes.Room
#print axioms Solidity.Evm.Memory.LoopScopes.Room
#check @Solidity.Evm.Memory.frameNeedProg
#print axioms Solidity.Evm.Memory.frameNeedProg
#check @Solidity.Evm.Memory.allocationCostProg
#print axioms Solidity.Evm.Memory.allocationCostProg
#check @Solidity.Evm.Memory.Construction.allocationCostProg
#print axioms Solidity.Evm.Memory.Construction.allocationCostProg
#check @Solidity.Evm.Memory.StorageCopy.allocationCostProg
#print axioms Solidity.Evm.Memory.StorageCopy.allocationCostProg
#check @Solidity.Evm.Memory.copyBoundProg
#print axioms Solidity.Evm.Memory.copyBoundProg
#check @Solidity.Held.OK
#print axioms Solidity.Held.OK
#check @Solidity.Upd.Lands
#print axioms Solidity.Upd.Lands
#check @Solidity.Upd.afterT
#print axioms Solidity.Upd.afterT
#check @Solidity.StateInv.at
#print axioms Solidity.StateInv.at
#check @Solidity.ExecF
#print axioms Solidity.ExecF
#check @Solidity.Fml.hasTransfer
#print axioms Solidity.Fml.hasTransfer
#check @Solidity.Frames.hasTransfer
#print axioms Solidity.Frames.hasTransfer
#check @Solidity.Stmt.forksIn
#print axioms Solidity.Stmt.forksIn
#check @Solidity.Stmt.hasTransfer
#print axioms Solidity.Stmt.hasTransfer
#check @Solidity.Prog.hasTransfer
#print axioms Solidity.Prog.hasTransfer
#check @Solidity.Hyps.boxOnly
#print axioms Solidity.Hyps.boxOnly
#check @Solidity.Fml.modalFree
#print axioms Solidity.Fml.modalFree
#check @Solidity.Stmt.keyStep
#print axioms Solidity.Stmt.keyStep
#check @Solidity.Evm.Memory.LoopPrefix
#print axioms Solidity.Evm.Memory.LoopPrefix
#check @Solidity.Evm.Memory.LoopRoom
#print axioms Solidity.Evm.Memory.LoopRoom
#check @Solidity.Evm.Compiler.Compilation
#print axioms Solidity.Evm.Compiler.Compilation
#check @Solidity.Evm.Memory.CompiledProg
#print axioms Solidity.Evm.Memory.CompiledProg
#check @Solidity.Evm.Memory.ReferenceArrays.CompiledProg
#print axioms Solidity.Evm.Memory.ReferenceArrays.CompiledProg
#check @Solidity.Evm.Memory.Objects.CompiledProg
#print axioms Solidity.Evm.Memory.Objects.CompiledProg
#check @Solidity.Evm.Memory.Construction.CompiledProg
#print axioms Solidity.Evm.Memory.Construction.CompiledProg
#check @Solidity.Evm.Memory.Loops.CompiledProg
#print axioms Solidity.Evm.Memory.Loops.CompiledProg
#check @Solidity.Evm.Memory.LoopScopes.CompiledProg
#print axioms Solidity.Evm.Memory.LoopScopes.CompiledProg
#check @Solidity.Evm.Memory.Calls.Program
#print axioms Solidity.Evm.Memory.Calls.Program
#check @Solidity.Evm.Memory.StorageCopy.CompiledProg
#print axioms Solidity.Evm.Memory.StorageCopy.CompiledProg
#check @Solidity.Evm.Memory.Fixed.CompiledProg
#print axioms Solidity.Evm.Memory.Fixed.CompiledProg
#check @Solidity.Evm.Memory.CopyConstruction.CompiledProg
#print axioms Solidity.Evm.Memory.CopyConstruction.CompiledProg
#check @Solidity.Assurance.NonVacuityH28.construction_allocator_growth
#print axioms Solidity.Assurance.NonVacuityH28.construction_allocator_growth
#check @Solidity.Assurance.NonVacuityH28.primitive_allocator_growth
#print axioms Solidity.Assurance.NonVacuityH28.primitive_allocator_growth
#check @Solidity.Assurance.NonVacuityH28.construction_cursor_observation
#print axioms Solidity.Assurance.NonVacuityH28.construction_cursor_observation
#check @Solidity.Assurance.NonVacuityH28.construction_cursor_erasure_rejected
#print axioms Solidity.Assurance.NonVacuityH28.construction_cursor_erasure_rejected
#check @Solidity.Assurance.NonVacuityH28.assertion_runs
#print axioms Solidity.Assurance.NonVacuityH28.assertion_runs
#check @Solidity.Assurance.NonVacuityH28.assertion_derivation
#print axioms Solidity.Assurance.NonVacuityH28.assertion_derivation
#check @Solidity.Assurance.NonVacuityH28.calculus_application
#print axioms Solidity.Assurance.NonVacuityH28.calculus_application
#check @Solidity.Assurance.NonVacuityH28.direct_application
#print axioms Solidity.Assurance.NonVacuityH28.direct_application
#check @Solidity.Assurance.NonVacuityH28.solkey_application
#print axioms Solidity.Assurance.NonVacuityH28.solkey_application
#check @Solidity.Assurance.NonVacuityH28.callback_application
#print axioms Solidity.Assurance.NonVacuityH28.callback_application
#check @Solidity.Assurance.NonVacuityH28.noCallback_application
#print axioms Solidity.Assurance.NonVacuityH28.noCallback_application
#check @Solidity.Assurance.NonVacuityH28.noCallback_equivalence
#print axioms Solidity.Assurance.NonVacuityH28.noCallback_equivalence
#check @Solidity.Assurance.NonVacuityH28.cleanTail_application
#print axioms Solidity.Assurance.NonVacuityH28.cleanTail_application
#check @Solidity.Assurance.NonVacuityH28.symex_application
#print axioms Solidity.Assurance.NonVacuityH28.symex_application
#check @Solidity.Assurance.NonVacuityH28.solkey_equivalence
#print axioms Solidity.Assurance.NonVacuityH28.solkey_equivalence
#check @Solidity.Assurance.NonVacuityH28.solkey_strict
#print axioms Solidity.Assurance.NonVacuityH28.solkey_strict
#check @Solidity.Assurance.NonVacuityH28.solkey_rule_application
#print axioms Solidity.Assurance.NonVacuityH28.solkey_rule_application
#check @Solidity.Assurance.NonVacuityH28.solkey_admission_application
#print axioms Solidity.Assurance.NonVacuityH28.solkey_admission_application
#check @Solidity.Assurance.NonVacuityH28.zero_unwind_strict
#print axioms Solidity.Assurance.NonVacuityH28.zero_unwind_strict
#check @Solidity.Assurance.NonVacuityH28.false_invariant_entry_rejected
#print axioms Solidity.Assurance.NonVacuityH28.false_invariant_entry_rejected
#check @Solidity.Assurance.NonVacuityH28.false_annotation_run
#print axioms Solidity.Assurance.NonVacuityH28.false_annotation_run
#check @Solidity.Assurance.NonVacuityH28.false_annotation_entry
#print axioms Solidity.Assurance.NonVacuityH28.false_annotation_entry
#check @Solidity.Assurance.NonVacuityH28.false_annotation_rule
#print axioms Solidity.Assurance.NonVacuityH28.false_annotation_rule
#check @Solidity.Assurance.NonVacuityH28.false_annotation_init_rejected
#print axioms Solidity.Assurance.NonVacuityH28.false_annotation_init_rejected
#check @Solidity.Assurance.NonVacuityH28.assertion_rule_semantics
#print axioms Solidity.Assurance.NonVacuityH28.assertion_rule_semantics
#check @Solidity.Assurance.NonVacuityH28.competing_assertion_rule_rejected
#print axioms Solidity.Assurance.NonVacuityH28.competing_assertion_rule_rejected
#check @Solidity.Assurance.NonVacuityH28.symex_actual_progress
#print axioms Solidity.Assurance.NonVacuityH28.symex_actual_progress
#check @Solidity.Assurance.NonVacuityH28.callback_nil_frame
#print axioms Solidity.Assurance.NonVacuityH28.callback_nil_frame
#check @Solidity.Assurance.NonVacuityH28.callback_seq_frame
#print axioms Solidity.Assurance.NonVacuityH28.callback_seq_frame
#check @Solidity.Assurance.NonVacuityH28.callback_halt_frame
#print axioms Solidity.Assurance.NonVacuityH28.callback_halt_frame
#check @Solidity.Assurance.NonVacuityH28.callback_violated_frame
#print axioms Solidity.Assurance.NonVacuityH28.callback_violated_frame
#check @Solidity.Assurance.NonVacuityH28.callback_pop_frame
#print axioms Solidity.Assurance.NonVacuityH28.callback_pop_frame
#check @Solidity.Assurance.NonVacuityH28.callback_drop_frame
#print axioms Solidity.Assurance.NonVacuityH28.callback_drop_frame
#check @Solidity.Assurance.NonVacuityH28.callback_frame_observation
#print axioms Solidity.Assurance.NonVacuityH28.callback_frame_observation
#check @Solidity.Assurance.NonVacuityH28.callback_violation
#print axioms Solidity.Assurance.NonVacuityH28.callback_violation
#check @Solidity.Assurance.NonVacuityH28.callback_resume
#print axioms Solidity.Assurance.NonVacuityH28.callback_resume
#check @Solidity.Assurance.NonVacuityH28.noCallback_transfer
#print axioms Solidity.Assurance.NonVacuityH28.noCallback_transfer
#check @Solidity.Assurance.NonVacuityH28.callback_revert
#print axioms Solidity.Assurance.NonVacuityH28.callback_revert
#check @Solidity.Assurance.NonVacuityH28.callback_observations
#print axioms Solidity.Assurance.NonVacuityH28.callback_observations
#check @Solidity.Assurance.NonVacuityH28.callback_observation_erasure_rejected
#print axioms Solidity.Assurance.NonVacuityH28.callback_observation_erasure_rejected
#check @Solidity.Assurance.NonVacuityH28.noCallback_unique
#print axioms Solidity.Assurance.NonVacuityH28.noCallback_unique
#check @Solidity.Assurance.NonVacuityH28.noCallback_excludes_resume
#print axioms Solidity.Assurance.NonVacuityH28.noCallback_excludes_resume
#check @Solidity.Assurance.NonVacuityH28.payment_derivation
#print axioms Solidity.Assurance.NonVacuityH28.payment_derivation
#check @Solidity.Assurance.NonVacuityH28.payment_headline
#print axioms Solidity.Assurance.NonVacuityH28.payment_headline
#check @Solidity.Assurance.NonVacuityH28.top_callback_policy
#print axioms Solidity.Assurance.NonVacuityH28.top_callback_policy
#check @Solidity.Assurance.NonVacuityH28.callback_program_resume
#print axioms Solidity.Assurance.NonVacuityH28.callback_program_resume
#check @Solidity.Assurance.NonVacuityH28.callback_program_noCallback
#print axioms Solidity.Assurance.NonVacuityH28.callback_program_noCallback
#check @Solidity.Assurance.NonVacuityH28.callback_program_revert
#print axioms Solidity.Assurance.NonVacuityH28.callback_program_revert
#check @Solidity.Assurance.NonVacuityH28.callback_program_violation
#print axioms Solidity.Assurance.NonVacuityH28.callback_program_violation
#check @Solidity.Assurance.NonVacuityH28.noCallback_payment_derivation
#print axioms Solidity.Assurance.NonVacuityH28.noCallback_payment_derivation
#check @Solidity.Assurance.NonVacuityH28.noCallback_payment_headline
#print axioms Solidity.Assurance.NonVacuityH28.noCallback_payment_headline
#check @Solidity.Assurance.NonVacuityH28.scalar_memory_source
#print axioms Solidity.Assurance.NonVacuityH28.scalar_memory_source
#check @Solidity.Assurance.NonVacuityH28.declare_memory_source
#print axioms Solidity.Assurance.NonVacuityH28.declare_memory_source
#check @Solidity.Assurance.NonVacuityH28.self_rebind_source
#print axioms Solidity.Assurance.NonVacuityH28.self_rebind_source
#check @Solidity.Assurance.NonVacuityH28.objects_supply_fixed
#print axioms Solidity.Assurance.NonVacuityH28.objects_supply_fixed
#check @Solidity.Assurance.NonVacuityH28.reference_array_input
#print axioms Solidity.Assurance.NonVacuityH28.reference_array_input
#check @Solidity.Assurance.NonVacuityH28.object_input
#print axioms Solidity.Assurance.NonVacuityH28.object_input
#check @Solidity.Assurance.NonVacuityH28.loop_input
#print axioms Solidity.Assurance.NonVacuityH28.loop_input
#check @Solidity.Assurance.NonVacuityH28.scope_input
#print axioms Solidity.Assurance.NonVacuityH28.scope_input
#check @Solidity.Assurance.NonVacuityH28.calls_input
#print axioms Solidity.Assurance.NonVacuityH28.calls_input
#check @Solidity.Assurance.NonVacuityH28.copy_input
#print axioms Solidity.Assurance.NonVacuityH28.copy_input
#check @Solidity.Assurance.NonVacuityH28.fixed_input
#print axioms Solidity.Assurance.NonVacuityH28.fixed_input
#check @Solidity.Assurance.NonVacuityH28.copy_construction_input
#print axioms Solidity.Assurance.NonVacuityH28.copy_construction_input
#check @Solidity.Assurance.NonVacuityH28.checked_families_joint
#print axioms Solidity.Assurance.NonVacuityH28.checked_families_joint
#check @Solidity.Assurance.NonVacuityH28.checked_success_after_source
#print axioms Solidity.Assurance.NonVacuityH28.checked_success_after_source
#check @Solidity.Assurance.NonVacuityH28.construction_input
#print axioms Solidity.Assurance.NonVacuityH28.construction_input
#check @Solidity.Assurance.NonVacuityH28.construction_joint
#print axioms Solidity.Assurance.NonVacuityH28.construction_joint
#check @Solidity.Assurance.NonVacuityH28.construction_live_pointer
#print axioms Solidity.Assurance.NonVacuityH28.construction_live_pointer
#check @Solidity.Assurance.NonVacuityH28.environment_simulation
#print axioms Solidity.Assurance.NonVacuityH28.environment_simulation
#check @Solidity.Assurance.NonVacuityH28.mismatched_timestamp
#print axioms Solidity.Assurance.NonVacuityH28.mismatched_timestamp
#check @Solidity.Assurance.NonVacuityH28.sender_source
#print axioms Solidity.Assurance.NonVacuityH28.sender_source
#check @Solidity.Assurance.NonVacuityH28.sender_target
#print axioms Solidity.Assurance.NonVacuityH28.sender_target
#check @Solidity.Assurance.NonVacuityH28.sender_fragment
#print axioms Solidity.Assurance.NonVacuityH28.sender_fragment
#check @Solidity.Assurance.NonVacuityH28.sender_representation
#print axioms Solidity.Assurance.NonVacuityH28.sender_representation
#check @Solidity.Assurance.NonVacuityH28.rule_family
#print axioms Solidity.Assurance.NonVacuityH28.rule_family
#check @Solidity.Assurance.NonVacuityH28.unique_family
#print axioms Solidity.Assurance.NonVacuityH28.unique_family
#check @Solidity.Assurance.NonVacuityH28.fragment_family
#print axioms Solidity.Assurance.NonVacuityH28.fragment_family
#check @Solidity.Assurance.NonVacuityH28.simulation_family
#print axioms Solidity.Assurance.NonVacuityH28.simulation_family
#check @Solidity.Assurance.NonVacuityH28.checked_family
#print axioms Solidity.Assurance.NonVacuityH28.checked_family
#check @Solidity.Assurance.NonVacuityH28.impossible_resource
#print axioms Solidity.Assurance.NonVacuityH28.impossible_resource
#check @Solidity.Assurance.NonVacuityH28.source_true
#print axioms Solidity.Assurance.NonVacuityH28.source_true
#check @Solidity.Assurance.NonVacuityH28.source_false
#print axioms Solidity.Assurance.NonVacuityH28.source_false
#check @Solidity.Assurance.NonVacuityH28.target_true
#print axioms Solidity.Assurance.NonVacuityH28.target_true
#check @Solidity.Assurance.NonVacuityH28.target_false
#print axioms Solidity.Assurance.NonVacuityH28.target_false
#check @Solidity.Assurance.NonVacuityH28.nonempty_program
#print axioms Solidity.Assurance.NonVacuityH28.nonempty_program
#check @Solidity.Assurance.NonVacuityH28.nonempty_code
#print axioms Solidity.Assurance.NonVacuityH28.nonempty_code
#check @Solidity.Assurance.NonVacuityH28.always_revert_rejected
#print axioms Solidity.Assurance.NonVacuityH28.always_revert_rejected
#check @Solidity.Assurance.NonVacuityH28.correct_success
#print axioms Solidity.Assurance.NonVacuityH28.correct_success
#check @Solidity.Assurance.NonVacuityH28.net_success
#print axioms Solidity.Assurance.NonVacuityH28.net_success
#check @Solidity.Assurance.NonVacuityH28.mismatched_funds
#print axioms Solidity.Assurance.NonVacuityH28.mismatched_funds
#check @Solidity.Assurance.NonVacuityH28.closed_simulation
#print axioms Solidity.Assurance.NonVacuityH28.closed_simulation
#check @Solidity.Assurance.NonVacuityH28.closed_joint_witness
#print axioms Solidity.Assurance.NonVacuityH28.closed_joint_witness
#check @Solidity.Assurance.NonVacuityH28.inhabited_fragment
#print axioms Solidity.Assurance.NonVacuityH28.inhabited_fragment
#check @Solidity.Assurance.NonVacuityH28.rule_step_family
#print axioms Solidity.Assurance.NonVacuityH28.rule_step_family
#check @Solidity.Assurance.NonVacuityH28.rule_from_step_family
#print axioms Solidity.Assurance.NonVacuityH28.rule_from_step_family
#check @Solidity.Assurance.NonVacuityH28.mismatched_oracle
#print axioms Solidity.Assurance.NonVacuityH28.mismatched_oracle
#check @Solidity.Assurance.NonVacuityH28.correct_revert
#print axioms Solidity.Assurance.NonVacuityH28.correct_revert
#check @Solidity.Assurance.NonVacuityH28.every_rule_inhabited
#print axioms Solidity.Assurance.NonVacuityH28.every_rule_inhabited
#check @Solidity.Assurance.NonVacuityH28.mismatched_self_ledger
#print axioms Solidity.Assurance.NonVacuityH28.mismatched_self_ledger
#check @Solidity.Assurance.NonVacuityH28.mismatched_external_ledger
#print axioms Solidity.Assurance.NonVacuityH28.mismatched_external_ledger
#check @Solidity.Assurance.NonVacuityH28.fragile_fragment
#print axioms Solidity.Assurance.NonVacuityH28.fragile_fragment
#check @Solidity.Assurance.NonVacuityH28.fragile_source
#print axioms Solidity.Assurance.NonVacuityH28.fragile_source
#check @Solidity.Assurance.NonVacuityH28.fragile_joint
#print axioms Solidity.Assurance.NonVacuityH28.fragile_joint
#check @Solidity.Assurance.NonVacuityH28.concrete_object_allocator_kept
#print axioms Solidity.Assurance.NonVacuityH28.concrete_object_allocator_kept
#check @Solidity.Assurance.NonVacuityH28.concrete_object_cursor_kept
#print axioms Solidity.Assurance.NonVacuityH28.concrete_object_cursor_kept
#check @Solidity.Assurance.NonVacuityH28.live_base_extension_queried
#print axioms Solidity.Assurance.NonVacuityH28.live_base_extension_queried
#check @Solidity.Assurance.NonVacuityH28.live_array_layout_queried
#print axioms Solidity.Assurance.NonVacuityH28.live_array_layout_queried
#check @Solidity.Assurance.NonVacuityH28.allocated_single_object
#print axioms Solidity.Assurance.NonVacuityH28.allocated_single_object
#check @Solidity.Assurance.NonVacuityH28.primitive_source_observations
#print axioms Solidity.Assurance.NonVacuityH28.primitive_source_observations
#check @Solidity.Assurance.NonVacuityH28.distinct_object_domain_empty
#print axioms Solidity.Assurance.NonVacuityH28.distinct_object_domain_empty
#check @Solidity.Assurance.NonVacuityH28.payment_entry_identification
#print axioms Solidity.Assurance.NonVacuityH28.payment_entry_identification
#check @Solidity.Assurance.NonVacuityH28.joint_payment_world
#print axioms Solidity.Assurance.NonVacuityH28.joint_payment_world
#check @Solidity.Assurance.NonVacuityH28.joint_payment_compiler_application
#print axioms Solidity.Assurance.NonVacuityH28.joint_payment_compiler_application
#check @Solidity.Assurance.NonVacuityH28.represented_success
#print axioms Solidity.Assurance.NonVacuityH28.represented_success
#check @Solidity.Assurance.NonVacuityH28.value_fragment
#print axioms Solidity.Assurance.NonVacuityH28.value_fragment
#check @Solidity.Assurance.NonVacuityH28.value_source
#print axioms Solidity.Assurance.NonVacuityH28.value_source
#check @Solidity.Assurance.NonVacuityH28.value_target
#print axioms Solidity.Assurance.NonVacuityH28.value_target
#check @Solidity.Assurance.NonVacuityH28.value_representation
#print axioms Solidity.Assurance.NonVacuityH28.value_representation
#check @Solidity.Assurance.NonVacuityH28.value_field
#print axioms Solidity.Assurance.NonVacuityH28.value_field
#check @Solidity.Assurance.NonVacuityH28.alias_fragment
#print axioms Solidity.Assurance.NonVacuityH28.alias_fragment
#check @Solidity.Assurance.NonVacuityH28.alias_source
#print axioms Solidity.Assurance.NonVacuityH28.alias_source
#check @Solidity.Assurance.NonVacuityH28.alias_target
#print axioms Solidity.Assurance.NonVacuityH28.alias_target
#check @Solidity.Assurance.NonVacuityH28.alias_representation
#print axioms Solidity.Assurance.NonVacuityH28.alias_representation
#check @Solidity.Assurance.NonVacuityH28.alias_field
#print axioms Solidity.Assurance.NonVacuityH28.alias_field
#check @Solidity.Assurance.NonVacuityH28.payment_syntax_gates
#print axioms Solidity.Assurance.NonVacuityH28.payment_syntax_gates
#check @Solidity.Assurance.NonVacuityH28.frame_callback_gates
#print axioms Solidity.Assurance.NonVacuityH28.frame_callback_gates
#check @Solidity.Assurance.NonVacuityH28.calculus_context_gates
#print axioms Solidity.Assurance.NonVacuityH28.calculus_context_gates
#check @Solidity.Assurance.NonVacuityH28.universal_binder_control
#print axioms Solidity.Assurance.NonVacuityH28.universal_binder_control
#check @Solidity.Assurance.NonVacuityH28.halt_gate_domains
#print axioms Solidity.Assurance.NonVacuityH28.halt_gate_domains
#check @Solidity.Assurance.NonVacuityH28.scalar_loop_demand
#print axioms Solidity.Assurance.NonVacuityH28.scalar_loop_demand
#check @Solidity.Assurance.NonVacuityH28.scalar_loop_cost
#print axioms Solidity.Assurance.NonVacuityH28.scalar_loop_cost
#check @Solidity.Assurance.NonVacuityH28.scalar_scope_demand
#print axioms Solidity.Assurance.NonVacuityH28.scalar_scope_demand
#check @Solidity.Assurance.NonVacuityH28.scalar_scope_cost
#print axioms Solidity.Assurance.NonVacuityH28.scalar_scope_cost
#check @Solidity.Assurance.NonVacuityH28.false_loop_stmt_source
#print axioms Solidity.Assurance.NonVacuityH28.false_loop_stmt_source
#check @Solidity.Assurance.NonVacuityH28.skipped_loop_source
#print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_source
#check @Solidity.Assurance.NonVacuityH28.skipped_body_reverts
#print axioms Solidity.Assurance.NonVacuityH28.skipped_body_reverts
#check @Solidity.Assurance.NonVacuityH28.skipped_loop_input
#print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_input
#check @Solidity.Assurance.NonVacuityH28.skipped_loop_code_nonempty
#print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_code_nonempty
#check @Solidity.Assurance.NonVacuityH28.zero_condition_target
#print axioms Solidity.Assurance.NonVacuityH28.zero_condition_target
#check @Solidity.Assurance.NonVacuityH28.skipped_loop_target
#print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_target
#check @Solidity.Assurance.NonVacuityH28.skipped_loop_demand
#print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_demand
#check @Solidity.Assurance.NonVacuityH28.skipped_loop_cost
#print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_cost
#check @Solidity.Assurance.NonVacuityH28.skipped_loop_checked
#print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_checked
#check @Solidity.Assurance.NonVacuityH28.skipped_loop_joint
#print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_joint
#check @Solidity.Assurance.NonVacuityH28.skipped_loop_joint_layout
#print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_joint_layout
#check @Solidity.Assurance.NonVacuityH28.entered_revert_source
#print axioms Solidity.Assurance.NonVacuityH28.entered_revert_source
#check @Solidity.Assurance.NonVacuityH28.entered_revert_target
#print axioms Solidity.Assurance.NonVacuityH28.entered_revert_target
#check @Solidity.Assurance.NonVacuityH28.entered_revert_input
#print axioms Solidity.Assurance.NonVacuityH28.entered_revert_input
#check @Solidity.Assurance.NonVacuityH28.entered_revert_demand
#print axioms Solidity.Assurance.NonVacuityH28.entered_revert_demand
#check @Solidity.Assurance.NonVacuityH28.entered_revert_joint
#print axioms Solidity.Assurance.NonVacuityH28.entered_revert_joint
#check @Solidity.Assurance.NonVacuityH28.near_end_state
#print axioms Solidity.Assurance.NonVacuityH28.near_end_state
#check @Solidity.Assurance.NonVacuityH28.near_end_allocator
#print axioms Solidity.Assurance.NonVacuityH28.near_end_allocator
#check @Solidity.Assurance.NonVacuityH28.near_end_allocation_rejected
#print axioms Solidity.Assurance.NonVacuityH28.near_end_allocation_rejected
#check @Solidity.Assurance.NonVacuityH28.pointer_erasure_rejected
#print axioms Solidity.Assurance.NonVacuityH28.pointer_erasure_rejected
#check @Solidity.Assurance.NonVacuityH28.allocated_erasure_countercontrol
#print axioms Solidity.Assurance.NonVacuityH28.allocated_erasure_countercontrol
#check @Solidity.Assurance.NonVacuityH28.empty_object_heap
#print axioms Solidity.Assurance.NonVacuityH28.empty_object_heap
#check @Solidity.Assurance.NonVacuityH28.fresh_object_state
#print axioms Solidity.Assurance.NonVacuityH28.fresh_object_state
#check @Solidity.Assurance.NonVacuityH28.fresh_free_memory
#print axioms Solidity.Assurance.NonVacuityH28.fresh_free_memory
#check @Solidity.Assurance.NonVacuityH28.fresh_object_allocator
#print axioms Solidity.Assurance.NonVacuityH28.fresh_object_allocator
#check @Solidity.Assurance.NonVacuityH28.primitive_input
#print axioms Solidity.Assurance.NonVacuityH28.primitive_input
#check @Solidity.Assurance.NonVacuityH28.primitive_source_eq
#print axioms Solidity.Assurance.NonVacuityH28.primitive_source_eq
#check @Solidity.Assurance.NonVacuityH28.primitive_pointer
#print axioms Solidity.Assurance.NonVacuityH28.primitive_pointer
#check @Solidity.Assurance.NonVacuityH28.primitive_source
#print axioms Solidity.Assurance.NonVacuityH28.primitive_source
#check @Solidity.Assurance.NonVacuityH28.primitive_checked
#print axioms Solidity.Assurance.NonVacuityH28.primitive_checked
#check @Solidity.Assurance.NonVacuityH28.primitive_joint
#print axioms Solidity.Assurance.NonVacuityH28.primitive_joint
#check @Solidity.Assurance.NonVacuityH28.original_arms_input
#print axioms Solidity.Assurance.NonVacuityH28.original_arms_input
#check @Solidity.Assurance.NonVacuityH28.original_calculus_induction
#print axioms Solidity.Assurance.NonVacuityH28.original_calculus_induction
#check @Solidity.Assurance.NonVacuityH28.original_callback_formula
#print axioms Solidity.Assurance.NonVacuityH28.original_callback_formula
#check @Solidity.Assurance.NonVacuityH28.original_noCallback_formula
#print axioms Solidity.Assurance.NonVacuityH28.original_noCallback_formula
#check @Solidity.Assurance.NonVacuityH28.original_invariant_inputs
#print axioms Solidity.Assurance.NonVacuityH28.original_invariant_inputs
#check @Solidity.Assurance.NonVacuityH28.original_clean_tail
#print axioms Solidity.Assurance.NonVacuityH28.original_clean_tail
#check @Solidity.Assurance.NonVacuityH28.empty_fragment_acceptance_rejected
#print axioms Solidity.Assurance.NonVacuityH28.empty_fragment_acceptance_rejected
#check @Solidity.Assurance.NonVacuityH28.panic_source
#print axioms Solidity.Assurance.NonVacuityH28.panic_source
#check @Solidity.Assurance.NonVacuityH28.panic_target
#print axioms Solidity.Assurance.NonVacuityH28.panic_target
#check @Solidity.Assurance.NonVacuityH28.panic_fragment
#print axioms Solidity.Assurance.NonVacuityH28.panic_fragment
#check @Solidity.Assurance.NonVacuityH28.compiler_panic_application
#print axioms Solidity.Assurance.NonVacuityH28.compiler_panic_application
#check @Solidity.Assurance.NonVacuityH28.payment_fragment
#print axioms Solidity.Assurance.NonVacuityH28.payment_fragment
#check @Solidity.Assurance.NonVacuityH28.payment_simulation
#print axioms Solidity.Assurance.NonVacuityH28.payment_simulation
#check @Solidity.Assurance.NonVacuityH28.payment_source
#print axioms Solidity.Assurance.NonVacuityH28.payment_source
#check @Solidity.Assurance.NonVacuityH28.payment_target
#print axioms Solidity.Assurance.NonVacuityH28.payment_target
#check @Solidity.Assurance.NonVacuityH28.payment_observations
#print axioms Solidity.Assurance.NonVacuityH28.payment_observations
#check @Solidity.Assurance.NonVacuityH28.payment_net_application
#print axioms Solidity.Assurance.NonVacuityH28.payment_net_application
#check @Solidity.Assurance.NonVacuityH28.payment_checked_application
#print axioms Solidity.Assurance.NonVacuityH28.payment_checked_application
#check @Solidity.Assurance.NonVacuityH28.poor_payment_source
#print axioms Solidity.Assurance.NonVacuityH28.poor_payment_source
#check @Solidity.Assurance.NonVacuityH28.poor_payment_target
#print axioms Solidity.Assurance.NonVacuityH28.poor_payment_target
#check @Solidity.Assurance.NonVacuityH28.refused_simulation
#print axioms Solidity.Assurance.NonVacuityH28.refused_simulation
#check @Solidity.Assurance.NonVacuityH28.refused_source
#print axioms Solidity.Assurance.NonVacuityH28.refused_source
#check @Solidity.Assurance.NonVacuityH28.refused_target
#print axioms Solidity.Assurance.NonVacuityH28.refused_target
#check @Solidity.Assurance.NonVacuityH28.refused_checked_application
#print axioms Solidity.Assurance.NonVacuityH28.refused_checked_application
#check @Solidity.Assurance.NonVacuityH28.identity_loop_diverges
#print axioms Solidity.Assurance.NonVacuityH28.identity_loop_diverges
#check @Solidity.Assurance.NonVacuityH28.divergence_source
#print axioms Solidity.Assurance.NonVacuityH28.divergence_source
#check @Solidity.Assurance.NonVacuityH28.machine_loop_diverges
#print axioms Solidity.Assurance.NonVacuityH28.machine_loop_diverges
#check @Solidity.Assurance.NonVacuityH28.divergence_target
#print axioms Solidity.Assurance.NonVacuityH28.divergence_target
#check @Solidity.Assurance.NonVacuityH28.divergence_fragment
#print axioms Solidity.Assurance.NonVacuityH28.divergence_fragment
#check @Solidity.Assurance.NonVacuityH28.compiler_divergence_application
#print axioms Solidity.Assurance.NonVacuityH28.compiler_divergence_application
#check @Solidity.Assurance.NonVacuityH28.unset_alias_not_ok
#print axioms Solidity.Assurance.NonVacuityH28.unset_alias_not_ok
#check @Solidity.Assurance.NonVacuityH28.dead_alias_simulation
#print axioms Solidity.Assurance.NonVacuityH28.dead_alias_simulation
#check @Solidity.Assurance.NonVacuityH28.dead_alias_fragment_rejected
#print axioms Solidity.Assurance.NonVacuityH28.dead_alias_fragment_rejected
#check @Solidity.Assurance.NonVacuityH28.dead_alias_source_reverts
#print axioms Solidity.Assurance.NonVacuityH28.dead_alias_source_reverts
#check @Solidity.Assurance.NonVacuityH28.dead_alias_target_faults
#print axioms Solidity.Assurance.NonVacuityH28.dead_alias_target_faults
#check @Solidity.Assurance.NonVacuityH28.unset_memory_core_simulation
#print axioms Solidity.Assurance.NonVacuityH28.unset_memory_core_simulation
#check @Solidity.Assurance.NonVacuityH28.unset_memory_pointer_rejected
#print axioms Solidity.Assurance.NonVacuityH28.unset_memory_pointer_rejected
#check @Solidity.Assurance.NonVacuityH28.primitive_value_fragment
#print axioms Solidity.Assurance.NonVacuityH28.primitive_value_fragment
#check @Solidity.Assurance.NonVacuityH28.primitive_value_source
#print axioms Solidity.Assurance.NonVacuityH28.primitive_value_source
#check @Solidity.Assurance.NonVacuityH28.primitive_value_target
#print axioms Solidity.Assurance.NonVacuityH28.primitive_value_target
#check @Solidity.Assurance.NonVacuityH28.all_primitive_values_represented
#print axioms Solidity.Assurance.NonVacuityH28.all_primitive_values_represented
#check @Solidity.Assurance.NonVacuityH28.all_primitive_value_fields
#print axioms Solidity.Assurance.NonVacuityH28.all_primitive_value_fields
#check @Solidity.Assurance.NonVacuityH28.negative_int_word
#print axioms Solidity.Assurance.NonVacuityH28.negative_int_word
#check @Solidity.Assurance.NonVacuityH28.negative_int_observation_not_erased
#print axioms Solidity.Assurance.NonVacuityH28.negative_int_observation_not_erased
#check @Solidity.Assurance.NonVacuityH28.flag_step
#print axioms Solidity.Assurance.NonVacuityH28.flag_step
#check @Solidity.Assurance.NonVacuityH28.flag_lands
#print axioms Solidity.Assurance.NonVacuityH28.flag_lands
#check @Solidity.Assurance.NonVacuityH28.flag_source
#print axioms Solidity.Assurance.NonVacuityH28.flag_source
#check @Solidity.Assurance.NonVacuityH28.flag_changed
#print axioms Solidity.Assurance.NonVacuityH28.flag_changed
#check @Solidity.Assurance.NonVacuityH28.flag_update_antecedent
#print axioms Solidity.Assurance.NonVacuityH28.flag_update_antecedent
#check @Solidity.Assurance.NonVacuityH28.flag_rule_application
#print axioms Solidity.Assurance.NonVacuityH28.flag_rule_application
#check @Solidity.Assurance.NonVacuityH28.flag_require_source_true
#print axioms Solidity.Assurance.NonVacuityH28.flag_require_source_true
#check @Solidity.Assurance.NonVacuityH28.flag_require_source_false
#print axioms Solidity.Assurance.NonVacuityH28.flag_require_source_false
#check @Solidity.Assurance.NonVacuityH28.flag_split_antecedent
#print axioms Solidity.Assurance.NonVacuityH28.flag_split_antecedent
#check @Solidity.Assurance.NonVacuityH28.flag_split_application
#print axioms Solidity.Assurance.NonVacuityH28.flag_split_application
#check @Solidity.Assurance.NonVacuityH28.flag_binding_step
#print axioms Solidity.Assurance.NonVacuityH28.flag_binding_step
#check @Solidity.Assurance.NonVacuityH28.flag_binding_antecedent
#print axioms Solidity.Assurance.NonVacuityH28.flag_binding_antecedent
#check @Solidity.Assurance.NonVacuityH28.flag_binding_source
#print axioms Solidity.Assurance.NonVacuityH28.flag_binding_source
#check @Solidity.Assurance.NonVacuityH28.flag_binding_application
#print axioms Solidity.Assurance.NonVacuityH28.flag_binding_application
#check @Solidity.Assurance.NonVacuityH28.revert_done_true
#print axioms Solidity.Assurance.NonVacuityH28.revert_done_true
#check @Solidity.Assurance.NonVacuityH28.revert_rule_application
#print axioms Solidity.Assurance.NonVacuityH28.revert_rule_application
#check @Solidity.Assurance.NonVacuityH28.write_fragment
#print axioms Solidity.Assurance.NonVacuityH28.write_fragment
#check @Solidity.Assurance.NonVacuityH28.write_source
#print axioms Solidity.Assurance.NonVacuityH28.write_source
#check @Solidity.Assurance.NonVacuityH28.write_target
#print axioms Solidity.Assurance.NonVacuityH28.write_target
#check @Solidity.Assurance.NonVacuityH28.changed_observation
#print axioms Solidity.Assurance.NonVacuityH28.changed_observation
#check @Solidity.Assurance.NonVacuityH28.storage_observation_erasure_rejected
#print axioms Solidity.Assurance.NonVacuityH28.storage_observation_erasure_rejected
#check @Solidity.Assurance.NonVacuityH28.write_compiler_application
#print axioms Solidity.Assurance.NonVacuityH28.write_compiler_application
#check @Solidity.Assurance.NonVacuityH28.tail_clean_valid
#print axioms Solidity.Assurance.NonVacuityH28.tail_clean_valid
#check @Solidity.Assurance.NonVacuityH28.tail_clean_status
#print axioms Solidity.Assurance.NonVacuityH28.tail_clean_status
#check @Solidity.Assurance.NonVacuityH28.tail_clean_source
#print axioms Solidity.Assurance.NonVacuityH28.tail_clean_source
#check @Solidity.Assurance.NonVacuityH28.tail_clean_main
#print axioms Solidity.Assurance.NonVacuityH28.tail_clean_main
#check @Solidity.Assurance.NonVacuityH28.dirty_tail_reachable
#print axioms Solidity.Assurance.NonVacuityH28.dirty_tail_reachable
#check @Solidity.Assurance.NonVacuityH28.dirty_tail_not_clean
#print axioms Solidity.Assurance.NonVacuityH28.dirty_tail_not_clean
#check @Solidity.Assurance.NonVacuityH28.tail_dirty_status
#print axioms Solidity.Assurance.NonVacuityH28.tail_dirty_status
#check @Solidity.Assurance.NonVacuityH28.tail_dirty_source
#print axioms Solidity.Assurance.NonVacuityH28.tail_dirty_source
#check @Solidity.Assurance.NonVacuityH28.tail_dirty_frames_panic
#print axioms Solidity.Assurance.NonVacuityH28.tail_dirty_frames_panic
#check @Solidity.Assurance.NonVacuityH28.tail_premise_cannot_be_erased
#print axioms Solidity.Assurance.NonVacuityH28.tail_premise_cannot_be_erased
#check @Solidity.Assurance.NonVacuityH28.done_false_antecedent_rejected
#print axioms Solidity.Assurance.NonVacuityH28.done_false_antecedent_rejected
#check @Solidity.Assurance.NonVacuityH28.empty_goal_guard_rejected
#print axioms Solidity.Assurance.NonVacuityH28.empty_goal_guard_rejected
#check @Solidity.Assurance.NonVacuityH28.empty_cases_guard_rejected
#print axioms Solidity.Assurance.NonVacuityH28.empty_cases_guard_rejected
#check @Solidity.Assurance.NonVacuityH28.callback_false_derivation_rejected
#print axioms Solidity.Assurance.NonVacuityH28.callback_false_derivation_rejected
#check @Solidity.Assurance.NonVacuityH28.violated_after_rejected
#print axioms Solidity.Assurance.NonVacuityH28.violated_after_rejected
#check @Solidity.Assurance.NonVacuityH28.assumption_exhausts
#print axioms Solidity.Assurance.NonVacuityH28.assumption_exhausts
#check @Solidity.Assurance.NonVacuityH28.assumption_not_successful
#print axioms Solidity.Assurance.NonVacuityH28.assumption_not_successful
#check @Solidity.Assurance.NonVacuityH28.assumption_fragment_rejected
#print axioms Solidity.Assurance.NonVacuityH28.assumption_fragment_rejected
#check @Solidity.Assurance.NonVacuityH28.assumption_erased_code
#print axioms Solidity.Assurance.NonVacuityH28.assumption_erased_code
#check @Solidity.Assurance.NonVacuityH28.expression_nonrevert_halt_rejected
#print axioms Solidity.Assurance.NonVacuityH28.expression_nonrevert_halt_rejected

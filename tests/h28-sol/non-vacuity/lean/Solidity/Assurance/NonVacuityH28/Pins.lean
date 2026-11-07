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

/-! Exact measured axiom pins. Changed sets fail the kernel gate. -/

/-- info: 'Solidity.Main.rule_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.rule_sound

/-- info: 'Solidity.Main.rule_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.rule_unique

/-- info: 'Solidity.Main.rule_is_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.rule_is_step

/-- info: 'Solidity.Main.rule_exists' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Main.rule_exists

/-- info: 'Solidity.Main.rule_of_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Main.rule_of_step

/-- info: 'Solidity.Main.solkey_rule_exists' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Main.solkey_rule_exists

/-- info: 'Solidity.Main.solkey_rule_lt_calculus' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Main.solkey_rule_lt_calculus

/-- info: 'Solidity.Main.solkey_step_taclet' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Main.solkey_step_taclet

/-- info: 'Solidity.Main.solkey_eq_calculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.solkey_eq_calculus

/-- info: 'Solidity.Main.solkey_lt_calculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.solkey_lt_calculus

/-- info: 'Solidity.Main.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.soundness

/-- info: 'Solidity.Main.soundness'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.soundness'

/-- info: 'Solidity.Main.solkey_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.solkey_soundness

/-- info: 'Solidity.Main.callback_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.callback_soundness

/-- info: 'Solidity.Main.noCallback_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.noCallback_soundness

/-- info: 'Solidity.Main.noCallback_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.noCallback_iff

/-- info: 'Solidity.Main.cleanTail_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.cleanTail_holds

/-- info: 'Solidity.Main.symex_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.symex_sound

/-- info: 'Solidity.Main.compiler_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.compiler_correct

/-- info: 'Solidity.Main.compiler_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.compiler_net

/-- info: 'Solidity.Main.compiler_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.compiler_checked

/-- info: 'Solidity.Stmt.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Stmt.sound

/-- info: 'Solidity.Rule.premise_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Rule.premise_unique

/-- info: 'Solidity.Rule.toStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Rule.toStep

/-- info: 'Solidity.Stmt.rule_exists' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Stmt.rule_exists

/-- info: 'Solidity.Rule.ofStep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Rule.ofStep

/-- info: 'Solidity.Stmt.step_taclet' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Stmt.step_taclet

/-- info: 'Solidity.Stmt.solkey_lt_calculus' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Stmt.solkey_lt_calculus

/-- info: 'Solidity.Stmt.taclet_of_admits' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Stmt.taclet_of_admits

/-- info: 'Solidity.Proves.solkey_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Proves.solkey_iff

/-- info: 'Solidity.Proves.solkey_lt_calculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Proves.solkey_lt_calculus

/-- info: 'Solidity.Proves.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Proves.sound

/-- info: 'Solidity.Proves.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Proves.valid

/-- info: 'Solidity.ProvesC.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.ProvesC.valid

/-- info: 'Solidity.validC_false_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.validC_false_iff

/-- info: 'Solidity.ValidTail.holds_of_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.ValidTail.holds_of_clean

/-- info: 'Solidity.symex_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.symex_sound

/-- info: 'Solidity.Evm.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.compile_correct

/-- info: 'Solidity.Evm.compile_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.compile_net

/-- info: 'Solidity.Evm.Compiler.Compilation.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Compiler.Compilation.correct

/-- info: 'Solidity.Proves.sound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Proves.sound_of

/-- info: 'Solidity.ProvesC.fmlValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.ProvesC.fmlValid

/-- info: 'Solidity.Evm.Sim.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Sim.init

/-- info: 'Solidity.Main.ValidUnder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.ValidUnder

/-- info: 'Solidity.Main.Derives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.Derives

/-- info: 'Solidity.Main.DerivesK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.DerivesK

/-- info: 'Solidity.Main.Rewrites' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Main.Rewrites

/-- info: 'Solidity.Main.RewritesK' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Main.RewritesK

/-- info: 'Solidity.Main.DoesAs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.DoesAs

/-- info: 'Solidity.Main.Runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.Runs

/-- info: 'Solidity.Main.MRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.MRuns

/-- info: 'Solidity.Main.MReverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.MReverts

/-- info: 'Solidity.Main.Compiles' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Main.Compiles

/-- info: 'Solidity.Main.Represents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Main.Represents

/-- info: 'Solidity.Evm.Frag' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Evm.Frag

/-- info: 'Solidity.Evm.inFrag' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.inFrag

/-- info: 'Solidity.Evm.inFragP' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.inFragP

/-- info: 'Solidity.Evm.SimL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.SimL

/-- info: 'Solidity.Evm.Sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Sim

/-- info: 'Solidity.Evm.ReprV' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Evm.ReprV

/-- info: 'Solidity.Evm.ReprAt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.ReprAt

/-- info: 'Solidity.Evm.ReprStore' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.ReprStore

/-- info: 'Solidity.Evm.PathAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.PathAt

/-- info: 'Solidity.Evm.PathSlot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.PathSlot

/-- info: 'Solidity.Evm.EnvSim' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Evm.EnvSim

/-- info: 'Solidity.Evm.Compiler.Compilation.Input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Compiler.Compilation.Input

/-- info: 'Solidity.Evm.Compiler.Compilation.Rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Compiler.Compilation.Rep

/-- info: 'Solidity.Evm.Compiler.Compilation.Agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Compiler.Compilation.Agrees

/-- info: 'Solidity.Premise.Sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Premise.Sound

/-- info: 'Solidity.Stmt.Sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Stmt.Sound

/-- info: 'Solidity.Premise.fml' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Premise.fml

/-- info: 'Solidity.Modality.forallB' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Modality.forallB

/-- info: 'Solidity.Hyps.wrap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Hyps.wrap

/-- info: 'Solidity.RuleSet.admits' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.RuleSet.admits

/-- info: 'Solidity.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.holds

/-- info: 'Solidity.Modality.afterRunTR' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Modality.afterRunTR

/-- info: 'Solidity.Fml.Valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Fml.Valid

/-- info: 'Solidity.Spec.sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Spec.sat

/-- info: 'Solidity.Spec.Valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Spec.Valid

/-- info: 'Solidity.Spec.toFml' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Spec.toFml

/-- info: 'Solidity.Spec.satC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Spec.satC

/-- info: 'Solidity.Spec.ValidC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Spec.ValidC

/-- info: 'Solidity.Fml.stateInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Fml.stateInv

/-- info: 'Solidity.COut.thenF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.COut.thenF

/-- info: 'Solidity.holdsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.holdsC

/-- info: 'Solidity.Invariant' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Invariant

/-- info: 'Solidity.ValidC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.ValidC

/-- info: 'Solidity.StateInv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.StateInv

/-- info: 'Solidity.Stmt.callsBack' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Stmt.callsBack

/-- info: 'Solidity.Prog.callsBack' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Prog.callsBack

/-- info: 'Solidity.Frames.callsBack' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frames.callsBack

/-- info: 'Solidity.Fml.callsBack' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Fml.callsBack

/-- info: 'Solidity.COut.after' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.COut.after

/-- info: 'Solidity.Fml.FO' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Fml.FO

/-- info: 'Solidity.Stmt.inSolkey' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Stmt.inSolkey

/-- info: 'Solidity.Fml.inSolkey' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Fml.inSolkey

/-- info: 'Solidity.ValidTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.ValidTail

/-- info: 'Solidity.ordinaryDefaultFold' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.ordinaryDefaultFold

/-- info: 'Solidity.SVal.OrdinaryDefault' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.SVal.OrdinaryDefault

/-- info: 'Solidity.SFields.OrdinaryDefault' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.SFields.OrdinaryDefault

/-- info: 'Solidity.SList.OrdinaryDefault' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.SList.OrdinaryDefault

/-- info: 'Solidity.SVec.OrdinaryDefault' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.SVec.OrdinaryDefault

/-- info: 'Solidity.cleanTailH' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.cleanTailH

/-- info: 'Solidity.SVal.CleanTail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.SVal.CleanTail

/-- info: 'Solidity.SFields.CleanTail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.SFields.CleanTail

/-- info: 'Solidity.Storage.CleanTail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Storage.CleanTail

/-- info: 'Solidity.Modality.onTHalt' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Modality.onTHalt

/-- info: 'Solidity.Modality.onHalt' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Modality.onHalt

/-- info: 'Solidity.Evm.Memory.PointerRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.PointerRepr

/-- info: 'Solidity.Evm.Memory.StateRepr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.StateRepr

/-- info: 'Solidity.Evm.Memory.ArrayRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.ArrayRepr

/-- info: 'Solidity.Evm.Memory.HeapRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.HeapRepr

/-- info: 'Solidity.Evm.Memory.StructRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.StructRepr

/-- info: 'Solidity.Evm.Memory.StructHeapRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.StructHeapRepr

/-- info: 'Solidity.Evm.Memory.StructArraySeparated' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.StructArraySeparated

/-- info: 'Solidity.Evm.Memory.RefFieldsRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.RefFieldsRepr

/-- info: 'Solidity.Evm.Memory.FreeMemory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.FreeMemory

/-- info: 'Solidity.Evm.Memory.AllocatorRepr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.AllocatorRepr

/-- info: 'Solidity.Evm.Memory.StructAllocatorRepr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.StructAllocatorRepr

/-- info: 'Solidity.Evm.Memory.Objects.ValueRepr' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.ValueRepr

/-- info: 'Solidity.Evm.Memory.Objects.header' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.header

/-- info: 'Solidity.Evm.Memory.Objects.cells' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.cells

/-- info: 'Solidity.Evm.Memory.Objects.Ownership' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.Ownership

/-- info: 'Solidity.Evm.Memory.Objects.ArrayRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.ArrayRepr

/-- info: 'Solidity.Evm.Memory.Objects.HeapRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.HeapRepr

/-- info: 'Solidity.Evm.Memory.Objects.StateRepr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.StateRepr

/-- info: 'Solidity.Evm.Memory.Objects.AllocatorRepr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.AllocatorRepr

/-- info: 'Solidity.Evm.Memory.Objects.AllocationInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.AllocationInput

/-- info: 'Solidity.Evm.Memory.Objects.GrowsAllocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.GrowsAllocator

/-- info: 'Solidity.Evm.Memory.Objects.KeepsAllocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.KeepsAllocator

/-- info: 'Solidity.Evm.Memory.BaseExtends' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Evm.Memory.BaseExtends

/-- info: 'Solidity.Evm.Memory.GrowsAllocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.GrowsAllocator

/-- info: 'Solidity.Evm.Memory.AllocationInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.AllocationInput

/-- info: 'Solidity.Evm.Memory.RefArrayRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.RefArrayRepr

/-- info: 'Solidity.Evm.Memory.RefArrayHeapRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.RefArrayHeapRepr

/-- info: 'Solidity.Evm.Memory.RefArrayStateRepr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.RefArrayStateRepr

/-- info: 'Solidity.Evm.Memory.FixedArrayRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.FixedArrayRepr

/-- info: 'Solidity.Evm.Memory.FixedHeapRepr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.FixedHeapRepr

/-- info: 'Solidity.Evm.Memory.FixedStateRepr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.FixedStateRepr

/-- info: 'Solidity.Evm.Memory.Loops.StmtCert.Cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Loops.StmtCert.Cost

/-- info: 'Solidity.Evm.Memory.Loops.Cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Loops.Cost

/-- info: 'Solidity.Evm.Memory.Loops.StmtCert.Demand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Loops.StmtCert.Demand

/-- info: 'Solidity.Evm.Memory.Loops.Demand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Loops.Demand

/-- info: 'Solidity.Evm.Memory.Loops.Room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Loops.Room

/-- info: 'Solidity.Evm.Memory.LoopScopes.StmtCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.LoopScopes.StmtCost

/-- info: 'Solidity.Evm.Memory.LoopScopes.Cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.LoopScopes.Cost

/-- info: 'Solidity.Evm.Memory.LoopScopes.StmtDemand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.LoopScopes.StmtDemand

/-- info: 'Solidity.Evm.Memory.LoopScopes.Demand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.LoopScopes.Demand

/-- info: 'Solidity.Evm.Memory.LoopScopes.Room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.LoopScopes.Room

/-- info: 'Solidity.Evm.Memory.frameNeedProg' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.frameNeedProg

/-- info: 'Solidity.Evm.Memory.allocationCostProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.allocationCostProg

/-- info: 'Solidity.Evm.Memory.Construction.allocationCostProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Construction.allocationCostProg

/-- info: 'Solidity.Evm.Memory.StorageCopy.allocationCostProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.StorageCopy.allocationCostProg

/-- info: 'Solidity.Evm.Memory.copyBoundProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.copyBoundProg

/-- info: 'Solidity.Held.OK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Held.OK

/-- info: 'Solidity.Upd.Lands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Upd.Lands

/-- info: 'Solidity.Upd.afterT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Upd.afterT

/-- info: 'Solidity.StateInv.at' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.StateInv.at

/-- info: 'Solidity.ExecF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.ExecF

/-- info: 'Solidity.Fml.hasTransfer' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Fml.hasTransfer

/-- info: 'Solidity.Frames.hasTransfer' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frames.hasTransfer

/-- info: 'Solidity.Stmt.forksIn' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Stmt.forksIn

/-- info: 'Solidity.Stmt.hasTransfer' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Stmt.hasTransfer

/-- info: 'Solidity.Prog.hasTransfer' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Prog.hasTransfer

/-- info: 'Solidity.Hyps.boxOnly' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Hyps.boxOnly

/-- info: 'Solidity.Fml.modalFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Fml.modalFree

/-- info: 'Solidity.Stmt.keyStep' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Stmt.keyStep

/-- info: 'Solidity.Evm.Memory.LoopPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.LoopPrefix

/-- info: 'Solidity.Evm.Memory.LoopRoom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.LoopRoom

/-- info: 'Solidity.Evm.Compiler.Compilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Compiler.Compilation

/-- info: 'Solidity.Evm.Memory.CompiledProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.CompiledProg

/-- info: 'Solidity.Evm.Memory.ReferenceArrays.CompiledProg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.ReferenceArrays.CompiledProg

/-- info: 'Solidity.Evm.Memory.Objects.CompiledProg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Objects.CompiledProg

/-- info: 'Solidity.Evm.Memory.Construction.CompiledProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Construction.CompiledProg

/-- info: 'Solidity.Evm.Memory.Loops.CompiledProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Loops.CompiledProg

/-- info: 'Solidity.Evm.Memory.LoopScopes.CompiledProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.LoopScopes.CompiledProg

/-- info: 'Solidity.Evm.Memory.Calls.Program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Calls.Program

/-- info: 'Solidity.Evm.Memory.StorageCopy.CompiledProg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.StorageCopy.CompiledProg

/-- info: 'Solidity.Evm.Memory.Fixed.CompiledProg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.Fixed.CompiledProg

/-- info: 'Solidity.Evm.Memory.CopyConstruction.CompiledProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Memory.CopyConstruction.CompiledProg

/-- info: 'Solidity.Assurance.NonVacuityH28.construction_allocator_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.construction_allocator_growth

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_allocator_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_allocator_growth

/-- info: 'Solidity.Assurance.NonVacuityH28.construction_cursor_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.construction_cursor_observation

/-- info: 'Solidity.Assurance.NonVacuityH28.construction_cursor_erasure_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.construction_cursor_erasure_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.assertion_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.assertion_runs

/-- info: 'Solidity.Assurance.NonVacuityH28.assertion_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.assertion_derivation

/-- info: 'Solidity.Assurance.NonVacuityH28.calculus_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.calculus_application

/-- info: 'Solidity.Assurance.NonVacuityH28.direct_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.direct_application

/-- info: 'Solidity.Assurance.NonVacuityH28.solkey_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.solkey_application

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_application

/-- info: 'Solidity.Assurance.NonVacuityH28.noCallback_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.noCallback_application

/-- info: 'Solidity.Assurance.NonVacuityH28.noCallback_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.noCallback_equivalence

/-- info: 'Solidity.Assurance.NonVacuityH28.cleanTail_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.cleanTail_application

/-- info: 'Solidity.Assurance.NonVacuityH28.symex_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.symex_application

/-- info: 'Solidity.Assurance.NonVacuityH28.solkey_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.solkey_equivalence

/-- info: 'Solidity.Assurance.NonVacuityH28.solkey_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.solkey_strict

/-- info: 'Solidity.Assurance.NonVacuityH28.solkey_rule_application' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.solkey_rule_application

/-- info: 'Solidity.Assurance.NonVacuityH28.solkey_admission_application' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.solkey_admission_application

/-- info: 'Solidity.Assurance.NonVacuityH28.zero_unwind_strict' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.zero_unwind_strict

/-- info: 'Solidity.Assurance.NonVacuityH28.false_invariant_entry_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.false_invariant_entry_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.false_annotation_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.false_annotation_run

/-- info: 'Solidity.Assurance.NonVacuityH28.false_annotation_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.false_annotation_entry

/-- info: 'Solidity.Assurance.NonVacuityH28.false_annotation_rule' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.false_annotation_rule

/-- info: 'Solidity.Assurance.NonVacuityH28.false_annotation_init_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.false_annotation_init_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.assertion_rule_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.assertion_rule_semantics

/-- info: 'Solidity.Assurance.NonVacuityH28.competing_assertion_rule_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.competing_assertion_rule_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.symex_actual_progress' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.symex_actual_progress

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_nil_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_nil_frame

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_seq_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_seq_frame

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_halt_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_halt_frame

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_violated_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_violated_frame

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_pop_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_pop_frame

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_drop_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_drop_frame

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_frame_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_frame_observation

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_violation

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_resume

/-- info: 'Solidity.Assurance.NonVacuityH28.noCallback_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.noCallback_transfer

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_revert

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_observations

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_observation_erasure_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_observation_erasure_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.noCallback_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.noCallback_unique

/-- info: 'Solidity.Assurance.NonVacuityH28.noCallback_excludes_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.noCallback_excludes_resume

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_derivation

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_headline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_headline

/-- info: 'Solidity.Assurance.NonVacuityH28.top_callback_policy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.top_callback_policy

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_program_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_program_resume

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_program_noCallback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_program_noCallback

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_program_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_program_revert

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_program_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_program_violation

/-- info: 'Solidity.Assurance.NonVacuityH28.noCallback_payment_derivation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.noCallback_payment_derivation

/-- info: 'Solidity.Assurance.NonVacuityH28.noCallback_payment_headline' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.noCallback_payment_headline

/-- info: 'Solidity.Assurance.NonVacuityH28.scalar_memory_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.scalar_memory_source

/-- info: 'Solidity.Assurance.NonVacuityH28.declare_memory_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.declare_memory_source

/-- info: 'Solidity.Assurance.NonVacuityH28.self_rebind_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.self_rebind_source

/-- info: 'Solidity.Assurance.NonVacuityH28.objects_supply_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.objects_supply_fixed

/-- info: 'Solidity.Assurance.NonVacuityH28.reference_array_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.reference_array_input

/-- info: 'Solidity.Assurance.NonVacuityH28.object_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.object_input

/-- info: 'Solidity.Assurance.NonVacuityH28.loop_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.loop_input

/-- info: 'Solidity.Assurance.NonVacuityH28.scope_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.scope_input

/-- info: 'Solidity.Assurance.NonVacuityH28.calls_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.calls_input

/-- info: 'Solidity.Assurance.NonVacuityH28.copy_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.copy_input

/-- info: 'Solidity.Assurance.NonVacuityH28.fixed_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.fixed_input

/-- info: 'Solidity.Assurance.NonVacuityH28.copy_construction_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.copy_construction_input

/-- info: 'Solidity.Assurance.NonVacuityH28.checked_families_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.checked_families_joint

/-- info: 'Solidity.Assurance.NonVacuityH28.checked_success_after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.checked_success_after_source

/-- info: 'Solidity.Assurance.NonVacuityH28.construction_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.construction_input

/-- info: 'Solidity.Assurance.NonVacuityH28.construction_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.construction_joint

/-- info: 'Solidity.Assurance.NonVacuityH28.construction_live_pointer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.construction_live_pointer

/-- info: 'Solidity.Assurance.NonVacuityH28.environment_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.environment_simulation

/-- info: 'Solidity.Assurance.NonVacuityH28.mismatched_timestamp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.mismatched_timestamp

/-- info: 'Solidity.Assurance.NonVacuityH28.sender_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.sender_source

/-- info: 'Solidity.Assurance.NonVacuityH28.sender_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.sender_target

/-- info: 'Solidity.Assurance.NonVacuityH28.sender_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.sender_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.sender_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.sender_representation

/-- info: 'Solidity.Assurance.NonVacuityH28.rule_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.rule_family

/-- info: 'Solidity.Assurance.NonVacuityH28.unique_family' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.unique_family

/-- info: 'Solidity.Assurance.NonVacuityH28.fragment_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.fragment_family

/-- info: 'Solidity.Assurance.NonVacuityH28.simulation_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.simulation_family

/-- info: 'Solidity.Assurance.NonVacuityH28.checked_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.checked_family

/-- info: 'Solidity.Assurance.NonVacuityH28.impossible_resource' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.impossible_resource

/-- info: 'Solidity.Assurance.NonVacuityH28.source_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.source_true

/-- info: 'Solidity.Assurance.NonVacuityH28.source_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.source_false

/-- info: 'Solidity.Assurance.NonVacuityH28.target_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.target_true

/-- info: 'Solidity.Assurance.NonVacuityH28.target_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.target_false

/-- info: 'Solidity.Assurance.NonVacuityH28.nonempty_program' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.nonempty_program

/-- info: 'Solidity.Assurance.NonVacuityH28.nonempty_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.nonempty_code

/-- info: 'Solidity.Assurance.NonVacuityH28.always_revert_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.always_revert_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.correct_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.correct_success

/-- info: 'Solidity.Assurance.NonVacuityH28.net_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.net_success

/-- info: 'Solidity.Assurance.NonVacuityH28.mismatched_funds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.mismatched_funds

/-- info: 'Solidity.Assurance.NonVacuityH28.closed_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.closed_simulation

/-- info: 'Solidity.Assurance.NonVacuityH28.closed_joint_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.closed_joint_witness

/-- info: 'Solidity.Assurance.NonVacuityH28.inhabited_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.inhabited_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.rule_step_family' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.rule_step_family

/-- info: 'Solidity.Assurance.NonVacuityH28.rule_from_step_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.rule_from_step_family

/-- info: 'Solidity.Assurance.NonVacuityH28.mismatched_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.mismatched_oracle

/-- info: 'Solidity.Assurance.NonVacuityH28.correct_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.correct_revert

/-- info: 'Solidity.Assurance.NonVacuityH28.every_rule_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.every_rule_inhabited

/-- info: 'Solidity.Assurance.NonVacuityH28.mismatched_self_ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.mismatched_self_ledger

/-- info: 'Solidity.Assurance.NonVacuityH28.mismatched_external_ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.mismatched_external_ledger

/-- info: 'Solidity.Assurance.NonVacuityH28.fragile_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.fragile_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.fragile_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.fragile_source

/-- info: 'Solidity.Assurance.NonVacuityH28.fragile_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.fragile_joint

/-- info: 'Solidity.Assurance.NonVacuityH28.concrete_object_allocator_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.concrete_object_allocator_kept

/-- info: 'Solidity.Assurance.NonVacuityH28.concrete_object_cursor_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.concrete_object_cursor_kept

/-- info: 'Solidity.Assurance.NonVacuityH28.live_base_extension_queried' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.live_base_extension_queried

/-- info: 'Solidity.Assurance.NonVacuityH28.live_array_layout_queried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.live_array_layout_queried

/-- info: 'Solidity.Assurance.NonVacuityH28.allocated_single_object' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.allocated_single_object

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_source_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_source_observations

/-- info: 'Solidity.Assurance.NonVacuityH28.distinct_object_domain_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.distinct_object_domain_empty

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_entry_identification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_entry_identification

/-- info: 'Solidity.Assurance.NonVacuityH28.joint_payment_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.joint_payment_world

/-- info: 'Solidity.Assurance.NonVacuityH28.joint_payment_compiler_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.joint_payment_compiler_application

/-- info: 'Solidity.Assurance.NonVacuityH28.represented_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.represented_success

/-- info: 'Solidity.Assurance.NonVacuityH28.value_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.value_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.value_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.value_source

/-- info: 'Solidity.Assurance.NonVacuityH28.value_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.value_target

/-- info: 'Solidity.Assurance.NonVacuityH28.value_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.value_representation

/-- info: 'Solidity.Assurance.NonVacuityH28.value_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.value_field

/-- info: 'Solidity.Assurance.NonVacuityH28.alias_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.alias_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.alias_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.alias_source

/-- info: 'Solidity.Assurance.NonVacuityH28.alias_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.alias_target

/-- info: 'Solidity.Assurance.NonVacuityH28.alias_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.alias_representation

/-- info: 'Solidity.Assurance.NonVacuityH28.alias_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.alias_field

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_syntax_gates' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_syntax_gates

/-- info: 'Solidity.Assurance.NonVacuityH28.frame_callback_gates' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.frame_callback_gates

/-- info: 'Solidity.Assurance.NonVacuityH28.calculus_context_gates' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.calculus_context_gates

/-- info: 'Solidity.Assurance.NonVacuityH28.universal_binder_control' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.universal_binder_control

/-- info: 'Solidity.Assurance.NonVacuityH28.halt_gate_domains' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.halt_gate_domains

/-- info: 'Solidity.Assurance.NonVacuityH28.scalar_loop_demand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.scalar_loop_demand

/-- info: 'Solidity.Assurance.NonVacuityH28.scalar_loop_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.scalar_loop_cost

/-- info: 'Solidity.Assurance.NonVacuityH28.scalar_scope_demand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.scalar_scope_demand

/-- info: 'Solidity.Assurance.NonVacuityH28.scalar_scope_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.scalar_scope_cost

/-- info: 'Solidity.Assurance.NonVacuityH28.false_loop_stmt_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.false_loop_stmt_source

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_loop_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_source

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_body_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_body_reverts

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_loop_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_input

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_loop_code_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_code_nonempty

/-- info: 'Solidity.Assurance.NonVacuityH28.zero_condition_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.zero_condition_target

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_loop_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_target

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_loop_demand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_demand

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_loop_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_cost

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_loop_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_checked

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_loop_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_joint

/-- info: 'Solidity.Assurance.NonVacuityH28.skipped_loop_joint_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.skipped_loop_joint_layout

/-- info: 'Solidity.Assurance.NonVacuityH28.entered_revert_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.entered_revert_source

/-- info: 'Solidity.Assurance.NonVacuityH28.entered_revert_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.entered_revert_target

/-- info: 'Solidity.Assurance.NonVacuityH28.entered_revert_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.entered_revert_input

/-- info: 'Solidity.Assurance.NonVacuityH28.entered_revert_demand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.entered_revert_demand

/-- info: 'Solidity.Assurance.NonVacuityH28.entered_revert_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.entered_revert_joint

/-- info: 'Solidity.Assurance.NonVacuityH28.near_end_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.near_end_state

/-- info: 'Solidity.Assurance.NonVacuityH28.near_end_allocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.near_end_allocator

/-- info: 'Solidity.Assurance.NonVacuityH28.near_end_allocation_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.near_end_allocation_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.pointer_erasure_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.pointer_erasure_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.allocated_erasure_countercontrol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.allocated_erasure_countercontrol

/-- info: 'Solidity.Assurance.NonVacuityH28.empty_object_heap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.empty_object_heap

/-- info: 'Solidity.Assurance.NonVacuityH28.fresh_object_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.fresh_object_state

/-- info: 'Solidity.Assurance.NonVacuityH28.fresh_free_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.fresh_free_memory

/-- info: 'Solidity.Assurance.NonVacuityH28.fresh_object_allocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.fresh_object_allocator

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_input

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_source_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_source_eq

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_pointer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_pointer

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_source

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_checked

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_joint

/-- info: 'Solidity.Assurance.NonVacuityH28.original_arms_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.original_arms_input

/-- info: 'Solidity.Assurance.NonVacuityH28.original_calculus_induction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.original_calculus_induction

/-- info: 'Solidity.Assurance.NonVacuityH28.original_callback_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.original_callback_formula

/-- info: 'Solidity.Assurance.NonVacuityH28.original_noCallback_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.original_noCallback_formula

/-- info: 'Solidity.Assurance.NonVacuityH28.original_invariant_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.original_invariant_inputs

/-- info: 'Solidity.Assurance.NonVacuityH28.original_clean_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.original_clean_tail

/-- info: 'Solidity.Assurance.NonVacuityH28.empty_fragment_acceptance_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.empty_fragment_acceptance_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.panic_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.panic_source

/-- info: 'Solidity.Assurance.NonVacuityH28.panic_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.panic_target

/-- info: 'Solidity.Assurance.NonVacuityH28.panic_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.panic_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.compiler_panic_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.compiler_panic_application

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_simulation

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_source

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_target

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_observations' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_observations

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_net_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_net_application

/-- info: 'Solidity.Assurance.NonVacuityH28.payment_checked_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.payment_checked_application

/-- info: 'Solidity.Assurance.NonVacuityH28.poor_payment_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.poor_payment_source

/-- info: 'Solidity.Assurance.NonVacuityH28.poor_payment_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.poor_payment_target

/-- info: 'Solidity.Assurance.NonVacuityH28.refused_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.refused_simulation

/-- info: 'Solidity.Assurance.NonVacuityH28.refused_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.refused_source

/-- info: 'Solidity.Assurance.NonVacuityH28.refused_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.refused_target

/-- info: 'Solidity.Assurance.NonVacuityH28.refused_checked_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.refused_checked_application

/-- info: 'Solidity.Assurance.NonVacuityH28.identity_loop_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.identity_loop_diverges

/-- info: 'Solidity.Assurance.NonVacuityH28.divergence_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.divergence_source

/-- info: 'Solidity.Assurance.NonVacuityH28.machine_loop_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.machine_loop_diverges

/-- info: 'Solidity.Assurance.NonVacuityH28.divergence_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.divergence_target

/-- info: 'Solidity.Assurance.NonVacuityH28.divergence_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.divergence_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.compiler_divergence_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.compiler_divergence_application

/-- info: 'Solidity.Assurance.NonVacuityH28.unset_alias_not_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.unset_alias_not_ok

/-- info: 'Solidity.Assurance.NonVacuityH28.dead_alias_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.dead_alias_simulation

/-- info: 'Solidity.Assurance.NonVacuityH28.dead_alias_fragment_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.dead_alias_fragment_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.dead_alias_source_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.dead_alias_source_reverts

/-- info: 'Solidity.Assurance.NonVacuityH28.dead_alias_target_faults' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.dead_alias_target_faults

/-- info: 'Solidity.Assurance.NonVacuityH28.unset_memory_core_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.unset_memory_core_simulation

/-- info: 'Solidity.Assurance.NonVacuityH28.unset_memory_pointer_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.unset_memory_pointer_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_value_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_value_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_value_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_value_source

/-- info: 'Solidity.Assurance.NonVacuityH28.primitive_value_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.primitive_value_target

/-- info: 'Solidity.Assurance.NonVacuityH28.all_primitive_values_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.all_primitive_values_represented

/-- info: 'Solidity.Assurance.NonVacuityH28.all_primitive_value_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.all_primitive_value_fields

/-- info: 'Solidity.Assurance.NonVacuityH28.negative_int_word' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.negative_int_word

/-- info: 'Solidity.Assurance.NonVacuityH28.negative_int_observation_not_erased' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.negative_int_observation_not_erased

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_step

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_lands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_lands

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_source

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_changed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_changed

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_update_antecedent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_update_antecedent

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_rule_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_rule_application

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_require_source_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_require_source_true

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_require_source_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_require_source_false

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_split_antecedent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_split_antecedent

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_split_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_split_application

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_binding_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_binding_step

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_binding_antecedent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_binding_antecedent

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_binding_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_binding_source

/-- info: 'Solidity.Assurance.NonVacuityH28.flag_binding_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.flag_binding_application

/-- info: 'Solidity.Assurance.NonVacuityH28.revert_done_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.revert_done_true

/-- info: 'Solidity.Assurance.NonVacuityH28.revert_rule_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.revert_rule_application

/-- info: 'Solidity.Assurance.NonVacuityH28.write_fragment' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.write_fragment

/-- info: 'Solidity.Assurance.NonVacuityH28.write_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.write_source

/-- info: 'Solidity.Assurance.NonVacuityH28.write_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.write_target

/-- info: 'Solidity.Assurance.NonVacuityH28.changed_observation' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.changed_observation

/-- info: 'Solidity.Assurance.NonVacuityH28.storage_observation_erasure_rejected' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.storage_observation_erasure_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.write_compiler_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.write_compiler_application

/-- info: 'Solidity.Assurance.NonVacuityH28.tail_clean_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.tail_clean_valid

/-- info: 'Solidity.Assurance.NonVacuityH28.tail_clean_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.tail_clean_status

/-- info: 'Solidity.Assurance.NonVacuityH28.tail_clean_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.tail_clean_source

/-- info: 'Solidity.Assurance.NonVacuityH28.tail_clean_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.tail_clean_main

/-- info: 'Solidity.Assurance.NonVacuityH28.dirty_tail_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.dirty_tail_reachable

/-- info: 'Solidity.Assurance.NonVacuityH28.dirty_tail_not_clean' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.dirty_tail_not_clean

/-- info: 'Solidity.Assurance.NonVacuityH28.tail_dirty_status' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.tail_dirty_status

/-- info: 'Solidity.Assurance.NonVacuityH28.tail_dirty_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.tail_dirty_source

/-- info: 'Solidity.Assurance.NonVacuityH28.tail_dirty_frames_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.tail_dirty_frames_panic

/-- info: 'Solidity.Assurance.NonVacuityH28.tail_premise_cannot_be_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.tail_premise_cannot_be_erased

/-- info: 'Solidity.Assurance.NonVacuityH28.done_false_antecedent_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.done_false_antecedent_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.empty_goal_guard_rejected' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.empty_goal_guard_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.empty_cases_guard_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.empty_cases_guard_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.callback_false_derivation_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.callback_false_derivation_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.violated_after_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.violated_after_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.assumption_exhausts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.assumption_exhausts

/-- info: 'Solidity.Assurance.NonVacuityH28.assumption_not_successful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.assumption_not_successful

/-- info: 'Solidity.Assurance.NonVacuityH28.assumption_fragment_rejected' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.assumption_fragment_rejected

/-- info: 'Solidity.Assurance.NonVacuityH28.assumption_erased_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.assumption_erased_code

/-- info: 'Solidity.Assurance.NonVacuityH28.expression_nonrevert_halt_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Assurance.NonVacuityH28.expression_nonrevert_halt_rejected

import Solidity.Yul.Compilation.FramedControl
import Solidity.Yul.Compilation.FramedWordLoweringControls
/-! Concrete sequential composition of existing original statement/expression
compilers. The entire intermediate stack is derived, not an input assumption.
These are compiler-model controls, not native bytes/1024-word admission or a
new source construct. Dirty numeric caller words and all nonstack fields stay. -/
namespace Solidity.Yul.Compilation.FramedControl.Controls
open Backend Scalar Selection MachineAdapter
open SignedInstructionCertificates.Controls

def leftModel := SignedExecution.Controls.statementModel
def leftCode := SignedExecution.Controls.statementCode
def rightModel := model
def rightCode := program

def certificate : FramedLoweringCertificate (leftModel++rightModel)
 (.seq (.code leftCode) (.code rightCode)) :=
 seq FramedWordLowering.Controls.statementCertificate FramedWordLowering.Controls.certificate

/-- Genuine whole-sequence success for all full words, numeric caller tails
and entire machine frames. Both source-indexed compiler laws discharge their
component executions at the ACTUAL updated locals. -/
theorem combination (locals : Vector Scalar.Word 2) (tail : Stack) (m : Evm.Machine) :
 Evm.run (leftModel++rightModel) {m with stack := irStack (locals.toList++tail)} =
 .ok {m with stack := irStack (compiled.value (SignedExecution.Controls.statementCompiled.update locals)::
     ((SignedExecution.Controls.statementCompiled.update locals).toList++tail))} 0 := by
 apply (certificate.success (locals.toList++tail) _ {m with stack := irStack (locals.toList++tail)} rfl).mpr
 apply StructuredExec.seq
 · apply StructuredExec.code
   simpa only [Vector.toList_empty,List.nil_append] using
    SignedExecution.Controls.statementCompiled.lowered.correct 0 leftCode
     (Option.some_get (by rfl)).symm locals #v[] tail
 · apply StructuredExec.code
   simpa only [Vector.toList_empty,List.nil_append] using
    compiled.lowered.correct 0 rightCode SignedExecution.Controls.actual_emission
     (SignedExecution.Controls.statementCompiled.update locals) #v[] tail

/-- Reflect the real whole run through the composed contract: component
intermediate execution and pending zero are consequences, not premises. -/
theorem reflect_combination (locals : Vector Scalar.Word 2) (tail : Stack)
 (m final : Evm.Machine) (skip : Nat)
 (ran : Evm.run (leftModel++rightModel) {m with stack := irStack (locals.toList++tail)} = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {m with stack := irStack output} ∧
 StructuredExec (.seq (.code leftCode) (.code rightCode)) (locals.toList++tail) output := by
 simpa only [] using certificate.reflect (locals.toList++tail)
  {m with stack := irStack (locals.toList++tail)} final skip rfl ran

/-- A later producer cannot rescue an already-faulting earlier component. -/
theorem prefix_fault (m : Evm.Machine) :
 Evm.run (failingModel++rightModel) {m with stack := []} = .fault := by
 change Evm.exec (failingModel++rightModel) 0 {m with stack := []} = _
 rw [Evm.exec_append]
 change (Evm.run failingModel {m with stack := []}).bind _ = _
 rw [prefix_failure m]
 rfl

/-- Pending control can be consumed by appended code in the actual model;
this is exactly why a leaf success-iff alone is insufficient for reflection. -/
theorem consumed_skip (m : Evm.Machine) :
 Evm.run ([.jump 1]++[.push (coreWord dirty)]) m = .ok m 0 := rfl

/-- The stronger published contract constructively refuses that pending
prefix, so sequential composition cannot smuggle this counterexample. -/
theorem pending_prefix_refused (block : Backend.Block) :
 ¬ Nonempty (FramedLoweringCertificate [.jump 1] block) := by
 rintro ⟨c⟩
 obtain ⟨_,zero,_,_⟩ := c.reflect [] Evm.Machine.init Evm.Machine.init 1 rfl (by rfl)
 omega

#guard SignedExecution.Controls.statementCompiled.update #v[negativeSeven,3] = #v[negativeTwo,1]
#guard compiled.value #v[dirty,3] ≠ compiled.value #v[257,3]
#guard Scalar.run failingProgram [] = none
/-- info: 'Solidity.Yul.Compilation.FramedControl.Controls.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate
/-- info: 'Solidity.Yul.Compilation.FramedControl.Controls.combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms combination
/-- info: 'Solidity.Yul.Compilation.FramedControl.Controls.reflect_combination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflect_combination
/-- info: 'Solidity.Yul.Compilation.FramedControl.Controls.prefix_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prefix_fault
/-- info: 'Solidity.Yul.Compilation.FramedControl.Controls.consumed_skip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms consumed_skip
/-- info: 'Solidity.Yul.Compilation.FramedControl.Controls.pending_prefix_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pending_prefix_refused
end Solidity.Yul.Compilation.FramedControl.Controls

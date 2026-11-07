import Solidity.Yul.Compilation.FramedBranch
import Solidity.Yul.Compilation.FramedControl
/-! Whole conditional composition of the existing strong lowering contract.
Actual condition execution, guard and taken-arm trace are derived. This is
compiler-model structured control, not Source/G24, native bytes/resources,
physical views or recursive/divergent source adequacy. -/
namespace Solidity.Yul.Compilation.FramedConditional
open Backend Scalar Selection MachineAdapter

theorem irStack_cons (word : Scalar.Word) (input : Stack) :
 irStack (word::input) = coreWord word::irStack input := by
 change Evm.Word.val (Evm.wmod word.toNat)::irStack input = _
 rw [Evm.wmod_of_lt word.isLt]
 rfl

/-- Every actual whole conditional success determines its real guard and arm.
No condition result, guard nonzeroness, chosen execution or pending0 is assumed. -/
theorem reflect {c : Backend.Program} {a b : Backend.Block} {qc qa qb : List Evm.Instr}
 (condition : FramedLoweringCertificate qc (.code c))
 (left : FramedLoweringCertificate qa a) (right : FramedLoweringCertificate qb b)
 (input : Stack) (initial final : Evm.Machine) (skip : Nat)
 (represented : initial.stack = irStack input)
 (ran : Evm.run (MachineControl.branchCode qc qa qb) initial = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {initial with stack := irStack output} ∧
 StructuredExec (.ite c a b) input output := by
 have whole : (Evm.run qc initial).bind
   (fun m k => Evm.exec (MachineControl.branchTail qa qb) k m) = .ok final skip := by
  simpa only [MachineControl.branchCode,Evm.run,Evm.exec_append] using ran
 cases actual : Evm.run qc initial with
 | revert => rw [actual] at whole; cases whole
 | fault => rw [actual] at whole; cases whole
 | ok middle pending =>
   obtain ⟨guarded,zero,frame,conditionTrace⟩ := condition.reflect input initial middle pending represented actual
   rw [actual,zero] at whole
   change Evm.run (MachineControl.branchTail qa qb) middle = .ok final skip at whole
   rw [frame] at whole
   cases guarded with
   | nil => cases whole
   | cons word rest =>
     rw [irStack_cons] at whole
     obtain ⟨output,done,finalFrame,arm⟩ := FramedBranch.tail_reflect left right word rest
       {initial with stack := irStack rest} final skip rfl whole
     refine ⟨output,done,finalFrame,?_⟩
     cases conditionTrace with
     | code conditionRun =>
       by_cases isZero : word = 0
       · subst word
         exact StructuredExec.iteFalse conditionRun (by simpa only [if_pos rfl] using arm)
       · exact StructuredExec.iteTrue conditionRun isZero (by simpa only [if_neg isZero] using arm)

/-- Forward structured execution uses only the selected arm, including when
an untaken arm faults on the input left by the condition. -/
theorem forward {c : Backend.Program} {a b : Backend.Block} {qc qa qb : List Evm.Instr}
 (condition : FramedLoweringCertificate qc (.code c))
 (left : FramedLoweringCertificate qa a) (right : FramedLoweringCertificate qb b)
 (input output : Stack) (initial : Evm.Machine)
 (represented : initial.stack = irStack input)
 (trace : StructuredExec (.ite c a b) input output) :
 Evm.run (MachineControl.branchCode qc qa qb) initial = .ok {initial with stack := irStack output} 0 := by
 cases trace with
 | @iteTrue _ _ _ _ rest _ word conditionRun nonzero arm =>
   have ran := (condition.success input (word::rest) initial represented).mpr (.code conditionRun)
   rw [MachineControl.branchCode,Evm.run_append_ok ran,irStack_cons]
   exact FramedBranch.tail_forward left right word rest output
    {initial with stack := irStack rest} rfl (by simpa only [if_neg nonzero] using arm)
 | @iteFalse _ _ _ _ rest _ conditionRun arm =>
   have ran := (condition.success input (0::rest) initial represented).mpr (.code conditionRun)
   rw [MachineControl.branchCode,Evm.run_append_ok ran,irStack_cons]
   exact FramedBranch.tail_forward left right 0 rest output
    {initial with stack := irStack rest} rfl (by simpa only [if_pos rfl] using arm)

/-- Concrete producer of the unchanged published strong conditional contract. -/
def conditional {c : Backend.Program} {a b : Backend.Block} {qc qa qb : List Evm.Instr}
 (condition : FramedLoweringCertificate qc (.code c))
 (left : FramedLoweringCertificate qa a) (right : FramedLoweringCertificate qb b) :
 FramedLoweringCertificate (MachineControl.branchCode qc qa qb) (.ite c a b) where
 reflect := reflect condition left right
 success := by
  intro input output initial represented
  constructor
  · intro ran
    obtain ⟨actual,_,frame,trace⟩ := reflect condition left right input initial _ 0 represented ran
    have same : output = actual := irStack_injective (congrArg Evm.Machine.stack frame)
    simpa only [same] using trace
  · exact forward condition left right input output initial represented

/-- info: 'Solidity.Yul.Compilation.FramedConditional.irStack_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms irStack_cons
/-- info: 'Solidity.Yul.Compilation.FramedConditional.reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reflect
/-- info: 'Solidity.Yul.Compilation.FramedConditional.forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forward
/-- info: 'Solidity.Yul.Compilation.FramedConditional.conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conditional
end Solidity.Yul.Compilation.FramedConditional

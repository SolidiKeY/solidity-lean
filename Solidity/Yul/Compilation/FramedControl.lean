import Solidity.Backend.Selection.FramedLoweringInterface
import Solidity.Backend.Selection.LiteralSelection
/-! Composition over the unchanged Backend.Block and published framed lowering
contract. Successful intermediate stacks are derived from actual execution;
no favourable intermediate-run or pending-skip premise is accepted. Numeric
representation is explicit; native bytes, capacity, faults/reverts/divergence,
physical/source/G24 adequacy remain separate obligations. -/
namespace Solidity.Yul.Compilation.FramedControl
open Backend Scalar Selection

/-- Actual whole-sequence success yields both real scalar component runs.
The left certificate forces its own pending skip to zero before the right
code is run, and both exact nonstack frames compose. -/
theorem seq_reflect {a b : Backend.Block} {qa qb : List Evm.Instr}
 (left : FramedLoweringCertificate qa a) (right : FramedLoweringCertificate qb b)
 (input : Stack) (initial final : Evm.Machine) (skip : Nat)
 (represented : initial.stack = irStack input)
 (ran : Evm.run (qa++qb) initial = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {initial with stack := irStack output} ∧
 StructuredExec (.seq a b) input output := by
 have whole : (Evm.run qa initial).bind (fun m k => Evm.exec qb k m) = .ok final skip := by
   simpa only [Evm.run,Evm.exec_append] using ran
 cases actual : Evm.run qa initial with
 | revert => rw [actual] at whole; cases whole
 | fault => rw [actual] at whole; cases whole
 | ok middle pending =>
   obtain ⟨intermediate,zero,frame,traceLeft⟩ := left.reflect input initial middle pending represented actual
   rw [actual,zero] at whole
   have runRight : Evm.run qb middle = .ok final skip := whole
   have middleRep : middle.stack = irStack intermediate := congrArg Evm.Machine.stack frame
   obtain ⟨output,done,frameRight,traceRight⟩ := right.reflect intermediate middle final skip middleRep runRight
   refine ⟨output,done,?_,StructuredExec.seq traceLeft traceRight⟩
   rw [frame] at frameRight
   exact frameRight

/-- Concrete algebraic producer for the EXISTING strong contract. Both input
certificates are real typed obligations; this theorem proves composition,
not an instance of any missing Source/runtime/native producer. -/
def seq {a b : Backend.Block} {qa qb : List Evm.Instr}
 (left : FramedLoweringCertificate qa a) (right : FramedLoweringCertificate qb b) :
 FramedLoweringCertificate (qa++qb) (.seq a b) where
 reflect := seq_reflect left right
 success := by
   intro input output initial represented
   constructor
   · intro ran
     obtain ⟨actual,_,frame,trace⟩ := seq_reflect left right input initial _ 0 represented ran
     have same : output = actual := irStack_injective (congrArg Evm.Machine.stack frame)
     simpa only [same] using trace
   · intro trace
     cases trace with
     | @seq _ _ _ middle _ traceLeft traceRight =>
       have runLeft := (left.success input middle initial represented).mpr traceLeft
       have runRight := (right.success middle output {initial with stack := irStack middle} rfl).mpr traceRight
       rw [Evm.run_append_ok runLeft]
       exact runRight

/-- info: 'Solidity.Yul.Compilation.FramedControl.seq_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seq_reflect
/-- info: 'Solidity.Yul.Compilation.FramedControl.seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seq
end Solidity.Yul.Compilation.FramedControl

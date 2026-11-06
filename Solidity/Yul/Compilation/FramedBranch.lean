import Solidity.Yul.Compilation.FramedWordLowering
import Solidity.Yul.Compilation.MachineControl
/-! Transport through the existing relative-skip conditional tail. Guards are
full physical words. Only the taken arm must actually succeed; no favourable
untaken-arm run is assumed. This is target preparation, not whole-source/G24,
condition compilation, native-byte/resource or recursive-control adequacy. -/
namespace Solidity.Yul.Compilation.FramedBranch
open Backend Scalar Selection MachineAdapter

/-- Nonzero jumps exactly past the untaken arm and its terminal jump.
The result is exact even when the taken arm faults or has a pending skip. -/
theorem nonzero_tail (word : Scalar.Word) (yes no : List Evm.Instr)
 (initial : Evm.Machine) (nonzero : word ≠ 0) :
 Evm.run (MachineControl.branchTail yes no) {initial with stack := coreWord word::initial.stack} =
 Evm.run yes initial := by
 have nz : word.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 simp only [MachineControl.branchTail,Evm.run,Evm.exec_cons_zero,Evm.Instr.step,
   coreWord,nz,ite_false,Evm.Out.ok_bind]
 rw [Evm.exec_skip_append]
 rfl

/-- Reflection derives the taken arm trace, exact frame and pending zero from
actual whole-tail success. Both strong certificates keep their exact code;
no arm executions or intermediate stacks are premises. -/
theorem tail_reflect {a b : Backend.Block} {yes no : List Evm.Instr}
 (left : FramedLoweringCertificate yes a) (right : FramedLoweringCertificate no b)
 (word : Scalar.Word) (input : Stack) (initial final : Evm.Machine) (skip : Nat)
 (represented : initial.stack = irStack input)
 (ran : Evm.run (MachineControl.branchTail yes no)
   {initial with stack := coreWord word::initial.stack} = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {initial with stack := irStack output} ∧
 (if word = 0 then StructuredExec b input output else StructuredExec a input output) := by
 by_cases zero : word = 0
 · subst word
   change Evm.run (no++(.jump yes.length::yes)) initial = .ok final skip at ran
   have whole : (Evm.run no initial).bind
      (fun m k => Evm.exec (.jump yes.length::yes) k m) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run no initial with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok middle pending =>
     obtain ⟨output,done,frame,trace⟩ := right.reflect input initial middle pending represented actual
     rw [actual,done] at whole
     have exactTail : Evm.exec (.jump yes.length::yes) 0 middle = .ok middle 0 := Evm.exec_length yes middle
     change Evm.exec (.jump yes.length::yes) 0 middle = .ok final skip at whole
     rw [exactTail] at whole
     have parts := Evm.Out.ok.inj whole
     exact ⟨output,parts.2.symm,parts.1.symm.trans frame,by simpa only [if_pos rfl] using trace⟩
 · rw [nonzero_tail word yes no initial zero] at ran
   obtain ⟨output,done,frame,trace⟩ := left.reflect input initial final skip represented ran
   exact ⟨output,done,frame,by simpa only [if_neg zero] using trace⟩

/-- Only the chosen arm's actual structured trace is required. In particular,
the other arm may fault on this input without blocking the selected branch. -/
theorem tail_forward {a b : Backend.Block} {yes no : List Evm.Instr}
 (left : FramedLoweringCertificate yes a) (right : FramedLoweringCertificate no b)
 (word : Scalar.Word) (input output : Stack) (initial : Evm.Machine)
 (represented : initial.stack = irStack input)
 (trace : if word = 0 then StructuredExec b input output else StructuredExec a input output) :
 Evm.run (MachineControl.branchTail yes no) {initial with stack := coreWord word::initial.stack} =
 .ok {initial with stack := irStack output} 0 := by
 by_cases zero : word = 0
 · subst word
   have arm := (right.success input output initial represented).mpr (by simpa only [if_pos rfl] using trace)
   change Evm.run (no++(.jump yes.length::yes)) initial = _
   rw [Evm.run_append_ok arm]
   exact Evm.exec_length yes _
 · rw [nonzero_tail word yes no initial zero]
   exact (left.success input output initial represented).mpr (by simpa only [if_neg zero] using trace)

/-- info: 'Solidity.Yul.Compilation.FramedBranch.nonzero_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nonzero_tail
/-- info: 'Solidity.Yul.Compilation.FramedBranch.tail_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tail_reflect
/-- info: 'Solidity.Yul.Compilation.FramedBranch.tail_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tail_forward
end Solidity.Yul.Compilation.FramedBranch

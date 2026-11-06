import Solidity.Yul.Compilation.SignedExecution
import Solidity.Yul.Compilation.WordClosedExecution
/-! Exact existing signed-selector execution on the COMPLETE numeric stack.
Actual signed success producers and word refusal are reused; no new signed
semantics, selector/admission or arbitrary caller suffix failure law is added.
Native/charged/capacity and full Source/G24 adequacy remain separate. -/
namespace Solidity.Yul.Compilation.SignedClosedExecution
open Backend Scalar MachineAdapter

/-- The four added signed operators require two actual numeric operands.
Other selected cases reuse the exact existing word refusal theorem. -/
theorem step_failure (i : Backend.Instr) (j : Evm.Instr)
 (selected : SignedMachine.selectInstr i = some j) (xs : Stack)
 (failed : Scalar.step i xs = none) (m : Evm.Machine) :
 j.step {m with stack := xs.map coreWord} = .fault := by
 cases i with
 | push width bytes => cases failed
 | op opcode =>
   cases opcode <;> try (refine WordClosedExecution.step_failure _ j ?_ xs failed m; exact selected)
   all_goals cases selected
   all_goals cases xs with
     | nil => rfl
     | cons a xs =>
       cases xs with
       | nil => rfl
       | cons b xs => cases failed

/-- Exact selected one-step result; success reuses the general word theorem. -/
theorem step (i : Backend.Instr) (j : Evm.Instr)
 (selected : SignedMachine.selectInstr i = some j) (xs : Stack) (m : Evm.Machine) :
 j.step {m with stack := xs.map coreWord} =
 match Scalar.step i xs with
 | none => .fault
 | some ys => .ok {m with stack := ys.map coreWord} 0 := by
 cases actual : Scalar.step i xs with
 | none => exact step_failure i j selected xs actual m
 | some ys =>
   simpa only [List.append_nil] using SignedExecution.step i j selected xs ys actual m []

/-- Exact whole selected program, including failures after successful prefixes.
The model still erases PUSH widths and has no 1024-word capacity enforcement. -/
theorem run (p : Backend.Program) (q : List Evm.Instr)
 (selected : SignedMachine.selectCode p = some q) (input : Stack) (m : Evm.Machine) :
 Evm.run q {m with stack := input.map coreWord} =
 match Scalar.run p input with
 | none => .fault
 | some output => .ok {m with stack := output.map coreWord} 0 := by
 induction p generalizing q input with
 | nil => cases selected; rfl
 | cons i p ih =>
   obtain ⟨j,hi,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨target,hp,same⟩ := Option.map_eq_some_iff.mp rest
   subst q
   rw [Evm.run,Evm.exec_cons_zero,step i j hi input m]
   cases actual : Scalar.step i input with
   | none => rw [Scalar.run,actual]; rfl
   | some middle =>
     rw [Scalar.run,actual]
     simp only [Option.bind_some,Evm.Out.ok_bind]
     exact ih target hp middle

theorem failure_iff (p : Backend.Program) (q : List Evm.Instr)
 (selected : SignedMachine.selectCode p = some q) (input : Stack) (m : Evm.Machine) :
 Evm.run q {m with stack := input.map coreWord} = .fault ↔ Scalar.run p input = none := by
 rw [run p q selected input m]
 cases Scalar.run p input <;> simp only [reduceCtorEq]

theorem success_iff (p : Backend.Program) (q : List Evm.Instr)
 (selected : SignedMachine.selectCode p = some q) (input output : Stack) (m : Evm.Machine) :
 Evm.run q {m with stack := input.map coreWord} = .ok {m with stack := output.map coreWord} 0 ↔
 Scalar.run p input = some output := by
 rw [run p q selected input m]
 cases actual : Scalar.run p input with
 | none => simp only [reduceCtorEq]
 | some found =>
   constructor
   · intro same
     have stacks : found.map coreWord = output.map coreWord :=
       congrArg Evm.Machine.stack (Evm.Out.ok.inj same).1
     have equal : found = output := (List.map_inj_right (fun _ _ h => coreWord_injective h)).mp stacks
     exact congrArg some equal
   · intro same
     cases Option.some.inj same
     rfl


/-- info: 'Solidity.Yul.Compilation.SignedClosedExecution.step_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_failure

/-- info: 'Solidity.Yul.Compilation.SignedClosedExecution.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step

/-- info: 'Solidity.Yul.Compilation.SignedClosedExecution.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run

/-- info: 'Solidity.Yul.Compilation.SignedClosedExecution.failure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms failure_iff

/-- info: 'Solidity.Yul.Compilation.SignedClosedExecution.success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms success_iff
end Solidity.Yul.Compilation.SignedClosedExecution

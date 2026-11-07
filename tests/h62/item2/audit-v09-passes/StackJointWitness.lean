import tests.h62.item2.«audit-v09-passes».P20InterfaceV2Controls
import Solidity.Backend.Passes.Stack

/-! Regression: a compiler preserving only the empty operand stack must not
satisfy saved-tail transport. The same concrete checked store jointly supplies
all hypotheses of the three public frozen Stack theorems, for every saved tail,
with full Input and G24 Rep. A general observation lemma rejects a different
returned tail. This covers three public premise bundles only; private helpers,
other compiler branches, gas/fork and whole-audit adequacy remain open. -/
namespace Solidity.Backend.Passes.AuditStack
open Evm Evm.Compiler
open Yul.Compilation.P20.InterfaceV2.Controls

/-- One populated tuple supplies the common hypotheses simultaneously. -/
theorem premises : compilation.Input 1 64 bases target machine ∧
    Evm.Prog.pays program = false ∧ program.run target = .ok (output target) :=
  ⟨joint_input, rfl, source_run target⟩

/-- The arbitrary-tail Input uses that exact original state, frame and map. -/
theorem input_tail (tail : List Word) :
    compilation.Input 1 64 bases target {machine with stack := tail} :=
  compilation_input_stack compilation premises.1 tail

theorem input_iff (tail : List Word) :
    compilation.Input 1 64 bases target {machine with stack := tail} ↔
    compilation.Input 1 64 bases target machine :=
  compilation_input_stack_iff compilation tail

/-- Source success and all observations hold for every actual saved tail. -/
theorem joint (tail : List Word) : ∃ final : Machine,
    compilation.Input 1 64 bases target {machine with stack := tail} ∧
    Evm.Prog.pays program = false ∧ program.run target = .ok (output target) ∧
    Evm.run compilation.code {machine with stack := tail} = .ok final 0 ∧
    final.stack = tail ∧
    compilation.Rep (1 + Evm.Prog.pushes program) 64 bases target
      {machine with stack := tail} (output target).st final := by
  obtain ⟨final, ran, stack, represented⟩ :=
    compilation_success_tail compilation premises.1 premises.2.1 premises.2.2 tail
  exact ⟨final, input_tail tail, premises.2.1, premises.2.2, ran, stack, represented⟩

/-- General exact-stack discrimination, independent of the fixture. -/
theorem success_stack_refuses (code : List Evm.Instr) (initial actual fake : Machine)
    (tail wrong : List Word) (ran : Evm.run code initial = .ok actual 0)
    (stack : actual.stack = tail) (different : tail ≠ wrong) :
    Evm.run code initial ≠ .ok {fake with stack := wrong} 0 := by
  intro forged
  have same := (Evm.Out.ok.inj (ran.symm.trans forged)).1
  have observed := congrArg Machine.stack same
  exact different (stack.symm.trans observed)

/-- No forged machine can hide corruption of any saved tail in the fixture. -/
theorem wrong_tail_refused (tail wrong : List Word) (different : tail ≠ wrong)
    (fake : Machine) :
    Evm.run compilation.code {machine with stack := tail} ≠
      .ok {fake with stack := wrong} 0 := by
  obtain ⟨actual, _, _, _, ran, stack, _⟩ := joint tail
  exact success_stack_refuses compilation.code {machine with stack := tail}
    actual fake tail wrong ran stack different

/-- info: 'Solidity.Backend.Passes.AuditStack.premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStack.premises
/-- info: 'Solidity.Backend.Passes.AuditStack.input_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStack.input_tail
/-- info: 'Solidity.Backend.Passes.AuditStack.input_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStack.input_iff
/-- info: 'Solidity.Backend.Passes.AuditStack.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStack.joint
/-- info: 'Solidity.Backend.Passes.AuditStack.success_stack_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStack.success_stack_refuses
/-- info: 'Solidity.Backend.Passes.AuditStack.wrong_tail_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditStack.wrong_tail_refused
end Solidity.Backend.Passes.AuditStack

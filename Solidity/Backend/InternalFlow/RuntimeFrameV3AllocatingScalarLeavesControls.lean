import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingGuardedTurn

/-! Populated exact scalar-leaf and allocating-root receipts. Wrong literals,
operators and destinations are actual syntax inputs, not semantic hypotheses. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev A := RefTy.array (.prim .uint)

theorem guard_checked {C : Contract} {R : RefTy} :
 checkGuard (guard (C:=C) (R:=R))=some ⟨rfl⟩ := by rfl

theorem zero_checked {C : Contract} {R : RefTy} :
 checkZero (zero (C:=C) (R:=R))=some ⟨rfl⟩ := by rfl

theorem increment_checked {C : Contract} {R : RefTy} :
 checkIncrement (increment (C:=C) (R:=R))=some ⟨rfl⟩ := by rfl

theorem wrong_guard_operator {C : Contract} {R : RefTy} :
 checkGuard (.binop .ge rfl rfl (.simple (.local (.there .here))) (.simple (.lit 0 rfl)) : Val C (Frame R) .bool)=none := by rfl

theorem wrong_guard_slot {C : Contract} {R : RefTy} :
 checkGuard (.binop .gt rfl rfl (.simple (.local .here)) (.simple (.lit 0 rfl)) : Val C (Frame R) .bool)=none := by rfl

theorem wrong_guard_literal {C : Contract} {R : RefTy} :
 checkGuard (.binop .gt rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 rfl)) : Val C (Frame R) .bool)=none := by rfl

theorem wrong_zero_value {C : Contract} {R : RefTy} :
 checkZero (.assignLocal .here (.simple (.lit 1 rfl)) : Stmt C (Frame R) (Frame R))=none := by rfl

theorem wrong_destination {C : Contract} {R : RefTy} :
 checkZero (.assignLocal (.there .here) (.simple (.lit 0 rfl)) : Stmt C (Frame R) (Frame R))=none := by rfl

theorem wrong_increment_operator {C : Contract} {R : RefTy} :
 checkIncrement (.assignLocal .here (.binop .sub rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl))) :
 Stmt C (Frame R) (Frame R))=none := by rfl

theorem wrong_increment_value {C : Contract} {R : RefTy} :
 checkIncrement (.assignLocal .here (.binop .add rfl rfl (.simple (.local .here)) (.simple (.lit 2 rfl))) :
 Stmt C (Frame R) (Frame R))=none := by rfl

theorem actual_root {C : Contract} (depth : Nat) (child : Unit → Prog C (Frame A) (Frame A)) :
 AllocatingGuardedTurn.read A (AllocatingScalarSource.step A rfl depth child)=
 some ⟨AllocatingScalarSource.continuation A rfl depth child,rfl⟩ := by rfl

theorem actual_tail {C : Contract} {R : RefTy} :
 AllocatingGuardedTurn.checkTail (.cons increment .nil : Prog C (Frame R) (Frame R))=some ⟨rfl⟩ := by rfl

theorem extra_tail {C : Contract} {R : RefTy} :
 AllocatingGuardedTurn.checkTail (.cons increment (.cons .assumeFalse .nil) : Prog C (Frame R) (Frame R))=none := by rfl

theorem wrong_alternative {C : Contract} (depth : Nat) (child : Unit → Prog C (Frame A) (Frame A)) :
 AllocatingGuardedTurn.read A (.cons (.ite guard
 (.cons AllocatingScalarSource.allocate (AllocatingScalarSource.continuation A rfl depth child))
 (.cons .revert .nil)) .nil)=none := by rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.guard_checked' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.guard_checked
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.zero_checked' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.zero_checked
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.increment_checked' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.increment_checked
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_guard_operator' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_guard_operator
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_guard_slot' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_guard_slot
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_guard_literal' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_guard_literal
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_zero_value' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_zero_value
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_destination' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_destination
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_increment_operator' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_increment_operator
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_increment_value' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_increment_value
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.actual_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.actual_root
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.actual_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.actual_tail
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.extra_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.extra_tail
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_alternative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarLeaves.Controls.wrong_alternative

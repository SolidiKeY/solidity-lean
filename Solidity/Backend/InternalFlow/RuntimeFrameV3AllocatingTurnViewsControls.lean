import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingTurnViews

/-! Actual allocating-turn shape receipts, including preserved unrecognized
continuations and alternative branches. These are syntax receipts only. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev A := RefTy.array (.prim .uint)

theorem actual_turn {C : Contract} (depth : Nat)
 (child : Unit → Prog C (Frame A) (Frame A)) :
 read (AllocatingScalarSource.step A rfl depth child)=
 some ⟨guard,AllocatingScalarSource.continuation A rfl depth child,.cons zero .nil,rfl⟩ := by rfl

theorem nil_refused {C : Contract} {Γ : Ctx} : read (.nil : Prog C Γ Γ)=none := by rfl

theorem nonconditional_refused {C : Contract} {Γ : Ctx} :
 read (.cons .revert .nil : Prog C Γ Γ)=none := by rfl

theorem extra_root_refused {C : Contract} (depth : Nat)
 (child : Unit → Prog C (Frame A) (Frame A)) :
 read (.cons (.ite guard
   (.cons AllocatingScalarSource.allocate (AllocatingScalarSource.continuation A rfl depth child))
   (.cons zero .nil)) (.cons .assumeFalse .nil))=none := by rfl

theorem missing_allocation_refused {C : Contract} :
 read (.cons (.ite guard (.cons .revert .nil) (.cons zero .nil)) .nil :
 Prog C (Frame A) (Frame A))=none := by rfl

theorem empty_positive_refused {C : Contract} :
 read (.cons (.ite guard .nil (.cons zero .nil)) .nil :
 Prog C (Frame A) (Frame A))=none := by rfl

theorem continuation_preserved {C : Contract}
 (condition : Val C (Frame A) .bool)
 (continuation alternative : Prog C (Frame A) (Frame A)) :
 read (.cons (.ite condition (.cons AllocatingScalarSource.allocate continuation) alternative) .nil)=
 some ⟨condition,continuation,alternative,rfl⟩ := by rfl

theorem extended_branch_refused {C : Contract} :
 read (.cons (.ite guard
   (.cons AllocatingScalarSource.allocate (.cons (.declLocal .uint (.user "extra") none) .nil))
   (.cons zero .nil)) .nil : Prog C (Frame A) (Frame A))=none := by rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.actual_turn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.actual_turn
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.nil_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.nil_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.nonconditional_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.nonconditional_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.extra_root_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.extra_root_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.missing_allocation_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.missing_allocation_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.empty_positive_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.empty_positive_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.continuation_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.continuation_preserved

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.extended_branch_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingTurnViews.Controls.extended_branch_refused

import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScopedCheck
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingRecursiveCheckControls

/-! Actual scoped-family checks at the fixed original reference A, with
arbitrary contract, quotation index, decorator primitive and name. These
receipts do not assert completeness for other decoration profiles. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev A := RefTy.array (.prim .uint)

theorem decorated {C : Contract} (body : Prog C (Frame A) (Frame A)) (p : PrimTy) (name : Var) :
 AllocatingScopeView.read (ScopedSource.decorate body p name)=some ⟨body,p,name,rfl⟩ := by rfl

theorem canonical_checked {C : Contract} (p : PrimTy) (name : Var) (depth : Nat) :
 certify A rfl depth (AllocatingSourceCertificate.scopedBody (C:=C) A rfl p name depth)=
 some ⟨AllocatingSourceCertificate.scoped_certificate A rfl p name depth⟩ := by
 induction depth with
 | zero => rfl
 | succ depth ih =>
   change certify A rfl (depth+1)
     (ScopedSource.decorate (AllocatingScalarSource.step A rfl depth
       (fun _ => AllocatingSourceCertificate.scopedBody A rfl p name depth)) p name)=_
   simp only [certify,decorated,AllocatingRecursiveCheck.Controls.actual_head,
     bind,Option.bind_some,dif_pos True.intro,ih,pure]

theorem initialized_refused {C : Contract} (body : Prog C (Frame A) (Frame A)) :
 AllocatingScopeView.read (.cons (.block (.cons (.block body)
   (.cons (.declLocal .bool (.user "unused") (some (.simple (.bool true)))) .nil))) .nil)=none := by rfl

theorem reordered_refused {C : Contract} :
 AllocatingScopeView.read (.cons (.block (.cons (.declLocal .bool (.user "unused") none)
   (.cons (.block .nil) .nil))) .nil : Prog C (Frame A) (Frame A))=none := by rfl

theorem extra_root_refused {C : Contract} (body : Prog C (Frame A) (Frame A)) :
 AllocatingScopeView.read (.cons (.block (.cons (.block body)
   (.cons (.declLocal .bool (.user "unused") none) .nil))) (.cons .assumeFalse .nil))=none := by rfl

theorem unscoped_turn_refused {C : Contract} (depth : Nat) (child : Unit → Prog C (Frame A) (Frame A)) :
 certify A rfl (depth+1) (AllocatingScalarSource.step A rfl depth child)=none := by rfl

theorem wrong_index {C : Contract} (p : PrimTy) (name : Var) (depth : Nat)
 (child : Unit → Prog C (Frame A) (Frame A)) :
 certify A rfl (depth+1) (ScopedSource.decorate (AllocatingScalarSource.step A rfl (depth+1) child) p name)=none := by
 simp only [certify,decorated,AllocatingRecursiveCheck.Controls.actual_head,bind,Option.bind_some,
   Nat.add_one_ne_self,dif_neg (by decide : ¬False)]

theorem wrong_child {C : Contract} (p : PrimTy) (name : Var) :
 certify A rfl 1 (ScopedSource.decorate
   (AllocatingScalarSource.step (C:=C) A rfl 0 (fun _ => .cons .revert .nil)) p name)=none := by
 simp only [certify,decorated,AllocatingRecursiveCheck.Controls.actual_head,bind,Option.bind_some,dif_pos True.intro]
 rfl

theorem decorated_base_refused {C : Contract} (p : PrimTy) (name : Var) :
 certify A rfl 0 (ScopedSource.decorate (Prog.recBase : Prog C (Frame A) (Frame A)) p name)=none := by rfl

theorem open_inner_refused {C : Contract} :
 AllocatingScopeView.read (.cons (.block (.cons
   (.block (.cons (.declLocal .bool (.user "inner") none) .nil))
   (.cons (.declLocal .bool (.user "unused") none) .nil))) .nil : Prog C (Frame A) (Frame A))=none := by rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.decorated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.decorated
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.canonical_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.canonical_checked
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.initialized_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.initialized_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.reordered_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.reordered_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.extra_root_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.extra_root_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.unscoped_turn_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.unscoped_turn_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.wrong_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.wrong_index
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.wrong_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.wrong_child
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.decorated_base_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.decorated_base_refused

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.open_inner_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedCheck.Controls.open_inner_refused

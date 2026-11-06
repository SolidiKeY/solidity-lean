import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingRecursiveCheck
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarLeavesControls

/-! Populated original argument/return and full recursive syntax receipts.
All quotation indices are covered constructively; malformed children and
indices are actual rejected syntax. These are source certificates, not a
public compiler selector or approved-domain producer. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev A := RefTy.array (.prim .uint)

theorem next_checked {C : Contract} :
 AllocatingCallLeaves.checkNext (R:=A) rfl (next A rfl (C:=C))=some ⟨rfl⟩ := by rfl

theorem result_checked {R : RefTy} : AllocatingCallLeaves.checkResult (result R)=some ⟨rfl⟩ := by rfl

def arguments {C : Contract} (aliasName countName : Var) (expression : Val C (Frame A) .uint) :
 Args C (Frame A) (Parameters A) :=
 .snoc (.snocMemory .nil A aliasName (.var (.there (.there .here)) rfl)) .uint countName expression

def decrement {C : Contract} : Val C (Frame A) .uint :=
 .binop .sub rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 rfl))

theorem wrong_alias_name {C : Contract} :
 AllocatingCallLeaves.checkNext (R:=A) rfl (arguments (C:=C) (.user "different") (.user "count") decrement)=none := by rfl

theorem wrong_count_name {C : Contract} :
 AllocatingCallLeaves.checkNext (R:=A) rfl (arguments (C:=C) (.user "alias") (.user "different") decrement)=none := by rfl

theorem wrong_argument_slot {C : Contract} :
 AllocatingCallLeaves.checkNext (R:=A) rfl (arguments (C:=C) (.user "alias") (.user "count")
 (.binop .sub rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl))))=none := by rfl

theorem wrong_argument_operator {C : Contract} :
 AllocatingCallLeaves.checkNext (R:=A) rfl (arguments (C:=C) (.user "alias") (.user "count")
 (.binop .add rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 rfl))))=none := by rfl

theorem wrong_argument_literal {C : Contract} :
 AllocatingCallLeaves.checkNext (R:=A) rfl (arguments (C:=C) (.user "alias") (.user "count")
 (.binop .sub rfl rfl (.simple (.local (.there .here))) (.simple (.lit 2 rfl))))=none := by rfl

theorem wrong_result_name {R : RefTy} :
 AllocatingCallLeaves.checkResult (.val .uint (.user "different") (some (.here : Idx (Frame R) (.val .uint))))=none := by rfl

theorem missing_destination {R : RefTy} :
 AllocatingCallLeaves.checkResult (.val .uint (.user "result") (none : Option (Idx (Frame R) (.val .uint))))=none := by rfl

theorem wrong_destination {R : RefTy} :
 AllocatingCallLeaves.checkResult (.val .uint (.user "result") (some (.there .here : Idx (Frame R) (.val .uint))))=none := by rfl

theorem actual_head {C : Contract} (depth : Nat) (child : Unit → Prog C (Frame A) (Frame A)) :
 readHead A rfl (AllocatingScalarSource.step A rfl depth child)=some ⟨depth,child,rfl⟩ := by
 simp only [readHead,AllocatingScalarLeaves.Controls.actual_root,bind,Option.bind_some,
   AllocatingSourceViews.readClosedCons,AllocatingSourceViews.readCons,Option.map_some,
   AllocatingSourceViews.closeCons,AllocatingScalarSource.continuation,
   AllocatingScalarLeaves.Controls.actual_tail,AllocatingHeadViews.readRecursiveCall,
   AllocatingHeadViews.read,closeCall,dif_pos True.intro,next_checked,result_checked,pure,assemble]

theorem canonical_checked {C : Contract} (depth : Nat) :
 certify A rfl depth (AllocatingScalarSource.body (C:=C) A rfl depth)=
 some ⟨AllocatingSourceCertificate.canonical A rfl depth⟩ := by
 induction depth with
 | zero => rfl
 | succ depth ih =>
   change certify A rfl (depth+1)
     (AllocatingScalarSource.step A rfl depth (fun _ => AllocatingScalarSource.body A rfl depth))=_
   simp only [certify,actual_head,bind,Option.bind_some,dif_pos True.intro,ih,pure]

theorem wrong_index {C : Contract} (depth : Nat) (child : Unit → Prog C (Frame A) (Frame A)) :
 certify A rfl (depth+1) (AllocatingScalarSource.step A rfl (depth+1) child)=none := by
 simp only [certify,actual_head,bind,Option.bind_some,Nat.add_one_ne_self,dif_neg (by decide : ¬False)]

theorem wrong_child {C : Contract} :
 certify A rfl 1 (AllocatingScalarSource.step (C:=C) A rfl 0 (fun _ => .cons .revert .nil))=none := by
 simp only [certify,actual_head,bind,Option.bind_some,dif_pos True.intro]
 rfl

theorem malformed_base {C : Contract} :
 certify A rfl 0 (.nil : Prog C (Frame A) (Frame A))=none := by rfl

def wrongSignature {C : Contract} (depth : Nat) : Prog C (Frame A) (Frame A) :=
 .cons (.ite guard (.cons AllocatingScalarSource.allocate
   (.cons (.callRec "allocatingScalar" depth .nil .none (fun _ => .nil)) (.cons increment .nil)))
   (.cons zero .nil)) .nil

theorem wrong_signature {C : Contract} (depth : Nat) : readHead A rfl (wrongSignature (C:=C) depth)=none := by rfl

theorem guarded_continuation {C : Contract} (continuation : Prog C (Frame A) (Frame A)) :
 AllocatingGuardedTurn.read A
   (.cons (.ite guard (.cons AllocatingScalarSource.allocate continuation) (.cons zero .nil)) .nil)=
 some ⟨continuation,rfl⟩ := by rfl

def wrongFunction {C : Contract} (depth : Nat) (child : Unit → Prog C (Frame A) (Frame A)) :
 Prog C (Frame A) (Frame A) :=
 .cons (.ite guard (.cons AllocatingScalarSource.allocate
   (.cons (.callRec "different" depth (next A rfl) (result A) child) (.cons increment .nil)))
   (.cons zero .nil)) .nil

theorem wrong_function_name {C : Contract} (depth : Nat) (child : Unit → Prog C (Frame A) (Frame A)) :
 readHead A rfl (wrongFunction depth child)=none := by
 simp only [wrongFunction,readHead,guarded_continuation,bind,Option.bind_some,
     AllocatingSourceViews.readClosedCons,AllocatingSourceViews.readCons,Option.map_some,
     AllocatingSourceViews.closeCons,AllocatingScalarLeaves.Controls.actual_tail,
     AllocatingHeadViews.readRecursiveCall,AllocatingHeadViews.read,closeCall,
     dif_pos True.intro,next_checked,result_checked,dif_neg (by decide : ("different" : Name)≠"allocatingScalar")]

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.next_checked' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.next_checked
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.result_checked' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.result_checked
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_alias_name' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_alias_name
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_count_name' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_count_name
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_argument_slot' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_argument_slot
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_argument_operator' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_argument_operator
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_argument_literal' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_argument_literal
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_result_name' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_result_name
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.missing_destination' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.missing_destination
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_destination' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_destination
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.actual_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.actual_head
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.canonical_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.canonical_checked
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_index
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_child
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.malformed_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.malformed_base
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_signature' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_signature

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.guarded_continuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.guarded_continuation
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_function_name' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingRecursiveCheck.Controls.wrong_function_name

import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingDeclarationCheck
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarTarget

/-! Actual typed head-view and allocation-checker receipts. The allocation
leaf remains linked to its existing public compiler selection. Complete
recursive-head decoding and whole-call selection remain separate duties. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem conditional_root {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R)) :
 readConditional (.ite guard
   (.cons AllocatingScalarSource.allocate (AllocatingScalarSource.continuation R hm depth child))
   (.cons zero .nil) : Stmt C (Frame R) (Frame R))=
 some ⟨Frame R,Frame R,guard,
   .cons AllocatingScalarSource.allocate (AllocatingScalarSource.continuation R hm depth child),
   .cons zero .nil,rfl,HEq.rfl⟩ := by rfl

theorem recursive_root {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R)) :
 readRecursiveCall (.callRec "allocatingScalar" depth (next R hm) (result R) child)=
 some ⟨Parameters R,[.val .uint],"allocatingScalar",depth,next R hm,result R,child,rfl⟩ := by rfl

theorem unsupported_refused {C : Contract} {Γ : Ctx} : read (.revert : Stmt C Γ Γ)=none := by rfl

theorem allocation_root {C : Contract} {Γ : Ctx} :
 AllocatingDeclarationCheck.check (AllocatingDeclarationCheck.allocation (C:=C) (Γ:=Γ))=some ⟨rfl⟩ := by rfl

def candidate {C : Contract} {Γ : Ctx} (number : Int) (valid : PrimTy.uint.inRange number=true) (name : Var) : Stmt C Γ Γ :=
 .block (.cons (.declMem AllocatingDeclarationCheck.Array name (some (.newArr (.lit number valid) rfl)) rfl rfl) .nil)

theorem wrong_length {C : Contract} {Γ : Ctx} :
 AllocatingDeclarationCheck.check (candidate (C:=C) (Γ:=Γ) 4 rfl (.user "private"))=none := by rfl

theorem wrong_name {C : Contract} {Γ : Ctx} :
 AllocatingDeclarationCheck.check (candidate (C:=C) (Γ:=Γ) 3 rfl (.user "different"))=none := by rfl

def wrongReference {C : Contract} {Γ : Ctx} : Stmt C Γ Γ :=
 .block (.cons (.declMem (.array (.prim .uint)) (.user "private") (some (.newArr (.lit 3 rfl) rfl)) rfl rfl) .nil)

theorem wrong_reference {C : Contract} {Γ : Ctx} :
 AllocatingDeclarationCheck.check (wrongReference (C:=C) (Γ:=Γ))=none := by rfl

def uninitialized {C : Contract} {Γ : Ctx} : Stmt C Γ Γ :=
 .block (.cons (.declMem AllocatingDeclarationCheck.Array (.user "private") none rfl rfl) .nil)

theorem missing_initializer {C : Contract} {Γ : Ctx} :
 AllocatingDeclarationCheck.check (uninitialized (C:=C) (Γ:=Γ))=none := by rfl

def extraStatement {C : Contract} {Γ : Ctx} : Stmt C Γ Γ :=
 .block (.cons (.declMem AllocatingDeclarationCheck.Array (.user "private")
   (some (.newArr (.lit 3 rfl) rfl)) rfl rfl) (.cons .assumeFalse .nil))

theorem extra_statement {C : Contract} {Γ : Ctx} :
 AllocatingDeclarationCheck.check (extraStatement (C:=C) (Γ:=Γ))=none := by rfl

theorem compiler_link :
 AllocatingDeclarationCheck.check (AllocatingScalarSource.allocate (C:=CountdownWitness.P.C) (R:=CountdownWitness.A))=some ⟨rfl⟩ ∧
 Memory.compileStmt 2 AllocatingScalarTarget.F (AllocatingScalarSource.allocate (C:=CountdownWitness.P.C) (R:=CountdownWitness.A))=
   some AllocatingScalarTarget.selected :=
 ⟨allocation_root,AllocatingScalarTarget.public_selection⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.conditional_root' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.conditional_root
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.recursive_root' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.recursive_root
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.unsupported_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.unsupported_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.allocation_root' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.allocation_root
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.wrong_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.wrong_length
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.wrong_name' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.wrong_name
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.wrong_reference' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.wrong_reference
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.missing_initializer' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.missing_initializer
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.extra_statement' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.extra_statement
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.compiler_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHeadViews.Controls.compiler_link

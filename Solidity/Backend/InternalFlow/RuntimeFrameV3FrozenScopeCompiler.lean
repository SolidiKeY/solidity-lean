import Solidity.Backend.InternalFlow.RuntimeFrameV3FrozenScopeFamily
import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveScopeCompiler

/-! Actual public selection for the exact frozen source constructor family.
The checked semantic-body and public value-emitter receipts remain explicit;
no target execution or approved-domain witness is a constructor premise. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeCompiler
open Evm Evm.Memory ScalarRecursiveSource

def source {C : Contract} {Γ : Ctx} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (reference : Idx Γ (.mem R)) (count : Val C Γ .uint) (destination : Idx Γ (.val .uint))
 (function : Name) (p : PrimTy) (name : Var) (depth : Nat) : Stmt C Γ Γ :=
 InterfaceV1.recursiveSource function (DisjointScalarEntry.args hm reference count)
   (.val .uint (.user "result") (some destination)) (FrozenScopeFamily.step R hm p name) depth

def selected {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {count : Val C Γ .uint} (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted)
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 (function : Name) (p : PrimTy) (name : Var) (depth : Nat) :
 RecursiveScopeCompiler.Selected b c frame pointer bottom F (source hm reference count destination function p name depth) :=
 RecursiveScopeCompiler.make hm reference count destination (.user "alias") (.user "count") (.user "result") function depth
   (fun _ => FrozenScopeFamily.body R hm p name depth)
   (FrozenScopeFamily.body_run R hm p name depth) (FrozenScopeFamily.recognized R hm p name depth) emitted root

theorem selected_root {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {count : Val C Γ .uint} (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted)
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 (function : Name) (p : PrimTy) (name : Var) (depth : Nat) :
 RecursiveScopeCompiler.compile b c frame pointer bottom F (source hm reference count destination function p name depth)=
 some (selected emitted root hm reference destination function p name depth) :=
 RecursiveScopeCompiler.compile_call hm reference count destination (.user "alias") (.user "count") (.user "result") function depth
   (fun _ => FrozenScopeFamily.body R hm p name depth)
   (FrozenScopeFamily.body_run R hm p name depth) (FrozenScopeFamily.recognized R hm p name depth) emitted root

/-- This same existing data plan selects one code image at every index. -/
def plan {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {count : Val C Γ .uint} (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint)) := ScalarDemand.plan emitted reference destination

theorem plan_eq {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {count : Val C Γ .uint} (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted)
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 (function : Name) (p : PrimTy) (name : Var) (depth : Nat) :
 (selected emitted root hm reference destination function p name depth).plan=(plan emitted reference destination).at depth := rfl

theorem returns {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {count : Val C Γ .uint} (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted) (below : bottom<pointer)
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 (function : Name) (p : PrimTy) (name : Var) (depth : Nat) :
 InterfaceV1.ReturnClaim b F (source hm reference count destination function p name depth)
   ((plan emitted reference destination).at depth) :=
 (selected emitted root hm reference destination function p name depth).returns below

theorem bare_revert {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {count : Val C Γ .uint} (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted) (below : bottom<pointer)
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 (function : Name) (p : PrimTy) (name : Var) (depth : Nat) :
 InterfaceV1.BareRevertClaim b F (source hm reference count destination function p name depth)
   ((plan emitted reference destination).at depth) :=
 (selected emitted root hm reference destination function p name depth).bare_revert below

end Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeCompiler

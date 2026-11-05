import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveScopeLaws
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveAgreement

/-! The exact frozen recursiveSource constructor family with scoped scalar
turns and the UNCHANGED Prog.recBase. No alternative base, evaluator or source
observation index is substituted. Profile/target duties remain separate. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeFamily
open Evm Evm.Memory ScalarRecursiveSource

def step {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (p : PrimTy) (name : Var)
 (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R)) : Prog C (Frame R) (Frame R) :=
 ScopedSource.decorate (ScalarRecursiveSource.step R hm depth child) p name

def body {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (p : PrimTy) (name : Var)
 (depth : Nat) : Prog C (Frame R) (Frame R) :=
 recUnroll Prog.recBase (step R hm p name) depth

theorem body_run {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (p : PrimTy) (name : Var)
 (depth : Nat) : (body (C:=C) R hm p name depth).runR=(ScalarRecursiveSource.body R hm depth).runR := by
 induction depth with
 | zero => rfl
 | succ depth ih =>
   exact (ScopedSource.decorate_run
     (ScalarRecursiveSource.step R hm depth (fun _ => body R hm p name depth)) p name).trans
     (RecursiveScopes.step_congr hm depth (fun _ => body R hm p name depth)
       (fun _ => ScalarRecursiveSource.body R hm depth) ih)

theorem recognized {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (p : PrimTy) (name : Var)
 (depth : Nat) : RecursiveScopes.check (C:=C) R hm depth (body R hm p name depth)=some ⟨body_run R hm p name depth⟩ := by
 induction depth with
 | zero => rfl
 | succ depth ih =>
   change RecursiveScopes.turn R hm depth _
     (RecursiveScopes.strip (ScopedSource.decorate
       (ScalarRecursiveSource.step R hm depth (fun _ => body R hm p name depth)) p name))
     (RecursiveScopes.check R hm depth)=_
   rw [RecursiveScopes.strip_decorate]
   simp only [RecursiveScopes.turn,ScalarSourceCheck.read_step,bind,Option.bind,ScalarSourceCheck.canonicalHead,pure]
   rw [dif_pos True.intro,ih]

/-- Full outcome equality for the actual frozen family, with the same caller,
arguments and return binder; not merely agreement after assumed success. -/
theorem source_run {C : Contract} {Γ Δ : Ctx} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (p : PrimTy) (name : Var) (function : Name) (args : Args C Γ (RecursiveSource.Parameters R))
 (ret : CallRet Γ [.val .uint] Δ) (depth : Nat) :
 (InterfaceV1.recursiveSource function args ret (step R hm p name) depth).runR=
 (InterfaceV1.recursiveSource function args ret (ScalarRecursiveSource.step R hm) depth).runR := by
 change TRun.call args ret (body R hm p name depth).ext (body R hm p name depth).runR=
   TRun.call args ret (ScalarRecursiveSource.body R hm depth).ext (ScalarRecursiveSource.body R hm depth).runR
 have scope : (body (C:=C) R hm p name depth).ext=(ScalarRecursiveSource.body (C:=C) R hm depth).ext := Subsingleton.elim _ _
 rw [scope,body_run]

theorem source_coherence {C : Contract} {Γ Δ : Ctx} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (p : PrimTy) (name : Var) (function : Name) (args : Args C Γ (RecursiveSource.Parameters R))
 (ret : CallRet Γ [.val .uint] Δ) :
 InterfaceV1.RecursiveReturnCoherence function args ret (step R hm p name) := by
 intro caller n k left right first second
 exact ScalarRecursiveSource.source_coherence hm function args ret caller n k left right
   ((congrFun (source_run hm p name function args ret n) caller).symm.trans first)
   ((congrFun (source_run hm p name function args ret k) caller).symm.trans second)

end Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeFamily

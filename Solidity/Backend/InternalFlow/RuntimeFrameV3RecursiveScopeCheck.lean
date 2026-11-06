import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCheckLaws
import Solidity.Backend.InternalFlow.RuntimeFrameScopedSource

/-! Full-outcome recognition of optional unused-default-local scopes at each
existing scalar quotation level. Recursion follows only the existing source
index, inspecting the actual child. There is no new evaluator or cutoff. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopes
open ScalarRecursiveSource

/-- Actual recursive child execution, including errors and dependent outputs,
is transported through the existing sequence, branch and native call. -/
theorem step_congr {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (depth : Nat)
 (left right : Unit → Prog C (Frame R) (Frame R)) (same : (left ()).runR=(right ()).runR) :
 (step R hm depth left).runR=(step R hm depth right).runR := by
 change TRun.seq (TRun.ite guard .refl
   (TRun.seq (TRun.call (next R hm) (result R) (left ()).ext (left ()).runR)
     (TRun.seq increment.runR TRun.nil)) .refl (TRun.seq zero.runR TRun.nil)) TRun.nil=
   TRun.seq (TRun.ite guard .refl
   (TRun.seq (TRun.call (next R hm) (result R) (right ()).ext (right ()).runR)
     (TRun.seq increment.runR TRun.nil)) .refl (TRun.seq zero.runR TRun.nil)) TRun.nil
 have scope : (left ()).ext=(right ()).ext := Subsingleton.elim _ _
 rw [scope,same]

structure Stripped {C : Contract} {Γ : Ctx} (source : Prog C Γ Γ) where
 program : Prog C Γ Γ
 same : source.runR=program.runR

/-- Strip at most one exact decorator. A different shape/context is retained
for normal head/base rejection; it is not silently erased. -/
def strip {C : Contract} {Γ : Ctx} (source : Prog C Γ Γ) : Stripped source :=
 match source with
 | .cons (.block (.cons (@Stmt.block _ _ Δ inner) (.cons (.declLocal p name none) .nil))) .nil =>
   if context : Δ=Γ then by
     subst Δ
     exact ⟨inner,ScopedSource.decorate_run inner p name⟩
   else ⟨.cons (.block (.cons (.block inner) (.cons (.declLocal p name none) .nil))) .nil,rfl⟩
 | actual => ⟨actual,rfl⟩

/-- Explicit construction boundary: proof terms refer to this actual core
argument, not an independently expanded stripping expression. -/
def base {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (source : Prog C (Frame R) (Frame R)) (core : Stripped source) :
 Option (PLift (source.runR=(body R hm 0).runR)) := do
 let same ← ScalarSourceCheck.checkBase core.program
 pure ⟨core.same.trans (congrArg Prog.runR same.down)⟩

def turn {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (depth : Nat)
 (source : Prog C (Frame R) (Frame R)) (core : Stripped source)
 (follow : (actual : Prog C (Frame R) (Frame R)) → Option (PLift (actual.runR=(body R hm depth).runR))) :
 Option (PLift (source.runR=(body R hm (depth+1)).runR)) := do
 let head ← ScalarSourceCheck.readHead R hm core.program
 if indexEq : head.index=depth then
   let child ← follow (head.child ())
   pure ⟨core.same.trans ((congrArg Prog.runR head.shape).trans (by
     rw [indexEq]
     exact step_congr hm depth head.child (fun _ => body R hm depth) child.down))⟩
 else none

/-- Complete semantic checking recurses only at the existing lower quotation
index; each actually reached child is supplied to that recursive check. -/
def check {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) :
 (depth : Nat) → (source : Prog C (Frame R) (Frame R)) →
 Option (PLift (source.runR=(body R hm depth).runR))
 | 0, source => base R hm source (strip source)
 | depth+1, source => turn R hm depth source (strip source) (check R hm depth)

/-- An actual new quotation family, with a default local scoped at every
activation, including the exhausted base. All levels remain real callRec. -/
def scopedBody {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (p : PrimTy) (name : Var) : Nat → Prog C (Frame R) (Frame R)
 | 0 => ScopedSource.decorate Prog.recBase p name
 | depth+1 => ScopedSource.decorate (step R hm depth (fun _ => scopedBody R hm p name depth)) p name

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopes

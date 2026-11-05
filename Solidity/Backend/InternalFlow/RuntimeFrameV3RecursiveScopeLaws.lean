import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveScopeCheck

/-! Small construction boundaries for actual scoped recursive quotations.
Full outcome agreement and actual recognition are separate proved facts. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopes
open ScalarRecursiveSource

theorem strip_decorate {C : Contract} {Γ : Ctx} (program : Prog C Γ Γ) (p : PrimTy) (name : Var) :
 strip (ScopedSource.decorate program p name)=⟨program,ScopedSource.decorate_run program p name⟩ := by
 unfold strip
 dsimp only [ScopedSource.decorate]
 simp only
 rw [dif_pos True.intro]

theorem scoped_run {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (p : PrimTy) (name : Var) (depth : Nat) :
 (scopedBody (C:=C) R hm p name depth).runR=(body R hm depth).runR := by
 induction depth with
 | zero => exact ScopedSource.decorate_run Prog.recBase p name
 | succ depth ih =>
   exact (ScopedSource.decorate_run (step R hm depth (fun _ => scopedBody R hm p name depth)) p name).trans
     (step_congr hm depth (fun _ => scopedBody R hm p name depth) (fun _ => body R hm depth) ih)

theorem complete {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (p : PrimTy) (name : Var) (depth : Nat) :
 check (C:=C) R hm depth (scopedBody R hm p name depth)=some ⟨scoped_run R hm p name depth⟩ := by
 induction depth with
 | zero =>
   change base R hm (ScopedSource.decorate Prog.recBase p name) (strip (ScopedSource.decorate Prog.recBase p name))=_
   rw [strip_decorate]
   rfl
 | succ depth ih =>
   change turn R hm depth _ (strip (ScopedSource.decorate (step R hm depth (fun _ => scopedBody R hm p name depth)) p name)) (check R hm depth)=_
   rw [strip_decorate]
   simp only [turn,ScalarSourceCheck.read_step,bind,Option.bind,ScalarSourceCheck.canonicalHead,pure]
   rw [dif_pos True.intro,ih]

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopes

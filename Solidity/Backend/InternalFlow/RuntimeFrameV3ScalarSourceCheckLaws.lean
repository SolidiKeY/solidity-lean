import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCheck

/-! Small checked source-construction equations and all-index recognition.
The same actual child thunk is inspected at every source quotation index. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCheck
open ScalarRecursiveSource

def canonicalHead {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R)) : Head R hm (step R hm depth child) :=
 ⟨depth,child,rfl⟩

theorem read_step {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R)) :
 readHead R hm (step R hm depth child)=some (canonicalHead R hm depth child) := by rfl

theorem complete {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (depth : Nat) :
 check (C:=C) R hm depth (body R hm depth)=some ⟨rfl⟩ := by
 induction depth with
 | zero => rfl
 | succ depth ih =>
   change check R hm (depth+1) (step R hm depth (fun _ => body R hm depth))=some ⟨rfl⟩
   simp only [check.eq_2,read_step,bind,Option.bind,canonicalHead,ih,pure]
   rw [dif_pos True.intro]

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCheck

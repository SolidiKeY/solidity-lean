import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveSource

/-! Actual primitive return to a typed caller destination. This is native
source execution, not a target recursive-call compiler or profile instance. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource
open Evm Evm.Memory RecursiveSource

/-- Arguments, private default result, recursive return and caller restoration
are all from the existing call semantics. Every quotation index is covered. -/
theorem call_all_horizons {C : Contract} {Γ : Ctx} {R : RefTy}
 (hm : (Ty.ref R).mapFree=true) (f : Name) (args : Args C Γ (Parameters R))
 (destination : Idx Γ (.val .uint)) (depth : Nat) (caller : State C Γ)
 (count : Nat) (bound : count<W) (ref : HRef caller.H R)
 (evaluated : args.evalT caller=.ok (countValue count bound,(some ref,()))) :
 (InterfaceV1.recursiveSource f args (.val .uint (.user "result") (some destination)) (step R hm) depth).run caller=
 if count<depth then .ok ⟨caller.setLocal destination (countValue count bound),List.prefix_refl _⟩ else .error .exhausted := by
 let child : State C (Frame R) :=
   (caller.withEnv (Δ:=Parameters R) (countValue count bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)
 have inner := all_horizons hm depth child count bound ref rfl rfl
 change TRun.call args (.val .uint (.user "result") (some destination)) (body (C:=C) R hm depth).ext
   (body R hm depth).runR caller=_
 have scope : (body (C:=C) R hm depth).ext=Ext.refl := Subsingleton.elim _ _
 unfold TRun.call
 simp only [evaluated,ok_bind,CallRet.enterT,scope]
 change (do
   let out ← (body R hm depth).run child
   pure (⟨out.st.withEnv
     ((CallRet.val .uint (.user "result") (some destination)).leaveT
       (TEnv.wk ((List.prefix_refl caller.H).trans out.ext) Γ caller.env) (TEnv.take [.val .uint] out.st.env)),
     (List.prefix_refl caller.H).trans out.ext⟩ : Solidity.Out C caller.H Γ))=_
 rw [inner]
 by_cases enough : count<depth
 · simp only [if_pos enough,ok_bind,CallRet.leaveT,TEnv.wk_self]
   rfl
 · simp only [if_neg enough,error_bind]

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource

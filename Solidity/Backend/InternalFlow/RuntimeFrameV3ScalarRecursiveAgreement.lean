import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveSource
import Solidity.Backend.InternalFlow.RuntimeFrameResultAgreement

/-! Successful quotation coherence for actual scalar-result recursion,
including callers outside the inhabited successful controls. Errors are not
identified and no target/profile obligation follows. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource
open Evm Evm.Memory RecursiveSource

theorem arm_steps {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (depth : Nat) :
 (arm (C:=C) R hm depth (fun _ => body R hm depth)).runR=
 TRun.seq (TRun.call (next R hm) (result R) (body (C:=C) R hm depth).ext (body R hm depth).runR)
   (TRun.seq increment.runR TRun.nil) := by
 rw [Prog.runR_eq (arm R hm depth (fun _ => body R hm depth)),
   Prog.runR_eq (body R hm depth),Stmt.runR_eq (increment (C:=C) (R:=R))]
 rfl

/-- All actual successful dependent outputs agree; no success premise is
injected into a profile or used to identify exhausted and reverting runs. -/
theorem bodies {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (n k : Nat) :
 ResultAgreement.Steps (body (C:=C) R hm n).runR (body R hm k).runR := by
 induction n generalizing k with
 | zero => intro σ;exact ResultAgreement.error_left .exhausted _
 | succ n ih =>
   cases k with
   | zero => intro σ;exact ResultAgreement.error_right _ .exhausted
   | succ k =>
     have branch : ResultAgreement.Steps
         (arm (C:=C) R hm n (fun _ => body R hm n)).runR
         (arm R hm k (fun _ => body R hm k)).runR := by
       rw [arm_steps,arm_steps]
       have ns : (body (C:=C) R hm n).ext=Ext.refl := Subsingleton.elim _ _
       have ks : (body (C:=C) R hm k).ext=Ext.refl := Subsingleton.elim _ _
       rw [ns,ks]
       exact ResultAgreement.seq (ResultAgreement.call (next R hm) (result R) .refl (ih k))
         (ResultAgreement.same (TRun.seq increment.runR TRun.nil))
     intro σ
     change ResultAgreement.Agree ((body R hm (n+1)).run σ) ((body R hm (k+1)).run σ)
     rw [successor_run hm n σ,successor_run hm k σ]
     exact ResultAgreement.seq
       (ResultAgreement.ite guard .refl .refl branch (ResultAgreement.same (TRun.seq zero.runR TRun.nil)))
       (ResultAgreement.same TRun.nil) σ

/-- The frozen source-coherence clause for this actual scalar family, for any
compatible typed caller/result binder. Target emission is still a separate duty. -/
theorem source_coherence {C : Contract} {Γ Δ : Ctx} {R : RefTy}
 (hm : (Ty.ref R).mapFree=true) (f : Name) (args : Args C Γ (Parameters R))
 (ret : CallRet Γ [.val .uint] Δ) : InterfaceV1.RecursiveReturnCoherence f args ret (step R hm) := by
 intro caller n k left right first second
 change TRun.call args ret (body (C:=C) R hm n).ext (body R hm n).runR caller=.ok left at first
 change TRun.call args ret (body (C:=C) R hm k).ext (body R hm k).runR caller=.ok right at second
 have ns : (body (C:=C) R hm n).ext=Ext.refl := Subsingleton.elim _ _
 have ks : (body (C:=C) R hm k).ext=Ext.refl := Subsingleton.elim _ _
 rw [ns] at first
 rw [ks] at second
 exact ResultAgreement.call args ret .refl (bodies hm n k) caller left right first second

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource

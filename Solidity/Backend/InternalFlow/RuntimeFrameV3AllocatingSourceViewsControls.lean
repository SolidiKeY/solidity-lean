import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingSourceViews
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterClaimsControls

/-! Actual base-checker acceptance/refusal receipts and a certificate consumer.
This checks only the base; recursive-head decoding and public compiler
selection remain open. No cache, target or source premise is fabricated. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem base_root {C : Contract} {Γ : Ctx} : checkBase (Prog.recBase (C:=C) (Γ:=Γ))=some ⟨rfl⟩ := by rfl

theorem certificate_root {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) :
 certifyBase (C:=C) R hm Prog.recBase=some ⟨AllocatingSourceCertificate.Certificate.base⟩ := by rfl

theorem nil_refused {C : Contract} {Γ : Ctx} : checkBase (.nil : Prog C Γ Γ)=none := by rfl

theorem revert_refused {C : Contract} {Γ : Ctx} : checkBase (.cons .revert .nil : Prog C Γ Γ)=none := by rfl

theorem extra_refused {C : Contract} {Γ : Ctx} :
 checkBase (.cons .assumeFalse (.cons .assumeFalse .nil) : Prog C Γ Γ)=none := by rfl

def checkedBase {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) :
 PLift (AllocatingSourceCertificate.Certificate (C:=C) R hm 0 Prog.recBase) :=
 (certifyBase R hm Prog.recBase).get (by rw [certificate_root];rfl)

theorem actual_failure :
 (AllocatingSourceCertificate.call 0 Prog.recBase).run AllocatingOuterClaims.Controls.failing=.error .revert ∧
 run (AllocatingOuterPlan.plan.at 0).code AllocatingOuterClaims.Controls.before=.revert := by
 have checked := (checkedBase (C:=C) A (by rfl)).down
 have native : (AllocatingSourceCertificate.call 0 Prog.recBase).run AllocatingOuterClaims.Controls.failing=.error .revert :=
   (congrFun (AllocatingSourceCertificate.call_run checked) AllocatingOuterClaims.Controls.failing).trans
     (AllocatingOuterClaims.Controls.failure 0).1
 have target := AllocatingSourceCertificate.bare_revert checked 1 16 AllocatingOuterClaims.Controls.failing
   CountdownWitness.P.base AllocatingOuterClaims.Controls.before 9 (AllocatingOuterClaims.Controls.entry 0) native
 exact ⟨native,target⟩

theorem actual_exhaustion :
 (AllocatingSourceCertificate.call 0 Prog.recBase).run AllocatingOuterPlan.Controls.σ=.error .exhausted ∧
 (AllocatingSourceCertificate.call 0 Prog.recBase).run AllocatingOuterPlan.Controls.σ≠.error .revert := by
 have checked := (checkedBase (C:=C) A (by rfl)).down
 have native : (AllocatingSourceCertificate.call 0 Prog.recBase).run AllocatingOuterPlan.Controls.σ=.error .exhausted :=
   (congrFun (AllocatingSourceCertificate.call_run checked) AllocatingOuterPlan.Controls.σ).trans
     (AllocatingOuterClaims.source_short 0 1 AllocatingOuterPlan.Controls.σ (by decide) CountdownWitness.P.r0 rfl rfl (by decide))
 refine ⟨native,?_⟩
 rw [native];intro wrong;cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.base_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.base_root
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.certificate_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.certificate_root
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.nil_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.nil_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.revert_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.revert_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.extra_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.extra_refused
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.actual_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.actual_failure
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.actual_exhaustion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.Controls.actual_exhaustion

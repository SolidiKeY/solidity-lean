import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingSourceCertificate
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterClaimsControls

/-! Actual scoped recursive syntax, constructive certificates and transported
success/failure claims. Negative cases concern certificate inhabitation, not
an arbitrary-input parser or changed compiler admission. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent
abbrev σ := AllocatingOuterPlan.Controls.σ
abbrev input := AllocatingOuterPlan.Controls.before

def program (depth : Nat) : Prog C (Frame A) (Frame A) :=
 scopedBody A (by rfl) .bool (.user "unused") depth

theorem certified (depth : Nat) : Certificate A (by rfl) depth (program depth) :=
 scoped_certificate A (by rfl) .bool (.user "unused") depth

theorem success (depth : Nat) (enough : 1<depth) :
 ∃ out, (call depth (program depth)).run σ=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at depth) 1 2 16 σ CountdownWitness.P.base input 9 out := by
 obtain ⟨out,native,known⟩ := AllocatingOuterPlan.Controls.actual depth enough
 have actual : (call depth (program depth)).run σ=.ok out := (congrFun (call_run (certified depth)) σ).trans native
 exact ⟨out,actual,returns (certified depth) 1 16 σ CountdownWitness.P.base input 9 (AllocatingOuterPlan.Controls.entry depth) out actual⟩

theorem failure (depth : Nat) :
 (call depth (program depth)).run AllocatingOuterClaims.Controls.failing=.error .revert ∧
 run (AllocatingOuterPlan.plan.at depth).code AllocatingOuterClaims.Controls.before=.revert ∧
 (call depth (program depth)).run AllocatingOuterClaims.Controls.failing≠.error .exhausted ∧
 (call depth (program depth)).run AllocatingOuterClaims.Controls.failing≠.error .panic := by
 have native := (AllocatingOuterClaims.Controls.failure depth).1
 have actual : (call depth (program depth)).run AllocatingOuterClaims.Controls.failing=.error .revert :=
   (congrFun (call_run (certified depth)) AllocatingOuterClaims.Controls.failing).trans native
 have target := bare_revert (certified depth) 1 16 AllocatingOuterClaims.Controls.failing CountdownWitness.P.base
   AllocatingOuterClaims.Controls.before 9 (AllocatingOuterClaims.Controls.entry depth) actual
 refine ⟨actual,target,?_,?_⟩
 · rw [actual];intro wrong;cases wrong
 · rw [actual];intro wrong;cases wrong

theorem nil_uncertifiable : ¬ Certificate (C:=C) A (by rfl) 0 (.nil : Prog C (Frame A) (Frame A)) := by
 intro checked
 have actual := congrFun (sound checked) σ
 change Except.ok (⟨σ,List.prefix_refl _⟩ : Solidity.Out C σ.H (Frame A))=Except.error THalt.exhausted at actual
 cases actual

theorem wrong_index_uncertifiable : ¬ Certificate (C:=C) A (by rfl) 1 (Prog.recBase : Prog C (Frame A) (Frame A)) := by
 intro checked
 have actual := congrFun (sound checked) AllocatingOuterClaims.Controls.failing
 have native := AllocatingScalarSource.source_zero (C:=C) (R:=A) (by rfl) AllocatingOuterClaims.Controls.failing 0 rfl
 change (Except.error THalt.exhausted : TRes (Solidity.Out C AllocatingOuterClaims.Controls.failing.H (Frame A)))=
   (AllocatingScalarSource.body A (by rfl) 1).run AllocatingOuterClaims.Controls.failing at actual
 rw [native] at actual
 cases actual

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.certified' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.certified
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.success
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.failure
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.nil_uncertifiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.nil_uncertifiable
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.wrong_index_uncertifiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.Controls.wrong_index_uncertifiable

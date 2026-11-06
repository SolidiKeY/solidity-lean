import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingSource
import Solidity.Backend.InternalFlow.RuntimeFrameResultAgreement

/-! Successful allocating recursive returns agree at all actual quotation
indices, including caller export. No read-domain or target simulation premise
is required for the source coherence obligation. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCoherence
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Agreement is obtained from the actual finite syntax and source execution
operators, not from a supplied desired recursive return equation. -/
theorem bodies {C : Contract} (n k : Nat) :
 ResultAgreement.Steps (AllocatingActivation.body (C:=C) n).runR (AllocatingActivation.body k).runR := by
 induction n generalizing k with
 | zero => intro σ;exact ResultAgreement.error_left .exhausted _
 | succ n ih =>
   cases k with
   | zero => intro σ;exact ResultAgreement.error_right _ .exhausted
   | succ k =>
     change ResultAgreement.Steps
       (TRun.seq (TRun.ite nonzero .refl
         (TRun.seq (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR
           (TRun.seq GuardedRecursion.probe.runR
             (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (AllocatingActivation.body n).runR) TRun.nil)))
         .refl TRun.nil) TRun.nil)
       (TRun.seq (TRun.ite nonzero .refl
         (TRun.seq (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR
           (TRun.seq GuardedRecursion.probe.runR
             (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (AllocatingActivation.body k).runR) TRun.nil)))
         .refl TRun.nil) TRun.nil)
     exact ResultAgreement.seq
       (ResultAgreement.ite nonzero .refl .refl
         (ResultAgreement.seq (ResultAgreement.same _)
           (ResultAgreement.seq (ResultAgreement.same _)
             (ResultAgreement.seq (ResultAgreement.call (nextArgs A rfl) .none .refl (ih k)) (ResultAgreement.same _))))
         (ResultAgreement.same _)) (ResultAgreement.same _)

/-- The exact frozen source-coherence field is now inhabited for this
allocating family, for arbitrary typed argument expressions and caller frames. -/
theorem source_coherence {C : Contract} {Γ : Ctx} (f : Name) (args : Args C Γ (Parameters A)) :
 InterfaceV1.RecursiveReturnCoherence f args .none AllocatingActivation.step := by
 intro caller n k left right leftRun rightRun
 exact ResultAgreement.call args .none .refl (bodies n k) caller left right leftRun rightRun

namespace Checks
open CountdownWitness

/-- Existing populated successful execution witnesses the coherence claim.
Every sufficient index returns the SAME full dependent Out, not just equal
selected locals or equal heap lengths. -/
theorem all_sufficient (depth : Nat) (enough : 2<depth) :
 (AllocatingSource.Checks.call depth).run caller=.ok AllocatingSource.Checks.returned := by
 obtain ⟨out,actual,growth,locals,kept⟩ :=
   AllocatingSource.call_success "allocatingCountdown" CountdownWitness.args depth caller 2 (by decide) P.r0
     CountdownWitness.arguments AllocatingSource.Checks.read_bound enough
 have equal := source_coherence "allocatingCountdown" CountdownWitness.args caller depth 3
   out AllocatingSource.Checks.returned actual AllocatingSource.Checks.specification.1
 rw [equal] at actual
 exact actual

noncomputable def wrongScalar : Solidity.Out P.C caller.H P.Γ :=
 ⟨AllocatingSource.Checks.returned.st.setLocal .here (countValue 1 (by decide)),AllocatingSource.Checks.returned.ext⟩

noncomputable def wrongAlias : Solidity.Out P.C caller.H P.Γ :=
 ⟨AllocatingSource.Checks.returned.st.setLocal (.there .here)
   (some (Evm.Memory.CompileExamples.r1.wk AllocatingSource.Checks.returned.ext)),AllocatingSource.Checks.returned.ext⟩

theorem wrong_scalar (depth : Nat) (enough : 2<depth) :
 (AllocatingSource.Checks.call depth).run caller≠.ok wrongScalar := by
 rw [all_sufficient depth enough]
 intro wrong
 have equal := Except.ok.inj wrong
 have observed := congrArg (fun out : Solidity.Out P.C caller.H P.Γ =>
   (TEnv.get (.here : Idx P.Γ (.val .uint)) out.st.env).val) equal
 have scalar := congrArg (fun x => x.1) AllocatingSource.Checks.ordered_bindings
 change (TEnv.get (.here : Idx P.Γ (.val .uint)) AllocatingSource.Checks.returned.st.env).val=2 at scalar
 change (TEnv.get (.here : Idx P.Γ (.val .uint)) AllocatingSource.Checks.returned.st.env).val=1 at observed
 rw [scalar] at observed
 exact (by decide : (2:Int)≠1) observed

theorem wrong_alias (depth : Nat) (enough : 2<depth) :
 (AllocatingSource.Checks.call depth).run caller≠.ok wrongAlias := by
 rw [all_sufficient depth enough]
 intro wrong
 have equal := Except.ok.inj wrong
 have observed := congrArg (fun out : Solidity.Out P.C caller.H P.Γ =>
   (TEnv.get (.there .here : Idx P.Γ (.mem CountdownWitness.A)) out.st.env).map HRef.id) equal
 have alias := congrArg (fun x => x.2.1) AllocatingSource.Checks.ordered_bindings
 change (TEnv.get (.there .here : Idx P.Γ (.mem CountdownWitness.A)) AllocatingSource.Checks.returned.st.env).map HRef.id=some 0 at alias
 change (TEnv.get (.there .here : Idx P.Γ (.mem CountdownWitness.A)) AllocatingSource.Checks.returned.st.env).map HRef.id=some 1 at observed
 rw [alias] at observed
 exact (by decide : (some 0 : Option Nat)≠some 1) observed

/-- Agreement is deliberately success-only. It cannot be used to identify
bare revert and panic, or supply a successful failed State. -/
theorem distinct_halts :
 ResultAgreement.Agree (.error .revert : TRes Unit) (.error .panic) ∧
 (.error .revert : TRes Unit)≠.error .panic := by
 exact ⟨ResultAgreement.error_left .revert _,by intro impossible;cases impossible⟩

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCoherence

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCoherence.source_coherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCoherence.source_coherence

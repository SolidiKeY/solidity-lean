import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarSource
import Solidity.Backend.InternalFlow.RuntimeFrameResultAgreement

/-! The frozen recursive-call success-coherence duty for the actual allocating
scalar family. This covers arbitrary compatible callers and result binders,
not just the populated successful inputs. Error classes remain separate;
no target compiler or approved-profile instance is asserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem continuation_steps {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (depth : Nat) :
 (AllocatingScalarSource.continuation (C:=C) R hm depth (fun _ => AllocatingScalarSource.body R hm depth)).runR=
 TRun.seq (TRun.call (next R hm) (result R) (AllocatingScalarSource.body (C:=C) R hm depth).ext
   (AllocatingScalarSource.body R hm depth).runR) (TRun.seq increment.runR TRun.nil) := by
 rw [Prog.runR_eq (AllocatingScalarSource.continuation R hm depth (fun _ => AllocatingScalarSource.body R hm depth)),
   Prog.runR_eq (AllocatingScalarSource.body (C:=C) R hm depth),Stmt.runR_eq (increment (C:=C) (R:=R))]
 rfl

theorem successor_steps {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (depth : Nat) :
 (AllocatingScalarSource.body (C:=C) R hm (depth+1)).runR=
 TRun.seq (TRun.ite guard .refl
   (TRun.seq AllocatingScalarSource.allocate.runR
     (AllocatingScalarSource.continuation R hm depth (fun _ => AllocatingScalarSource.body R hm depth)).runR)
   .refl (TRun.seq zero.runR TRun.nil)) TRun.nil := by
 rw [Prog.runR_eq (AllocatingScalarSource.body (C:=C) R hm (depth+1)),
   Stmt.runR_eq (AllocatingScalarSource.allocate (C:=C) (R:=R)),
   Prog.runR_eq (AllocatingScalarSource.continuation (C:=C) R hm depth (fun _ => AllocatingScalarSource.body R hm depth)),
   Stmt.runR_eq (zero (C:=C) (R:=R))]
 rfl

theorem bodies {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (n k : Nat) :
 ResultAgreement.Steps (AllocatingScalarSource.body (C:=C) R hm n).runR
   (AllocatingScalarSource.body R hm k).runR := by
 induction n generalizing k with
 | zero => intro σ;exact ResultAgreement.error_left .exhausted _
 | succ n ih =>
   cases k with
   | zero => intro σ;exact ResultAgreement.error_right _ .exhausted
   | succ k =>
     have continuation : ResultAgreement.Steps
         (AllocatingScalarSource.continuation (C:=C) R hm n (fun _ => AllocatingScalarSource.body R hm n)).runR
         (AllocatingScalarSource.continuation R hm k (fun _ => AllocatingScalarSource.body R hm k)).runR := by
       rw [continuation_steps,continuation_steps]
       have ns : (AllocatingScalarSource.body (C:=C) R hm n).ext=Ext.refl := Subsingleton.elim _ _
       have ks : (AllocatingScalarSource.body (C:=C) R hm k).ext=Ext.refl := Subsingleton.elim _ _
       rw [ns,ks]
       exact ResultAgreement.seq (ResultAgreement.call (next R hm) (result R) .refl (ih k))
         (ResultAgreement.same (TRun.seq increment.runR TRun.nil))
     rw [successor_steps,successor_steps]
     exact ResultAgreement.seq
       (ResultAgreement.ite guard .refl .refl
         (ResultAgreement.seq (ResultAgreement.same AllocatingScalarSource.allocate.runR) continuation)
         (ResultAgreement.same (TRun.seq zero.runR TRun.nil))) (ResultAgreement.same TRun.nil)

theorem source_coherence {C : Contract} {Γ Δ : Ctx} {R : RefTy}
 (hm : (Ty.ref R).mapFree=true) (f : Name) (args : Args C Γ (Parameters R))
 (ret : CallRet Γ [.val .uint] Δ) :
 InterfaceV1.RecursiveReturnCoherence f args ret (AllocatingScalarSource.step R hm) := by
 intro caller n k left right first second
 change TRun.call args ret (AllocatingScalarSource.body (C:=C) R hm n).ext
   (AllocatingScalarSource.body R hm n).runR caller=.ok left at first
 change TRun.call args ret (AllocatingScalarSource.body (C:=C) R hm k).ext
   (AllocatingScalarSource.body R hm k).runR caller=.ok right at second
 have ns : (AllocatingScalarSource.body (C:=C) R hm n).ext=Ext.refl := Subsingleton.elim _ _
 have ks : (AllocatingScalarSource.body (C:=C) R hm k).ext=Ext.refl := Subsingleton.elim _ _
 rw [ns] at first
 rw [ks] at second
 exact ResultAgreement.call args ret .refl (bodies hm n k) caller left right first second

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.source_coherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.source_coherence

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.continuation_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.continuation_steps

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.successor_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.successor_steps

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.bodies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingCallCoherence.bodies

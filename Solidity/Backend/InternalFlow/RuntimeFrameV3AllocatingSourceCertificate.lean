import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterClaims
import Solidity.Backend.InternalFlow.RuntimeFrameScopedSource

/-! Closed syntax certificates for the actual allocating recursive family.
No field assumes source equivalence, execution, target simulation or admission.
Proof recursors generalize the certificate indices; builders recurse on the
existing quotation Nat only. This is constructive syntax coverage, not an
arbitrary-input parser or public compiler-selector implementation. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

inductive Certificate {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) :
 Nat → Prog C (Frame R) (Frame R) → Prop where
 | base : Certificate R hm 0 Prog.recBase
 | turn {depth : Nat} {child : Unit → Prog C (Frame R) (Frame R)}
     (checked : Certificate R hm depth (child ())) :
     Certificate R hm (depth+1) (AllocatingScalarSource.step R hm depth child)
 | scope {depth : Nat} {source : Prog C (Frame R) (Frame R)} (p : PrimTy) (name : Var)
     (checked : Certificate R hm depth source) :
     Certificate R hm depth (ScopedSource.decorate source p name)

theorem step_congr {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (depth : Nat)
 (left right : Unit → Prog C (Frame R) (Frame R)) (same : (left ()).runR=(right ()).runR) :
 (AllocatingScalarSource.step R hm depth left).runR=(AllocatingScalarSource.step R hm depth right).runR := by
 change TRun.seq (TRun.ite guard .refl
   (TRun.seq AllocatingScalarSource.allocate.runR
     (TRun.seq (TRun.call (next R hm) (result R) (left ()).ext (left ()).runR)
       (TRun.seq increment.runR TRun.nil))) .refl (TRun.seq zero.runR TRun.nil)) TRun.nil=
   TRun.seq (TRun.ite guard .refl
   (TRun.seq AllocatingScalarSource.allocate.runR
     (TRun.seq (TRun.call (next R hm) (result R) (right ()).ext (right ()).runR)
       (TRun.seq increment.runR TRun.nil))) .refl (TRun.seq zero.runR TRun.nil)) TRun.nil
 have scope : (left ()).ext=(right ()).ext := Subsingleton.elim _ _
 rw [scope,same]

theorem sound {C : Contract} {R : RefTy} {hm : (Ty.ref R).mapFree=true}
 {depth : Nat} {source : Prog C (Frame R) (Frame R)} (checked : Certificate R hm depth source) :
 source.runR=(AllocatingScalarSource.body R hm depth).runR := by
 induction checked with
 | base => rfl
 | @turn depth child checked ih =>
   exact step_congr hm depth child (fun _ => AllocatingScalarSource.body R hm depth) ih
 | @scope depth source p name checked ih =>
   exact (ScopedSource.decorate_run source p name).trans ih

theorem canonical {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (depth : Nat) :
 Certificate (C:=C) R hm depth (AllocatingScalarSource.body R hm depth) := by
 induction depth with
 | zero => exact .base
 | succ depth ih => exact .turn ih

def scopedStep {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (p : PrimTy) (name : Var)
 (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R)) : Prog C (Frame R) (Frame R) :=
 ScopedSource.decorate (AllocatingScalarSource.step R hm depth child) p name

def scopedBody {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (p : PrimTy) (name : Var) (depth : Nat) :
 Prog C (Frame R) (Frame R) := recUnroll Prog.recBase (scopedStep R hm p name) depth

theorem scoped_certificate {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (p : PrimTy) (name : Var) (depth : Nat) :
 Certificate (C:=C) R hm depth (scopedBody R hm p name depth) := by
 induction depth with
 | zero => exact .base
 | succ depth ih => exact .scope p name (.turn ih)

def call (depth : Nat) (source : Prog C (Frame A) (Frame A)) : Stmt C (Frame A) (Frame A) :=
 .callRec "outerAllocating" depth (next A (by rfl)) (result A) (fun _ => source)

theorem call_run {depth : Nat} {source : Prog C (Frame A) (Frame A)} (checked : Certificate A (by rfl) depth source) :
 (call depth source).runR=(AllocatingOuterFamily.source depth).runR := by
 change TRun.call (next A (by rfl)) (result A) source.ext source.runR=
   TRun.call (next A (by rfl)) (result A) (AllocatingScalarSource.body A (by rfl) depth).ext
     (AllocatingScalarSource.body A (by rfl) depth).runR
 have scope : source.ext=(AllocatingScalarSource.body (C:=C) A (by rfl) depth).ext := Subsingleton.elim _ _
 rw [scope,sound checked]

theorem returns {depth : Nat} {source : Prog C (Frame A) (Frame A)} (checked : Certificate A (by rfl) depth source) :
 InterfaceV1.ReturnClaim 2 F (call depth source) (AllocatingOuterPlan.plan.at depth) := by
 intro L frame caller base before start entry out actual
 have native : (AllocatingOuterFamily.source depth).run caller=.ok out :=
   (congrFun (call_run checked) caller).symm.trans actual
 exact AllocatingOuterClaims.returns depth L frame caller base before start entry out native

theorem bare_revert {depth : Nat} {source : Prog C (Frame A) (Frame A)} (checked : Certificate A (by rfl) depth source) :
 InterfaceV1.BareRevertClaim 2 F (call depth source) (AllocatingOuterPlan.plan.at depth) := by
 intro L frame caller base before start entry actual
 have native : (AllocatingOuterFamily.source depth).run caller=.error .revert :=
   (congrFun (call_run checked) caller).symm.trans actual
 exact AllocatingOuterClaims.bare_revert depth L frame caller base before start entry native

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.step_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.step_congr
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.sound
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.canonical' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.canonical
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.scoped_certificate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.scoped_certificate
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.call_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.call_run
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.returns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.returns
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.bare_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceCertificate.bare_revert

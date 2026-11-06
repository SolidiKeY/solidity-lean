import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScopedCheckControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScopedTransport
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterPlanControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterZeroControls

/-! Populated target return from an actually checked scoped source. The
original reference A, caller, target image, Entry and all Returned obligations
are retained. This supplies no public recursive selector or approved profile. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

def source (p : PrimTy) (name : Var) (depth : Nat) : Prog C (Frame A) (Frame A) :=
 AllocatingSourceCertificate.scopedBody A rfl p name depth

theorem accepted (p : PrimTy) (name : Var) (depth : Nat) :
 (AllocatingScopedCheck.certify A rfl depth (source p name depth)).isSome=true := by
 change (AllocatingScopedCheck.certify A rfl depth
   (AllocatingSourceCertificate.scopedBody A rfl p name depth)).isSome=true
 rw [AllocatingScopedCheck.Controls.canonical_checked]
 rfl

def checked (p : PrimTy) (name : Var) (depth : Nat) :
 AllocatingSourceCertificate.Certificate A rfl depth (source p name depth) :=
 ((AllocatingScopedCheck.certify A rfl depth (source p name depth)).get (accepted p name depth)).down

def call (p : PrimTy) (name : Var) (depth : Nat) : Stmt C (Frame A) (Frame A) :=
 AllocatingSourceCertificate.call depth (source p name depth)

abbrev caller := AllocatingOuterPlan.Controls.σ
abbrev before := AllocatingOuterPlan.Controls.before

theorem actual (p : PrimTy) (name : Var) (depth : Nat) (enough : 1<depth) :
 ∃ out, (call p name depth).run caller=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at depth) 1 2 16 caller CountdownWitness.P.base before 9 out := by
 obtain ⟨out,native,_known⟩ := AllocatingOuterPlan.Controls.actual depth enough
 have same : (call p name depth).run caller=(AllocatingOuterFamily.source depth).run caller :=
   congrFun (AllocatingSourceCertificate.call_run (checked p name depth)) caller
 have scopedRun : (call p name depth).run caller=.ok out := same.trans native
 exact ⟨out,scopedRun,(AllocatingScopedTransport.claims (accepted p name depth)).1
   1 16 caller CountdownWitness.P.base before 9 (AllocatingOuterPlan.Controls.entry depth) out scopedRun⟩

theorem observations (p : PrimTy) (name : Var) (depth : Nat) (enough : 1<depth) :
 ∃ (out : Solidity.Out C caller.H (Frame A)) (target : Machine) (addresses : Nat → Fin W),
 (call p name depth).run caller=.ok out ∧
 run (AllocatingOuterPlan.plan.at depth).code before=.ok target 0 ∧
 StateRepr 1 2 16 F out.st addresses target ∧
 target.stack=before.stack ∧ BaseExtends caller.H CountdownWitness.P.base addresses ∧
 GrowsAllocator 2 16 ((AllocatingOuterPlan.plan.at depth).heapCost caller)
   caller CountdownWitness.P.base before out.st addresses target ∧
 target.mem (AllocatingOuterPlan.plan.at depth).pointerCell=.val (wmod 9) ∧
 Footprint.Words (AllocatingOuterPlan.plan.at depth).localLimit 9 before target ∧
 (target.stack,[target.mem 0,target.mem 2,target.mem 3,target.mem 4,target.mem 8])=
 ([w[77]],[w[26],w[16],w[2],w[1],w[9]]) := by
 obtain ⟨out,scopedRun,target,addresses,executed,represented,stack,baseExtended,growth,pointer,older⟩ := actual p name depth enough
 obtain ⟨_seen,last,_otherAddresses,_oldSource,oldRun,_oldRepr,vector,_notRevert⟩ :=
   AllocatingOuterPlan.Controls.observations depth enough
 have same : last=target := (Evm.Out.ok.inj (oldRun.symm.trans executed)).1
 subst last
 exact ⟨out,target,addresses,scopedRun,executed,represented,stack,baseExtended,growth,pointer,older,vector⟩

abbrev zeroCaller := AllocatingOuterZero.Controls.caller
abbrev zeroBefore := AllocatingOuterZero.Controls.before

theorem zero_actual (p : PrimTy) (name : Var) (depth : Nat) :
 (∃ out, (call p name (depth+1)).run zeroCaller=.ok out ∧
 InterfaceV1.Returned (AllocatingOuterPlan.plan.at (depth+1)) 1 2 16 zeroCaller
   CountdownWitness.P.base zeroBefore 10 out) ∧
 ¬∃ cursor, StructAllocatorRepr zeroCaller.heap CountdownWitness.P.base 16 cursor zeroBefore := by
 obtain ⟨⟨out,native,_known⟩,noOwner⟩ := AllocatingOuterZero.Controls.actual depth
 have same : (call p name (depth+1)).run zeroCaller=(AllocatingOuterFamily.source (depth+1)).run zeroCaller :=
   congrFun (AllocatingSourceCertificate.call_run (checked p name (depth+1))) zeroCaller
 have scopedRun : (call p name (depth+1)).run zeroCaller=.ok out := same.trans native
 exact ⟨⟨out,scopedRun,(AllocatingScopedTransport.claims (accepted p name (depth+1))).1
   1 16 zeroCaller CountdownWitness.P.base zeroBefore 10 (AllocatingOuterZero.Controls.entry (depth+1)) out scopedRun⟩,noOwner⟩

theorem zero_observations (p : PrimTy) (name : Var) (depth : Nat) :
 ∃ (out : Solidity.Out C zeroCaller.H (Frame A)) (target : Machine) (addresses : Nat → Fin W),
 (call p name (depth+1)).run zeroCaller=.ok out ∧
 run (AllocatingOuterPlan.plan.at (depth+1)).code zeroBefore=.ok target 0 ∧
 StateRepr 1 2 16 F out.st addresses target ∧
 target.stack=zeroBefore.stack ∧ BaseExtends zeroCaller.H CountdownWitness.P.base addresses ∧
 GrowsAllocator 2 16 ((AllocatingOuterPlan.plan.at (depth+1)).heapCost zeroCaller)
   zeroCaller CountdownWitness.P.base zeroBefore out.st addresses target ∧
 target.mem (AllocatingOuterPlan.plan.at (depth+1)).pointerCell=.val (wmod 10) ∧
 Footprint.Words (AllocatingOuterPlan.plan.at (depth+1)).localLimit 10 zeroBefore target ∧
 (target.stack,[target.mem 0,target.mem 2,target.mem 3,target.mem 4,target.mem 8])=
 ([w[77]],[w[0],w[16],w[1],w[0],w[10]]) ∧
 (¬∃ cursor, StructAllocatorRepr zeroCaller.heap CountdownWitness.P.base 16 cursor zeroBefore) := by
 obtain ⟨⟨out,scopedRun,target,addresses,executed,represented,stack,baseExtended,growth,pointer,older⟩,noOwner⟩ :=
   zero_actual p name depth
 obtain ⟨_seen,last,_otherAddresses,_oldSource,oldRun,_oldRepr,vector,_cursorWrong,_notRevert⟩ :=
   AllocatingOuterZero.Controls.observations depth
 have same : last=target := (Evm.Out.ok.inj (oldRun.symm.trans executed)).1
 subst last
 exact ⟨out,target,addresses,scopedRun,executed,represented,stack,baseExtended,growth,pointer,older,vector,noOwner⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.accepted
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.actual
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.zero_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.zero_actual
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.zero_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopedEndpoint.zero_observations

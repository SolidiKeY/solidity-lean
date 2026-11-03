import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingReturn

/-! Internal allocating recursive failure transport. A real allocation reaches
an actual represented intermediate machine before a checked old-array read
reverts. Failure has no output state or allocator/rollback conclusion. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingFailure
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Genuine allocation preserves the exact evaluated old-object read, including
its bare-revert result; this is not a law about arbitrary mutating bodies. -/
theorem allocated_failure {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (failed : ArrayProbe.value.evalT σ=.error .revert) :
 ArrayProbe.value.evalT (AllocatingActivation.allocated σ)=.error .revert := by
 have parameters := AllocatingActivation.allocated_parameters σ n fit ref counter alias
 exact (DomainTransport.probe_keeps σ (AllocatingActivation.allocated σ) (AllocatingActivation.extension σ)
   (Heap.keeps_alloc σ.heap (AllocatingActivation.object σ)) n fit ref counter alias parameters.1 parameters.2).trans failed

/-- Allocation and the actual failing read occur before the native recursive
call at every positive quotation. Depth zero remains exhausted. -/
theorem source_failure {C : Contract} (σ : State C (Parameters A)) (depth n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (failed : ArrayProbe.value.evalT σ=.error .revert) :
 (AllocatingActivation.body (depth+1)).run σ=.error .revert := by
 have guard := guard_eval σ (n+1) (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 have allocated := DomainTransport.scoped_source σ .bool AllocatingActivation.lengthExpr AllocatingActivation.size rfl
 have probed := probe_failure (AllocatingActivation.allocated σ) (allocated_failure σ n fit ref counter alias failed)
 change (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR σ=
   .ok ⟨AllocatingActivation.allocated σ,AllocatingActivation.extension σ⟩ at allocated
 change GuardedRecursion.probe.runR (AllocatingActivation.allocated σ)=.error .revert at probed
 change TRun.seq (TRun.ite nonzero .refl
   (TRun.seq (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).runR
     (TRun.seq GuardedRecursion.probe.runR
       (TRun.seq (TRun.call (nextArgs A rfl) .none .refl (AllocatingActivation.body depth).runR) TRun.nil)))
   .refl TRun.nil) TRun.nil σ=_
 simp only [TRun.seq,TRun.ite,guard,positive,boolT,if_true,allocated,probed,ok_bind,Except.map]

/-- Native caller export propagates the same halt, without producing a failed
caller state. Evaluated arguments are a necessary actual execution premise. -/
theorem call_failure {C : Contract} {Γ : Ctx} (name : Name) (args : Args C Γ (Parameters A))
 (caller : State C Γ) (depth n : Nat) (fit : n+1<W) (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue (n+1) fit,(some ref,())))
 (failed : ArrayProbe.value.evalT (caller.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,())))=.error .revert) :
 (InterfaceV1.recursiveSource name args .none AllocatingActivation.step (depth+1)).run caller=.error .revert := by
 have body := source_failure (caller.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,()))) depth n fit ref rfl rfl failed
 change TRun.call args .none .refl (AllocatingActivation.body (depth+1)).runR caller=_
 unfold TRun.call
 simp only [evaluated,ok_bind,CallRet.enterT]
 change (do
   let out ← (AllocatingActivation.body (depth+1)).run (caller.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,())))
   pure (exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl caller (countValue (n+1) fit,(some ref,())) out))=_
 rw [body]
 rfl

/-- The same checked allocation reaches its represented output and then the
actual read failure absorbs activation and any further target suffix. -/
theorem target_suffix {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (failed : ArrayProbe.value.evalT σ=.error .revert)
 (base : Nat → Fin W) (machine : Machine) (repr : StateRepr L b frame F σ base machine)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor machine)
 (positive : 0<b) (space : cursor.val+4<W) (room : b+3≤frame) (pointer : Nat) (suffix : List Instr) :
 run (AllocatingActivation.code (C:=C) b F pointer ++ suffix) machine=.revert := by
 obtain ⟨source,allocated,represented,owned,stack,words⟩ :=
   Footprint.declare repr owner positive .bool AllocatingActivation.lengthExpr rfl AllocatingActivation.size rfl space
     (lo:=b+3) (by change b+(2+1)≤b+3;omega) (by change b+(2+1)≤frame;exact room)
 have reached := represented.drop (.push .refl)
 have checked := ArrayProbe.failure_suffix reached (allocated_failure σ n fit ref counter alias failed)
   (activationCode (C:=C) b F pointer ++ suffix)
 simpa only [AllocatingActivation.code,List.append_assoc] using (run_append_ok allocated).trans checked

/-- Failure of the real allocating loop turn propagates through the fixed
return image as bare revert, never abstract fault or successful unwind. -/
theorem target_image {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (failed : ArrayProbe.value.evalT σ=.error .revert)
 (base : Nat → Fin W) (machine : Machine) (repr : StateRepr L b frame F σ base machine)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor machine)
 (positive : 0<b) (space : cursor.val+4<W) (room : b+3≤frame) (pointer bottom : Nat) :
 run (AllocatingReturn.image (C:=C) b F pointer bottom) machine=.revert := by
 have guard := guard_run σ (n+1) fit counter base machine repr
 have positiveGuard : decide (0<n+1)=true := decide_eq_true (by omega)
 have checkedGuard : run (guardCompiled (C:=C) b F).code machine=.ok (machine.push w[1]) 0 := by
   simpa only [positiveGuard,bword] using guard
 have failedTurn : run (AllocatingActivation.code (C:=C) b F pointer) machine=.revert := by
   simpa only [List.append_nil] using target_suffix σ n fit ref counter alias failed base machine repr cursor owner positive space room pointer []
 exact failing_loop _ _ _ machine (failing_turn _ _ machine checkedGuard failedTurn)

namespace Checks
open CountdownWitness
abbrev bad := ArrayProbe.Checks.bad
abbrev before := ArrayProbe.Checks.badMachine
abbrev F := CountdownWitness.F
def after := AllocatingActivation.allocated bad
def addresses := upd P.base bad.H.length (⟨22,by decide⟩ : Fin W)
def reached := writeMachine (allocateMachine before (⟨22,by decide⟩ : Fin W) AllocatingActivation.size) 4 w[22]

/-- This successful intermediate is an actual allocation endpoint, NOT a
failed-state reconstruction from the later revert. -/
theorem allocation :
 (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).run bad=
   .ok ⟨after,AllocatingActivation.extension bad⟩ ∧
 run (declareNewCode 2 (AllocatingActivation.lengthExpr (C:=P.C))) before=.ok reached 0 ∧
 StateRepr 1 2 16 F after addresses reached ∧
 StructAllocatorRepr after.heap addresses 16 (⟨26,by decide⟩ : Fin W) reached ∧
 reached.stack=before.stack := by
 obtain ⟨source,target,repr,owner,stack,words⟩ :=
   Footprint.declare ArrayProbe.Checks.bad_repr ArrayProbe.Checks.bad_ownership (by decide)
     .bool AllocatingActivation.lengthExpr rfl AllocatingActivation.size rfl (by decide)
     (lo:=8) (by decide) (by decide)
 exact ⟨DomainTransport.scoped_source bad .bool AllocatingActivation.lengthExpr AllocatingActivation.size rfl,
   target,repr.drop (.push .refl),owner,stack⟩

theorem observations :
 (reached.stack,[reached.mem 0,reached.mem 1,reached.mem 2,reached.mem 3,reached.mem 4,reached.mem 7,
 reached.mem 8,reached.mem 9,reached.mem 16,reached.mem 17,reached.mem 18,reached.mem 20,reached.mem 21,
 reached.mem 22,reached.mem 23,reached.mem 24,reached.mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[3],w[22],w[0],w[10],w[99],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0]]) := by rfl

theorem read_after : ArrayProbe.value.evalT after=.error .revert :=
 allocated_failure bad 2 (by decide) P.r0 rfl rfl ArrayProbe.Checks.bad_evaluated

theorem source (depth : Nat) : (AllocatingActivation.body (depth+1)).run bad=.error .revert :=
 source_failure bad depth 2 (by decide) P.r0 rfl rfl ArrayProbe.Checks.bad_evaluated

def badCaller := CountdownWitness.caller.setLocal (.here : Idx P.Γ (.val .uint)) (countValue 3 (by decide))
def call (depth : Nat) : Stmt P.C P.Γ P.Γ :=
 InterfaceV1.recursiveSource "allocatingCountdown" CountdownWitness.args .none AllocatingActivation.step depth

theorem arguments : CountdownWitness.args.evalT badCaller=.ok bad.env := by rfl

theorem native_call (depth : Nat) : (call (depth+1)).run badCaller=.error .revert :=
 call_failure "allocatingCountdown" CountdownWitness.args badCaller depth 2 (by decide) P.r0 arguments ArrayProbe.Checks.bad_evaluated

theorem target (suffix : List Instr) :
 run (AllocatingActivation.code (C:=P.C) 2 F 8 ++ suffix) before=.revert :=
 target_suffix bad 2 (by decide) P.r0 rfl rfl ArrayProbe.Checks.bad_evaluated P.base before
   ArrayProbe.Checks.bad_repr ⟨22,by decide⟩ ArrayProbe.Checks.bad_ownership (by decide) (by decide) (by decide) 8 suffix

theorem whole_image : run (AllocatingReturn.image (C:=P.C) 2 F 8 7) before=.revert :=
 target_image bad 2 (by decide) P.r0 rfl rfl ArrayProbe.Checks.bad_evaluated P.base before
   ArrayProbe.Checks.bad_repr ⟨22,by decide⟩ ArrayProbe.Checks.bad_ownership (by decide) (by decide) (by decide) 8 7

/-- Matched admitted successful baseline uses the identical image. -/
theorem successful_baseline :
 run (AllocatingReturn.image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input=
 .ok AllocatingReturn.Checks.machine 0 := AllocatingReturn.Checks.specification.2.1

theorem depth_zero : (AllocatingActivation.body 0).run bad=.error .exhausted :=
 AllocatingActivation.base_exhausts bad

theorem wrong_source_class (depth : Nat) :
 (AllocatingActivation.body (depth+1)).run bad≠.error .exhausted ∧
 (AllocatingActivation.body (depth+1)).run bad≠.error .panic := by
 rw [source]
 constructor <;> (intro wrong;cases wrong)

theorem wrong_target_class : run (AllocatingReturn.image (C:=P.C) 2 F 8 7) before≠.fault := by
 rw [whole_image]
 intro wrong
 cases wrong

theorem failed_not_success (last : Machine) (result : Nat) :
 run (AllocatingReturn.image (C:=P.C) 2 F 8 7) before≠.ok last result := by
 rw [whole_image]
 intro wrong
 cases wrong

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingFailure

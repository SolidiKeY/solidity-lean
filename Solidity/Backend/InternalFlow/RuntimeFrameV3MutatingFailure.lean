import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingCompletion

/-! Invalid first-write transport for the mutating recursive image. The checked
write certificate supplies the target halt before the allocating suffix.
Error results supply no failed state, allocation frontier or rollback claim. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingFailure
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Actual index evaluation, including the original write receiver and value. -/
theorem write_failure {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (outside : σ.heap.len ref .dyn≤n) : (MutatingActivation.write (C:=C)).run σ=.error .revert := by
 have index := decrement_eval rfl σ n fit ref counter alias
 change TRun.assignMem (.index .dyn (.var (.there .here) rfl) decrement) (.val MutatingActivation.value) σ=_
 simp only [TRun.assignMem,MSrc.mvalT,MutatingActivation.value,Val.evalT,Simple.evalT,MLoc.addrT,MPath.mvalT,alias,index,ok_bind]
 simp only [pure,Except.pure,bind,Except.bind]
 change (do
   let hp ← TRes.ofOpt (σ.heap.writeAddr (.index ref .dyn (countValue n (by omega))) σ.env.1)
   pure (⟨σ.withHeap hp,List.prefix_refl _⟩ : Solidity.Out C σ.H (Parameters A)))=_
 have failed : σ.heap.writeAddr (.index ref .dyn (countValue n (by omega))) σ.env.1=none := by
   simp only [Heap.writeAddr,Heap.setIndex,HeapDomain.index_nat]
   simp only [Heap.len] at outside
   exact if_neg (by omega)
 rw [failed]
 rfl

/-- Every positive native quotation encounters the same first write failure.
This says nothing about the exhausted zero quotation. -/
theorem source_failure {C : Contract} (σ : State C (Parameters A)) (depth n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (outside : σ.heap.len ref .dyn≤n) : (MutatingActivation.body (depth+1)).run σ=.error .revert := by
 have guard := guard_eval σ (n+1) (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 apply MutatingActivation.source_failure σ depth .revert
 · simpa only [positive] using guard
 · exact write_failure σ n fit ref counter alias outside

/-- Actual evaluated native arguments propagate the callee write halt through
caller export. Evaluation success is explicit; no target call compiler is inferred. -/
theorem call_failure {C : Contract} {Γ : Ctx} (name : Name) (args : Args C Γ (Parameters A))
 (caller : State C Γ) (depth n : Nat) (fit : n+1<W) (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue (n+1) fit,(some ref,())))
 (outside : caller.heap.len ref .dyn≤n) :
 (InterfaceV1.recursiveSource name args .none MutatingActivation.step (depth+1)).run caller=.error .revert := by
 have body := source_failure (caller.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,())))
   depth n fit ref rfl rfl outside
 change TRun.call args .none .refl (MutatingActivation.body (depth+1)).runR caller=_
 unfold TRun.call
 simp only [evaluated,ok_bind,CallRet.enterT]
 change (do
   let out ← (MutatingActivation.body (depth+1)).run (caller.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,())))
   pure (exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl caller (countValue (n+1) fit,(some ref,())) out))=_
 rw [body]
 rfl

/-- The real public write selector and its certificate suffice. No allocator
capacity for the unreachable private allocation is assumed. -/
theorem target_suffix {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (outside : σ.heap.len ref .dyn≤n)
 (base : Nat → Fin W) (machine : Machine) (repr : StateRepr L b frame F σ base machine)
 (room : b+frameNeedStmt (MutatingActivation.write (C:=C))≤frame)
 (pointer : Nat) (suffix : List Instr) :
 run (MutatingActivation.code (C:=C) b F pointer ++ suffix) machine=.revert := by
 have actual := (MutatingActivation.selected (C:=C) b F).cert.correct repr room (.inl rfl)
 rcases actual with ⟨out,last,addresses,source,target,represented,stack,extended,growth⟩ | ⟨source,target⟩
 · rw [write_failure σ n fit ref counter alias outside] at source
   cases source
 · exact run_append_revert (run_append_revert target)

/-- The same actual image as successful completion, with its unwind absorbed
by the first failing target turn. No successful failed-state is reconstructed. -/
theorem target_image {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (outside : σ.heap.len ref .dyn≤n)
 (base : Nat → Fin W) (machine : Machine) (repr : StateRepr L b frame F σ base machine)
 (room : b+frameNeedStmt (MutatingActivation.write (C:=C))≤frame) (pointer bottom : Nat) :
 run (MutatingCompletion.image (C:=C) b F pointer bottom) machine=.revert := by
 have guard := guard_run σ (n+1) fit counter base machine repr
 have positive : decide (0<n+1)=true := decide_eq_true (by omega)
 have checkedGuard : run (guardCompiled (C:=C) b F).code machine=.ok (machine.push w[1]) 0 := by
   simpa only [positive,bword] using guard
 have failed : run (MutatingActivation.code (C:=C) b F pointer) machine=.revert := by
   simpa only [List.append_nil] using target_suffix σ n fit ref counter alias outside base machine repr room pointer []
 exact failing_loop _ _ _ machine (failing_turn _ _ machine checkedGuard failed)

namespace Checks
open CountdownWitness
abbrev bad := ArrayProbe.Checks.bad
abbrev input := ArrayProbe.Checks.badMachine

theorem source (depth : Nat) : (MutatingActivation.body (depth+1)).run bad=.error .revert :=
 source_failure bad depth 2 (by decide) P.r0 rfl rfl (by
   change callee.heap.len P.r0 .dyn≤2
   rw [HeapDomain.Checks.length_zero]
   decide)

def args : Args P.C (Parameters CountdownWitness.A) (Parameters CountdownWitness.A) := entryArgs CountdownWitness.A rfl (.there .here) .here

theorem arguments : args.evalT bad=.ok (countValue 3 (by decide),(some P.r0,())) := rfl

theorem native_call (depth : Nat) :
 (InterfaceV1.recursiveSource "mutatingFailure" args .none MutatingActivation.step (depth+1)).run bad=.error .revert :=
 call_failure _ args bad depth 2 (by decide) P.r0 arguments (by
   change callee.heap.len P.r0 .dyn≤2
   rw [HeapDomain.Checks.length_zero]
   decide)

theorem target : run (MutatingCompletion.image (C:=P.C) 2 F 8 7) input=.revert :=
 target_image bad 2 (by decide) P.r0 rfl rfl (by
   change callee.heap.len P.r0 .dyn≤2
   rw [HeapDomain.Checks.length_zero]
   decide) P.base input ArrayProbe.Checks.bad_repr (by decide) 8 7

theorem not_fault : run (MutatingCompletion.image (C:=P.C) 2 F 8 7) input≠.fault := by
 rw [target]
 intro falseEquality
 cases falseEquality

theorem not_success (last : Machine) (pc : Nat) :
 run (MutatingCompletion.image (C:=P.C) 2 F 8 7) input≠.ok last pc := by
 rw [target]
 intro falseEquality
 cases falseEquality

theorem zero_exhausted : (MutatingActivation.body 0).run bad=.error .exhausted := rfl

/-- The unchanged populated successful control uses the identical target image;
its full ordered snapshot and allocator proof remain in MutatingCompletion. -/
theorem successful_control :
 run (MutatingCompletion.image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input=
 .ok MutatingCompletion.Checks.machine 0 := MutatingCompletion.Checks.specification.2.1

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingFailure

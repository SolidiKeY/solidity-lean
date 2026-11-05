import Solidity.Backend.InternalFlow.RuntimeFrameV3GuardedPrefixes

/-! Actual native call entry/return and complete caller-tail representation for
the guarded countdown image. This is not public recursive compiler admission. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.GuardedCaller
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Native enter/leave transport restores EVERY caller local, at every source
horizon. Arguments and read validity are actual source evaluation facts. -/
theorem call_all_horizons {C : Contract} {Γ : Ctx} (name : Name)
 (args : Args C Γ (Parameters A)) (depth : Nat) (caller : State C Γ)
 (count : Nat) (bound : count<W) (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue count bound,(some ref,())))
 (reads : ReadDomain (caller.withEnv (Δ:=Parameters A) (countValue count bound,(some ref,()))) ref count) :
 (InterfaceV1.recursiveSource name args .none GuardedRecursion.step depth).run caller=
 if count<depth then .ok ⟨caller,List.prefix_refl _⟩ else .error .exhausted := by
 let child : State C (Parameters A) := caller.withEnv (countValue count bound,(some ref,()))
 have inner := GuardedPrefixes.all_horizons depth child count bound ref rfl rfl reads
 change TRun.call args .none .refl (GuardedRecursion.body depth).runR caller=_
 unfold TRun.call
 simp only [evaluated,ok_bind,CallRet.enterT]
 change (do
   let out ← (GuardedRecursion.body depth).run child
   pure (⟨out.st.withEnv (TEnv.wk ((List.prefix_refl caller.H).trans out.ext) Γ caller.env),
     (List.prefix_refl caller.H).trans out.ext⟩ : Solidity.Out C caller.H Γ))=_
 rw [inner]
 by_cases enough : count<depth
 · simp only [if_pos enough,ok_bind]
   change (Except.ok (⟨child.withEnv (TEnv.wk (List.prefix_refl caller.H) Γ caller.env),List.prefix_refl _⟩ : Solidity.Out C caller.H Γ) : TRes (Solidity.Out C caller.H Γ))=_
   rw [TEnv.wk_self]
   rfl
 · simp only [if_neg enough,error_bind]

/-- A real failed read after successful argument evaluation propagates through
native call entry. Error output supplies no final State or body-effect trace. -/
theorem call_read_failure {C : Contract} {Γ : Ctx} (name : Name)
 (args : Args C Γ (Parameters A)) (depth : Nat) (caller : State C Γ)
 (n : Nat) (bound : n+1<W) (ref : HRef caller.H A)
 (evaluated : args.evalT caller=.ok (countValue (n+1) bound,(some ref,())))
 (failed : ArrayProbe.value.evalT (caller.withEnv (Δ:=Parameters A) (countValue (n+1) bound,(some ref,())))=.error .revert) :
 (InterfaceV1.recursiveSource name args .none GuardedRecursion.step (depth+1)).run caller=.error .revert := by
 let child : State C (Parameters A) := caller.withEnv (countValue (n+1) bound,(some ref,()))
 have guard := guard_eval child (n+1) rfl
 have positive : nonzero.evalT child=.ok true := by
   simpa only [show decide (0<n+1)=true from decide_eq_true (by omega)] using guard
 have bodyFailed := source_failure child depth positive failed
 change TRun.call args .none .refl (GuardedRecursion.body (depth+1)).runR caller=_
 unfold TRun.call
 simp only [evaluated,ok_bind,CallRet.enterT]
 change (do
   let out ← (GuardedRecursion.body (depth+1)).run child
   pure (⟨out.st.withEnv (TEnv.wk ((List.prefix_refl caller.H).trans out.ext) Γ caller.env),
     (List.prefix_refl caller.H).trans out.ext⟩ : Solidity.Out C caller.H Γ))=_
 rw [bodyFailed]
 simp only [error_bind]

/-- Reconstruct an arbitrary represented caller tail after actual guarded
execution. The tail's words follow from the reached low-memory frame, not from
an assumed target context equation or an alias-liveness premise. -/
theorem endpoint {C : Contract} {tail : Ctx} {L b frame : Nat}
 {F : Frag (Parameters A ++ tail)} (name : Name)
 (caller : State C (Parameters A ++ tail)) (count : Nat) (bound : count<W)
 (ref : HRef caller.H A)
 (counter : TEnv.get (.here : Idx (Parameters A ++ tail) (.val .uint)) caller.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A ++ tail) (.mem A)) caller.env=some ref)
 (reads : ReadDomain (caller.withEnv (Δ:=Parameters A) (countValue count bound,(some ref,()))) ref count)
 (base : Nat → Fin W) (before : Machine) (initial : StateRepr L b frame F caller base before)
 (lo pointer bottom start : Nat) (localBound : b+tail.length+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (bottomAbove : b+tail.length+2≤bottom) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) (bottomValue : before.mem bottom=.val (wmod start)) :
 ∃ last,
 (∀ depth, count<depth →
   (InterfaceV1.recursiveSource name (entryArgs A rfl (.there .here) .here) .none GuardedRecursion.step depth).run caller=.ok ⟨caller,List.prefix_refl _⟩) ∧
 run (image (C:=C) (b+tail.length) (Frag.init (Parameters A)) pointer bottom) before=.ok last 0 ∧
 StateRepr L b frame F caller base last ∧ last.stack=before.stack ∧
 last.mem pointer=.val (wmod start) ∧
 (∀ {t : LTy} (index : Idx (Parameters A ++ tail) t), last.mem (cellOf b index)=before.mem (cellOf b index)) ∧
 (∀ x, x<start → last.mem x=before.mem x) ∧
 (∀ x, frame≤x → last.mem x=before.mem x) ∧
 (∀ j, j<count → last.mem (start+2*j)=before.mem (b+tail.length) ∧
   last.mem (start+2*j+1)=.val (wmod (count-j))) := by
 let child : State C (Parameters A) := caller.withEnv (countValue count bound,(some ref,()))
 have parameters : TEnv.take (Parameters A) caller.env=(countValue count bound,(some ref,())) := by
   exact Prod.ext counter (Prod.ext alias rfl)
 have projected := parameter_projection (tail:=tail) initial
 rw [parameters] at projected
 obtain ⟨last,source,executed,reached,stack,cursor,low,high,saved⟩ :=
   success_endpoint count bound child ref rfl rfl reads base before projected
     lo pointer bottom start localBound pointerAbove pointerBelow bottomAbove bottomBefore bottomSeparate
     payloadAbove pointerBefore capacity fits current bottomValue
 have locals : ∀ {t : LTy} (index : Idx (Parameters A ++ tail) t),
     last.mem (cellOf b index)=before.mem (cellOf b index) := by
   intro t index
   have small := lvl_lt b index
   change cellOf b index<b+(Parameters A ++ tail).length at small
   have length : (Parameters A ++ tail).length=tail.length+2 := by simp only [List.length_append,List.length_cons,List.length_nil];omega
   rw [length] at small
   exact low _ (by omega)
 have transported := Restored.memory_transport initial last.mem (fun index observed => locals index) high
 have callerRepr : StateRepr L b frame F caller base last :=
   ⟨⟨reached.core.store,transported.core.vals,transported.core.aliases,
     reached.core.net,reached.core.netSelf,initial.core.bound,transported.core.fragile,
     reached.core.env,reached.core.funds,reached.core.oracle⟩,
     reached.heap,transported.pointers,transported.locals,reached.structs,reached.separated,reached.refs⟩
 refine ⟨last,?_,executed,callerRepr,stack,cursor,locals,low,high,saved⟩
 intro depth enough
 have evaluated : (entryArgs A rfl (.there .here) .here).evalT caller=.ok (countValue count bound,(some ref,())) := by
   simp only [entryArgs,Args.evalT,MPath.mvalT,alias,Val.evalT,Simple.evalT,counter,ok_bind]
   rfl
 simpa only [if_pos enough] using call_all_horizons name _ depth caller count bound ref evaluated reads

namespace Checks
open CountdownWitness

def call (depth : Nat) : Stmt P.C P.Γ P.Γ :=
 InterfaceV1.recursiveSource "guardedCountdown" CountdownWitness.args .none GuardedRecursion.step depth

theorem source_all (depth : Nat) : (call depth).run caller=
 if 2<depth then .ok ⟨caller,List.prefix_refl _⟩ else .error .exhausted :=
 call_all_horizons "guardedCountdown" CountdownWitness.args depth caller 2 (by decide) P.r0
 CountdownWitness.arguments GuardedPrefixes.Checks.read_domain

/-- Actual header prefix execution, not an assumed represented midpoint. -/
def input := writeMachine CountdownWitness.machine 7 w[10]
theorem input_run : run [.push w[10],.mstore 7] CountdownWitness.machine=.ok input 0 := by rfl
theorem input_repr : StateRepr 1 0 16 (Frag.init P.Γ) caller P.base input :=
 reserved_write CountdownWitness.caller_repr 7 (by decide) (by decide) w[10]

/-- This whole-caller fixture has local reference word zero, not an allocator
cursor. No inhabited AllocationInput is claimed for it. -/
noncomputable def returned : Machine :=
 (endpoint (tail:=[.mem CountdownWitness.A,.mem CountdownWitness.A]) "guardedCountdown" caller 2 (by decide) P.r0 rfl rfl
   GuardedPrefixes.Checks.read_domain P.base input input_repr
   8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide) (by decide) rfl rfl).choose

theorem specification :
 (∀ depth, 2<depth → (call depth).run caller=.ok ⟨caller,List.prefix_refl _⟩) ∧
 run (image (C:=P.C) 2 CountdownWitness.F 8 7) input=.ok returned 0 ∧
 StateRepr 1 0 16 (Frag.init P.Γ) caller P.base returned ∧ returned.stack=input.stack ∧
 returned.mem 8=w[10] ∧
 (∀ {t : LTy} (index : Idx P.Γ t), returned.mem (cellOf 0 index)=input.mem (cellOf 0 index)) ∧
 (∀ x, x<10 → returned.mem x=input.mem x) ∧
 (∀ x, 16≤x → returned.mem x=input.mem x) ∧
 (∀ j, j<2 → returned.mem (10+2*j)=input.mem 2 ∧ returned.mem (10+2*j+1)=.val (wmod (2-j))) :=
 (endpoint (tail:=[.mem CountdownWitness.A,.mem CountdownWitness.A]) "guardedCountdown" caller 2 (by decide) P.r0 rfl rfl
   GuardedPrefixes.Checks.read_domain P.base input input_repr
   8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
   (by decide) (by decide) (by decide) (by decide) rfl rfl).choose_spec

/-- The complete legacy caller/heap/physical-parent vector, now proved for
the guarded image without changing any old fixture's observation. -/
theorem observations : (CountdownWitness.observed returned,returned.mem 7)=
 (([w[77]],[w[20],w[16],w[16],w[2],w[10],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]),w[10]) := by
 rcases specification with ⟨source,executed,repr,stack,cursor,locals,low,high,saved⟩
 have p0 := saved 0 (by decide)
 have p1 := saved 1 (by decide)
 change ((returned.stack,[returned.mem 0,returned.mem 1,returned.mem 2,returned.mem 3,
   returned.mem 8,returned.mem 9,returned.mem 10,returned.mem 11,returned.mem 12,returned.mem 13,
   returned.mem 16,returned.mem 17,returned.mem 18,returned.mem 20,returned.mem 21]),returned.mem 7)=_
 rw [stack,cursor,low 7 (by decide),low 0 (by decide),low 1 (by decide),low 2 (by decide),low 3 (by decide),low 9 (by decide),
   high 16 (by decide),high 17 (by decide),high 18 (by decide),high 20 (by decide),high 21 (by decide)]
 change returned.mem 10=input.mem 2 ∧ returned.mem 11=w[2] at p0
 change returned.mem 12=input.mem 2 ∧ returned.mem 13=w[1] at p1
 rw [p0.1,p0.2,p1.1,p1.2]
 rfl

/-- Actual successful prefix followed by the returning image. -/
theorem whole (depth : Nat) (enough : 2<depth) :
 (call depth).run caller=.ok ⟨caller,List.prefix_refl _⟩ ∧
 run ([.push w[10],.mstore 7] ++ image (C:=P.C) 2 CountdownWitness.F 8 7) CountdownWitness.machine=.ok returned 0 :=
 ⟨specification.1 depth enough,(run_append_ok input_run).trans specification.2.1⟩

theorem caller_aliases : returned.mem 0=w[20] ∧ returned.mem 1=w[16] ∧ returned.mem 2=w[16] ∧ returned.mem 3=w[2] := by
 rcases specification with ⟨source,executed,repr,stack,cursor,locals,low,high,saved⟩
 exact ⟨low 0 (by decide),low 1 (by decide),low 2 (by decide),low 3 (by decide)⟩

theorem wrong_alias : returned.mem 1≠w[20] := by rw [caller_aliases.2.1];decide
theorem lost_distinct : returned.mem 0≠w[16] := by rw [caller_aliases.1];decide
theorem wrong_scalar : returned.mem 3≠w[1] := by rw [caller_aliases.2.2.2];decide

def badCaller := caller.setLocal (.here : Idx P.Γ (.val .uint)) (countValue 3 (by decide))
def badMachine := writeMachine input 3 w[3]
theorem bad_repr : StateRepr 1 0 16 (Frag.init P.Γ) badCaller P.base badMachine :=
 input_repr.setVal .here (countValue 3 (by decide)) w[3] (ReprV.uint_of rfl)

theorem bad_source (depth : Nat) : (call (depth+1)).run badCaller=.error .revert :=
 call_read_failure "guardedCountdown" CountdownWitness.args depth badCaller 2 (by decide) P.r0 rfl ArrayProbe.Checks.bad_evaluated

theorem bad_target : run (image (C:=P.C) 2 CountdownWitness.F 8 7) badMachine=.revert := by
 have projected := parameter_projection (tail:=[.mem CountdownWitness.A,.mem CountdownWitness.A]) bad_repr
 exact target_failure _ 2 (by decide) rfl P.base badMachine projected 8 7 ArrayProbe.Checks.bad_evaluated

theorem bad_not_fault : run (image (C:=P.C) 2 CountdownWitness.F 8 7) badMachine≠.fault := by
 rw [bad_target]
 intro mismatch
 cases mismatch

theorem shallow_not_return : (call 2).run caller≠.ok ⟨caller,List.prefix_refl _⟩ := by
 rw [source_all]
 simp only [show ¬2<2 from by decide,if_false]
 intro mismatch
 cases mismatch

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.GuardedCaller

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.GuardedCaller.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.GuardedCaller.endpoint

import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingPrefixes

/-! Couple reached allocating target prefixes to actual residual native source
execution. Continuation is an equation over existing Prog.run, not an evaluator,
trace semantics or supplied simulation certificate. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Native no-result caller export across the already proved prefix extension.
All reached heap, storage and other state fields come from the actual output. -/
def reexport {C : Contract} (σ : State C (Parameters A)) {H : HTy} (e : σ.H <+: H)
 (out : Solidity.Out C H (Parameters A)) : Solidity.Out C σ.H (Parameters A) :=
 ⟨out.st.withEnv (TEnv.wk (e.trans out.ext) (Parameters A) σ.env),e.trans out.ext⟩

/-- Actual residual execution is transported through the native saved callers.
The equation preserves each error class without assigning a failed State. -/
def Continuation {C : Contract} (σ τ : State C (Parameters A)) (e : σ.H <+: τ.H) (steps : Nat) : Prop :=
 ∀ depth, (AllocatingActivation.body (depth+steps)).run σ=
   ((AllocatingActivation.body depth).run τ).map (reexport σ e)

theorem successful_env {C : Contract} (σ : State C (Parameters A)) (count : Nat) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn) (depth : Nat) (out : Solidity.Out C σ.H (Parameters A))
 (actual : (AllocatingActivation.body depth).run σ=.ok out) : out.st.env=TEnv.wk out.ext (Parameters A) σ.env := by
 by_cases enough : count<depth
 · obtain ⟨known,executed,size,locals,kept⟩ := AllocatingSource.success depth σ count bound ref counter alias reads enough
   have same : out=known := Except.ok.inj (actual.symm.trans executed)
   cases same
   exact locals
 · have failed := AllocatingSource.exhaustion depth σ count bound ref counter alias reads (by omega)
   rw [failed] at actual
   cases actual

theorem reexport_self {C : Contract} (σ : State C (Parameters A)) (out : Solidity.Out C σ.H (Parameters A))
 (locals : out.st.env=TEnv.wk out.ext (Parameters A) σ.env) : reexport σ (List.prefix_refl _) out=out := by
 cases out with
 | mk st extension =>
   change st.env=TEnv.wk extension (Parameters A) σ.env at locals
   change (⟨st.withEnv (TEnv.wk extension (Parameters A) σ.env),extension⟩ : Solidity.Out C σ.H (Parameters A))=⟨st,extension⟩
   rw [←locals]
   rfl

/-- Every reached positive turn consumes the actual allocation/probe/capture
producer. Room is needed for reached turns only; no desired running prefix,
midpoint representation or heap-preservation oracle is assumed. -/
theorem coupled {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (steps count : Nat) (reached : steps≤count) (bound : count<W)
 (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor before)
 (positive : 0<b) (heapSpace : cursor.val+4*steps<W)
 (lo pointer start : Nat) (localBound : b+2<lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*steps≤frame) (fits : start+2*steps<W)
 (current : before.mem pointer=.val (wmod start)) :
 ∃ (τ : State C (Parameters A)) (e : σ.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 loopIterN (run (guardCompiled (C:=C) b F).code)
   (run (AllocatingActivation.code (C:=C) b F pointer)) steps before=.inl after ∧
 StateRepr L b frame F τ addresses after ∧
 τ.env=(countValue (count-steps) (by omega),(some (ref.wk e),())) ∧
 τ.H.length=σ.H.length+steps ∧ Heap.Keeps e σ.heap τ.heap ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (4*steps) σ base before τ addresses after ∧
 StructAllocatorRepr τ.heap addresses frame ⟨cursor.val+4*steps,heapSpace⟩ after ∧
 after.mem pointer=.val (wmod (start+2*steps)) ∧ Continuation σ τ e steps := by
 induction steps generalizing count σ base before cursor start with
 | zero =>
   refine ⟨σ,List.prefix_refl _,before,base,rfl,repr,?_,?_,Heap.Keeps.refl σ.heap,rfl,BaseExtends.refl base,?_,?_,?_,?_⟩
   · change σ.env=(countValue count bound,(some ref,()))
     exact Prod.ext counter (Prod.ext alias (by cases σ.env.2.2;rfl))
   · change σ.H.length=σ.H.length+0
     omega
   · intro other hb initial space
     simpa only [Nat.mul_zero,Nat.add_zero] using initial
   · change StructAllocatorRepr σ.heap base frame cursor before
     exact owner
   · simpa only [Nat.mul_zero,Nat.add_zero] using current
   · intro depth
     cases actual : (AllocatingActivation.body depth).run σ with
     | error halt => simp only [Nat.add_zero,actual,Except.map]
     | ok out =>
       simp only [Nat.add_zero,actual,Except.map]
       rw [reexport_self σ out (successful_env σ count bound ref counter alias reads depth out actual)]
 | succ steps ih =>
   cases count with
   | zero => omega
   | succ count =>
     let parent := AllocatingActivation.allocated σ
     let firstExtension := AllocatingActivation.extension σ
     let inherited := ref.wk firstExtension
     let child : State C (Parameters A) := parent.withEnv (countValue count (by omega),(some inherited,()))
     have firstSpace : cursor.val+4<W := by omega
     obtain ⟨next,addresses,args,entered,executed,represented,stack,extended,growth,nextPointer,payload,exterior⟩ :=
       AllocatingActivation.activation σ count bound ref counter alias (by omega) base before repr cursor owner
         positive firstSpace lo pointer start localBound pointerAbove pointerBelow payloadAbove (by omega)
         pointerBefore (by omega) current
     let nextCursor : Fin W := ⟨cursor.val+4,firstSpace⟩
     have nextOwner : StructAllocatorRepr child.heap addresses frame nextCursor next := growth cursor positive owner firstSpace
     have kept : Heap.Keeps firstExtension σ.heap child.heap := Heap.keeps_alloc σ.heap (AllocatingActivation.object σ)
     have length : child.heap.len inherited .dyn=σ.heap.len ref .dyn := kept.len ref .dyn
     have childReads : count≤child.heap.len inherited .dyn := by rw [length];omega
     have remainingSpace : nextCursor.val+4*steps<W := by change cursor.val+4+4*steps<W;omega
     obtain ⟨τ,lastExtension,after,finalAddresses,running,finalRepr,finalEnv,finalSize,finalKeeps,finalStack,finalBase,finalGrowth,finalOwner,finalPointer,resume⟩ :=
       ih (count:=count) (reached:=by omega) (bound:=by omega) (σ:=child) (ref:=inherited)
         (counter:=rfl) (alias:=rfl) (reads:=childReads) (base:=addresses) (before:=next)
         (repr:=represented) (cursor:=nextCursor) (owner:=nextOwner) (heapSpace:=remainingSpace)
         (start:=start+2) (payloadAbove:=by omega) (pointerBefore:=by omega) (capacity:=by omega)
         (fits:=by omega) (current:=nextPointer)
     have guard := guard_run σ (count+1) bound counter base before repr
     have positiveGuard : run (guardCompiled (C:=C) b F).code before=.ok (before.push w[1]) 0 := by
       simpa only [show decide (0<count+1)=true from decide_eq_true (by omega)] using guard
     have turn := successful_turn _ _ _ _ positiveGuard executed
     refine ⟨τ,firstExtension.trans lastExtension,after,finalAddresses,?_,finalRepr,?_,?_,kept.trans finalKeeps,
       finalStack.trans stack,extended.trans firstExtension finalBase,?_,?_,?_,?_⟩
     · simpa only [loopIterN,turn] using running
     · simpa only [Nat.add_sub_add_right] using finalEnv
     · change τ.H.length=(σ.H++([.array (.prim .bool)] : HTy)).length+steps at finalSize
       simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 steps] using finalSize
     · have combined := growth.comp finalGrowth
       have arithmetic : 4+4*steps=4*(steps+1) := by omega
       rw [arithmetic] at combined
       exact combined
     · have cursorEq : (⟨nextCursor.val+4*steps,remainingSpace⟩ : Fin W)=⟨cursor.val+4*(steps+1),heapSpace⟩ :=
         Fin.ext (by change cursor.val+4+4*steps=cursor.val+4*(steps+1);omega)
       rw [cursorEq] at finalOwner
       exact finalOwner
     · have arithmetic : start+2+2*steps=start+2*(steps+1) := by omega
       simpa only [arithmetic] using finalPointer

     · intro depth
       have index : depth+(steps+1)=(depth+steps)+1 := by omega
       rw [index,AllocatingActivation.source_positive σ (depth+steps) count bound ref counter alias (by omega)]
       have evaluated : (nextArgs (C:=C) A rfl).evalT parent=.ok child.env := args
       have native : (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body (depth+steps)) :
           Stmt C (Parameters A) (Parameters A)).run parent=
           ((AllocatingActivation.body depth).run τ).map
             (fun out => exported CallRet.none Ext.refl parent child.env (reexport child lastExtension out)) := by
         change TRun.call (nextArgs A rfl) .none .refl (AllocatingActivation.body (depth+steps)).runR parent=_
         unfold TRun.call
         simp only [evaluated,ok_bind,CallRet.enterT]
         change (do
           let out ← (AllocatingActivation.body (depth+steps)).run child
           pure (exported CallRet.none Ext.refl parent child.env out)) = _
         rw [resume depth]
         cases actual : (AllocatingActivation.body depth).run τ with
         | error halt => rfl
         | ok out => rfl
       rw [native]
       cases actual : (AllocatingActivation.body depth).run τ with
       | error halt => rfl
       | ok out =>
         change Except.ok (⟨out.st.withEnv
           (TEnv.wk (lastExtension.trans out.ext) (Parameters A) (TEnv.wk firstExtension (Parameters A) σ.env)),
           firstExtension.trans (lastExtension.trans out.ext)⟩ : Solidity.Out C σ.H (Parameters A))=
           .ok (reexport σ (firstExtension.trans lastExtension) out)
         rw [TEnv.wk_trans]
         rfl

/-- A genuinely zero-counter residual body discharges Continuation's source
premise. The resulting source heap is the SAME reached heap, not inferred
merely from object counts, old-object preservation or target determinism. -/
theorem finish {C : Contract} (σ τ : State C (Parameters A)) (e : σ.H <+: τ.H) (steps : Nat)
 (zero : TEnv.get (.here : Idx (Parameters A) (.val .uint)) τ.env=countValue 0 W_pos)
 (resume : Continuation σ τ e steps) :
 (AllocatingActivation.body (steps+1)).run σ=.ok (reexport σ e ⟨τ,List.prefix_refl _⟩) := by
 have done := AllocatingActivation.source_zero τ 0 zero
 have actual := resume 1
 rw [done] at actual
 simpa only [Nat.add_comm 1 steps,Except.map] using actual

/-- The descent loop terminates at child zero, and the completed native
source body returns the EXACT same reached heap with original caller locals.
Target unwind is still required to represent that returned environment. -/
theorem complete {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (count : Nat) (bound : count<W)
 (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor before)
 (positive : 0<b) (heapSpace : cursor.val+4*count<W)
 (lo pointer start : Nat) (localBound : b+2<lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) :
 ∃ (τ : State C (Parameters A)) (e : σ.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 (AllocatingActivation.body (count+1)).run σ=.ok (reexport σ e ⟨τ,List.prefix_refl _⟩) ∧
 run [.loop (guardCompiled (C:=C) b F).code (AllocatingActivation.code (C:=C) b F pointer)] before=.ok after 0 ∧
 loopIterN (run (guardCompiled (C:=C) b F).code)
   (run (AllocatingActivation.code (C:=C) b F pointer)) (count+1) before=.inr (.ok after 0) ∧
 StateRepr L b frame F τ addresses after ∧
 τ.env=(countValue 0 W_pos,(some (ref.wk e),())) ∧
 τ.H.length=σ.H.length+count ∧ Heap.Keeps e σ.heap τ.heap ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (4*count) σ base before τ addresses after ∧
 StructAllocatorRepr τ.heap addresses frame ⟨cursor.val+4*count,heapSpace⟩ after ∧
 after.mem pointer=.val (wmod (start+2*count)) := by
 obtain ⟨τ,e,after,addresses,running,represented,env,size,kept,stack,extended,growth,owned,currentAfter,resume⟩ :=
   coupled count count (by omega) bound σ ref counter alias reads base before repr cursor owner positive heapSpace
     lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current
 have zeroEnv : τ.env=(countValue 0 W_pos,(some (ref.wk e),())) := by
   simpa only [Nat.sub_self] using env
 have zeroCounter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) τ.env=countValue 0 W_pos := by rw [zeroEnv];rfl
 have source := finish σ τ e count zeroCounter resume
 have guard := guard_run τ 0 W_pos zeroCounter addresses after represented
 have done := empty_turn _ (run (AllocatingActivation.code (C:=C) b F pointer)) _ guard
 have stopped := GuardedPrefixes.finish_prefix _ _ count _ _ _ running done
 exact ⟨τ,e,after,addresses,source,successful_loop _ _ _ _ _ stopped,stopped,represented,zeroEnv,size,kept,
   stack,extended,growth,owned,currentAfter⟩

namespace Checks
open CountdownWitness

theorem available (steps : Nat) (small : steps≤2) :
 ∃ (τ : State P.C (Parameters CountdownWitness.A)) (e : callee.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
   (run (AllocatingActivation.code (C:=P.C) 2 F 8)) steps ParentPrefixes.Checks.input=.inl after ∧
 StateRepr 1 2 16 F τ addresses after ∧
 τ.env=(countValue (2-steps) (by have h : 2<W := (by decide);omega),(some (P.r0.wk e),())) ∧
 τ.H.length=callee.H.length+steps ∧ Heap.Keeps e callee.heap τ.heap ∧
 after.stack=ParentPrefixes.Checks.input.stack ∧ BaseExtends callee.H P.base addresses ∧
 GrowsAllocator 2 16 (4*steps) callee P.base ParentPrefixes.Checks.input τ addresses after ∧
 StructAllocatorRepr τ.heap addresses 16 ⟨22+4*steps,by have h : 30<W := (by decide);omega⟩ after ∧
 after.mem 8=.val (wmod (10+2*steps)) ∧ Continuation callee τ e steps :=
 coupled steps 2 small (by decide) callee P.r0 rfl rfl AllocatingSource.Checks.read_bound
   P.base ParentPrefixes.Checks.input ParentPrefixes.Checks.initial ⟨22,by decide⟩ ParentPrefixes.Checks.ownership
   (by decide) (by have h : 30<W := (by decide);change 22+4*steps<W;omega)
   8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
   (by have h : 14<W := (by decide);omega) rfl

noncomputable def source (steps : Nat) (small : steps≤2) := (available steps small).choose
noncomputable def extension (steps : Nat) (small : steps≤2) : callee.H <+: (source steps small).H :=
 (available steps small).choose_spec.choose
noncomputable def machine (steps : Nat) (small : steps≤2) : Machine :=
 (available steps small).choose_spec.choose_spec.choose
noncomputable def addresses (steps : Nat) (small : steps≤2) : Nat → Fin W :=
 (available steps small).choose_spec.choose_spec.choose_spec.choose

theorem specification (steps : Nat) (small : steps≤2) :
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
   (run (AllocatingActivation.code (C:=P.C) 2 F 8)) steps ParentPrefixes.Checks.input=.inl (machine steps small) ∧
 StateRepr 1 2 16 F (source steps small) (addresses steps small) (machine steps small) ∧
 (source steps small).env=(countValue (2-steps) (by have h : 2<W := (by decide);omega),(some (P.r0.wk (extension steps small)),())) ∧
 (source steps small).H.length=callee.H.length+steps ∧ Heap.Keeps (extension steps small) callee.heap (source steps small).heap ∧
 (machine steps small).stack=ParentPrefixes.Checks.input.stack ∧ BaseExtends callee.H P.base (addresses steps small) ∧
 GrowsAllocator 2 16 (4*steps) callee P.base ParentPrefixes.Checks.input (source steps small) (addresses steps small) (machine steps small) ∧
 StructAllocatorRepr (source steps small).heap (addresses steps small) 16 ⟨22+4*steps,by have h : 30<W := (by decide);omega⟩ (machine steps small) ∧
 (machine steps small).mem 8=.val (wmod (10+2*steps)) ∧ Continuation callee (source steps small) (extension steps small) steps :=
 (available steps small).choose_spec.choose_spec.choose_spec.choose_spec

/-- Same target execution, not an assumed equality of source model states. -/
theorem same_machine (steps : Nat) (small : steps≤2) :
 machine steps small=AllocatingPrefixes.Checks.machine steps small :=
 Sum.inl.inj ((specification steps small).1.symm.trans (AllocatingPrefixes.Checks.specification steps small).1)

theorem observations (steps : Nat) (small : steps≤2) :
 ((machine steps small).stack,[(machine steps small).mem 0,(machine steps small).mem 2,(machine steps small).mem 3,
 (machine steps small).mem 8,(machine steps small).mem 16,(machine steps small).mem 17,(machine steps small).mem 18,
 (machine steps small).mem 20,(machine steps small).mem 21])=
 ([w[77]],[.val (wmod (22+4*steps)),w[16],.val (wmod (2-steps)),.val (wmod (10+2*steps)),w[2],w[7],w[9],w[1],w[4]]) := by
 rw [same_machine steps small]
 exact AllocatingPrefixes.Checks.observations steps small

noncomputable def returned : Solidity.Out P.C callee.H (Parameters CountdownWitness.A) :=
 reexport callee (extension 2 (by decide)) ⟨source 2 (by decide),List.prefix_refl _⟩

theorem source_result : (AllocatingActivation.body 3).run callee=.ok returned := by
 rcases specification 2 (by decide) with ⟨running,repr,env,size,kept,stack,extended,growth,owner,pointer,resume⟩
 have zero : TEnv.get (.here : Idx (Parameters CountdownWitness.A) (.val .uint)) (source 2 (by decide)).env=countValue 0 W_pos := by rw [env];rfl
 exact finish callee (source 2 (by decide)) (extension 2 (by decide)) 2 zero resume

theorem source_all (depth : Nat) (enough : 2<depth) :
 (AllocatingActivation.body depth).run callee=.ok returned := by
 obtain ⟨out,actual,size,locals,kept⟩ := AllocatingSource.success depth callee 2 (by decide) P.r0 rfl rfl
   AllocatingSource.Checks.read_bound enough
 have equal := AllocatingCoherence.bodies depth 3 callee out returned actual source_result
 rw [equal] at actual
 exact actual

noncomputable def outerReturned : Solidity.Out P.C caller.H P.Γ :=
 exported CallRet.none Ext.refl caller callee.env returned

theorem caller_result : (AllocatingSource.Checks.call 3).run caller=.ok outerReturned :=
 call_return CountdownWitness.args .none .refl (AllocatingActivation.body 3).runR caller callee.env
   CountdownWitness.arguments returned source_result

/-- Full dependent output equality identifies the reached heap with the
already witnessed native caller result, not just with an old-object view. -/
theorem caller_identity : outerReturned=AllocatingSource.Checks.returned :=
 Except.ok.inj (caller_result.symm.trans AllocatingSource.Checks.specification.1)

theorem shallow : (AllocatingActivation.body 2).run callee=.error .exhausted := by
 rcases specification 2 (by decide) with ⟨running,repr,env,size,kept,stack,extended,growth,owner,pointer,resume⟩
 have actual := resume 0
 rw [AllocatingActivation.base_exhausts] at actual
 exact actual

theorem shallow_not_revert : (AllocatingActivation.body 2).run callee≠.error .revert := by
 rw [shallow]
 intro wrong
 cases wrong

/-- Heap coupling does not make the descent endpoint a returned parent. -/
theorem still_needs_unwind : ¬StateRepr 1 2 16 F returned.st (addresses 2 (by decide)) (machine 2 (by decide)) := by
 intro parent
 have expected := RecursiveHistory.counter_word returned.st 2 (by decide) rfl (addresses 2 (by decide)) (machine 2 (by decide)) parent
 have active := (AllocatingPrefixes.Checks.word_facts 2 (by decide)).2.2.2.1
 rw [←same_machine 2 (by decide)] at active
 rw [active] at expected
 exact (by decide : (.val (wmod 0) : Word)≠.val (wmod 2)) expected

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.coupled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingResume.coupled

import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingSource
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingResume

/-! Couple reached mutating allocating target prefixes to actual residual native source
execution. Continuation is an equation over existing Prog.run, not an evaluator,
trace semantics or supplied simulation certificate. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingResume
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Actual residual execution is transported through the native saved callers.
The equation preserves each error class without assigning a failed State. -/
def Continuation {C : Contract} (σ τ : State C (Parameters A)) (e : σ.H <+: τ.H) (steps : Nat) : Prop :=
 ∀ depth, (MutatingActivation.body (depth+steps)).run σ=
   ((MutatingActivation.body depth).run τ).map (AllocatingResume.reexport σ e)

theorem successful_env {C : Contract} (σ : State C (Parameters A)) (count : Nat) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn) (depth : Nat) (out : Solidity.Out C σ.H (Parameters A))
 (actual : (MutatingActivation.body depth).run σ=.ok out) : out.st.env=TEnv.wk out.ext (Parameters A) σ.env := by
 by_cases enough : count<depth
 · obtain ⟨known,executed,size,locals,kept⟩ := MutatingSource.success depth σ count bound ref counter alias reads enough
   have same : out=known := Except.ok.inj (actual.symm.trans executed)
   cases same
   exact locals
 · have failed := MutatingSource.exhaustion depth σ count bound ref counter alias reads (by omega)
   rw [failed] at actual
   cases actual

/-- Every reached positive turn consumes the actual write/allocation/probe/capture
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
   (run (MutatingActivation.code (C:=C) b F pointer)) steps before=.inl after ∧
 StateRepr L b frame F τ addresses after ∧
 τ.env=(countValue (count-steps) (by omega),(some (ref.wk e),())) ∧
 τ.H.length=σ.H.length+steps ∧ (∀ {R : RefTy} {E : Ty} (old : HRef σ.H R) (a : ArrTy R E), τ.heap.len (old.wk e) a=σ.heap.len old a) ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (4*steps) σ base before τ addresses after ∧
 StructAllocatorRepr τ.heap addresses frame ⟨cursor.val+4*steps,heapSpace⟩ after ∧
 after.mem pointer=.val (wmod (start+2*steps)) ∧ Continuation σ τ e steps := by
 induction steps generalizing count σ base before cursor start with
 | zero =>
   refine ⟨σ,List.prefix_refl _,before,base,rfl,repr,?_,?_,(fun _ _ => rfl),rfl,BaseExtends.refl base,?_,?_,?_,?_⟩
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
     cases actual : (MutatingActivation.body depth).run σ with
     | error halt => simp only [Nat.add_zero,actual,Except.map]
     | ok out =>
       simp only [Nat.add_zero,actual,Except.map]
       rw [AllocatingResume.reexport_self σ out (successful_env σ count bound ref counter alias reads depth out actual)]
 | succ steps ih =>
   cases count with
   | zero => omega
   | succ count =>
     let mutated := MutatingActivation.changed σ ref count
     let parent := AllocatingActivation.allocated mutated
     let firstExtension := AllocatingActivation.extension mutated
     let inherited := ref.wk firstExtension
     let child : State C (Parameters A) := parent.withEnv (countValue count (by omega),(some inherited,()))
     have firstSpace : cursor.val+4<W := by omega
     obtain ⟨word,next,addresses,wordRepr,written,args,entered,executed,represented,stack,extended,growth,nextPointer,payload,low,exterior⟩ :=
       MutatingActivation.activation σ count bound ref counter alias (by omega) base before repr cursor owner
         positive firstSpace lo pointer start localBound pointerAbove pointerBelow payloadAbove (by omega)
         pointerBefore (by omega) current
     let nextCursor : Fin W := ⟨cursor.val+4,firstSpace⟩
     have nextOwner : StructAllocatorRepr child.heap addresses frame nextCursor next := growth cursor positive owner firstSpace
     have kept : Heap.Keeps firstExtension mutated.heap child.heap := Heap.keeps_alloc mutated.heap (AllocatingActivation.object mutated)
     have firstLengths : ∀ {R : RefTy} {E : Ty} (old : HRef σ.H R) (a : ArrTy R E),
         child.heap.len (old.wk firstExtension) a=σ.heap.len old a := by
       intro R E old a
       exact (kept.len old a).trans (MutatingActivation.lengths σ ref count (by omega) (by omega) old a)
     have length : child.heap.len inherited .dyn=σ.heap.len ref .dyn := firstLengths ref .dyn
     have childReads : count≤child.heap.len inherited .dyn := by rw [length];omega
     have remainingSpace : nextCursor.val+4*steps<W := by change cursor.val+4+4*steps<W;omega
     obtain ⟨τ,lastExtension,after,finalAddresses,running,finalRepr,finalEnv,finalSize,finalLengths,finalStack,finalBase,finalGrowth,finalOwner,finalPointer,resume⟩ :=
       ih (count:=count) (reached:=by omega) (bound:=by omega) (σ:=child) (ref:=inherited)
         (counter:=rfl) (alias:=rfl) (reads:=childReads) (base:=addresses) (before:=next)
         (repr:=represented) (cursor:=nextCursor) (owner:=nextOwner) (heapSpace:=remainingSpace)
         (start:=start+2) (payloadAbove:=by omega) (pointerBefore:=by omega) (capacity:=by omega)
         (fits:=by omega) (current:=nextPointer)
     have guard := guard_run σ (count+1) bound counter base before repr
     have positiveGuard : run (guardCompiled (C:=C) b F).code before=.ok (before.push w[1]) 0 := by
       simpa only [show decide (0<count+1)=true from decide_eq_true (by omega)] using guard
     have turn := successful_turn _ _ _ _ positiveGuard executed
     refine ⟨τ,firstExtension.trans lastExtension,after,finalAddresses,?_,finalRepr,?_,?_,?_,
       finalStack.trans stack,extended.trans firstExtension finalBase,?_,?_,?_,?_⟩
     · simpa only [loopIterN,turn] using running
     · simpa only [Nat.add_sub_add_right] using finalEnv
     · change τ.H.length=(σ.H++([.array (.prim .bool)] : HTy)).length+steps at finalSize
       simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm 1 steps] using finalSize
     · intro R E old a
       exact (finalLengths (old.wk firstExtension) a).trans (firstLengths old a)
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
       rw [index,MutatingActivation.source_positive σ (depth+steps) count bound ref counter alias (by omega)]
       have evaluated : (nextArgs (C:=C) A rfl).evalT parent=.ok child.env := args
       have native : (.call "mutatingCountdown" (nextArgs A rfl) .none (MutatingActivation.body (depth+steps)) :
           Stmt C (Parameters A) (Parameters A)).run parent=
           ((MutatingActivation.body depth).run τ).map
             (fun out => exported CallRet.none Ext.refl parent child.env (AllocatingResume.reexport child lastExtension out)) := by
         change TRun.call (nextArgs A rfl) .none .refl (MutatingActivation.body (depth+steps)).runR parent=_
         unfold TRun.call
         simp only [evaluated,ok_bind,CallRet.enterT]
         change (do
           let out ← (MutatingActivation.body (depth+steps)).run child
           pure (exported CallRet.none Ext.refl parent child.env out)) = _
         rw [resume depth]
         cases actual : (MutatingActivation.body depth).run τ with
         | error halt => rfl
         | ok out => rfl
       rw [native]
       cases actual : (MutatingActivation.body depth).run τ with
       | error halt => rfl
       | ok out =>
         change Except.ok (⟨out.st.withEnv
           (TEnv.wk (lastExtension.trans out.ext) (Parameters A) (TEnv.wk firstExtension (Parameters A) σ.env)),
           firstExtension.trans (lastExtension.trans out.ext)⟩ : Solidity.Out C σ.H (Parameters A))=
           .ok (AllocatingResume.reexport σ (firstExtension.trans lastExtension) out)
         rw [TEnv.wk_trans]
         rfl

/-- A genuinely zero-counter residual body discharges Continuation's source
premise. The resulting source heap is the SAME reached heap, not inferred
merely from object counts, old-object preservation or target determinism. -/
theorem finish {C : Contract} (σ τ : State C (Parameters A)) (e : σ.H <+: τ.H) (steps : Nat)
 (zero : TEnv.get (.here : Idx (Parameters A) (.val .uint)) τ.env=countValue 0 W_pos)
 (resume : Continuation σ τ e steps) :
 (MutatingActivation.body (steps+1)).run σ=.ok (AllocatingResume.reexport σ e ⟨τ,List.prefix_refl _⟩) := by
 have done := MutatingActivation.source_zero τ 0 zero
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
 (MutatingActivation.body (count+1)).run σ=.ok (AllocatingResume.reexport σ e ⟨τ,List.prefix_refl _⟩) ∧
 run [.loop (guardCompiled (C:=C) b F).code (MutatingActivation.code (C:=C) b F pointer)] before=.ok after 0 ∧
 loopIterN (run (guardCompiled (C:=C) b F).code)
   (run (MutatingActivation.code (C:=C) b F pointer)) (count+1) before=.inr (.ok after 0) ∧
 StateRepr L b frame F τ addresses after ∧
 τ.env=(countValue 0 W_pos,(some (ref.wk e),())) ∧
 τ.H.length=σ.H.length+count ∧ (∀ {R : RefTy} {E : Ty} (old : HRef σ.H R) (a : ArrTy R E), τ.heap.len (old.wk e) a=σ.heap.len old a) ∧
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
 have done := empty_turn _ (run (MutatingActivation.code (C:=C) b F pointer)) _ guard
 have stopped := GuardedPrefixes.finish_prefix _ _ count _ _ _ running done
 exact ⟨τ,e,after,addresses,source,successful_loop _ _ _ _ _ stopped,stopped,represented,zeroEnv,size,kept,
   stack,extended,growth,owned,currentAfter⟩


namespace Checks
open CountdownWitness
abbrev A := CountdownWitness.A

theorem available (steps : Nat) (small : steps≤2) :
 ∃ (τ : State P.C (Parameters CountdownWitness.A)) (e : callee.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
   (run (MutatingActivation.code (C:=P.C) 2 F 8)) steps ParentPrefixes.Checks.input=.inl after ∧
 StateRepr 1 2 16 F τ addresses after ∧
 τ.env=(countValue (2-steps) (by have h : 2<W := (by decide);omega),(some (P.r0.wk e),())) ∧
 τ.H.length=callee.H.length+steps ∧ (∀ {R : RefTy} {E : Ty} (old : HRef callee.H R) (a : ArrTy R E), τ.heap.len (old.wk e) a=callee.heap.len old a) ∧
 after.stack=ParentPrefixes.Checks.input.stack ∧ BaseExtends callee.H P.base addresses ∧
 GrowsAllocator 2 16 (4*steps) callee P.base ParentPrefixes.Checks.input τ addresses after ∧
 StructAllocatorRepr τ.heap addresses 16 ⟨22+4*steps,by have h : 30<W := (by decide);omega⟩ after ∧
 after.mem 8=.val (wmod (10+2*steps)) ∧ Continuation callee τ e steps :=
 coupled steps 2 small (by decide) callee P.r0 rfl rfl MutatingSource.Checks.read_bound
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
   (run (MutatingActivation.code (C:=P.C) 2 F 8)) steps ParentPrefixes.Checks.input=.inl (machine steps small) ∧
 StateRepr 1 2 16 F (source steps small) (addresses steps small) (machine steps small) ∧
 (source steps small).env=(countValue (2-steps) (by have h : 2<W := (by decide);omega),(some (P.r0.wk (extension steps small)),())) ∧
 (source steps small).H.length=callee.H.length+steps ∧ (∀ {R : RefTy} {E : Ty} (old : HRef callee.H R) (a : ArrTy R E), (source steps small).heap.len (old.wk (extension steps small)) a=callee.heap.len old a) ∧
 (machine steps small).stack=ParentPrefixes.Checks.input.stack ∧ BaseExtends callee.H P.base (addresses steps small) ∧
 GrowsAllocator 2 16 (4*steps) callee P.base ParentPrefixes.Checks.input (source steps small) (addresses steps small) (machine steps small) ∧
 StructAllocatorRepr (source steps small).heap (addresses steps small) 16 ⟨22+4*steps,by have h : 30<W := (by decide);omega⟩ (machine steps small) ∧
 (machine steps small).mem 8=.val (wmod (10+2*steps)) ∧ Continuation callee (source steps small) (extension steps small) steps :=
 (available steps small).choose_spec.choose_spec.choose_spec.choose_spec


/-- Only machines are identified from deterministic target runs. -/
theorem same_first : machine 1 (by decide)=MutatingActivation.Checks.machine :=
 Sum.inl.inj ((specification 1 (by decide)).1.symm.trans MutatingActivation.Checks.running_prefix)

theorem same_second : machine 2 (by decide)=MutatingPrefixes.Checks.machine :=
 Sum.inl.inj ((specification 2 (by decide)).1.symm.trans MutatingPrefixes.Checks.running)

theorem zero_horizon : machine 0 (by decide)=ParentPrefixes.Checks.input := by
 have run := (specification 0 (by decide)).1
 exact (Sum.inl.inj run).symm

noncomputable def returned : Solidity.Out P.C callee.H (Parameters A) :=
 AllocatingResume.reexport callee (extension 2 (by decide)) ⟨source 2 (by decide),List.prefix_refl _⟩

theorem source_result : (MutatingActivation.body 3).run callee=.ok returned := by
 rcases specification 2 (by decide) with ⟨running,repr,env,size,lengths,stack,extended,growth,owner,pointer,resume⟩
 have zero : TEnv.get (.here : Idx (Parameters A) (.val .uint)) (source 2 (by decide)).env=countValue 0 W_pos := by rw [env];rfl
 exact finish callee (source 2 (by decide)) (extension 2 (by decide)) 2 zero resume

/-- WHOLE output equality follows the actual source execution, not the target. -/
theorem source_identity : returned=MutatingSource.Checks.rootOut :=
 Except.ok.inj (source_result.symm.trans MutatingSource.Checks.root)

/-- Recover the entered child using its proved zero counter and saved tail. -/
theorem entered_state : source 2 (by decide)=MutatingPrefixes.Checks.child := by
 rcases specification 2 (by decide) with ⟨running,repr,env,size,lengths,stack,extended,growth,owner,pointer,resume⟩
 have zero : (source 2 (by decide)).env.1=countValue 0 W_pos := by rw [env]
 have tail : (source 2 (by decide)).env.2=(TEnv.wk (extension 2 (by decide)) (Parameters A) callee.env).2 := by
   rw [env]
   rfl
 have locals : (source 2 (by decide)).env=TEnv.wk (List.prefix_refl _) (Parameters A) (source 2 (by decide)).env :=
   (TEnv.wk_self (List.prefix_refl _) (Parameters A) (source 2 (by decide)).env).symm
 have recovered := NativeUnwind.recover_export callee (source 2 (by decide)) (extension 2 (by decide)) 0 W_pos
   zero tail ⟨source 2 (by decide),List.prefix_refl _⟩ locals
 change ParentPrefixes.sourceAt returned.st 0 W_pos=source 2 (by decide) at recovered
 rw [source_identity,MutatingSource.Checks.root_state] at recovered
 have canonical : ParentPrefixes.sourceAt (ParentPrefixes.sourceAt MutatingPrefixes.Checks.child 2 (by decide)) 0 W_pos=
     MutatingPrefixes.Checks.child := rfl
 exact recovered.symm.trans canonical

noncomputable def outerReturned : Solidity.Out P.C caller.H P.Γ :=
 exported CallRet.none Ext.refl caller callee.env returned

theorem caller_result : (MutatingSource.Checks.call 3).run caller=.ok outerReturned :=
 call_return CountdownWitness.args .none .refl (MutatingActivation.body 3).runR caller callee.env
   CountdownWitness.arguments returned source_result

theorem caller_identity : outerReturned=MutatingSource.Checks.returned :=
 Except.ok.inj (caller_result.symm.trans MutatingSource.Checks.actual)

theorem caller_bindings :
 ((TEnv.get (.here : Idx P.Γ (.val .uint)) outerReturned.st.env).val,
  (TEnv.get (.there .here : Idx P.Γ (.mem A)) outerReturned.st.env).map HRef.id,
  (TEnv.get (.there (.there .here) : Idx P.Γ (.mem A)) outerReturned.st.env).map HRef.id,
  (TEnv.get (.there (.there (.there .here)) : Idx P.Γ (.mem A)) outerReturned.st.env).map HRef.id)=
 (2,some 0,some 0,some 1) := by
 rw [caller_identity]
 exact MutatingSource.Checks.ordered_bindings

theorem objects :
 returned.st.heap.len (P.r0.wk returned.ext) .dyn=2 ∧
 returned.st.heap.readAddr (.index (P.r0.wk returned.ext) .dyn (countValue 0 W_pos))=some (P.uint 1 (by decide)) ∧
 returned.st.heap.readAddr (.index (P.r0.wk returned.ext) .dyn (countValue 1 (by decide)))=some (P.uint 2 (by decide)) ∧
 returned.st.heap.len (Evm.Memory.CompileExamples.r1.wk returned.ext) .dyn=1 ∧
 returned.st.heap.readAddr (.index (Evm.Memory.CompileExamples.r1.wk returned.ext) .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) := by
 rw [source_identity]
 exact MutatingSource.Checks.objects

theorem shallow (steps : Nat) (small : steps≤2) : (MutatingActivation.body steps).run callee=.error .exhausted := by
 rcases specification steps small with ⟨running,repr,env,size,lengths,stack,extended,growth,owner,pointer,resume⟩
 have actual := resume 0
 rw [MutatingActivation.base_exhausts] at actual
 simpa only [Nat.zero_add,Except.map] using actual

theorem unrestored_view : returned.st≠source 2 (by decide) := by
 intro same
 have actual := congrArg (fun σ : State P.C (Parameters A) => (TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env).val) same
 have locals := (specification 2 (by decide)).2.2.1
 rw [source_identity] at actual
 change (2:Int)=(TEnv.get (.here : Idx (Parameters A) (.val .uint)) (source 2 (by decide)).env).val at actual
 rw [locals] at actual
 change (2:Int)=0 at actual
 omega

theorem wrong_horizon : machine 2 (by decide)≠machine 1 (by decide) := by
 rw [same_first,same_second]
 exact MutatingPrefixes.Checks.wrong_horizon

theorem first_observations :
 ((machine 1 (by decide)).stack,[(machine 1 (by decide)).mem 0,(machine 1 (by decide)).mem 1,(machine 1 (by decide)).mem 2,(machine 1 (by decide)).mem 3,(machine 1 (by decide)).mem 4,
 (machine 1 (by decide)).mem 7,(machine 1 (by decide)).mem 8,(machine 1 (by decide)).mem 9,(machine 1 (by decide)).mem 10,(machine 1 (by decide)).mem 11,(machine 1 (by decide)).mem 12,(machine 1 (by decide)).mem 13,
 (machine 1 (by decide)).mem 16,(machine 1 (by decide)).mem 17,(machine 1 (by decide)).mem 18,(machine 1 (by decide)).mem 20,(machine 1 (by decide)).mem 21,
 (machine 1 (by decide)).mem 22,(machine 1 (by decide)).mem 23,(machine 1 (by decide)).mem 24,(machine 1 (by decide)).mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[1],w[22],w[10],w[12],w[99],w[16],w[2],w[0],w[0],w[2],w[7],w[2],w[1],w[4],w[3],w[0],w[0],w[0]]) := by
 rw [same_first]
 exact MutatingActivation.Checks.observations

theorem second_observations :
 ((machine 2 (by decide)).stack,[(machine 2 (by decide)).mem 0,(machine 2 (by decide)).mem 1,(machine 2 (by decide)).mem 2,(machine 2 (by decide)).mem 3,(machine 2 (by decide)).mem 4,
 (machine 2 (by decide)).mem 7,(machine 2 (by decide)).mem 8,(machine 2 (by decide)).mem 9,(machine 2 (by decide)).mem 10,(machine 2 (by decide)).mem 11,(machine 2 (by decide)).mem 12,(machine 2 (by decide)).mem 13,
 (machine 2 (by decide)).mem 16,(machine 2 (by decide)).mem 17,(machine 2 (by decide)).mem 18,(machine 2 (by decide)).mem 20,(machine 2 (by decide)).mem 21,
 (machine 2 (by decide)).mem 22,(machine 2 (by decide)).mem 23,(machine 2 (by decide)).mem 24,(machine 2 (by decide)).mem 25,
 (machine 2 (by decide)).mem 26,(machine 2 (by decide)).mem 27,(machine 2 (by decide)).mem 28,(machine 2 (by decide)).mem 29])=
 ([w[77]],[w[30],w[16],w[16],w[0],w[26],w[10],w[14],w[99],w[16],w[2],w[16],w[1],
 w[2],w[1],w[2],w[1],w[4],w[3],w[0],w[0],w[0],w[3],w[0],w[0],w[0]]) := by
 rw [same_second]
 exact MutatingPrefixes.Checks.observations

theorem source_all (depth : Nat) (enough : 2<depth) : (MutatingActivation.body depth).run callee=.ok returned := by
 obtain ⟨out,actual,growth,locals,lengths⟩ := MutatingSource.success depth callee 2 (by decide) P.r0 rfl rfl
   MutatingSource.Checks.read_bound enough
 have same := MutatingSource.bodies depth 3 callee out returned actual source_result
 rw [same] at actual
 exact actual

theorem shallow_not_revert (steps : Nat) (small : steps≤2) :
 (MutatingActivation.body steps).run callee≠.error .revert := by
 rw [shallow steps small]
 intro impossible
 cases impossible

theorem wrong_old_content : returned.st.heap.readAddr (.index (P.r0.wk returned.ext) .dyn (countValue 0 W_pos))≠
 some (P.uint 7 (by decide)) := by
 rw [objects.2.1]
 intro same
 have values := congrArg (fun v : PrimTy.uint.Denote => v.val) (Option.some.inj same)
 change (1:Int)=7 at values
 omega

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingResume

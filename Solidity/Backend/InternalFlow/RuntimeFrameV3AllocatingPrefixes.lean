import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingCoherence

/-! Actual fixed-image allocating descent prefixes, represented active native
children and exact reached allocator growth. This is not recursive return or
public compiler admission. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingPrefixes
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Every reached positive turn consumes the actual allocation/probe/capture
producer. Room is needed for reached turns only; no desired running prefix,
midpoint representation or heap-preservation oracle is assumed. -/
theorem reached {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
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
 after.mem pointer=.val (wmod (start+2*steps)) := by
 induction steps generalizing count σ base before cursor start with
 | zero =>
   refine ⟨σ,List.prefix_refl _,before,base,rfl,repr,?_,?_,Heap.Keeps.refl σ.heap,rfl,BaseExtends.refl base,?_,?_,?_⟩
   · change σ.env=(countValue count bound,(some ref,()))
     exact Prod.ext counter (Prod.ext alias (by cases σ.env.2.2;rfl))
   · change σ.H.length=σ.H.length+0
     omega
   · intro other hb initial space
     simpa only [Nat.mul_zero,Nat.add_zero] using initial
   · change StructAllocatorRepr σ.heap base frame cursor before
     exact owner
   · simpa only [Nat.mul_zero,Nat.add_zero] using current
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
     obtain ⟨τ,lastExtension,after,finalAddresses,running,finalRepr,finalEnv,finalSize,finalKeeps,finalStack,finalBase,finalGrowth,finalOwner,finalPointer⟩ :=
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
       finalStack.trans stack,extended.trans firstExtension finalBase,?_,?_,?_⟩
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

/-- Read an older primitive array from the SAME reached represented heap,
using its real reference weakening and preserved identity-to-address map. -/
theorem old_array {H H' : HTy} (e : H <+: H') {hp : Heap H} {hp' : Heap H'}
 (kept : Heap.Keeps e hp hp') {base addresses : Nat → Fin W} {frame : Nat} {m : Machine}
 (extended : BaseExtends H base addresses) (represented : HeapRepr hp' addresses frame m)
 {p : PrimTy} (r : HRef H (.array (.prim p))) : ArrayRepr hp r (base r.id) m := by
 have array := represented.arrays (r.wk e)
 change ArrayRepr hp' (r.wk e) (addresses r.id) m at array
 rw [extended r] at array
 have length := kept.len r .dyn
 have elements : MObj.elems .dyn (hp'.get (r.wk e))=MObj.elems .dyn (hp.get r) := by
   rw [kept r,MObj.elems_wk]
   exact List.map_id _
 refine ⟨?_,?_,?_⟩
 · simpa only [length] using array.space
 · simpa only [length] using array.length
 · intro i v actual
   apply array.elements i v
   rw [elements]
   exact actual

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
 after.mem 8=.val (wmod (10+2*steps)) :=
 reached steps 2 small (by decide) callee P.r0 rfl rfl AllocatingSource.Checks.read_bound
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
 (machine steps small).mem 8=.val (wmod (10+2*steps)) :=
 (available steps small).choose_spec.choose_spec.choose_spec.choose_spec

/-- Ordered primitive/pointer words are read from the SAME reached state.
No concrete loop or compiler certificate is replayed to obtain this snapshot. -/
theorem word_facts (steps : Nat) (small : steps≤2) :
 (machine steps small).stack=[w[77]] ∧
 (machine steps small).mem 0=.val (wmod (22+4*steps)) ∧
 (machine steps small).mem 2=w[16] ∧
 (machine steps small).mem 3=.val (wmod (2-steps)) ∧
 (machine steps small).mem 8=.val (wmod (10+2*steps)) ∧
 (machine steps small).mem 16=w[2] ∧ (machine steps small).mem 17=w[7] ∧
 (machine steps small).mem 18=w[9] ∧ (machine steps small).mem 20=w[1] ∧ (machine steps small).mem 21=w[4] := by
 rcases specification steps small with ⟨running,repr,env,size,kept,stack,extended,growth,owner,pointer⟩
 have counter : TEnv.get (.here : Idx (Parameters CountdownWitness.A) (.val .uint)) (source steps small).env=
     countValue (2-steps) (by have h : 2<W := (by decide);omega) := by rw [env];rfl
 have counterWord := RecursiveHistory.counter_word (source steps small) (2-steps) _ counter (addresses steps small) (machine steps small) repr
 obtain ⟨reference,binding,referenceWord⟩ := repr.pointers (.there .here)
 have expected : TEnv.get (.there .here : Idx (Parameters CountdownWitness.A) (.mem CountdownWitness.A)) (source steps small).env=
     some (P.r0.wk (extension steps small)) := by rw [env];rfl
 have same : reference=P.r0.wk (extension steps small) := Option.some.inj (binding.symm.trans expected)
 subst reference
 change (machine steps small).mem 2=.val (addresses steps small P.r0.id) at referenceWord
 rw [extended P.r0] at referenceWord
 have cursorWord : (machine steps small).mem 0=.val (wmod (22+4*steps)) := by
   rw [owner.arrays.free.cell]
   congr 1
   exact Fin.ext (Nat.mod_eq_of_lt (by have h : 30<W := (by decide);omega)).symm
 have first := old_array (extension steps small) kept extended repr.heap P.r0
 have other := old_array (extension steps small) kept extended repr.heap Evm.Memory.CompileExamples.r1
 have firstLength := first.length
 have otherLength := other.length
 rw [HeapDomain.Checks.length_zero] at firstLength
 rw [HeapDomain.Checks.length_one] at otherLength
 have first0 := first.elements 0 (P.uint 7 (by decide)) (by with_unfolding_all rfl)
 have first1 := first.elements 1 (P.uint 9 (by decide)) (by with_unfolding_all rfl)
 have other0 := other.elements 0 (P.uint 4 (by decide)) (by with_unfolding_all rfl)
 have word7 : (machine steps small).mem 17=w[7] := Restore.uint_unique first0 (ReprV.uint_of rfl)
 have word9 : (machine steps small).mem 18=w[9] := Restore.uint_unique first1 (ReprV.uint_of rfl)
 have word4 : (machine steps small).mem 21=w[4] := Restore.uint_unique other0 (ReprV.uint_of rfl)
 exact ⟨stack,cursorWord,referenceWord,counterWord,pointer,firstLength,word7,word9,otherLength,word4⟩

theorem observations (steps : Nat) (small : steps≤2) :
 ((machine steps small).stack,[(machine steps small).mem 0,(machine steps small).mem 2,(machine steps small).mem 3,
 (machine steps small).mem 8,(machine steps small).mem 16,(machine steps small).mem 17,(machine steps small).mem 18,
 (machine steps small).mem 20,(machine steps small).mem 21])=
 ([w[77]],[.val (wmod (22+4*steps)),w[16],.val (wmod (2-steps)),.val (wmod (10+2*steps)),w[2],w[7],w[9],w[1],w[4]]) := by
 rcases word_facts steps small with ⟨stack,cursor,reference,counter,pointer,length0,first0,first1,length1,other0⟩
 rw [stack,cursor,reference,counter,pointer,length0,first0,first1,length1,other0]

/-- The next false guard stops without reaching another allocation. -/
theorem stopped : loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
 (run (AllocatingActivation.code (C:=P.C) 2 F 8)) 3 ParentPrefixes.Checks.input=.inr (.ok (machine 2 (by decide)) 0) := by
 rcases specification 2 (by decide) with ⟨running,repr,env,size,kept,stack,extended,growth,owner,pointer⟩
 have counter : TEnv.get (.here : Idx (Parameters CountdownWitness.A) (.val .uint)) (source 2 (by decide)).env=countValue 0 W_pos := by rw [env];rfl
 have guard := guard_run (source 2 (by decide)) 0 W_pos counter (addresses 2 (by decide)) (machine 2 (by decide)) repr
 have done := empty_turn _ (run (AllocatingActivation.code (C:=P.C) 2 F 8)) _ guard
 exact GuardedPrefixes.finish_prefix _ _ 2 _ _ _ running done

theorem stopped_stable (horizon : Nat) (later : 3≤horizon) :
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
 (run (AllocatingActivation.code (C:=P.C) 2 F 8)) horizon ParentPrefixes.Checks.input=.inr (.ok (machine 2 (by decide)) 0) :=
 loopIterN_done_le later stopped

theorem target_loop : run [.loop (guardCompiled (C:=P.C) 2 F).code (AllocatingActivation.code (C:=P.C) 2 F 8)]
 ParentPrefixes.Checks.input=.ok (machine 2 (by decide)) 0 := successful_loop _ _ _ _ _ stopped

theorem wrong_alias (steps : Nat) (small : steps≤2) : (machine steps small).mem 2≠w[20] := by
 rw [(word_facts steps small).2.2.1]
 decide

theorem wrong_old_content (steps : Nat) (small : steps≤2) : (machine steps small).mem 18≠w[4] := by
 rw [(word_facts steps small).2.2.2.2.2.2.2.1]
 decide

theorem wrong_horizon : machine 0 (by decide)≠machine 1 (by decide) := by
 intro same
 have cursor := congrArg (fun m : Machine => m.mem 0) same
 change (machine 0 (by decide)).mem 0=(machine 1 (by decide)).mem 0 at cursor
 rw [(word_facts 0 (by decide)).2.1,(word_facts 1 (by decide)).2.1] at cursor
 exact (by decide : (.val (wmod 22) : Word)≠.val (wmod 26)) cursor

/-- Descent completion represents child zero, not the returned parent two. -/
theorem not_returned_parent : ¬StateRepr 1 2 16 F callee P.base (machine 2 (by decide)) := by
 intro represented
 have expected := RecursiveHistory.counter_word callee 2 (by decide) rfl P.base (machine 2 (by decide)) represented
 have active := (word_facts 2 (by decide)).2.2.2.1
 rw [active] at expected
 exact (by decide : (.val (wmod 0) : Word)≠.val (wmod 2)) expected

/-- Four cells would account for only one turn, not the actual two-turn prefix. -/
theorem wrong_cost : ¬GrowsAllocator 2 16 4 callee P.base ParentPrefixes.Checks.input
 (source 2 (by decide)) (addresses 2 (by decide)) (machine 2 (by decide)) := by
 intro wrong
 have owner := wrong ⟨22,by decide⟩ (by decide) ParentPrefixes.Checks.ownership (by decide)
 have cursor := owner.arrays.free.cell
 rw [(word_facts 2 (by decide)).2.1] at cursor
 exact (by decide : (.val (wmod 30) : Word)≠w[26]) cursor

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingPrefixes

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingPrefixes.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingPrefixes.reached

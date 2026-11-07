import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingActivation

/-! Actual fixed-image mutating/allocating descent prefixes. Each reached turn
consumes the real write, allocation and call-entry producer. Array lengths and
addresses are preserved, not old contents or a complete native return trace. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingPrefixes
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- Every reached positive turn consumes the actual write/allocation/probe/capture
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
   (run (MutatingActivation.code (C:=C) b F pointer)) steps before=.inl after ∧
 StateRepr L b frame F τ addresses after ∧
 τ.env=(countValue (count-steps) (by omega),(some (ref.wk e),())) ∧
 τ.H.length=σ.H.length+steps ∧
 (∀ {R : RefTy} {E : Ty} (old : HRef σ.H R) (a : ArrTy R E), τ.heap.len (old.wk e) a=σ.heap.len old a) ∧
 after.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (4*steps) σ base before τ addresses after ∧
 StructAllocatorRepr τ.heap addresses frame ⟨cursor.val+4*steps,heapSpace⟩ after ∧
 after.mem pointer=.val (wmod (start+2*steps)) := by
 induction steps generalizing count σ base before cursor start with
 | zero =>
   refine ⟨σ,List.prefix_refl _,before,base,rfl,repr,?_,?_,(fun _ _ => rfl),rfl,BaseExtends.refl base,?_,?_,?_⟩
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
     obtain ⟨τ,lastExtension,after,finalAddresses,running,finalRepr,finalEnv,finalSize,finalLengths,finalStack,finalBase,finalGrowth,finalOwner,finalPointer⟩ :=
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
       finalStack.trans stack,extended.trans firstExtension finalBase,?_,?_,?_⟩
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


namespace Checks
open CountdownWitness

theorem horizons (steps : Nat) (small : steps≤2) :
 ∃ (τ : State P.C (Parameters CountdownWitness.A)) (e : callee.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
   (run (MutatingActivation.code (C:=P.C) 2 F 8)) steps ParentPrefixes.Checks.input=.inl after ∧
 StateRepr 1 2 16 F τ addresses after ∧
 τ.env=(countValue (2-steps) (by have h : 2<W := (by decide);omega),(some (P.r0.wk e),())) ∧
 τ.H.length=callee.H.length+steps ∧
 (∀ {R : RefTy} {E : Ty} (old : HRef callee.H R) (a : ArrTy R E), τ.heap.len (old.wk e) a=callee.heap.len old a) ∧
 after.stack=ParentPrefixes.Checks.input.stack ∧ BaseExtends callee.H P.base addresses ∧
 GrowsAllocator 2 16 (4*steps) callee P.base ParentPrefixes.Checks.input τ addresses after ∧
 StructAllocatorRepr τ.heap addresses 16 ⟨22+4*steps,by have h : 30<W := (by decide);omega⟩ after ∧
 after.mem 8=.val (wmod (10+2*steps)) :=
 reached steps 2 small (by decide) callee P.r0 rfl rfl AllocatingSource.Checks.read_bound
   P.base ParentPrefixes.Checks.input ParentPrefixes.Checks.initial ⟨22,by decide⟩ ParentPrefixes.Checks.ownership
   (by decide) (by have h : 30<W := (by decide);change 22+4*steps<W;omega)
   8 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
   (by have h : 14<W := (by decide);omega) rfl

abbrev A := CountdownWitness.A
noncomputable abbrev first := MutatingActivation.Checks.machine
abbrev firstState := MutatingActivation.Checks.child
abbrev firstRef := MutatingActivation.Checks.reference
noncomputable abbrev firstAddresses := MutatingActivation.Checks.addresses

def mutated := MutatingActivation.changed firstState firstRef 0
def parent := AllocatingActivation.allocated mutated
def reference := firstRef.wk (AllocatingActivation.extension mutated)
def child := parent.withEnv (Δ:=Parameters A) (countValue 0 W_pos,(some reference,()))
noncomputable def allocationMachine := writeMachine
 (allocateMachine (writeMachine first 17 w[1]) (⟨26,by decide⟩ : Fin W) AllocatingActivation.size) 4 w[26]

theorem first_length : firstState.heap.len firstRef .dyn=2 := MutatingActivation.Checks.source_objects.1

theorem available : ∃ after addresses,
 (MutatingActivation.write (C:=P.C)).run firstState=.ok ⟨mutated,List.prefix_refl _⟩ ∧
 (nextArgs A rfl).evalT parent=.ok child.env ∧
 ((CallRet.none : CallRet (Parameters A) [] (Parameters A)).enterT (parent.withEnv child.env)).st=child ∧
 run (MutatingActivation.code (C:=P.C) 2 F 8) first=.ok after 0 ∧
 StateRepr 1 2 16 F child addresses after ∧ after.stack=first.stack ∧
 BaseExtends firstState.H firstAddresses addresses ∧
 GrowsAllocator 2 16 4 firstState firstAddresses first child addresses after ∧
 after.mem 8=w[14] ∧
 (∀ i,i<2 → after.mem (12+i)=first.mem (2+i)) ∧
 (∀ x,0<x → x<16 → x≠3 → x≠4 → x≠8 → (x<12 ∨ 14≤x) → after.mem x=first.mem x) ∧
 (∀ x,x≠8 → x≠3 → (x<12 ∨ 14≤x) → after.mem x=allocationMachine.mem x) := by
 rcases MutatingActivation.Checks.specification with ⟨args,entered,executed,repr,stack,extended,growth,pointer,payload,low,exterior⟩
 have owner : StructAllocatorRepr firstState.heap firstAddresses 16 (⟨26,by decide⟩ : Fin W) first :=
   growth (⟨22,by decide⟩ : Fin W) (by decide) ParentPrefixes.Checks.ownership (by decide)
 obtain ⟨word,after,addresses,value,source,args2,entered2,executed2,repr2,stack2,extended2,growth2,pointer2,payload2,low2,exterior2⟩ :=
   MutatingActivation.activation firstState 0 (by decide) firstRef rfl rfl (by rw [first_length];decide)
     firstAddresses first repr (⟨26,by decide⟩ : Fin W) owner (by decide) (by decide)
     8 8 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) pointer
 have same : word=w[1] := Restore.uint_unique value (ReprV.uint_of rfl)
 subst word
 have address : (firstAddresses firstRef.id).val+1+0=17 := by
   have old := extended P.r0
   change firstAddresses firstRef.id=P.base P.r0.id at old
   rw [old]
   rfl
 rw [address] at exterior2
 exact ⟨after,addresses,source,args2,entered2,executed2,repr2,stack2,extended2,growth2,pointer2,payload2,low2,exterior2⟩

noncomputable def machine : Machine := available.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose

theorem specification :
 (MutatingActivation.write (C:=P.C)).run firstState=.ok ⟨mutated,List.prefix_refl _⟩ ∧
 (nextArgs A rfl).evalT parent=.ok child.env ∧
 ((CallRet.none : CallRet (Parameters A) [] (Parameters A)).enterT (parent.withEnv child.env)).st=child ∧
 run (MutatingActivation.code (C:=P.C) 2 F 8) first=.ok machine 0 ∧
 StateRepr 1 2 16 F child addresses machine ∧ machine.stack=first.stack ∧
 BaseExtends firstState.H firstAddresses addresses ∧
 GrowsAllocator 2 16 4 firstState firstAddresses first child addresses machine ∧
 machine.mem 8=w[14] ∧
 (∀ i,i<2 → machine.mem (12+i)=first.mem (2+i)) ∧
 (∀ x,0<x → x<16 → x≠3 → x≠4 → x≠8 → (x<12 ∨ 14≤x) → machine.mem x=first.mem x) ∧
 (∀ x,x≠8 → x≠3 → (x<12 ∨ 14≤x) → machine.mem x=allocationMachine.mem x) :=
 available.choose_spec.choose_spec

/-- The reached child owns the next allocation input from the SAME first run. -/
theorem capacity : AllocationInput 2 16 4 firstState firstAddresses first := by
 rcases MutatingActivation.Checks.specification with ⟨_,_,_,_,_,_,growth,_⟩
 exact growth.nextInput (.inr ⟨by decide,⟨22,by decide⟩,ParentPrefixes.Checks.ownership,by decide⟩)

theorem total :
 machine.stack=ParentPrefixes.Checks.input.stack ∧
 BaseExtends callee.H P.base addresses ∧
 GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input child addresses machine ∧
 StructAllocatorRepr child.heap addresses 16 (⟨30,by decide⟩ : Fin W) machine := by
 rcases MutatingActivation.Checks.specification with ⟨_,_,_,_,firstStack,firstBase,firstGrowth,_⟩
 rcases specification with ⟨_,_,_,_,_,stack,base,growth,_⟩
 have combined : GrowsAllocator 2 16 8 callee P.base ParentPrefixes.Checks.input child addresses machine := firstGrowth.comp growth
 exact ⟨stack.trans firstStack,firstBase.trans (AllocatingActivation.extension MutatingActivation.Checks.mutated) base,
   combined,combined (⟨22,by decide⟩ : Fin W) (by decide) ParentPrefixes.Checks.ownership (by decide)⟩

theorem running :
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
  (run (MutatingActivation.code (C:=P.C) 2 F 8)) 2 ParentPrefixes.Checks.input=.inl machine := by
 rcases MutatingActivation.Checks.specification with ⟨_,_,_,repr,_⟩
 rcases specification with ⟨_,_,_,executed,_⟩
 have guard : run (guardCompiled (C:=P.C) 2 F).code first=.ok (first.push w[1]) 0 :=
   guard_run firstState 1 (by decide) rfl firstAddresses first repr
 have turn := successful_turn _ _ _ _ guard executed
 simp only [loopIterN,MutatingActivation.Checks.running_turn,turn]

theorem observations :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,machine.mem 11,machine.mem 12,machine.mem 13,
 machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 20,machine.mem 21,
 machine.mem 22,machine.mem 23,machine.mem 24,machine.mem 25,
 machine.mem 26,machine.mem 27,machine.mem 28,machine.mem 29])=
 ([w[77]],[w[30],w[16],w[16],w[0],w[26],w[10],w[14],w[99],w[16],w[2],w[16],w[1],
 w[2],w[1],w[2],w[1],w[4],w[3],w[0],w[0],w[0],w[3],w[0],w[0],w[0]]) := by
 rcases specification with ⟨source,args,entered,actual,repr,stack,extended,growth,pointer,payload,low,exterior⟩
 have counter := RecursiveHistory.counter_word child 0 W_pos rfl addresses machine repr
 have refWord := payload 0 (by decide)
 have countWord := payload 1 (by decide)
 change machine.mem 12=first.mem 2 at refWord
 change machine.mem 13=first.mem 3 at countWord
 have prior := congrArg Prod.snd MutatingActivation.Checks.observations
 simp only [List.cons.injEq,and_true] at prior
 rcases prior with ⟨h0,h1,h2,h3,h4,h7,h8,h9,h10,h11,h12,h13,h16,h17,h18,h20,h21,h22,h23,h24,h25⟩
 have owner : StructAllocatorRepr firstState.heap firstAddresses 16 (⟨26,by decide⟩ : Fin W) first := by
   rcases MutatingActivation.Checks.specification with ⟨_,_,_,_,_,_,g,_⟩
   exact g (⟨22,by decide⟩ : Fin W) (by decide) ParentPrefixes.Checks.ownership (by decide)
 have z27 := owner.arrays.free.zero 27 (by decide)
 have z28 := owner.arrays.free.zero 28 (by decide)
 have z29 := owner.arrays.free.zero 29 (by decide)
 rw [stack,counter,pointer,refWord,countWord,
   exterior 0 (by decide) (by decide) (.inl (by decide)),
   exterior 1 (by decide) (by decide) (.inl (by decide)),
   exterior 2 (by decide) (by decide) (.inl (by decide)),
   exterior 4 (by decide) (by decide) (.inl (by decide)),
   exterior 7 (by decide) (by decide) (.inl (by decide)),
   exterior 9 (by decide) (by decide) (.inl (by decide)),
   exterior 10 (by decide) (by decide) (.inl (by decide)),
   exterior 11 (by decide) (by decide) (.inl (by decide)),
   exterior 16 (by decide) (by decide) (.inr (by decide)),
   exterior 17 (by decide) (by decide) (.inr (by decide)),
   exterior 18 (by decide) (by decide) (.inr (by decide)),
   exterior 20 (by decide) (by decide) (.inr (by decide)),
   exterior 21 (by decide) (by decide) (.inr (by decide)),
   exterior 22 (by decide) (by decide) (.inr (by decide)),
   exterior 23 (by decide) (by decide) (.inr (by decide)),
   exterior 24 (by decide) (by decide) (.inr (by decide)),
   exterior 25 (by decide) (by decide) (.inr (by decide)),
   exterior 26 (by decide) (by decide) (.inr (by decide)),
   exterior 27 (by decide) (by decide) (.inr (by decide)),
   exterior 28 (by decide) (by decide) (.inr (by decide)),
   exterior 29 (by decide) (by decide) (.inr (by decide))]
 change (first.stack,[w[30],first.mem 1,first.mem 2,w[0],w[26],first.mem 7,w[14],first.mem 9,
 first.mem 10,first.mem 11,first.mem 2,first.mem 3,first.mem 16,w[1],first.mem 18,first.mem 20,first.mem 21,
 first.mem 22,first.mem 23,first.mem 24,first.mem 25,w[3],first.mem 27,first.mem 28,first.mem 29])=_
 have priorStack := congrArg Prod.fst MutatingActivation.Checks.observations
 change first.stack=[w[77]] at priorStack
 rw [priorStack,h1,h2,h3,h7,h9,h10,h11,h16,h18,h20,h21,h22,h23,h24,h25,z27,z28,z29]

theorem stopped :
 loopTurn (run (guardCompiled (C:=P.C) 2 F).code)
  (run (MutatingActivation.code (C:=P.C) 2 F 8)) machine=.inr (.ok machine 0) := by
 rcases specification with ⟨_,_,_,_,repr,_⟩
 exact empty_turn _ _ _ (guard_run child 0 W_pos rfl addresses machine repr)

theorem stopped_horizons (horizon : Nat) (later : 3≤horizon) :
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
  (run (MutatingActivation.code (C:=P.C) 2 F 8)) horizon ParentPrefixes.Checks.input=.inr (.ok machine 0) :=
 loopIterN_done_le later (finish_prefix _ _ 2 _ _ _ running stopped)

/-- Actual descent loop stops before the separate parent-unwind program. -/
theorem loop_endpoint :
 run [.loop (guardCompiled (C:=P.C) 2 F).code (MutatingActivation.code (C:=P.C) 2 F 8)]
  ParentPrefixes.Checks.input=.ok machine 0 :=
 successful_loop _ _ _ _ 3 (stopped_horizons 3 (by decide))

theorem child_source (depth : Nat) : (MutatingActivation.body (depth+1)).run child=.ok ⟨child,List.prefix_refl _⟩ :=
 MutatingActivation.source_zero child depth rfl

theorem child_exhausts : (MutatingActivation.body 0).run child=.error .exhausted := rfl

theorem source_objects :
 child.heap.len reference .dyn=2 ∧
 child.heap.readAddr (.index reference .dyn (countValue 0 W_pos))=some (P.uint 1 (by decide)) ∧
 child.heap.readAddr (.index reference .dyn (countValue 1 (by decide)))=some (P.uint 2 (by decide)) ∧
 child.heap.len ((Evm.Memory.CompileExamples.r1.wk (AllocatingActivation.extension MutatingActivation.Checks.mutated)).wk
   (AllocatingActivation.extension mutated)) .dyn=1 ∧
 child.heap.readAddr (.index ((Evm.Memory.CompileExamples.r1.wk (AllocatingActivation.extension MutatingActivation.Checks.mutated)).wk
   (AllocatingActivation.extension mutated)) .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) := by
 let other := Evm.Memory.CompileExamples.r1.wk (AllocatingActivation.extension MutatingActivation.Checks.mutated)
 have wrote := MutatingActivation.write_addr firstState firstRef 0 W_pos (by rw [first_length];decide)
 have kept : Heap.Keeps (AllocatingActivation.extension mutated) mutated.heap parent.heap :=
   Heap.keeps_alloc mutated.heap (AllocatingActivation.object mutated)
 have first1 : mutated.heap.readAddr (.index firstRef .dyn (countValue 0 W_pos))=some (P.uint 1 (by decide)) :=
   Heap.readAddr_writeAddr_same wrote
 have second2 : mutated.heap.readAddr (.index firstRef .dyn (countValue 1 (by decide)))=some (P.uint 2 (by decide)) :=
   (Heap.readAddr_writeAddr_apart wrote (bd:=.index firstRef .dyn (countValue 1 (by decide))) (by
     intro _ same
     have values := congrArg (fun v : PrimTy.uint.Denote => v.val) same
     change (0:Int)=1 at values
     omega)).trans MutatingActivation.Checks.source_objects.2.2.1
 have other4 : mutated.heap.readAddr (.index other .dyn (countValue 0 W_pos))=some (P.uint 4 (by decide)) :=
   (Heap.readAddr_writeAddr_apart wrote (bd:=.index other .dyn (countValue 0 W_pos)) (by
     intro same
     change (0:Nat)=1 at same
     omega)).trans MutatingActivation.Checks.source_objects.2.2.2.2
 have len0 := MutatingActivation.lengths firstState firstRef 0 W_pos (by rw [first_length];decide) firstRef .dyn
 have len1 := MutatingActivation.lengths firstState firstRef 0 W_pos (by rw [first_length];decide) other .dyn
 refine ⟨(kept.len firstRef .dyn).trans (len0.trans first_length),?_,?_,
   (kept.len other .dyn).trans (len1.trans MutatingActivation.Checks.source_objects.2.2.2.1),?_⟩
 · have same := kept.readAddr (.index firstRef .dyn (countValue 0 W_pos))
   rw [first1] at same
   exact same
 · have same := kept.readAddr (.index firstRef .dyn (countValue 1 (by decide)))
   rw [second2] at same
   exact same
 · have same := kept.readAddr (.index other .dyn (countValue 0 W_pos))
   rw [other4] at same
   exact same

/-- Reject the earlier one-turn machine as the two-turn result. -/
theorem wrong_horizon : machine≠first := by
 intro same
 have cursor := congrArg (fun m : Machine => m.mem 8) same
 change machine.mem 8=first.mem 8 at cursor
 rw [specification.2.2.2.2.2.2.2.2.1,MutatingActivation.Checks.specification.2.2.2.2.2.2.2.1] at cursor
 cases cursor

theorem target_facts : machine.mem 0=w[30] ∧ machine.mem 1=w[16] ∧ machine.mem 3=w[0] ∧
 machine.mem 11=w[2] ∧ machine.mem 13=w[1] ∧ machine.mem 17=w[1] ∧ machine.mem 18=w[2] ∧ machine.mem 21=w[4] := by
 have actual := congrArg Prod.snd observations
 simp only [List.cons.injEq,and_true] at actual
 rcases actual with ⟨h0,h1,h2,h3,h4,h7,h8,h9,h10,h11,h12,h13,h16,h17,h18,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩
 exact ⟨h0,h1,h3,h11,h13,h17,h18,h21⟩

theorem wrong_cursor : machine.mem 0≠w[26] := by rw [target_facts.1];decide
theorem wrong_alias : machine.mem 1≠w[20] := by rw [target_facts.2.1];decide
theorem missing_write : machine.mem 17≠w[7] := by rw [target_facts.2.2.2.2.2.1];decide
theorem swapped_parents : machine.mem 11≠machine.mem 13 := by rw [target_facts.2.2.2.1,target_facts.2.2.2.2.1];decide
theorem unrelated_write : machine.mem 21≠w[1] := by rw [target_facts.2.2.2.2.2.2.2];decide

theorem bad_horizons (n : Nat) :
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
  (run (MutatingActivation.code (C:=P.C) 2 F 8)) (n+1) MutatingActivation.Checks.badMachine=.inr .revert := by
 simp only [loopIterN,MutatingActivation.Checks.bad_turn]

end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingPrefixes

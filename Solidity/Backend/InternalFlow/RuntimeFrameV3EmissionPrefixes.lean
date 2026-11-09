import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingEmission

/-! Actual state-budgeted emission Entry to allocating descent horizons.
Reached source/target states, native continuations and saved parents are
outputs of existing execution producers, not assumed trace certificates. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EmissionPrefixes
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes AllocatingEmission
abbrev A : RefTy := CountdownWitness.A

/-- Self-entry arguments preserve the existing native body judgment, including
errors. No new evaluator or source continuation relation is defined. -/
theorem call_body {C : Contract} (name : Name) (σ : State C (Parameters A))
 (ref : HRef σ.H A) (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : (counter σ).val≤σ.heap.len ref .dyn) (depth : Nat) :
 (InterfaceV1.recursiveSource name AllocatingEmission.args .none AllocatingActivation.step depth).run σ=
 (AllocatingActivation.body depth).run σ := by
 cases actual : (AllocatingActivation.body depth).run σ with
 | ok out => exact body_is_call name σ ref alias reads depth out actual
 | error halt =>
   have canonical : σ.env=(countValue (counter σ).val (counter σ).isLt,(some ref,())) :=
     Prod.ext (counter_value σ) (Prod.ext alias (by cases σ.env.2.2;rfl))
   have evaluated : AllocatingEmission.args.evalT σ=.ok σ.env :=
     (arguments σ ref alias).trans (congrArg Except.ok canonical.symm)
   change TRun.call AllocatingEmission.args .none .refl (AllocatingActivation.body depth).runR σ=_
   simp only [TRun.call,evaluated,ok_bind,CallRet.enterT]
   change (do
     let out ← (AllocatingActivation.body depth).run σ
     pure (exported (ps:=Parameters A) (CallRet.none : CallRet (Parameters A) [] (Parameters A)) Ext.refl σ σ.env out))=_
   rw [actual]
   rfl

theorem code_parts {C : Contract} (b lo : Nat) (F : Frag (Parameters A)) :
 (plan (C:=C) b lo F).code=RecursiveIngress.code lo (lo-1)++
   ([.loop (guardCompiled (C:=C) b F).code (AllocatingActivation.code (C:=C) b F lo)]++PairedUnwind.code b lo (lo-1) A) := rfl

/-- All feasible running horizons of the actual image, including zero without
an ownership existence premise. Read validity is source data; all machine,
allocator, continuation and history facts are derived from actual Entry. -/
theorem running {C : Contract} {b lo L frame : Nat} {F : Frag (Parameters A)}
 (name : Name) (σ : State C (Parameters A)) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (entry : InterfaceV1.Entry (plan b lo F) L b frame F σ base before start)
 (reads : (counter σ).val≤length σ) (steps : Nat) (small : steps≤(counter σ).val) :
 ∃ (ref : HRef σ.H A) (entered : Machine) (τ : State C (Parameters A)) (e : σ.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref ∧
 run (RecursiveIngress.code lo (lo-1)) before=.ok entered 0 ∧
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F lo)) steps entered=.inl after ∧
 StateRepr L b frame F τ addresses after ∧
 τ.env=(countValue ((counter σ).val-steps) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (counter σ).isLt),(some (ref.wk e),())) ∧
 τ.H.length=σ.H.length+steps ∧ Heap.Keeps e σ.heap τ.heap ∧ after.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator b frame (4*steps) σ base before τ addresses after ∧
 after.mem lo=.val (wmod (start+2*steps)) ∧
 (∀ depth,(InterfaceV1.recursiveSource name AllocatingEmission.args .none AllocatingActivation.step (depth+steps)).run σ=
   ((AllocatingActivation.body depth).run τ).map (AllocatingResume.reexport σ e)) ∧
 (∀ j,j<steps → after.mem (start+2*j)=.val (base ref.id) ∧ after.mem (start+2*j+1)=.val (wmod ((counter σ).val-j))) ∧
 Footprint.Words (lo+1) start before after ∧ after.mem (lo-1)=.val (wmod start) ∧
 (∀ x,0<x → x<frame → x≠b+1 → x≠b+2 → x≠lo → x≠lo-1 →
   (x<start ∨ start+2*steps≤x) → after.mem x=before.mem x) := by
 obtain ⟨ref,alias,reference⟩ := entry.represented.pointers (.there .here)
 change before.mem b=.val (base ref.id) at reference
 have readable : (counter σ).val≤σ.heap.len ref .dyn := by rw [←length_of_alias σ ref alias];exact reads
 have prepared := RecursiveIngress.entry_prepared (plan b lo F) entry (by change 4≤4;decide) rfl
 obtain ⟨workspace,pointerBelow,pointerBefore,bottomAbove,bottomBefore,reserve,fits⟩ := entry_bounds entry reads
 cases steps with
 | zero =>
   have resume : AllocatingResume.Continuation σ σ (List.prefix_refl _) 0 := by
     intro depth
     cases actual : (AllocatingActivation.body depth).run σ with
     | error halt => simp only [Except.map]
     | ok out =>
       simp only [Except.map]
       rw [AllocatingResume.reexport_self σ out (AllocatingResume.successful_env σ (counter σ).val (counter σ).isLt ref
         (counter_value σ) alias readable depth out actual)]
   refine ⟨ref,RecursiveIngress.prepared before lo (lo-1),σ,List.prefix_refl _,RecursiveIngress.prepared before lo (lo-1),base,
     alias,prepared.1,rfl,prepared.2.1.represented,?_,?_,Heap.Keeps.refl σ.heap,rfl,BaseExtends.refl _,?_,?_,?_,?_,?_,prepared.2.2.1,?_⟩
   · change σ.env=(countValue (counter σ).val (counter σ).isLt,(some ref,()))
     exact Prod.ext (counter_value σ) (Prod.ext alias (by cases σ.env.2.2;rfl))
   · omega
   · simpa only [Nat.mul_zero,plan] using prepared.2.2.2.2
   · simpa only [Nat.mul_zero,Nat.add_zero,plan] using prepared.2.1.cursor
   · intro depth
     exact (call_body name σ ref alias readable (depth+0)).trans (resume depth)
   · intro j impossible;omega
   · intro x lower upper
     exact prepared.2.2.2.1 x (by change lo≤x;omega) upper
   · intro x positive below counterCell temporaryCell pointerCell bottomCell exterior
     exact upd_other _ _ bottomCell
 | succ steps =>
   have costEq : (plan b lo F).heapCost σ=4*(counter σ).val := by
     change cost σ=_
     rw [cost,length_of_alias σ ref alias,AllocatingOutcome.demand,ite_eq_left readable]
   have capacity : AllocationInput b frame (4*(counter σ).val) σ base (RecursiveIngress.prepared before lo (lo-1)) := by
     rw [←costEq]
     exact prepared.2.1.capacity
   rcases capacity with impossible | ⟨positive,cursor,owner,space⟩
   · omega
   · have stepSpace : cursor.val+4*(steps+1)<W := by omega
     obtain ⟨τ,e,after,addresses,actual,repr,env,size,kept,stack,extended,growth,owned,current,resume⟩ :=
       AllocatingResume.coupled (steps+1) (counter σ).val small (counter σ).isLt σ ref (counter_value σ) alias readable
         base (RecursiveIngress.prepared before lo (lo-1)) prepared.2.1.represented cursor owner positive stepSpace
         lo lo start (by omega) (by omega) pointerBelow entry.payloadAbove pointerBefore (by omega) (by omega) prepared.2.1.cursor
     obtain ⟨saved,outside,active⟩ := AllocatingHistory.history (steps+1) (counter σ).val small (counter σ).isLt σ ref (counter_value σ) alias readable
       base (RecursiveIngress.prepared before lo (lo-1)) prepared.2.1.represented cursor owner positive stepSpace
       lo lo start (by omega) (by omega) pointerBelow entry.payloadAbove pointerBefore (by omega) (by omega) prepared.2.1.cursor after actual
     have total := prepared.2.2.2.2.comp growth
     refine ⟨ref,RecursiveIngress.prepared before lo (lo-1),τ,e,after,addresses,alias,prepared.1,actual,repr,env,size,kept,stack,extended,?_,current,?_,?_,?_,?_,?_⟩
     · simpa only [Nat.zero_add] using total
     · intro depth
       exact (call_body name σ ref alias readable (depth+(steps+1))).trans (resume depth)
     · intro j lower
       exact ⟨(saved j lower).1.trans ((upd_other _ _ (by omega)).trans reference),(saved j lower).2⟩
     · intro x lower upper
       exact (outside x (by omega) (by omega) (by omega) (by omega) (by omega) (.inl upper)).trans (upd_other _ _ (by omega))
     · exact (outside (lo-1) (by omega) (by omega) (by omega) (by omega) (by omega) (.inl bottomBefore)).trans prepared.2.2.1
     · intro x positive below counterCell temporaryCell pointerCell bottomCell exterior
       exact (outside x positive below counterCell temporaryCell pointerCell exterior).trans (upd_other _ _ bottomCell)

/-- Completing descent performs one false guard after the last activation.
This stopped state is still the zero-counter callee, before paired unwind. -/
theorem full_stop {C : Contract} {b lo L frame : Nat} {F : Frag (Parameters A)}
 (name : Name) (σ : State C (Parameters A)) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (entry : InterfaceV1.Entry (plan b lo F) L b frame F σ base before start)
 (reads : (counter σ).val≤length σ) :
 ∃ (entered : Machine) (τ : State C (Parameters A)) (after : Machine) (addresses : Nat → Fin W),
 run (RecursiveIngress.code lo (lo-1)) before=.ok entered 0 ∧
 StateRepr L b frame F τ addresses after ∧
 TEnv.get (.here : Idx (Parameters A) (.val .uint)) τ.env=countValue 0 W_pos ∧
 (∀ horizon,(counter σ).val+1≤horizon →
   loopIterN (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F lo)) horizon entered=.inr (.ok after 0)) := by
 obtain ⟨ref,entered,τ,e,after,addresses,alias,setup,actual,repr,env,rest⟩ :=
   running name σ base before start entry reads (counter σ).val (Nat.le_refl _)
 have zero : TEnv.get (.here : Idx (Parameters A) (.val .uint)) τ.env=countValue 0 W_pos := by
   rw [env]
   change countValue ((counter σ).val-(counter σ).val) _=countValue 0 W_pos
   simp only [Nat.sub_self]
 have guard := guard_run τ 0 W_pos zero addresses after repr
 have stopped := GuardedPrefixes.finish_prefix _ _ (counter σ).val entered after (.ok after 0) actual
   (empty_turn _ (run (AllocatingActivation.code (C:=C) b F lo)) _ guard)
 exact ⟨entered,τ,after,addresses,setup,repr,zero,fun horizon bound => loopIterN_done_le bound stopped⟩

set_option backward.isDefEq.respectTransparency false in
/-- Invalid initial reads terminate on the actual first allocating turn.
Only the successful ingress machine is exposed; failure has no reached Out. -/
theorem failing {C : Contract} {b lo L frame : Nat} {F : Frag (Parameters A)}
 (name : Name) (σ : State C (Parameters A)) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (entry : InterfaceV1.Entry (plan b lo F) L b frame F σ base before start)
 (bad : ¬(counter σ).val≤length σ) :
 ∃ entered, run (RecursiveIngress.code lo (lo-1)) before=.ok entered 0 ∧
 (∀ depth,(InterfaceV1.recursiveSource name AllocatingEmission.args .none AllocatingActivation.step (depth+1)).run σ=.error .revert) ∧
 (∀ horizon,1≤horizon → loopIterN (run (guardCompiled (C:=C) b F).code)
   (run (AllocatingActivation.code (C:=C) b F lo)) horizon entered=.inr .revert) := by
 obtain ⟨ref,alias,reference⟩ := entry.represented.pointers (.there .here)
 have readable : ¬(counter σ).val≤σ.heap.len ref .dyn := by rw [←length_of_alias σ ref alias];exact bad
 have prepared := RecursiveIngress.entry_prepared (plan b lo F) entry (by change 4≤4;decide) rfl
 have costEq : (plan b lo F).heapCost σ=4 := by change cost σ=4;rw [cost,AllocatingOutcome.demand,ite_eq_right bad]
 have capacity : AllocationInput b frame 4 σ base (RecursiveIngress.prepared before lo (lo-1)) := by rw [←costEq];exact prepared.2.1.capacity
 rcases capacity with impossible | ⟨positive,cursor,owner,space⟩
 · cases impossible
 · cases number : (counter σ).val with
   | zero => omega
   | succ n =>
     have bound : n+1<W := by have h:=(counter σ).isLt;omega
     have count : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) bound := by simpa only [number] using counter_value σ
     have failed : ArrayProbe.value.evalT σ=.error .revert := (HeapDomain.failure_iff σ n bound ref count alias).2 (by omega)
     have current := guard_run σ (n+1) bound count base (RecursiveIngress.prepared before lo (lo-1)) prepared.2.1.represented
     have currentOne : run (guardCompiled (C:=C) b F).code (RecursiveIngress.prepared before lo (lo-1))=
       .ok ((RecursiveIngress.prepared before lo (lo-1)).push w[1]) 0 := by
       simpa only [decide_eq_true (by omega : 0<n+1),bword,ite_true] using current
     have workspace : b+4≤lo := entry.workspace
     have below : lo<frame := entry.pointerBelow
     have body := AllocatingFailure.target_suffix σ n bound ref count alias failed base _ prepared.2.1.represented cursor owner positive space (by omega) lo []
     have turn := failing_turn _ _ _ currentOne (by simpa only [List.append_nil,plan] using body)
     have first : loopIterN (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F lo)) 1
       (RecursiveIngress.prepared before lo (lo-1))=.inr .revert := turn
     have canonical : σ.env=(countValue (n+1) bound,(some ref,())) := Prod.ext count (Prod.ext alias (by cases σ.env.2.2;rfl))
     have evaluated : AllocatingEmission.args.evalT σ=.ok (countValue (n+1) bound,(some ref,())) := by
       simpa only [number] using arguments σ ref alias
     have failedEntered : ArrayProbe.value.evalT (σ.withEnv (Δ:=Parameters A) (countValue (n+1) bound,(some ref,())))=.error .revert := by rw [←canonical];exact failed
     exact ⟨RecursiveIngress.prepared before lo (lo-1),prepared.1,
       fun depth => AllocatingFailure.call_failure name AllocatingEmission.args σ depth n bound ref evaluated failedEntered,
       fun horizon bound => loopIterN_done_le bound first⟩

namespace Checks
open CountdownWitness
abbrev before := AllocatorReturn.Checks.input

theorem setup : run (RecursiveIngress.code 8 7) before=.ok ParentPrefixes.Checks.input 0 := by
 rw [RecursiveIngress.executed,RecursiveIngress.Checks.initialized_eq]

theorem available (steps : Nat) (small : steps≤2) :
 ∃ (τ : State P.C (Parameters A)) (e : callee.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (AllocatingActivation.code (C:=P.C) 2 F 8)) steps ParentPrefixes.Checks.input=.inl after ∧
 StateRepr 1 2 16 F τ addresses after ∧
 τ.env=(countValue (2-steps) (by have h:2<W:=(by decide);omega),(some (P.r0.wk e),())) ∧
 τ.H.length=callee.H.length+steps ∧ Heap.Keeps e callee.heap τ.heap ∧ after.stack=before.stack ∧
 BaseExtends callee.H P.base addresses ∧ GrowsAllocator 2 16 (4*steps) callee P.base before τ addresses after ∧
 after.mem 8=.val (wmod (10+2*steps)) ∧
 (∀ depth,(InterfaceV1.recursiveSource "allocatingCountdown" AllocatingEmission.args .none AllocatingActivation.step (depth+steps)).run callee=
   ((AllocatingActivation.body depth).run τ).map (AllocatingResume.reexport callee e)) ∧
 (∀ j,j<steps → after.mem (10+2*j)=w[16] ∧ after.mem (10+2*j+1)=.val (wmod (2-j))) ∧
 Footprint.Words 9 10 before after ∧ after.mem 7=w[10] ∧
 (∀ x,0<x → x<16 → x≠3 → x≠4 → x≠8 → x≠7 → (x<10 ∨ 10+2*steps≤x) → after.mem x=before.mem x) := by
 obtain ⟨ref,entered,τ,e,after,addresses,alias,setupRun,actual,repr,env,size,kept,stack,extended,growth,current,resume,saved,words,bottom,exterior⟩ :=
   running "allocatingCountdown" callee P.base before 10 AllocatingEmission.Checks.entry
     (by rw [AllocatingEmission.Checks.counter_two,AllocatingEmission.Checks.length_two];decide) steps
     (by rw [AllocatingEmission.Checks.counter_two];exact small)
 have sameRef : ref=P.r0 := Option.some.inj alias.symm
 subst ref
 have sameEntry : entered=ParentPrefixes.Checks.input := (Evm.Out.ok.inj (setupRun.symm.trans setup)).1
 subst entered
 exact ⟨τ,e,after,addresses,actual,repr,env,size,kept,stack,extended,growth,current,resume,saved,words,bottom,exterior⟩

noncomputable def source (steps : Nat) (small : steps≤2) := (available steps small).choose
noncomputable def extension (steps : Nat) (small : steps≤2) := (available steps small).choose_spec.choose
noncomputable def machine (steps : Nat) (small : steps≤2) := (available steps small).choose_spec.choose_spec.choose
noncomputable def addresses (steps : Nat) (small : steps≤2) := (available steps small).choose_spec.choose_spec.choose_spec.choose

theorem specification (steps : Nat) (small : steps≤2) :
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (AllocatingActivation.code (C:=P.C) 2 F 8)) steps ParentPrefixes.Checks.input=.inl (machine steps small) ∧
 StateRepr 1 2 16 F (source steps small) (addresses steps small) (machine steps small) ∧
 (source steps small).env=(countValue (2-steps) (by have h:2<W:=(by decide);omega),(some (P.r0.wk (extension steps small)),())) ∧
 (source steps small).H.length=callee.H.length+steps ∧ Heap.Keeps (extension steps small) callee.heap (source steps small).heap ∧
 (machine steps small).stack=before.stack ∧ BaseExtends callee.H P.base (addresses steps small) ∧
 GrowsAllocator 2 16 (4*steps) callee P.base before (source steps small) (addresses steps small) (machine steps small) ∧
 (machine steps small).mem 8=.val (wmod (10+2*steps)) ∧
 (∀ depth,(InterfaceV1.recursiveSource "allocatingCountdown" AllocatingEmission.args .none AllocatingActivation.step (depth+steps)).run callee=
   ((AllocatingActivation.body depth).run (source steps small)).map (AllocatingResume.reexport callee (extension steps small))) ∧
 (∀ j,j<steps → (machine steps small).mem (10+2*j)=w[16] ∧ (machine steps small).mem (10+2*j+1)=.val (wmod (2-j))) ∧
 Footprint.Words 9 10 before (machine steps small) ∧ (machine steps small).mem 7=w[10] ∧
 (∀ x,0<x → x<16 → x≠3 → x≠4 → x≠8 → x≠7 → (x<10 ∨ 10+2*steps≤x) → (machine steps small).mem x=before.mem x) :=
 (available steps small).choose_spec.choose_spec.choose_spec.choose_spec

/-- Only the machine identity follows from target determinism. No source
state equality is assumed merely from equal lengths or observations. -/
theorem same_machine (steps : Nat) (small : steps≤2) : machine steps small=AllocatingResume.Checks.machine steps small :=
 Sum.inl.inj ((specification steps small).1.symm.trans (AllocatingResume.Checks.specification steps small).1)

theorem observations (steps : Nat) (small : steps≤2) :
 ((machine steps small).stack,[(machine steps small).mem 0,(machine steps small).mem 2,(machine steps small).mem 3,
 (machine steps small).mem 8,(machine steps small).mem 16,(machine steps small).mem 17,(machine steps small).mem 18,
 (machine steps small).mem 20,(machine steps small).mem 21])=
 ([w[77]],[.val (wmod (22+4*steps)),w[16],.val (wmod (2-steps)),.val (wmod (10+2*steps)),w[2],w[7],w[9],w[1],w[4]]) := by
 rw [same_machine steps small]
 exact AllocatingResume.Checks.observations steps small

theorem owned (steps : Nat) (small : steps≤2) :
 StructAllocatorRepr (source steps small).heap (addresses steps small) 16
   (⟨22+4*steps,by have bound:30<W:=(by decide);omega⟩ : Fin W) (machine steps small) := by
 have growth := (specification steps small).2.2.2.2.2.2.2.1
 exact growth ⟨22,by decide⟩ (by decide) AllocatorReturn.Checks.ownership (by change 22+4*steps<W;have bound:30<W:=(by decide);omega)

theorem continuation (steps : Nat) (small : steps≤2) (depth : Nat) :
 (InterfaceV1.recursiveSource "allocatingCountdown" AllocatingEmission.args .none AllocatingActivation.step (depth+steps)).run callee=
 ((AllocatingActivation.body depth).run (source steps small)).map (AllocatingResume.reexport callee (extension steps small)) :=
 (specification steps small).2.2.2.2.2.2.2.2.2.1 depth

theorem word_facts (steps : Nat) (small : steps≤2) :
 (machine steps small).stack=[w[77]] ∧ (machine steps small).mem 0=.val (wmod (22+4*steps)) ∧
 (machine steps small).mem 2=w[16] ∧ (machine steps small).mem 3=.val (wmod (2-steps)) ∧
 (machine steps small).mem 8=.val (wmod (10+2*steps)) ∧ (machine steps small).mem 16=w[2] ∧
 (machine steps small).mem 17=w[7] ∧ (machine steps small).mem 18=w[9] ∧ (machine steps small).mem 20=w[1] ∧ (machine steps small).mem 21=w[4] := by
 rw [same_machine steps small,AllocatingResume.Checks.same_machine steps small]
 exact AllocatingPrefixes.Checks.word_facts steps small

theorem complete_observations (steps : Nat) (small : steps≤2) :
 ((machine steps small).stack,[(machine steps small).mem 0,(machine steps small).mem 1,(machine steps small).mem 2,(machine steps small).mem 3,
 (machine steps small).mem 7,(machine steps small).mem 8,(machine steps small).mem 9,(machine steps small).mem 10,(machine steps small).mem 11,
 (machine steps small).mem 12,(machine steps small).mem 13,(machine steps small).mem 16,(machine steps small).mem 17,(machine steps small).mem 18,
 (machine steps small).mem 20,(machine steps small).mem 21])=
 ([w[77]],[.val (wmod (22+4*steps)),w[16],w[16],.val (wmod (2-steps)),w[10],.val (wmod (10+2*steps)),w[99],
 (if 0<steps then w[16] else w[0]),(if 0<steps then w[2] else w[0]),(if 1<steps then w[16] else w[0]),(if 1<steps then w[1] else w[0]),
 w[2],w[7],w[9],w[1],w[4]]) := by
 rcases word_facts steps small with ⟨stack,cursor,active,count,pointer,len0,a,b,len1,c⟩
 rcases specification steps small with ⟨running,repr,env,size,kept,oldStack,extended,growth,current,resume,saved,words,bottom,exterior⟩
 have older : (machine steps small).mem 1=w[16] := exterior 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
 have marker : (machine steps small).mem 9=w[99] := words 9 (by decide) (by decide)
 have first : (machine steps small).mem 10=(if 0<steps then w[16] else w[0]) ∧
   (machine steps small).mem 11=(if 0<steps then w[2] else w[0]) := by
   by_cases positive : 0<steps
   · rw [ite_eq_left positive,ite_eq_left positive]
     exact saved 0 positive
   · rw [ite_eq_right positive,ite_eq_right positive]
     exact ⟨exterior 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by omega)),
       exterior 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by omega))⟩
 have second : (machine steps small).mem 12=(if 1<steps then w[16] else w[0]) ∧
   (machine steps small).mem 13=(if 1<steps then w[1] else w[0]) := by
   by_cases positive : 1<steps
   · rw [ite_eq_left positive,ite_eq_left positive]
     exact saved 1 positive
   · rw [ite_eq_right positive,ite_eq_right positive]
     exact ⟨exterior 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by omega)),
       exterior 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by omega))⟩
 rw [stack,cursor,older,active,count,bottom,pointer,marker,first.1,first.2,second.1,second.2,len0,a,b,len1,c]

theorem stopped (horizon : Nat) (bound : 3≤horizon) :
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (AllocatingActivation.code (C:=P.C) 2 F 8)) horizon ParentPrefixes.Checks.input=
 .inr (.ok (machine 2 (by decide)) 0) := by
 have spec := specification 2 (by decide)
 have zero : TEnv.get (.here : Idx (Parameters A) (.val .uint)) (source 2 (by decide)).env=countValue 0 W_pos := by
   rw [spec.2.2.1]
   rfl
 have guard := guard_run (source 2 (by decide)) 0 W_pos zero (addresses 2 (by decide)) (machine 2 (by decide)) spec.2.1
 have done := GuardedPrefixes.finish_prefix _ _ 2 ParentPrefixes.Checks.input _ (.ok (machine 2 (by decide)) 0) spec.1
   (empty_turn _ (run (AllocatingActivation.code (C:=P.C) 2 F 8)) _ guard)
 exact loopIterN_done_le bound done

/-- Actual completed descent slice of the emitted image, excluding unwind. -/
theorem descent_target : run (RecursiveIngress.code 8 7++
 [.loop (guardCompiled (C:=P.C) 2 F).code (AllocatingActivation.code (C:=P.C) 2 F 8)]) before=
 .ok (machine 2 (by decide)) 0 :=
 (run_append_ok setup).trans (successful_loop _ _ _ _ 3 (stopped 3 (by decide)))

theorem native_shallow :
 (InterfaceV1.recursiveSource "allocatingCountdown" (AllocatingEmission.args (C:=P.C)) .none AllocatingActivation.step 2).run callee=.error .exhausted := by
 have actual := continuation 2 (by decide) 0
 rw [AllocatingActivation.base_exhausts] at actual
 exact actual

theorem wrong_horizon :
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (AllocatingActivation.code (C:=P.C) 2 F 8)) 1 ParentPrefixes.Checks.input≠
 .inl (machine 2 (by decide)) := by
 rw [(specification 1 (by decide)).1]
 intro wrong
 have same := congrArg (fun m : Machine => m.mem 8) (Sum.inl.inj wrong)
 change (machine 1 (by decide)).mem 8=(machine 2 (by decide)).mem 8 at same
 rw [(word_facts 1 (by decide)).2.2.2.2.1,(word_facts 2 (by decide)).2.2.2.2.1] at same
 exact (by decide : (.val (wmod (10+2*1)) : Word)≠.val (wmod (10+2*2))) same

theorem descent_not_returned : (machine 2 (by decide)).mem 8≠w[10] := by
 rw [(word_facts 2 (by decide)).2.2.2.2.1]
 decide

theorem not_final_machine : machine 2 (by decide)≠AllocatingEmission.Checks.target := by
 intro same
 apply descent_not_returned
 rw [same]
 exact AllocatingEmission.Checks.specification.2.2.2.2.2.1

theorem wrong_alias : (machine 1 (by decide)).mem 2≠w[20] := by
 rw [(word_facts 1 (by decide)).2.2.1]
 decide

theorem wrong_saved_order : (machine 2 (by decide)).mem 11≠w[1] ∧ (machine 2 (by decide)).mem 13≠w[2] := by
 rcases specification 2 (by decide) with ⟨running,repr,env,size,kept,stack,extended,growth,current,resume,saved,words,bottom,exterior⟩
 have first := (saved 0 (by decide)).2
 have second := (saved 1 (by decide)).2
 rw [first,second]
 constructor <;> decide

theorem wrong_cost : ¬GrowsAllocator 2 16 4 callee P.base before (source 2 (by decide)) (addresses 2 (by decide)) (machine 2 (by decide)) := by
 intro bad
 have wrong := (bad ⟨22,by decide⟩ (by decide) AllocatorReturn.Checks.ownership (by decide)).arrays.free.cell
 have actual := (owned 2 (by decide)).arrays.free.cell
 exact (by decide : (w[30] : Word)≠w[26]) (actual.symm.trans wrong)

theorem failure_horizons : ∃ entered,
 run (RecursiveIngress.code 8 7) AllocatingEmission.Checks.badBefore=.ok entered 0 ∧
 (∀ depth,(AllocatingEmission.Checks.call (depth+1)).run AllocatingEmission.Checks.bad=.error .revert) ∧
 (∀ horizon,1≤horizon → loopIterN (run (guardCompiled (C:=P.C) 2 F).code)
   (run (AllocatingActivation.code (C:=P.C) 2 F 8)) horizon entered=.inr .revert) :=
 failing "allocatingCountdown" AllocatingEmission.Checks.bad P.base AllocatingEmission.Checks.badBefore 10 AllocatingEmission.Checks.bad_entry
   (by rw [AllocatingEmission.Checks.counter_three,AllocatingEmission.Checks.bad_length_two];decide)

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.EmissionPrefixes

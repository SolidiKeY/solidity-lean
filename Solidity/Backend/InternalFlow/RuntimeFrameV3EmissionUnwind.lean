import Solidity.Backend.InternalFlow.RuntimeFrameV3EmissionPrefixes

/-! Partial paired unwind of the same state-budgeted recursive emission.
The zero-counter state and saved payload are derived from actual descent;
no returned caller, intermediate representation or heap oracle is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EmissionUnwind
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes AllocatingEmission
abbrev A : RefTy := CountdownWitness.A

/-- Every feasible parent horizon after actual allocating descent. The source
state under representation is the reached child with its restored parent
locals, not an independently assumed output of a source run. -/
theorem parents {C : Contract} {b lo L frame : Nat} {F : Frag (Parameters A)}
 (name : Name) (σ : State C (Parameters A)) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (entry : InterfaceV1.Entry (plan b lo F) L b frame F σ base before start)
 (reads : (counter σ).val≤length σ) (steps : Nat) (small : steps≤(counter σ).val) :
 ∃ (ref : HRef σ.H A) (entered : Machine) (τ : State C (Parameters A)) (e : σ.H <+: τ.H)
   (down last : Machine) (addresses : Nat → Fin W),
 TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref ∧
 run (RecursiveIngress.code lo (lo-1)) before=.ok entered 0 ∧
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F lo)) (counter σ).val entered=.inl down ∧
 loopIterN (run (PairedUnwind.condition lo (lo-1)))
   (run (Restore.restoreCells lo (Restore.contextCells b (Parameters A)))) steps down=.inl last ∧
 τ.env=(countValue 0 W_pos,(some (ref.wk e),())) ∧
 StateRepr L b frame F (ParentPrefixes.sourceAt τ steps (Nat.lt_of_le_of_lt small (counter σ).isLt)) addresses last ∧
 τ.H.length=σ.H.length+(counter σ).val ∧ Heap.Keeps e σ.heap τ.heap ∧
 last.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (4*(counter σ).val) σ base before
   (ParentPrefixes.sourceAt τ steps (Nat.lt_of_le_of_lt small (counter σ).isLt)) addresses last ∧
 last.mem lo=.val (wmod (start+2*((counter σ).val-steps))) ∧
 last.mem b=.val (base ref.id) ∧
 (∀ j,j<(counter σ).val → last.mem (start+2*j)=.val (base ref.id) ∧
   last.mem (start+2*j+1)=.val (wmod ((counter σ).val-j))) ∧
 (∀ x,x≠lo → x≠b → x≠b+1 → last.mem x=down.mem x) ∧
 Footprint.Words (lo+1) start before last ∧ last.mem (lo-1)=.val (wmod start) := by
 obtain ⟨ref,entered,τ,e,down,addresses,alias,setup,descent,repr,env,size,kept,stack,extended,growth,current,resume,saved,words,bottom,exterior⟩ :=
   EmissionPrefixes.running name σ base before start entry reads (counter σ).val (Nat.le_refl _)
 have zeroEnv : τ.env=(countValue 0 W_pos,(some (ref.wk e),())) := by
   simpa only [Nat.sub_self] using env
 have zeroAt : ParentPrefixes.sourceAt τ 0 W_pos=τ := by
   change τ.withEnv (Δ:=Parameters A) (countValue 0 W_pos,τ.env.2)=τ
   have data : (countValue 0 W_pos,τ.env.2)=τ.env := by rw [zeroEnv];rfl
   exact (congrArg (fun locals => τ.withEnv (Δ:=Parameters A) locals) data).trans rfl
 obtain ⟨reachedRef,reachedAlias,reachedWord⟩ := repr.pointers (.there .here)
 have reachedAlias' : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) τ.env=some (ref.wk e) := by rw [zeroEnv];rfl
 have same : reachedRef=ref.wk e := Option.some.inj (reachedAlias.symm.trans reachedAlias')
 subst reachedRef
 have reference : down.mem b=.val (base ref.id) := reachedWord.trans (congrArg Word.val (extended ref))
 have parentInput : StateRepr L b frame F
     (ParentPrefixes.sourceAt τ ((counter σ).val-(counter σ).val) (by omega)) addresses down := by
   simpa only [Nat.sub_self,zeroAt] using repr
 have savedHere : ∀ j,j<(counter σ).val → down.mem (start+2*j)=down.mem b ∧
     down.mem (start+2*j+1)=.val (wmod ((counter σ).val-j)) := by
   intro j bound
   exact ⟨(saved j bound).1.trans reference.symm,(saved j bound).2⟩
 obtain ⟨workspace,pointerBelow,pointerBefore,bottomAbove,bottomBefore,reserve,fits⟩ := entry_bounds entry reads
 obtain ⟨last,unwinding,parentRepr,parentStack,parentCursor,parentRef,parentGrowth,high,outside⟩ :=
   ParentPrefixes.running_prefix τ addresses (counter σ).val steps (counter σ).val small (Nat.le_refl _) (counter σ).isLt
     down parentInput lo lo (lo-1) start (by omega) (Nat.le_refl _) pointerBelow entry.payloadAbove pointerBefore
       (by omega) bottomBefore (by omega) fits current bottom savedHere
 have finalGrowth : GrowsAllocator b frame 0 τ addresses down
     (ParentPrefixes.sourceAt τ steps (Nat.lt_of_le_of_lt small (counter σ).isLt)) addresses last := by
   simpa only [Nat.sub_self,Nat.zero_add,zeroAt] using parentGrowth
 refine ⟨ref,entered,τ,e,down,last,addresses,alias,setup,descent,unwinding,zeroEnv,?_,size,kept,
   parentStack.trans stack,extended,?_,parentCursor,parentRef.trans reference,?_,outside,?_,?_⟩
 · simpa only [Nat.sub_self,Nat.zero_add] using parentRepr
 · simpa only [Nat.add_zero] using growth.comp finalGrowth
 · intro j bound
   exact ⟨(outside _ (by omega) (by omega) (by omega)).trans (saved j bound).1,
     (outside _ (by omega) (by omega) (by omega)).trans (saved j bound).2⟩
 · intro x lower upper
   exact (outside x (by omega) (by omega) (by omega)).trans (words x lower upper)
 · exact (outside (lo-1) (by omega) (by omega) (by omega)).trans bottom

namespace Checks
open CountdownWitness

/-- The original populated Entry witnesses zero, one and two restored parents.
All sixteen observed cells are retained, including private physical payload. -/
theorem horizons (steps : Nat) (small : steps≤2) :
 ∃ (τ : State P.C (Parameters A)) (e : callee.H <+: τ.H) (last : Machine) (addresses : Nat → Fin W),
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) steps
     (EmissionPrefixes.Checks.machine 2 (by decide))=.inl last ∧
 τ.env=(countValue 0 W_pos,(some (P.r0.wk e),())) ∧
 StateRepr 1 2 16 F (ParentPrefixes.sourceAt τ steps (by have h:2<W:=(by decide);omega)) addresses last ∧
 τ.H.length=callee.H.length+2 ∧ Heap.Keeps e callee.heap τ.heap ∧
 BaseExtends callee.H P.base addresses ∧
 GrowsAllocator 2 16 8 callee P.base EmissionPrefixes.Checks.before
   (ParentPrefixes.sourceAt τ steps (by have h:2<W:=(by decide);omega)) addresses last ∧
 ((last.stack),[last.mem 0,last.mem 1,last.mem 2,last.mem 3,last.mem 7,last.mem 8,last.mem 9,
   last.mem 10,last.mem 11,last.mem 12,last.mem 13,last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21])=
 ([w[77]],[w[30],w[16],w[16],.val (wmod steps),w[10],.val (wmod (10+2*(2-steps))),w[99],
   w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
 have actual := parents "allocatingCountdown" callee P.base EmissionPrefixes.Checks.before 10
   AllocatingEmission.Checks.entry (by rw [AllocatingEmission.Checks.counter_two,AllocatingEmission.Checks.length_two];decide)
   steps (by rw [AllocatingEmission.Checks.counter_two];exact small)
 simp only [AllocatingEmission.Checks.counter_two] at actual
 obtain ⟨ref,entered,τ,e,down,last,addresses,alias,setup,descent,unwinding,env,repr,size,kept,stack,extended,growth,cursor,reference,saved,outside,words,bottom⟩ := actual
 have sameRef : ref=P.r0 := Option.some.inj alias.symm
 subst ref
 have sameEntry : entered=ParentPrefixes.Checks.input :=
   (Evm.Out.ok.inj (setup.symm.trans EmissionPrefixes.Checks.setup)).1
 subst entered
 have sameDown : down=EmissionPrefixes.Checks.machine 2 (by decide) :=
   Sum.inl.inj (descent.symm.trans (EmissionPrefixes.Checks.specification 2 (by decide)).1)
 subst down
 have counterWord := RecursiveHistory.counter_word (ParentPrefixes.sourceAt τ steps (by have h:2<W:=(by decide);omega))
   steps (by have h:2<W:=(by decide);omega) rfl addresses last repr
 have old := EmissionPrefixes.Checks.complete_observations 2 (by decide)
 have cells := (Prod.mk.inj old).2
 simp only [List.cons.injEq] at cells
 rcases cells with ⟨a0,a1,a2,a3,a7,a8,a9,a10,a11,a12,a13,a16,a17,a18,a20,a21,tail⟩
 have observation :
   ((last.stack),[last.mem 0,last.mem 1,last.mem 2,last.mem 3,last.mem 7,last.mem 8,last.mem 9,
     last.mem 10,last.mem 11,last.mem 12,last.mem 13,last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21])=
   ([w[77]],[w[30],w[16],w[16],.val (wmod steps),w[10],.val (wmod (10+2*(2-steps))),w[99],
     w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) := by
   rw [stack,reference,counterWord,cursor,
     outside 0 (by decide) (by decide) (by decide),outside 1 (by decide) (by decide) (by decide),
     outside 7 (by decide) (by decide) (by decide),outside 9 (by decide) (by decide) (by decide),
     outside 10 (by decide) (by decide) (by decide),outside 11 (by decide) (by decide) (by decide),
     outside 12 (by decide) (by decide) (by decide),outside 13 (by decide) (by decide) (by decide),
     outside 16 (by decide) (by decide) (by decide),outside 17 (by decide) (by decide) (by decide),
     outside 18 (by decide) (by decide) (by decide),outside 20 (by decide) (by decide) (by decide),
     outside 21 (by decide) (by decide) (by decide),a0,a1,a7,a9,a10,a11,a12,a13,a16,a17,a18,a20,a21]
   rfl
 exact ⟨τ,e,last,addresses,unwinding,env,repr,size,kept,extended,growth,observation⟩

noncomputable def machine (steps : Nat) (small : steps≤2) : Machine :=
 (horizons steps small).choose_spec.choose_spec.choose

/-- These observations are projections of the represented endpoint witness,
not fresh full-program executions. -/
theorem word_facts (steps : Nat) (small : steps≤2) :
 (machine steps small).stack=[w[77]] ∧ (machine steps small).mem 0=w[30] ∧
 (machine steps small).mem 1=w[16] ∧ (machine steps small).mem 2=w[16] ∧
 (machine steps small).mem 3=.val (wmod steps) ∧
 (machine steps small).mem 8=.val (wmod (10+2*(2-steps))) ∧
 (machine steps small).mem 11=w[2] ∧ (machine steps small).mem 13=w[1] := by
 have specification := (horizons steps small).choose_spec.choose_spec.choose_spec.choose_spec
 rcases specification with ⟨running,env,repr,size,kept,extended,growth,snapshot⟩
 have stack := (Prod.mk.inj snapshot).1
 have cells := (Prod.mk.inj snapshot).2
 simp only [List.cons.injEq] at cells
 rcases cells with ⟨a0,a1,a2,a3,a7,a8,a9,a10,a11,a12,a13,a16,a17,a18,a20,a21,tail⟩
 exact ⟨stack,a0,a1,a2,a3,a8,a11,a13⟩

theorem wrong_horizon : machine 1 (by decide)≠machine 0 (by decide) := by
 intro same
 have counterWord : (machine 1 (by decide)).mem 3=(machine 0 (by decide)).mem 3 :=
   congrArg (fun m : Machine => m.mem 3) same
 rw [(word_facts 1 (by decide)).2.2.2.2.1,(word_facts 0 (by decide)).2.2.2.2.1] at counterWord
 exact (by decide : (.val (wmod 1) : Word)≠.val (wmod 0)) counterWord

theorem wrong_alias : (machine 1 (by decide)).mem 1≠w[20] := by
 rw [(word_facts 1 (by decide)).2.2.1]
 decide

theorem wrong_allocation : (machine 1 (by decide)).mem 0≠w[26] := by
 rw [(word_facts 1 (by decide)).2.1]
 decide

theorem wrong_parent_order : (machine 1 (by decide)).mem 11≠w[1] := by
 rw [(word_facts 1 (by decide)).2.2.2.2.2.2.1]
 decide

theorem not_final_pointer : (machine 1 (by decide)).mem 8≠w[10] := by
 rw [(word_facts 1 (by decide)).2.2.2.2.2.1]
 decide

theorem restored_pointer : (machine 2 (by decide)).mem 8=w[10] :=
 (word_facts 2 (by decide)).2.2.2.2.2.1

/-- A zero unwind horizon is the actual reached child machine. Only target
machine identity is inferred from this execution equation. -/
theorem zero_identity : machine 0 (by decide)=EmissionPrefixes.Checks.machine 2 (by decide) := by
 have specification := (horizons 0 (by decide)).choose_spec.choose_spec.choose_spec.choose_spec
 exact (Sum.inl.inj specification.1).symm

/-- The extra false guard completes the same paired unwind and every later
horizon retains that successful machine. -/
theorem stopped (horizon : Nat) (bound : 3≤horizon) :
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) horizon
     (EmissionPrefixes.Checks.machine 2 (by decide))=.inr (.ok (machine 2 (by decide)) 0) := by
 have specification := (horizons 2 (by decide)).choose_spec.choose_spec.choose_spec.choose_spec
 rcases specification with ⟨running,env,repr,size,kept,extended,growth,snapshot⟩
 have cells := (Prod.mk.inj snapshot).2
 simp only [List.cons.injEq] at cells
 rcases cells with ⟨a0,a1,a2,a3,a7,a8,a9,a10,a11,a12,a13,a16,a17,a18,a20,a21,tail⟩
 have finished := ParentStop.stop_after_running (R:=A) (b:=2) (start:=10) running a8 a7
 exact loopIterN_done_le bound finished

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.EmissionUnwind

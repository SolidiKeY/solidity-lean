import Solidity.Backend.InternalFlow.RuntimeFrameV3GuardedRecursion

/-! Arbitrary-counter source horizons and represented target prefixes for the
scoped bounds-probe family. ReadDomain is actual scalar evaluation at the
unchanged heap and lower countdown environments, not a simulation premise. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.GuardedPrefixes
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion

/-- Exactly the checked source reads needed at positive countdown values.
No condition, child execution, target outcome or frame preservation is supplied. -/
def ReadDomain {C : Contract} (σ : State C (Parameters A)) (ref : HRef σ.H A) (count : Nat) : Prop :=
 ∀ (k : Nat), 0<k → k≤count → ∀ (fit : k<W), ∃ v,
 ArrayProbe.value.evalT (σ.withEnv (Δ:=Parameters A) (countValue k fit,(some ref,())))=.ok v

set_option backward.isDefEq.respectTransparency false in
theorem environment {C : Contract} (σ : State C (Parameters A)) (count : Nat) (bound : count<W)
 (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref) :
 σ.withEnv (Δ:=Parameters A) (countValue count bound,(some ref,()))=σ := by
 have env : σ.env=(countValue count bound,(some ref,())) :=
   Prod.ext counter (Prod.ext alias (by cases σ.env.2.2;rfl))
 rw [←env]
 rfl

/-- All intrinsic quotation horizons, including real exhaustion. The read
premise contains only actual value evaluations, not recursive execution. -/
theorem all_horizons {C : Contract} (depth : Nat) (σ : State C (Parameters A))
 (count : Nat) (bound : count<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : ReadDomain σ ref count) :
 (GuardedRecursion.body depth).run σ=
 if count<depth then .ok ⟨σ,List.prefix_refl _⟩ else .error .exhausted := by
 induction depth generalizing σ count with
 | zero => simp only [base_exhausts,Nat.not_lt_zero,ite_false]
 | succ depth ih =>
   have guard := guard_eval σ count (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
   cases count with
   | zero =>
     have stopped := source_zero σ depth guard
     simpa only [Nat.zero_lt_succ,ite_true] using stopped
   | succ count =>
     obtain ⟨v,evaluated⟩ := reads (count+1) (by omega) (by omega) bound
     rw [environment σ (count+1) bound ref counter alias] at evaluated
     have positive : nonzero.evalT σ=.ok true := by simpa only [show decide (0<count+1)=true from decide_eq_true (by omega)] using guard
     rw [source_positive σ depth v positive evaluated]
     let child : State C (Parameters A) := σ.withEnv (countValue count (by omega),(some ref,()))
     have childReads : ReadDomain child ref count := by
       intro k hp hl hf
       exact reads k hp (by omega) hf
     have nested := ih child count (by omega) ref rfl rfl childReads
     by_cases enough : count<depth
     · have actual := child_returns σ count bound ref counter alias depth (by simpa only [ite_eq_left enough] using nested)
       simpa only [show count+1<depth+1 from by omega,ite_true] using actual
     · have actual := child_failure σ count bound ref counter alias depth .exhausted (by simpa only [ite_eq_right enough] using nested)
       simpa only [show ¬ count+1<depth+1 from by omega,ite_false] using actual

/-- Every actual running horizon of the guarded image, derived from checked
probe execution and capture/update. The capacity counts real saved contexts;
no running target prefix, desired StateRepr or heap preservation is assumed. -/
theorem reached_prefix {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (steps count : Nat) (reached : steps≤count) (bound : count<W)
 (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : ReadDomain σ ref count)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) :
 let source : State C (Parameters A) := σ.withEnv (countValue (count-steps) (by omega),(some ref,()))
 ∃ after addresses,
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (turnCode (C:=C) b F pointer)) steps before=.inl after ∧
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (activationCode (C:=C) b F pointer)) steps before=.inl after ∧
 StateRepr L b frame F source addresses after ∧ after.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame 0 σ base before source addresses after ∧
 after.mem pointer=.val (wmod (start+2*steps)) := by
 induction steps generalizing count σ base before start with
 | zero =>
   have same := environment σ count bound ref counter alias
   refine ⟨before,base,rfl,rfl,?_,rfl,BaseExtends.refl base,?_,?_⟩
   · simpa only [Nat.sub_zero,same] using repr
   · simp only [Nat.sub_zero,same]
     intro cursor hb ha hs
     simpa only [Nat.add_zero] using ha
   · simpa only [Nat.mul_zero,Nat.add_zero] using current
 | succ steps ih =>
   cases count with
   | zero => omega
   | succ count =>
     let child : State C (Parameters A) := σ.withEnv (countValue count (by omega),(some ref,()))
     obtain ⟨v,evaluated⟩ := reads (count+1) (by omega) (by omega) bound
     rw [environment σ (count+1) bound ref counter alias] at evaluated
     obtain ⟨saved,next,addresses,args,entry,captured,updated,executed,represented,stack,extended,growth,cursor,payload⟩ :=
       activation rfl σ count bound ref counter alias base before repr lo pointer start localBound
         pointerAbove pointerBelow payloadAbove (by omega) (.inl (by omega)) (by omega) current
     have turn := probed_turn σ count bound counter base before next repr pointer v evaluated executed
     have oldTurn := positive_turn σ count bound counter base before next repr pointer executed
     have childReads : ReadDomain child ref count := by
       intro k hp hl hf
       exact reads k hp (by omega) hf
     obtain ⟨after,finalAddresses,running,oldRunning,finalRepr,finalStack,finalExt,finalGrowth,finalCursor⟩ :=
       ih count (by omega) (by omega) child ref rfl rfl childReads addresses next represented (start+2)
         (by omega) (by omega) (by omega) (by omega) cursor
     refine ⟨after,finalAddresses,?_,?_,?_,finalStack.trans stack,?_,?_,?_⟩
     · simpa only [loopIterN,turn] using running
     · simpa only [loopIterN,oldTurn] using oldRunning
     · simpa only [child,State.withEnv,Nat.add_sub_add_right] using finalRepr
     · exact extended.trans (List.prefix_refl _) finalExt
     · exact growth.comp finalGrowth
     · have arithmetic : start+2+2*steps=start+2*(steps+1) := by omega
       simpa only [arithmetic] using finalCursor

/-- One actual terminal turn extends an actual running horizon. -/
theorem finish_prefix (rc rb : Machine → Evm.Out) (horizon : Nat) (before last : Machine) (result : Evm.Out)
 (running : loopIterN rc rb horizon before=.inl last) (done : loopTurn rc rb last=.inr result) :
 loopIterN rc rb (horizon+1) before=.inr result := by
 induction horizon generalizing before with
 | zero =>
   have same : before=last := Sum.inl.inj running
   subst before
   simp only [loopIterN,done]
 | succ horizon ih =>
   simp only [loopIterN] at running ⊢
   cases turn : loopTurn rc rb before with
   | inl next =>
     rw [turn] at running
     exact ih next running
   | inr halted =>
     rw [turn] at running
     cases running

/-- Arbitrary-counter success with an actual stopping prefix and actual paired
unwind. The existing unprobed endpoint is shared only after proving that both
images reach the SAME down machine; no full-program target run is a premise. -/
theorem success_endpoint {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (count : Nat) (bound : count<W) (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : ReadDomain σ ref count)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer bottom start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (bottomAbove : b+2≤bottom) (bottomBefore : bottom<start)
 (bottomSeparate : bottom≠pointer) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) (bottomValue : before.mem bottom=.val (wmod start)) :
 ∃ last,
 (∀ depth, count<depth → (GuardedRecursion.body depth).run σ=.ok ⟨σ,List.prefix_refl _⟩) ∧
 run (image (C:=C) b F pointer bottom) before=.ok last 0 ∧
 StateRepr L b frame F σ base last ∧ last.stack=before.stack ∧
 last.mem pointer=.val (wmod start) ∧
 (∀ x, x<start → last.mem x=before.mem x) ∧
 (∀ x, frame≤x → last.mem x=before.mem x) ∧
 (∀ j, j<count → last.mem (start+2*j)=before.mem b ∧
   last.mem (start+2*j+1)=.val (wmod (count-j))) := by
 obtain ⟨down,addresses,running,oldRunning,downRepr,downStack,downExt,downGrowth,downCursor⟩ :=
   reached_prefix count count (Nat.le_refl _) bound σ ref counter alias reads base before repr
     lo pointer start localBound pointerAbove pointerBelow payloadAbove pointerBefore capacity fits current
 let zero : State C (Parameters A) := σ.withEnv (countValue 0 W_pos,(some ref,()))
 have zeroRepr : StateRepr L b frame F zero addresses down := by
   simpa only [Nat.sub_self] using downRepr
 have guard := guard_run zero 0 W_pos rfl addresses down zeroRepr
 have done := empty_turn (run (guardCompiled (C:=C) b F).code) (run (turnCode (C:=C) b F pointer)) down guard
 have stopped := finish_prefix _ _ count before down (.ok down 0) running done
 have newRun := successful_loop _ _ _ _ _ stopped
 have oldDone := zero_turn zero rfl addresses down zeroRepr pointer
 have oldStopped := finish_prefix _ _ count before down (.ok down 0) oldRunning oldDone
 have oldRun := RecursiveDescent.run_of_stopped oldStopped
 obtain ⟨last,oldSource,oldWhole,finalRepr,finalStack,finalCursor,low,high,saved⟩ :=
   RecursiveReturn.endpoint rfl count bound σ ref counter alias base before repr lo pointer bottom start
     localBound pointerAbove pointerBelow bottomAbove bottomBefore bottomSeparate payloadAbove pointerBefore capacity fits current bottomValue
 have returned : run (PairedUnwind.code b pointer bottom A) down=.ok last 0 :=
   (run_append_ok oldRun).symm.trans oldWhole
 refine ⟨last,?_,(run_append_ok newRun).trans returned,finalRepr,finalStack,finalCursor,low,high,saved⟩
 intro depth enough
 simpa only [ite_eq_left enough] using all_horizons depth σ count bound ref counter alias reads

namespace Checks
open CountdownWitness
abbrev F := CountdownWitness.F

/-- The populated heap discharges EVERY positive read required by the domain,
not just the initial read: [7,9] is live at the retained reference. -/
theorem read_domain : ReadDomain callee P.r0 2 := by
 intro k positive within fit
 rcases (by omega : k=1 ∨ k=2) with rfl | rfl
 · exact ⟨_,GuardedRecursion.Checks.one_probe⟩
 · rw [environment callee 2 fit P.r0 rfl rfl]
   exact ⟨_,ArrayProbe.Checks.good_evaluated⟩

theorem source_all (depth : Nat) : (GuardedRecursion.body depth).run callee=
 if 2<depth then .ok ⟨callee,List.prefix_refl _⟩ else .error .exhausted :=
 all_horizons depth callee 2 (by decide) P.r0 rfl rfl read_domain

/-- Zero, one and two genuine running prefixes, each coupled to the SAME
unprobed execution and its represented counter/reference, stack and allocator. -/
theorem prefixes (steps : Nat) (small : steps≤2) :
 let source : State P.C (Parameters GuardedRecursion.A) := callee.withEnv (countValue (2-steps) (Nat.lt_of_le_of_lt (Nat.sub_le 2 steps) (by decide : 2<W)),(some P.r0,()))
 ∃ after addresses,
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (turnCode (C:=P.C) 2 F 8)) steps ParentPrefixes.Checks.input=.inl after ∧
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (activationCode (C:=P.C) 2 F 8)) steps ParentPrefixes.Checks.input=.inl after ∧
 StateRepr 1 2 16 F source addresses after ∧ after.stack=ParentPrefixes.Checks.input.stack ∧
 BaseExtends callee.H P.base addresses ∧
 GrowsAllocator 2 16 0 callee P.base ParentPrefixes.Checks.input source addresses after ∧
 after.mem 8=.val (wmod (10+2*steps)) :=
 reached_prefix steps 2 small (by decide) callee P.r0 rfl rfl read_domain
 P.base ParentPrefixes.Checks.input ParentPrefixes.Checks.initial 8 8 10
 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl

/-- Concrete admission of the generic returning image at the existing
populated represented input, with actual physical header and capacity bounds. -/
theorem endpoint : ∃ last,
 (∀ depth, 2<depth → (GuardedRecursion.body depth).run callee=.ok ⟨callee,List.prefix_refl _⟩) ∧
 run (image (C:=P.C) 2 F 8 7) ParentPrefixes.Checks.input=.ok last 0 ∧
 StateRepr 1 2 16 F callee P.base last ∧ last.stack=ParentPrefixes.Checks.input.stack ∧
 last.mem 8=w[10] ∧
 (∀ x, x<10 → last.mem x=ParentPrefixes.Checks.input.mem x) ∧
 (∀ x, 16≤x → last.mem x=ParentPrefixes.Checks.input.mem x) ∧
 (∀ j, j<2 → last.mem (10+2*j)=ParentPrefixes.Checks.input.mem 2 ∧
   last.mem (10+2*j+1)=.val (wmod (2-j))) :=
 success_endpoint 2 (by decide) callee P.r0 rfl rfl read_domain P.base ParentPrefixes.Checks.input
 ParentPrefixes.Checks.initial 8 8 7 10 (by decide) (by decide) (by decide) (by decide)
 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl

/-- Actual two-turn cursor and protected stack, with wrong-cursor and
wrong-stack controls from the SAME reached prefix rather than fresh execution. -/
theorem two_cursor : ∃ after,
 loopIterN (run (guardCompiled (C:=P.C) 2 F).code) (run (turnCode (C:=P.C) 2 F 8)) 2 ParentPrefixes.Checks.input=.inl after ∧
 after.mem 8=w[14] ∧ after.mem 8≠w[12] ∧ after.stack=[w[77]] ∧ after.stack≠[w[88]] := by
 obtain ⟨after,addresses,executed,oldRun,repr,stack,ext,growth,cursor⟩ := prefixes 2 (by decide)
 have actualCursor : after.mem 8=w[14] := cursor
 have actualStack : after.stack=[w[77]] := stack
 refine ⟨after,executed,actualCursor,?_,actualStack,?_⟩
 · rw [actualCursor]
   decide
 · rw [actualStack]
   decide

/-- The out-of-bounds start does NOT satisfy the positive read domain. -/
theorem bad_domain : ¬ReadDomain ArrayProbe.Checks.bad P.r0 3 := by
 intro domain
 obtain ⟨v,read⟩ := domain 3 (by decide) (by decide) (by decide)
 rw [environment ArrayProbe.Checks.bad 3 (by decide) P.r0 rfl rfl] at read
 rw [ArrayProbe.Checks.bad_evaluated] at read
 cases read

/-- A shallow horizon is not a completed native return even though its first
read succeeds. This control is derived from the full horizon classification. -/
theorem shallow_not_return : (GuardedRecursion.body 2).run callee≠.ok ⟨callee,List.prefix_refl _⟩ := by
 rw [source_all]
 simp only [show ¬2<2 from by decide,ite_false]
 intro bad
 cases bad

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.GuardedPrefixes

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.GuardedPrefixes.success_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.GuardedPrefixes.success_endpoint

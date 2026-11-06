import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulRuntime
import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulSourceSelectionControls

/-! Populated frozen runtime claims for heap-reading arguments, actual old
heap mutation, native scalar return, and both bare-revert stages. Every entry
uses the actual reached source/target pair. Profile adequacy remains open. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulRuntime.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F reference)
open EffectfulSourceSelection.Controls (input good badCallee)

theorem nonfragile {R : RefTy} (i : Idx Γ (.alias R)) : F.get i≠.fragile := by
 cases i with
 | there i => cases i with
   | there i => cases i with
     | there i => cases i with
       | there i => cases i

theorem good_arena (depth : Nat) :
 (plan (good depth) 5 9 8).arenaWords OrderedEffectfulScalar.Client.caller=6 := by
 change ScalarDemand.reserve OrderedEffectfulScalar.Client.count OrderedEffectfulScalar.Client.caller=6
 rw [ScalarDemand.reserve_value _ OrderedEffectfulScalar.Client.evaluated]
 rfl

theorem good_entry (depth : Nat) :
 InterfaceV1.Entry (plan (good depth) 5 9 8) 1 1 16 F OrderedEffectfulScalar.Client.caller
   OrderedEffectfulScalar.Client.base OrderedEffectfulScalar.Client.before 10 := by
 refine ⟨OrderedEffectfulScalar.Client.initial,(by change 1+Γ.length≤9;decide),(by change 1+Γ.length≤9;decide),
   (by change 1+(5+3-1)≤9;decide),(by change (9:Nat)≤9;decide),
   (by change (9:Nat)<16;decide),(by change (9:Nat)≤10;decide),
   ?_,?_,.inl (by change (9:Nat)<10;decide),?_,?_,.inl rfl⟩
 · change 10+(plan (good depth) 5 9 8).arenaWords _≤16
   rw [good_arena];decide
 · change Γ.length+1≤(plan (good depth) 5 9 8).arenaWords _
   rw [good_arena];decide
 · change 10+(plan (good depth) 5 9 8).arenaWords _<W
   rw [good_arena];decide
 · exact OrderedEffectfulScalar.Client.current

noncomputable def result :=
 (OrderedEffectfulScalar.changed OrderedEffectfulScalar.Client.caller OrderedEffectfulScalar.Client.ref).setLocal
   (.here : Idx Γ (.val .uint)) (countValue 3 (by decide))

theorem returned (depth : Nat) (enough : 3<depth) :
 InterfaceV1.Returned (plan (good depth) 5 9 8) 1 1 16 OrderedEffectfulScalar.Client.caller
   OrderedEffectfulScalar.Client.base OrderedEffectfulScalar.Client.before 10
   ⟨result,List.prefix_refl _⟩ :=
 returns (good depth) (by decide) (by decide) (by decide) nonfragile
   1 16 _ _ _ 10 (good_entry depth) _ (EffectfulSourceSelection.Controls.success depth enough).1

/-- The frozen witness ties the SAME successful caller to its represented
    entry. Source failure or quotation-zero exhaustion cannot instantiate it. -/
theorem successful_entry (depth : Nat) (enough : 3<depth) :
 InterfaceV2.SuccessfulEntry 1 F (input OrderedEffectfulScalar.Client.count depth) (plan (good depth) 5 9 8) :=
 ⟨1,16,OrderedEffectfulScalar.Client.caller,OrderedEffectfulScalar.Client.base,
   OrderedEffectfulScalar.Client.before,10,⟨result,List.prefix_refl _⟩,
   good_entry depth,(EffectfulSourceSelection.Controls.success depth enough).1⟩

/-- Freeze the actual target identity as well as its full returned relation. -/
theorem named_target (depth : Nat) (enough : 3<depth) :
 ∃ addresses,
 StateRepr 1 1 16 F result addresses OrderedEffectfulScalar.Client.machine ∧
 Footprint.Words 9 10 OrderedEffectfulScalar.Client.before OrderedEffectfulScalar.Client.machine ∧
 GrowsAllocator 1 16 0 OrderedEffectfulScalar.Client.caller OrderedEffectfulScalar.Client.base
   OrderedEffectfulScalar.Client.before result addresses OrderedEffectfulScalar.Client.machine := by
 obtain ⟨after,addresses,executed,reached,stack,extended,growth,cursor,protectedWords⟩ := returned depth enough
 have same : after=OrderedEffectfulScalar.Client.machine :=
   (Evm.Out.ok.inj (executed.symm.trans (EffectfulSourceSelection.Controls.success depth enough).2)).1
 subst after
 exact ⟨addresses,reached,protectedWords,growth⟩

theorem callee_arena (depth : Nat) : (plan (badCallee depth) 5 9 8).arenaWords SameCallInputs.caller=6 := by
 change ScalarDemand.reserve OrderedCalleeFailure.Client.count SameCallInputs.caller=6
 rw [ScalarDemand.reserve_value _ OrderedCalleeFailure.Client.evaluated]
 rfl

theorem callee_entry (depth : Nat) :
 InterfaceV1.Entry (plan (badCallee depth) 5 9 8) 1 1 16 F SameCallInputs.caller
   SameCallInputs.addresses SameCallInputs.machine 10 := by
 refine ⟨SameCallInputs.reached.2.2.1,(by change 1+Γ.length≤9;decide),(by change 1+Γ.length≤9;decide),
   (by change 1+(5+3-1)≤9;decide),(by change (9:Nat)≤9;decide),
   (by change (9:Nat)<16;decide),(by change (9:Nat)≤10;decide),
   ?_,?_,.inl (by change (9:Nat)<10;decide),?_,?_,.inl rfl⟩
 · change 10+(plan (badCallee depth) 5 9 8).arenaWords _≤16
   rw [callee_arena];decide
 · change Γ.length+1≤(plan (badCallee depth) 5 9 8).arenaWords _
   rw [callee_arena];decide
 · change 10+(plan (badCallee depth) 5 9 8).arenaWords _<W
   rw [callee_arena];decide
 · exact SameCallInputs.cursor

theorem callee_reverting_entry (depth : Nat) :
 InterfaceV2.RevertingEntry 1 F (input OrderedCalleeFailure.Client.count depth) (plan (badCallee depth) 5 9 8) :=
 ⟨1,16,SameCallInputs.caller,SameCallInputs.addresses,SameCallInputs.machine,10,callee_entry depth,
   (EffectfulSourceSelection.Controls.callee_failure depth).1⟩

theorem callee_revert (depth : Nat) :
 run (plan (badCallee depth) 5 9 8).code SameCallInputs.machine=.revert :=
 bare_revert (badCallee depth) (by decide) (by decide) (by decide) 1 16 _ _ _ 10
   (callee_entry depth) (EffectfulSourceSelection.Controls.callee_failure depth).1

theorem argument_arena (depth : Nat) : (plan (good depth) 5 9 8).arenaWords SameCallInputs.caller=5 := by
 change ScalarDemand.reserve OrderedEffectfulScalar.Client.count SameCallInputs.caller=5
 rw [ScalarDemand.reserve_error .revert SameCallInputs.count_fails]
 rfl

theorem argument_entry (depth : Nat) :
 InterfaceV1.Entry (plan (good depth) 5 9 8) 1 1 16 F SameCallInputs.caller
   SameCallInputs.addresses SameCallInputs.machine 10 := by
 refine ⟨SameCallInputs.reached.2.2.1,(by change 1+Γ.length≤9;decide),(by change 1+Γ.length≤9;decide),
   (by change 1+(5+3-1)≤9;decide),(by change (9:Nat)≤9;decide),
   (by change (9:Nat)<16;decide),(by change (9:Nat)≤10;decide),
   ?_,?_,.inl (by change (9:Nat)<10;decide),?_,?_,.inl rfl⟩
 · change 10+(plan (good depth) 5 9 8).arenaWords _≤16
   rw [argument_arena];decide
 · change Γ.length+1≤(plan (good depth) 5 9 8).arenaWords _
   rw [argument_arena];decide
 · change 10+(plan (good depth) 5 9 8).arenaWords _<W
   rw [argument_arena];decide
 · exact SameCallInputs.cursor

theorem argument_reverting_entry (depth : Nat) :
 InterfaceV2.RevertingEntry 1 F (input OrderedEffectfulScalar.Client.count depth) (plan (good depth) 5 9 8) :=
 ⟨1,16,SameCallInputs.caller,SameCallInputs.addresses,SameCallInputs.machine,10,argument_entry depth,
   (EffectfulSourceSelection.Controls.argument_failure depth).1⟩

theorem argument_revert (depth : Nat) :
 run (plan (good depth) 5 9 8).code SameCallInputs.machine=.revert :=
 bare_revert (good depth) (by decide) (by decide) (by decide) 1 16 _ _ _ 10
   (argument_entry depth) (EffectfulSourceSelection.Controls.argument_failure depth).1

theorem wrong_captured_count :
 (plan (good 4) 5 9 8).arenaWords OrderedEffectfulScalar.Client.caller≠74 := by
 rw [good_arena]
 decide

theorem wrong_halt : run (plan (badCallee 0) 5 9 8).code SameCallInputs.machine≠.fault := by
 rw [callee_revert]
 intro h
 cases h

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulRuntime.Controls

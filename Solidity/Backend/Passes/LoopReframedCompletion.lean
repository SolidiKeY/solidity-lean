import Solidity.Backend.Passes.ReframedLoops
import Solidity.Backend.Passes.LoopScopeTerminal

/-! DRAFT / UNVALIDATED. Independent next Backfill-A leaf:
CP27 has reached suffixInput5 but retains only suffixMappedOutput128.
This candidate obtains FULL suffixMappedOutput5 from the actual certificate,
with actual final execution equality; no equality follows merely from Rep. -/
namespace Solidity.Backend.Passes.LoopReframedCompletion
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls
open LoopScopeTrace (preparedTarget loopTarget finalTarget
  preparation_target loop_target suffix_target)

-- Keep concrete compiler certificates and computed machines behind their APIs.
-- The kernel retains their definitions; only local elaborator unfolding changes.
attribute [local irreducible] LoopScopeControls.preparation LoopScopeControls.enclosed
  LoopScopeControls.suffix LoopScopeControls.prepared LoopScopeControls.loopOut
  LoopScopeControls.final LoopScopeTrace.preparedTarget LoopScopeTrace.loopTarget
  LoopScopeTrace.finalTarget

/-- Actual final machine equality is established by execution. Prefix maps are
not replaced: the new suffix map is selected from its original frame5 Rep. -/
theorem canonical_completion :
    ∃ (mb nb ob : Nat → Fin W), loopTarget.stack = [] ∧
      MappedOutput (.memory preparation) 1 128 base initial machine
        prepared.st preparedTarget mb ∧
      MappedOutput checked 1 128 mb prepared.st preparedTarget
        loopOut.st loopTarget nb ∧
      (Compilation.memory suffix).Input 1 5 nb loopOut.st loopTarget ∧
      MappedOutput (.memory suffix) 1 5 nb loopOut.st loopTarget
        final.st finalTarget ob := by
  obtain ⟨mb,nb,ha,hb⟩ := LoopScopeTerminal.prefix_relations
  have link : ReframedLink checked (.memory suffix) 1 128 5 mb prepared.st preparedTarget := loop_scopes_shrinking_link enclosed suffix
    (base := mb) (σ := prepared.st) (m := preparedTarget)
    (L := 1) (beforeFrame := 128) (afterFrame := 5)
    (by decide) ReframedLoopControls.bounds.1 ReframedLoopControls.bounds.2 costs.2
  have step : (Compilation.memory suffix).Input
      (1 + Evm.Prog.pushes wrapped) 5 nb loopOut.st loopTarget := link loopOut loopTarget nb wrapped_source loop_target
    (by simpa only [enclosed.cert.pushes_zero,Nat.add_zero] using hb)
  have input : (Compilation.memory suffix).Input 1 5 nb loopOut.st loopTarget := by
    simpa only [enclosed.cert.pushes_zero,Nat.add_zero] using step
  obtain ⟨actual,target,stack,rep⟩ := compilation_success (.memory suffix) input
    (by decide +kernel) final_source
  have same : actual = finalTarget := (Evm.Out.ok.inj (target.symm.trans suffix_target)).1
  subst actual
  obtain ⟨ob,output⟩ := (mapped_output_iff (.memory suffix) _ _ _ _ _ _ _).mp rep
  have full : MappedOutput (.memory suffix) 1 5 nb loopOut.st loopTarget
      final.st finalTarget ob := by
    simpa only [suffix.cert.pushes_zero,Nat.add_zero] using output
  exact ⟨mb,nb,ob,stack.symm.trans LoopScopeTrace.final_stack,ha,hb,input,full⟩

/-- All three actual maps plus loop Cost/ext precede forall tail. For each
tail every stage Input/run/fullOutput holds, with suffixOutput NOW at5.
Both original intrinsic and emitted associations reach the same actual result. -/
theorem shared_completion :
    ∃ (mb nb ob : Nat → Fin W) (amount : Nat)
      (ext : prepared.st.H <+: loopOut.st.H),
      Memory.LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ amount ∧
      ((prepare.join wrapped).join consume).run initial =
        .ok ⟨final.st,(prepared.ext.trans loopOut.ext).trans final.ext⟩ ∧
      (prepare.join (wrapped.join consume)).run initial =
        .ok ⟨final.st,prepared.ext.trans (loopOut.ext.trans final.ext)⟩ ∧ ∀ tail,
      (Compilation.memory preparation).Input 1 128 base initial {machine with stack := tail} ∧
      run preparation.code {machine with stack := tail} =
        .ok {preparedTarget with stack := tail} 0 ∧
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {preparedTarget with stack := tail} mb ∧
      checked.Input 1 128 mb prepared.st {preparedTarget with stack := tail} ∧
      run enclosed.code {preparedTarget with stack := tail} =
        .ok {loopTarget with stack := tail} 0 ∧
      MappedOutput checked 1 128 mb prepared.st {preparedTarget with stack := tail}
        loopOut.st {loopTarget with stack := tail} nb ∧
      (Compilation.memory suffix).Input 1 5 nb loopOut.st {loopTarget with stack := tail} ∧
      run suffix.code {loopTarget with stack := tail} =
        .ok {finalTarget with stack := tail} 0 ∧
      MappedOutput (.memory suffix) 1 5 nb loopOut.st {loopTarget with stack := tail}
        final.st {finalTarget with stack := tail} ob ∧
      run ((preparation.code ++ enclosed.code) ++ suffix.code) {machine with stack := tail} =
        .ok {finalTarget with stack := tail} 0 ∧
      run (preparation.code ++ (enclosed.code ++ suffix.code)) {machine with stack := tail} =
        .ok {finalTarget with stack := tail} 0 := by
  let mb : Nat → Fin W := Classical.choose canonical_completion
  have mbSpec : ∃ (nb ob : Nat → Fin W), loopTarget.stack = [] ∧
      MappedOutput (.memory preparation) 1 128 base initial machine
        prepared.st preparedTarget mb ∧
      MappedOutput checked 1 128 mb prepared.st preparedTarget
        loopOut.st loopTarget nb ∧
      (Compilation.memory suffix).Input 1 5 nb loopOut.st loopTarget ∧
      MappedOutput (.memory suffix) 1 5 nb loopOut.st loopTarget
        final.st finalTarget ob :=
    Classical.choose_spec canonical_completion
  let nb : Nat → Fin W := Classical.choose mbSpec
  have nbSpec : ∃ (ob : Nat → Fin W), loopTarget.stack = [] ∧
      MappedOutput (.memory preparation) 1 128 base initial machine
        prepared.st preparedTarget mb ∧
      MappedOutput checked 1 128 mb prepared.st preparedTarget
        loopOut.st loopTarget nb ∧
      (Compilation.memory suffix).Input 1 5 nb loopOut.st loopTarget ∧
      MappedOutput (.memory suffix) 1 5 nb loopOut.st loopTarget
        final.st finalTarget ob :=
    Classical.choose_spec mbSpec
  let ob : Nat → Fin W := Classical.choose nbSpec
  have facts : loopTarget.stack = [] ∧
      MappedOutput (.memory preparation) 1 128 base initial machine
        prepared.st preparedTarget mb ∧
      MappedOutput checked 1 128 mb prepared.st preparedTarget
        loopOut.st loopTarget nb ∧
      (Compilation.memory suffix).Input 1 5 nb loopOut.st loopTarget ∧
      MappedOutput (.memory suffix) 1 5 nb loopOut.st loopTarget
        final.st finalTarget ob := Classical.choose_spec nbSpec
  have loopEmpty : loopTarget.stack = [] := facts.1
  have ha : MappedOutput (.memory preparation) 1 128 base initial machine
      prepared.st preparedTarget mb := facts.2.1
  have hb : MappedOutput checked 1 128 mb prepared.st preparedTarget
      loopOut.st loopTarget nb := facts.2.2.1
  have input : (Compilation.memory suffix).Input 1 5 nb loopOut.st loopTarget := facts.2.2.2.1
  have output : MappedOutput (.memory suffix) 1 5 nb loopOut.st loopTarget
      final.st finalTarget ob := facts.2.2.2.2
  have hbCopy : MappedOutput checked 1 128 mb prepared.st preparedTarget
      loopOut.st loopTarget nb := hb
  let amount : Nat := Classical.choose hb
  let ext : prepared.st.H <+: loopOut.st.H := Classical.choose (Classical.choose_spec hb)
  have cost : Memory.LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ amount :=
    (Classical.choose_spec (Classical.choose_spec hb)).1
  have loopInput : checked.Input 1 128 mb prepared.st preparedTarget := LoopScopeApplication.into_scope prepared preparedTarget mb
    prepared_source preparation_target ha
  refine ⟨mb,nb,ob,amount,ext,cost,LoopScopeApplication.joined_source.1,
    LoopScopeApplication.joined_source.2,?_⟩
  intro tail
  have hp : run preparation.code {machine with stack := tail} =
      .ok {preparedTarget with stack := tail} 0 := by
    have transported : run preparation.code {machine with stack := tail} =
        replaceOutStack tail (run preparation.code {machine with stack := []}) :=
      compilation_tail_exact (.memory preparation) LoopScopeApplication.preparation_input
        (by decide +kernel) tail
    change run preparation.code {machine with stack := tail} =
      replaceOutStack tail (run preparation.code machine) at transported
    exact transported.trans (congrArg (replaceOutStack tail) preparation_target)
  have hl : run enclosed.code {preparedTarget with stack := tail} =
      .ok {loopTarget with stack := tail} 0 := by
    have empty : preparedTarget.stack = [] := by decide +kernel
    have canonical : {preparedTarget with stack := []} = preparedTarget := by
      generalize preparedTarget = target at empty ⊢
      cases target
      cases empty
      rfl
    have transported : run enclosed.code {preparedTarget with stack := tail} =
        replaceOutStack tail (run enclosed.code {preparedTarget with stack := []}) :=
      compilation_tail_exact checked loopInput (by decide +kernel) tail
    exact transported.trans (congrArg (fun state => replaceOutStack tail (run enclosed.code state))
      canonical |>.trans (congrArg (replaceOutStack tail) loop_target))
  have transported : run suffix.code (appendTail loopTarget tail) =
      appendOut tail (run suffix.code loopTarget) := run_tail suffix.code loopTarget tail
    (by rw [suffix_target]; intro impossible; cases impossible)
  have hs : run suffix.code {loopTarget with stack := tail} =
      .ok {finalTarget with stack := tail} 0 := by
    have leftTail : appendTail loopTarget tail = {loopTarget with stack := tail} := by
      simp only [appendTail,loopEmpty,List.nil_append]
    have rightTail : appendOut tail (.ok finalTarget 0) =
        .ok {finalTarget with stack := tail} 0 := by
      simp only [appendOut,appendTail,LoopScopeTrace.final_stack,List.nil_append]
    exact (congrArg (fun state => run suffix.code state) leftTail.symm).trans
      (transported.trans ((congrArg (appendOut tail) suffix_target).trans rightTail))
  have whole : run (preparation.code ++ (enclosed.code ++ suffix.code))
      {machine with stack := tail} = .ok {finalTarget with stack := tail} 0 := by
    exact (run_append_ok (c₂ := enclosed.code ++ suffix.code) hp).trans
      ((run_append_ok (c₂ := suffix.code) hl).trans hs)
  exact ⟨compilation_input_stack (.memory preparation) LoopScopeApplication.preparation_input tail,
    hp,mapped_output_stack (.memory preparation) ha tail tail,
    compilation_input_stack checked loopInput tail,hl,
    mapped_output_stack checked hbCopy tail tail,
    compilation_input_stack (.memory suffix) input tail,hs,
    mapped_output_stack (.memory suffix) output tail tail,
    (congrArg (fun code => run code {machine with stack := tail})
      (List.append_assoc preparation.code enclosed.code suffix.code)).trans whole,whole⟩

/-- Actual old-reference identity transport and zero-cost allocator law use
the selected frame5 output. No global address-map equality is asserted. -/
theorem old_references_and_zero_cost :
    ∃ (mb nb ob : Nat → Fin W),
      BaseExtends prepared.st.H mb nb ∧
      BaseExtends loopOut.st.H nb ob ∧
      suffix.cert.cost loopOut.st = 0 ∧
      GrowsAllocator 1 5 0 loopOut.st nb loopTarget final.st ob finalTarget := by
  obtain ⟨mb,nb,ob,_,_,hb,_,output⟩ := canonical_completion
  rcases hb with ⟨amount,ext,cost,state,baseExt,growth⟩
  refine ⟨mb,nb,ob,baseExt,output.2.1,LoopScopeApplication.suffix_cost loopOut.st,?_⟩
  simpa only [LoopScopeApplication.suffix_cost] using output.2.2

theorem final_new_identity :
    (TEnv.get (.there .here : Idx LoopScopeControls.Ω (.mem A)) final.st.env).map
      (·.id) = some 1 := by decide +kernel

private theorem pointer_base {ob : Nat → Fin W} {target : Machine}
    (pointers : PointerRepr final.st ob 1 target)
    (observed : (match target.mem 3 with
      | .val value => some value.val | _ => none) = some 258) :
    ob 1 = wmod 258 := by
  obtain ⟨ref,henv,hptr⟩ := pointers
    (.there .here : Idx LoopScopeControls.Ω (.mem A))
  have ids : (TEnv.get (.there .here : Idx LoopScopeControls.Ω (.mem A)) final.st.env).map
      (·.id) = some ref.id := congrArg (Option.map (fun ref => ref.id)) henv
  rw [final_new_identity] at ids
  have id : ref.id = 1 := (Option.some.inj ids).symm
  have hcell : cellOf 1 (.there .here : Idx LoopScopeControls.Ω (.mem A)) = 3 := rfl
  rw [hcell, id] at hptr
  rw [hptr] at observed
  apply Fin.ext
  exact Option.some.inj observed

/-- The full small-frame output must represent the actually observed new
object's address; it cannot substitute an old-only map after completion. -/
theorem selected_final_base {nb ob : Nat → Fin W}
    (output : MappedOutput (.memory suffix) 1 5 nb loopOut.st loopTarget
      final.st finalTarget ob) : ob 1 = wmod 258 := by
  apply pointer_base output.1.pointers
  decide +kernel

theorem stale_final_map_refused {nb : Nat → Fin W} :
    ¬ MappedOutput (.memory suffix) 1 5 nb loopOut.st loopTarget
      final.st finalTarget LoopScopeTrace.oldOnly := by
  intro output
  have bad : (LoopScopeTrace.oldOnly 1).val = (wmod 258).val := congrArg Fin.val (selected_final_base output)
  change 0 = 258 at bad
  cases bad

theorem insufficient_consumer_frame {selected : Nat → Fin W}
    {σ : State C LoopScopeControls.Γ} {m : Machine} :
    ¬ (Compilation.memory suffix).Input 1 4 selected σ m := by
  intro input
  have room : 1 + frameNeedProg consume ≤ 4 := input.2.1
  have need : 1 + frameNeedProg consume = 5 := by decide +kernel
  omega

private def observed (m : Machine) : Option (List Nat) :=
  (m.stack ++ LoopScopeTrace.addresses.map m.mem).mapM fun word =>
    match word with | .val n => some n.val | .slot _ => none

/-- The complete ORIGINAL final vector; no altered expected observations. -/
theorem complete_final_vector :
    observed {finalTarget with stack := [w[77],w[88]]} =
      some [77,88,261,99,256,0,258,0,1,8,2,9,0] :=
  LoopScopeTrace.final_vector

theorem corrupt_saved_tail :
    observed {finalTarget with stack := [w[88],w[77]]} ≠
      some [77,88,261,99,256,0,258,0,1,8,2,9,0] :=
  LoopScopeTrace.corrupt_tail

end Solidity.Backend.Passes.LoopReframedCompletion

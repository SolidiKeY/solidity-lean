import Solidity.Backend.Passes.ReframedTriple
import Solidity.Backend.Passes.ReframedCapacity
import Solidity.Backend.Passes.ReframedLoops
import Solidity.Backend.Passes.LoopScopeTrace

/-! A real allocating block-loop uses frame64 after preparation at128 and a
nonallocating consumer at5. Exact reached capacity is transported, not assumed.
The emitted code and every original ordered observation remain unchanged. -/
namespace Solidity.Backend.Passes.ReframedTripleControls
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C initial base machine)
open LoopScopeControls

theorem middle_room (σ : State C LoopScopeControls.Γ)
    (selected : Nat → Fin W) (mid : Machine)
    (capacity : AllocationInput 1 64 3 σ selected mid) :
    LoopScopes.Room enclosed.cert 64 σ selected mid := by
  apply LoopScopes.room_block
  apply LoopScopes.room_base_singleton
  apply Loops.room_singleton conditionCompiled.cert bodyCompiled.cert (by decide +kernel)
  apply loopRoom_one_turn condition body σ selected mid body_stops
  simpa only [body_cost] using capacity

theorem first_link :
    ReframedLink (.memory preparation) checked 1 128 64 base initial machine := by
  intro o mid selected hs _ output
  have same : prepared = o := Except.ok.inj (prepared_source.symm.trans hs)
  subst o
  refine ⟨memory_state_shrink output.1 (by decide) (by decide +kernel),
    by decide +kernel,?_⟩
  apply middle_room
  apply allocation_input_reservation_shrink
    (output.2.2.nextInput (LoopScopeApplication.budget.of_le ?_)) (by decide) (by decide)
  rw [costs.1]
  decide

theorem second_link :
    ReachedReframedLink (.memory preparation) checked (.memory suffix)
      1 128 64 5 base initial machine := by
  intro o mid selected _ _ _
  exact loop_scopes_shrinking_link enclosed suffix (by decide)
    ReframedLoopControls.bounds.1 ReframedLoopControls.bounds.2 costs.2

theorem shared :
    ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine) (amount : Nat)
      (ext : prepared.st.H <+: loopOut.st.H),
      LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ amount ∧
      ((prepare.join wrapped).join consume).run initial =
        .ok ⟨final.st,(prepared.ext.trans loopOut.ext).trans final.ext⟩ ∧
      (prepare.join (wrapped.join consume)).run initial =
        .ok ⟨final.st,prepared.ext.trans (loopOut.ext.trans final.ext)⟩ ∧
      mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
      (Compilation.memory preparation).Input 1 128 base initial {machine with stack := tail} ∧
      run preparation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {mid with stack := tail} mb ∧
      checked.Input 1 64 mb prepared.st {mid with stack := tail} ∧
      run enclosed.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
      MappedOutput checked 1 64 mb prepared.st {mid with stack := tail}
        loopOut.st {next with stack := tail} nb ∧
      (Compilation.memory suffix).Input 1 5 nb loopOut.st {next with stack := tail} ∧
      run suffix.code {next with stack := tail} = .ok {out with stack := tail} 0 ∧
      MappedOutput (.memory suffix) 1 5 nb loopOut.st {next with stack := tail}
        final.st {out with stack := tail} ob ∧
      run ((preparation.code ++ enclosed.code) ++ suffix.code) {machine with stack := tail} =
        .ok {out with stack := tail} 0 ∧
      run (preparation.code ++ (enclosed.code ++ suffix.code)) {machine with stack := tail} =
        .ok {out with stack := tail} 0 := by
  obtain ⟨mb,nb,ob,mid,next,out,sl,sr,hm,hn,ho,all⟩ :=
    compilation_reframed_triple_shared (.memory preparation) checked (.memory suffix)
      LoopScopeApplication.preparation_input rfl first_link second_link
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      prepared_source wrapped_source final_source
  obtain ⟨_,_,_,_,_,middle,_,_,_,_,_⟩ := all []
  rcases middle with ⟨amount,ext,cost,state,baseExt,growth⟩
  refine ⟨mb,nb,ob,mid,next,out,amount,ext,cost,sl,sr,hm,hn,ho,?_⟩
  intro tail
  obtain ⟨ia,ha,ma,id,hd,md,ie,he,me,hl,hr⟩ := all tail
  have growing : GrowsAllocator 1 64 amount prepared.st mb {mid with stack := tail}
      loopOut.st nb {next with stack := tail} := by
    intro cursor hb allocator fit
    exact (growth cursor hb (allocator.mem_eq rfl) fit).mem_eq rfl
  refine ⟨ia,ha,?_,?_,hd,?_,?_,he,?_,hl,hr⟩
  · simpa only [show Evm.Prog.pushes prepare = 0 by decide +kernel,Nat.add_zero] using ma
  · simpa only [show Evm.Prog.pushes prepare = 0 by decide +kernel,Nat.add_zero] using id
  · exact ⟨amount,ext,cost,state.stack tail,baseExt,growing⟩
  · simpa only [show Evm.Prog.pushes prepare = 0 by decide +kernel,
      enclosed.cert.pushes_zero,Nat.add_zero] using ie
  · simpa only [show Evm.Prog.pushes prepare = 0 by decide +kernel,
      enclosed.cert.pushes_zero,suffix.cert.pushes_zero,Nat.add_zero] using me

/-- A zero legacy metric is still not a capacity witness for the actual
positive-cost loop, even after the reservation is correctly shrunk. -/
theorem wrong_zero_cost_refused (selected : Nat → Fin W) (m : Machine) :
    AllocationInput 1 64 0 prepared.st selected (LoopScopeObservations.fullCursor m) ∧
    ¬ LoopScopes.Room enclosed.cert 64 prepared.st selected (LoopScopeObservations.fullCursor m) := by
  refine ⟨.inl rfl,?_⟩
  intro room
  have capacity := scope_cost_allocation_input room actual_cost
  rcases capacity with impossible | ⟨hb,cursor,allocator,fit⟩
  · cases impossible
  · have cell : wMax = cursor := Word.val.inj allocator.arrays.free.cell
    subst cursor
    change W - 1 + 3 < W at fit
    have positive := W_pos
    omega

private def observed (m : Machine) : Option (List Nat) :=
  (m.stack ++ LoopScopeTrace.addresses.map m.mem).mapM fun word =>
    match word with | .val value => some value.val | .slot _ => none
private def observedRun : Evm.Out → Option (List Nat)
  | .ok m 0 => observed m
  | _ => none

theorem complete_observations :
    observedRun (run (preparation.code ++ (enclosed.code ++ suffix.code))
      {machine with stack := [w[77],w[88]]}) =
      some [77,88,261,99,256,0,258,0,1,8,2,9,0] := by
  change observedRun (run LoopScopeTrace.code {machine with stack := [w[77],w[88]]}) = _
  rw [LoopScopeTrace.whole_target_tail]
  exact LoopScopeTrace.final_vector

theorem saved_tail_corruption :
    observedRun (run (preparation.code ++ (enclosed.code ++ suffix.code))
      {machine with stack := [w[88],w[77]]}) ≠
      some [77,88,261,99,256,0,258,0,1,8,2,9,0] := by
  change observedRun (run LoopScopeTrace.code {machine with stack := [w[88],w[77]]}) ≠ _
  rw [LoopScopeTrace.whole_target_tail]
  exact LoopScopeTrace.corrupt_tail
end Solidity.Backend.Passes.ReframedTripleControls

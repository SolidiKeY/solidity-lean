import Solidity.Backend.Passes.LoopScopeControls
import Solidity.Backend.Passes.LoopSequence

namespace Solidity.Backend.Passes.LoopScopeApplication
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C initial base machine initial_repr)
open LoopScopeControls

theorem budget : AllocationInput 1 128 8 initial base machine :=
  .inr ⟨by decide,wmod 256,initial_repr.2,by decide +kernel⟩

theorem preparation_input : (Compilation.memory preparation).Input 1 128 base initial machine :=
  ⟨initial_repr.1,by decide +kernel,budget.of_le (by rw [LoopScopeControls.costs.1]; decide)⟩

/-- The actual loop body allocates once then disables its condition. Every
reached prefix, including a turn before failure, retains capacity. -/
theorem room (σ : State C LoopScopeControls.Γ) (selected : Nat → Fin W) (mid : Machine)
    (capacity : AllocationInput 1 128 3 σ selected mid) :
    LoopScopes.Room enclosed.cert 128 σ selected mid := by
  apply LoopScopes.room_block
  apply LoopScopes.room_base_singleton
  apply Loops.room_singleton conditionCompiled.cert bodyCompiled.cert (by decide +kernel)
  apply loopRoom_one_turn condition body σ selected mid body_stops
  simpa only [body_cost] using capacity

/-- Receiving Room comes from the first pass's ACTUAL allocator growth and
its original concrete total budget, never an assumed preservation result. -/
theorem into_scope : MappedBoundaryLink (.memory preparation) checked 1 128 base initial machine := by
  intro o mid selected hs _ output
  have same : prepared = o := Except.ok.inj (prepared_source.symm.trans hs)
  subst o
  refine ⟨output.1,frames.1,?_⟩
  apply room
  exact output.2.2.nextInput (budget.of_le (by rw [LoopScopeControls.costs.1]; decide))

theorem after_scope : ReachedMappedLink (.memory preparation) checked (.memory suffix)
    1 128 base initial machine := by
  intro o mid selected _ _ _
  exact loop_scopes_memory_link enclosed suffix frames.2 LoopScopeControls.costs.2

theorem joined_source :
    ((prepare.join wrapped).join consume).run initial =
      .ok ⟨final.st,(prepared.ext.trans loopOut.ext).trans final.ext⟩ ∧
    (prepare.join (wrapped.join consume)).run initial =
      .ok ⟨final.st,prepared.ext.trans (loopOut.ext.trans final.ext)⟩ :=
  triple_source_success initial prepared_source wrapped_source final_source

/-- Actual maps AND actual loop cost/extension are all selected before tails. -/
theorem shared : ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine) (amount : Nat)
      (ext : prepared.st.H <+: loopOut.st.H),
    LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ amount ∧
    mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
    run preparation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run enclosed.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    run suffix.code {next with stack := tail} = .ok {out with stack := tail} 0 ∧
    run ((preparation.code ++ enclosed.code) ++ suffix.code) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    run (preparation.code ++ (enclosed.code ++ suffix.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
      prepared.st {mid with stack := tail} mb ∧
    MappedOutput checked 1 128 mb prepared.st {mid with stack := tail}
      loopOut.st {next with stack := tail} nb ∧
    MappedOutput (.memory suffix) 1 128 nb loopOut.st {next with stack := tail}
      final.st {out with stack := tail} ob := by
  simpa only [show Evm.Prog.pushes prepare = 0 by decide +kernel,
    enclosed.cert.pushes_zero,suffix.cert.pushes_zero,Nat.add_zero] using
    loop_scopes_triple_shared (.memory preparation) enclosed (.memory suffix) preparation_input rfl
      into_scope after_scope (by decide +kernel) (by decide +kernel) (by decide +kernel)
      prepared_source wrapped_source final_source

theorem suffix_cost (σ : State C LoopScopeControls.Γ) : suffix.cert.cost σ = 0 :=
  allocationCostProg_zero consume LoopScopeControls.costs.2 σ

/-- Exact total is2+the selected ACTUAL loop cost, with the old nonempty heap
preserved across both physical boundaries. No guessed legacy loop metric. -/
theorem resources {tail : List Word} {mb nb ob : Nat → Fin W} {mid next out : Machine}
    (ha : MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
      prepared.st mid mb)
    (hb : MappedOutput checked 1 128 mb prepared.st mid loopOut.st next nb)
    (hc : MappedOutput (.memory suffix) 1 128 nb loopOut.st next final.st out ob) :
    ∃ amount, ∃ ext : prepared.st.H <+: loopOut.st.H,
      LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ amount ∧
      BaseExtends prepared.st.H mb nb ∧ BaseExtends prepared.st.H mb ob ∧
      GrowsAllocator 1 128 (2 + amount) initial base {machine with stack := tail} final.st ob out := by
  rcases hb with ⟨amount,ext,hcost,state,hbase,hgrowth⟩
  refine ⟨amount,ext,hcost,hbase,Memory.BaseExtends.trans loopOut.ext hbase hc.2.1,?_⟩
  have total := ha.2.2.comp (hgrowth.comp hc.2.2)
  simpa only [LoopScopeControls.costs.1,suffix_cost,Nat.add_zero] using total

end Solidity.Backend.Passes.LoopScopeApplication

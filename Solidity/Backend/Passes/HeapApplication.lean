import Solidity.Backend.Passes.HeapObservations
import Solidity.Backend.Passes.HeapPrefix

namespace Solidity.Backend.Passes.HeapApplication
open Evm Evm.Memory Evm.Compiler
open HeapBoundaryControls
open HeapObservations
open Backend.Passes.Controls.Fixture (C)

/-- All maps are chosen BEFORE arbitrary saved tails; every branch-specific
output, actual stage run and BOTH code associations are retained together with
the complete twelve-cell observation and distinct default-child identities. -/
theorem observed_success :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      (addresses mb).map final.mem = expected mb ∧ mb 1 ≠ mb 2 ∧
      ∀ tail,
        run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
        run mutation.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
        run observation.code {next with stack := tail} = .ok {final with stack := tail} 0 ∧
        run ((allocation.code ++ mutation.code) ++ observation.code) {machine with stack := tail} =
          .ok {final with stack := tail} 0 ∧
        run (allocation.code ++ (mutation.code ++ observation.code)) {machine with stack := tail} =
          .ok {final with stack := tail} 0 ∧
        MappedOutput (.construction allocation) 1 8 base initial {machine with stack := tail}
          first.st {mid with stack := tail} mb ∧
        MappedOutput (.referenceArrays mutation) 1 8 mb first.st {mid with stack := tail}
          second.st {next with stack := tail} nb ∧
        MappedOutput (.memory observation) 1 8 nb second.st {next with stack := tail}
          third.st {final with stack := tail} ob := by
  obtain ⟨mb,nb,ob,mid,next,final,sm,sn,sf,all⟩ :=
    compilation_triple_shared (.construction allocation) (.referenceArrays mutation) (.memory observation)
      input rfl (construction_referenceArrays_link allocation mutation) (reached_link [])
      rfl rfl rfl allocation_source mutation_source observation_source
  have em : {mid with stack := []} = mid := by rw [← sm]
  have en : {next with stack := []} = next := by rw [← sn]
  have ef : {final with stack := []} = final := by rw [← sf]
  have zero := all []
  simp only [em,en,ef] at zero
  obtain ⟨hm,hn,hf,_,_,ha,hd,_⟩ := zero
  obtain ⟨earlier,hr,h0,h1,h2,h15⟩ := HeapPrefix.allocation_observations
  have eqm : earlier = mid := (Out.ok.inj (hr.symm.trans hm)).1
  subst earlier
  have eqn := (Out.ok.inj (hn.symm.trans (mutation_shape ha.1))).1
  have eqf := (Out.ok.inj (hf.symm.trans (read_shape hd.2.state))).1
  have hv := complete_observations ha.1 h0 h1 h2 h15
  refine ⟨mb,nb,ob,mid,next,final,?_,hv.2,all⟩
  rw [eqf,eqn]
  exact hv.1

/-- Reusing the stale initial zero map for new objects violates actual heap
separation. This is a concrete represented-state rejection, not map inequality
assumed as a preservation premise. -/
theorem stale_map_refused :
    ¬ Objects.StateRepr 1 1 8 allocation.frag first.st base machine := by
  intro h
  have bound := h.heap.owner.above child
  change 8 ≤ 0 at bound
  omega

theorem skipped_effect : readExpression.evalT first.st = .ok (lenU 0 (by decide)) := by
  with_unfolding_all rfl

def badMutation : Prog C Locals Locals :=
  .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 2 rfl)))
    (.ref (.var (.there .here) rfl))) .nil
def badCompiled : ReferenceArrays.CompiledProg 1 allocation.frag badMutation :=
  (ReferenceArrays.compileProg 1 _ badMutation).get (by decide +kernel)

theorem reached_source_failure : badMutation.run first.st = .error .revert := by
  with_unfolding_all rfl

/-- The bounds failure is actually reached AFTER allocation, with any saved
tail. No later source success/Input is required on the failed branch. -/
theorem reached_target_failure (tail : List Word) :
    run (allocation.code ++ badCompiled.code) {machine with stack := tail} = .revert := by
  apply (compilation_mapped_revert_iff (.construction allocation) (.referenceArrays badCompiled)
    (compilation_input_stack (.construction allocation) input tail)
    (construction_referenceArrays_link allocation badCompiled) rfl rfl).mpr
  exact .inr ⟨first,allocation_source,.inl reached_source_failure⟩

/-- The third source stage succeeds; declaring that this fixture failed in
stage three contradicts its actual typed source run. -/
theorem wrong_failure_stage : ¬ TerminalFailure read second.st := by
  rintro (bad | ⟨_,bad⟩) <;> rw [observation_source] at bad <;> cases bad

theorem read_before_source : read.run first.st =
    .ok ⟨first.st.push (lenU 0 (by decide)),List.prefix_refl _⟩ := by
  with_unfolding_all rfl

/-- Wrong ordering reaches zero through actual compilation, rather than the
forty-two produced after the mutation. The original nonallocating frame link
is derived from the actual construction output. -/
theorem skipped_target (tail : List Word) :
    ∃ final, run (allocation.code ++ observation.code) {machine with stack := tail} = .ok final 0 ∧
      final.mem 3 = w[0] ∧ final.stack = tail := by
  obtain ⟨mb,ob,mid,final,_,_,ht,hstack,_,hout⟩ :=
    compilation_mapped_success (.construction allocation) (.memory observation)
      (compilation_input_stack (.construction allocation) input tail)
      (construction_memory_link allocation observation (by decide +kernel) (by decide +kernel))
      rfl rfl allocation_source read_before_source
  have hv := hout.1.core.vals (.here : Idx (.val .uint :: Locals) (.val .uint))
  change ReprV .uint (lenU 0 (by decide)) (final.mem 3) at hv
  obtain ⟨a,ha,he,hw⟩ := hv.uint_inv
  have zero : a = 0 := by change (0 : Int) = a at he; omega
  subst a
  exact ⟨final,ht,hw,hstack⟩

/-- An extra raw POP really destroys the saved tail of the successful triple;
it is not a typed compiler witness of source failure. -/
theorem corrupted_saved_tail :
    ∃ final, run (((allocation.code ++ mutation.code) ++ observation.code) ++ [.pop])
      {machine with stack := [w[77]]} = .ok final 0 ∧ final.stack = [] := by
  obtain ⟨mb,nb,ob,mid,next,final,_,_,all⟩ := observed_success
  have h := (all [w[77]]).2.2.2.1
  refine ⟨{final with stack := []},?_,rfl⟩
  rw [run_append_ok h]
  rfl

end Solidity.Backend.Passes.HeapApplication

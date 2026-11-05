import Solidity.Backend.Passes.LoopScopeTrace
import Solidity.Backend.Passes.Divergence

/-! Reached internal terminal controls after the allocating block-loop.
Actual prefix representations select maps before saved tails; failure has no
post-terminal machine/map. These observations do not identify ABI bytes. -/
namespace Solidity.Backend.Passes.LoopScopeTerminal
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls
open LoopScopeTrace (preparedTarget loopTarget preparation_target loop_target)

/-- The physical finite trace is the same execution selected by the compiler
certificate, so its maps retain the full reached representations. -/
theorem prefix_relations : ∃ mb nb,
    MappedOutput (.memory preparation) 1 128 base initial machine prepared.st preparedTarget mb ∧
    MappedOutput checked 1 128 mb prepared.st preparedTarget loopOut.st loopTarget nb := by
  obtain ⟨mid,ht,_,hr⟩ := compilation_success (.memory preparation)
    LoopScopeApplication.preparation_input (by decide +kernel) prepared_source
  have same : mid = preparedTarget := (Evm.Out.ok.inj (ht.symm.trans preparation_target)).1
  subst mid
  obtain ⟨mb,ha⟩ := (mapped_output_iff (.memory preparation) _ _ _ _ _ _ _).mp hr
  have ha' : MappedOutput (.memory preparation) 1 128 base initial machine prepared.st preparedTarget mb := by
    simpa only [show Evm.Prog.pushes prepare = 0 by decide +kernel,Nat.add_zero] using ha
  have hi := LoopScopeApplication.into_scope prepared preparedTarget mb prepared_source preparation_target ha'
  obtain ⟨next,hs,_,hr⟩ := compilation_success checked hi (by decide +kernel) wrapped_source
  have same : next = loopTarget := (Evm.Out.ok.inj (hs.symm.trans loop_target)).1
  subst next
  obtain ⟨nb,hb⟩ := (mapped_output_iff checked _ _ _ _ _ _ _).mp hr
  exact ⟨mb,nb,ha',by simpa only [enclosed.cert.pushes_zero,Nat.add_zero] using hb⟩

/-- Both prefixes are actually successful; no suffix success is required. -/
theorem prefix_tails : ∃ mb nb, ∀ tail,
    run preparation.code {machine with stack := tail} = .ok {preparedTarget with stack := tail} 0 ∧
    run enclosed.code {preparedTarget with stack := tail} = .ok {loopTarget with stack := tail} 0 ∧
    MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
      prepared.st {preparedTarget with stack := tail} mb ∧
    MappedOutput checked 1 128 mb prepared.st {preparedTarget with stack := tail}
      loopOut.st {loopTarget with stack := tail} nb := by
  obtain ⟨mb,nb,ha,hb⟩ := prefix_relations
  refine ⟨mb,nb,?_⟩
  intro tail
  have hpre := compilation_tail_exact (.memory preparation) LoopScopeApplication.preparation_input
    (by decide +kernel) tail
  change run preparation.code {machine with stack := tail} = replaceOutStack tail (run preparation.code machine) at hpre
  rw [preparation_target] at hpre
  have hmid := LoopScopeApplication.into_scope prepared preparedTarget mb prepared_source preparation_target ha
  have hloop := compilation_tail_exact checked hmid (by decide +kernel) tail
  change run enclosed.code {preparedTarget with stack := tail} =
    replaceOutStack tail (run enclosed.code {preparedTarget with stack := []}) at hloop
  have empty : {preparedTarget with stack := []} = preparedTarget := by
    have hs : preparedTarget.stack = [] := by decide +kernel
    generalize preparedTarget = m at hs ⊢
    cases m
    cases hs
    rfl
  rw [empty,loop_target] at hloop
  exact ⟨hpre,hloop,mapped_output_stack (.memory preparation) ha tail tail,
    mapped_output_stack checked hb tail tail⟩

def reject : Prog C LoopScopeControls.Γ LoopScopeControls.Γ := .cons .revert .nil
def rejected : CompiledProg 1 enclosed.frag reject :=
  (Memory.compileProg 1 _ reject).get (by decide +kernel)
theorem reject_source : reject.run loopOut.st = .error .revert := rfl

/-- The failing Input is derived from the actual prior loop output, at the
same selected map, before obtaining its actual emitted revert. -/
theorem reached_revert : ∃ mb nb, ∀ tail,
    MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
      prepared.st {preparedTarget with stack := tail} mb ∧
    MappedOutput checked 1 128 mb prepared.st {preparedTarget with stack := tail}
      loopOut.st {loopTarget with stack := tail} nb ∧
    (Compilation.memory rejected).Input 1 128 nb loopOut.st {loopTarget with stack := tail} ∧
    run rejected.code {loopTarget with stack := tail} = .revert ∧
    run (preparation.code ++ (enclosed.code ++ rejected.code)) {machine with stack := tail} = .revert ∧
    run ((preparation.code ++ enclosed.code) ++ rejected.code) {machine with stack := tail} = .revert := by
  obtain ⟨mb,nb,prefixes⟩ := prefix_tails
  refine ⟨mb,nb,?_⟩
  intro tail
  obtain ⟨hp,hl,ha,hb⟩ := prefixes tail
  have hi := loop_scopes_memory_link enclosed rejected (L := 1) (by decide +kernel) (by decide +kernel)
    loopOut {loopTarget with stack := tail} nb wrapped_source hl hb
  have ht := (compilation_revert_iff (.memory rejected) hi (by decide +kernel)).mpr (.inl reject_source)
  change run rejected.code {loopTarget with stack := tail} = .revert at ht
  have whole : run (preparation.code ++ (enclosed.code ++ rejected.code))
      {machine with stack := tail} = .revert := by
    rw [run_append_ok hp,run_append_ok hl,ht]
  exact ⟨ha,hb,hi,ht,whole,by simpa only [List.append_assoc] using whole⟩

theorem joined_revert :
    (prepare.join (wrapped.join reject)).run initial = .error .revert ∧
    ((prepare.join wrapped).join reject).run initial = .error .revert := by
  have h : (prepare.join (wrapped.join reject)).run initial = .error .revert :=
    (joined_halt_iff initial .revert).mpr (.inr ⟨prepared,prepared_source,
      (joined_halt_iff prepared.st .revert).mpr (.inr ⟨loopOut,wrapped_source,reject_source⟩)⟩)
  exact ⟨h,by simpa only [typed_sequencing_assoc] using h⟩

/-- Direct loop branch is separately inhabited with the same actual heap and
capacity, rather than equating all heap branches with isMemory. -/
theorem direct_input {mb : Nat → Fin W}
    (ha : MappedOutput (.memory preparation) 1 128 base initial machine prepared.st preparedTarget mb) :
    (Compilation.memoryLoops loopCompiled).Input 1 128 mb prepared.st preparedTarget := by
  refine ⟨ha.1,by decide +kernel,?_⟩
  apply Loops.room_singleton conditionCompiled.cert bodyCompiled.cert (by decide +kernel)
  apply loopRoom_one_turn condition body prepared.st mb preparedTarget body_stops
  simpa only [body_cost] using
    ha.2.2.nextInput (LoopScopeApplication.budget.of_le (by rw [LoopScopeControls.costs.1]; decide))

theorem direct_shared : ∃ (mb nb : Nat → Fin W) (amount : Nat) (ext : prepared.st.H <+: loopOut.st.H) (canonical : Machine),
    Loops.Cost loopCompiled.cert prepared.st ⟨loopOut.st,ext⟩ amount ∧
    canonical.stack = [] ∧ ∀ tail,
    run loopCompiled.code {preparedTarget with stack := tail} = .ok {canonical with stack := tail} 0 ∧
    StateRepr 1 1 128 loopCompiled.frag loopOut.st nb {canonical with stack := tail} ∧
    BaseExtends prepared.st.H mb nb ∧
    GrowsAllocator 1 128 amount prepared.st mb {preparedTarget with stack := tail}
      loopOut.st nb {canonical with stack := tail} ∧
    MappedOutput (.memoryLoops loopCompiled) 1 128 mb prepared.st {preparedTarget with stack := tail}
      loopOut.st {canonical with stack := tail} nb := by
  obtain ⟨mb,nb,ha,_⟩ := prefix_relations
  obtain ⟨selected,amount,ext,canonical,h⟩ := loops_success_shared loopCompiled
    (direct_input ha) (by decide +kernel) iteration_source
  exact ⟨mb,selected,amount,ext,canonical,h⟩

end Solidity.Backend.Passes.LoopScopeTerminal

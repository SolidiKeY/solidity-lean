import Solidity.Backend.Passes.LoopCallObservations

/-! Argument failure precedes default return allocation; a stale old argument
reaches the body after its default allocation, then fails before later body
allocations. No post-revert machine/map or unreachable suffix Input is invented. -/
namespace Solidity.Backend.Passes.LoopCallFailures
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls
open LoopScopeTrace (preparedTarget loopTarget)
open LoopCallControls

def badArguments : Prog C LoopScopeControls.Γ Returned :=
  .cons (.call "argumentFailure"
    (.snoc .nil .uint (.user "n")
      (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 2 rfl)))))
    (.mem A (.user "result") rfl rfl) MemoryCallFailures.argumentBody) .nil

def staleArgument : Prog C LoopScopeControls.Γ Returned :=
  .cons (.call "staleCapture"
    (.snocMemory .nil A (.user "a") (.var (.there (.there .here)) rfl))
    (.mem A (.user "result") rfl rfl) callee) .nil

def argument : Calls.Program 1 enclosed.frag badArguments :=
  (Calls.compile 1 _ badArguments).get (by decide +kernel)
def stale : Calls.Program 1 enclosed.frag staleArgument :=
  (Calls.compile 1 _ staleArgument).get (by decide +kernel)
theorem argument_free : Evm.Prog.pushes badArguments = 0 := by decide +kernel
theorem stale_free : Evm.Prog.pushes staleArgument = 0 := by decide +kernel

theorem argument_source : badArguments.run loopOut.st = .error .revert := by with_unfolding_all rfl
theorem stale_source : staleArgument.run loopOut.st = .error .revert := by with_unfolding_all rfl

theorem costs : argument.cost loopOut.st = 0 ∧ stale.cost loopOut.st = 1 := by decide +kernel
theorem frames : 1 + argument.need ≤ 128 ∧ 1 + stale.need ≤ 128 := by decide +kernel

def later : Prog C Returned (.mem A :: Returned) :=
  .cons (.declMem A (.user "unreachable") (some (.newArr (.lit 5 rfl) rfl)) rfl rfl) .nil
def laterCode (F : Frag Returned) : CompiledProg 1 F later := (Memory.compileProg 1 _ later).get (by rfl)

attribute [local irreducible] argument stale producer result preparation enclosed prepared loopOut preparedTarget loopTarget

/-- Actual previously reached representations supply the failing call Input
at SAME nb. Its prefix cost (at most1) is sufficient; later allocation needs
no success, Input or capacity premise after revert. -/
theorem reached {P : Prog C LoopScopeControls.Γ Returned}
    (bad : Calls.Program 1 enclosed.frag P) (free : Evm.Prog.pushes P = 0)
    (payment : Evm.Prog.pays P = false) (failed : P.run loopOut.st = .error .revert)
    (capacity : 1 + bad.need ≤ 128) (bound : bad.cost loopOut.st ≤ 1) :
    ∃ mb nb, ∀ tail,
      run preparation.code {machine with stack := tail} = .ok {preparedTarget with stack := tail} 0 ∧
      run enclosed.code {preparedTarget with stack := tail} = .ok {loopTarget with stack := tail} 0 ∧
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {preparedTarget with stack := tail} mb ∧
      MappedOutput LoopScopeControls.checked 1 128 mb prepared.st {preparedTarget with stack := tail}
        loopOut.st {loopTarget with stack := tail} nb ∧
      (Compilation.memoryCalls bad free).Input 1 128 nb loopOut.st {loopTarget with stack := tail} ∧
      run bad.code {loopTarget with stack := tail} = .revert ∧
      run (preparation.code ++ (enclosed.code ++ (bad.code ++ (laterCode bad.frag).code)))
        {machine with stack := tail} = .revert ∧
      run (((preparation.code ++ enclosed.code) ++ bad.code) ++ (laterCode bad.frag).code)
        {machine with stack := tail} = .revert := by
  obtain ⟨mb,nb,ha,hb⟩ := LoopScopeTerminal.prefix_relations
  have hi : (Compilation.memoryCalls bad free).Input 1 128 nb loopOut.st loopTarget := by
    refine ⟨?_,capacity,?_⟩
    · rcases hb with ⟨_,_,_,state,_,_⟩; exact state
    · exact .inr ⟨by decide,wmod 261,(LoopAllocatingSuffix.actual_resources ha hb).2.1,
        by
          have fit : (261 : Nat) + 1 < W := by decide +kernel
          change 261 + bad.cost loopOut.st < W
          omega⟩
  obtain ⟨mb2,nb2,prefixes⟩ := LoopScopeTerminal.prefix_tails
  refine ⟨mb,nb,?_⟩
  intro tail
  obtain ⟨hp,hl,_,_⟩ := prefixes tail
  have hit := compilation_input_stack (.memoryCalls bad free) hi tail
  have ht := (compilation_revert_iff (.memoryCalls bad free) hit payment).mpr (.inl failed)
  change run bad.code {loopTarget with stack := tail} = .revert at ht
  have whole : run (preparation.code ++ (enclosed.code ++ (bad.code ++ (laterCode bad.frag).code)))
      {machine with stack := tail} = .revert := by
    rw [run_append_ok hp,run_append_ok hl]
    exact run_append_revert ht
  exact ⟨hp,hl,mapped_output_stack (.memory preparation) ha tail tail,
    mapped_output_stack LoopScopeControls.checked hb tail tail,hit,ht,whole,
    by simpa only [List.append_assoc] using whole⟩

theorem argument_reached :
    ∃ mb nb, ∀ tail,
      run preparation.code {machine with stack := tail} = .ok {preparedTarget with stack := tail} 0 ∧
      run enclosed.code {preparedTarget with stack := tail} = .ok {loopTarget with stack := tail} 0 ∧
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {preparedTarget with stack := tail} mb ∧
      MappedOutput LoopScopeControls.checked 1 128 mb prepared.st {preparedTarget with stack := tail}
        loopOut.st {loopTarget with stack := tail} nb ∧
      (Compilation.memoryCalls argument argument_free).Input 1 128 nb loopOut.st {loopTarget with stack := tail} ∧
      run argument.code {loopTarget with stack := tail} = .revert ∧
      run (preparation.code ++ (enclosed.code ++ (argument.code ++ (laterCode argument.frag).code)))
        {machine with stack := tail} = .revert ∧
      run (((preparation.code ++ enclosed.code) ++ argument.code) ++ (laterCode argument.frag).code)
        {machine with stack := tail} = .revert := reached argument argument_free (by decide +kernel)
  argument_source frames.1 (by rw [costs.1]; decide)
theorem stale_reached :
    ∃ mb nb, ∀ tail,
      run preparation.code {machine with stack := tail} = .ok {preparedTarget with stack := tail} 0 ∧
      run enclosed.code {preparedTarget with stack := tail} = .ok {loopTarget with stack := tail} 0 ∧
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {preparedTarget with stack := tail} mb ∧
      MappedOutput LoopScopeControls.checked 1 128 mb prepared.st {preparedTarget with stack := tail}
        loopOut.st {loopTarget with stack := tail} nb ∧
      (Compilation.memoryCalls stale stale_free).Input 1 128 nb loopOut.st {loopTarget with stack := tail} ∧
      run stale.code {loopTarget with stack := tail} = .revert ∧
      run (preparation.code ++ (enclosed.code ++ (stale.code ++ (laterCode stale.frag).code)))
        {machine with stack := tail} = .revert ∧
      run (((preparation.code ++ enclosed.code) ++ stale.code) ++ (laterCode stale.frag).code)
        {machine with stack := tail} = .revert := reached stale stale_free (by decide +kernel)
  stale_source frames.2 (by rw [costs.2]; exact Nat.le_refl _)

theorem wrong_failure_stage : argument.cost loopOut.st ≠ stale.cost loopOut.st := by
  rw [costs.1,costs.2]; decide

theorem source_unreachable :
    (prepare.join (wrapped.join (badArguments.join later))).run initial = .error .revert ∧
    (prepare.join (wrapped.join (staleArgument.join later))).run initial = .error .revert := by
  constructor
  · exact (joined_halt_iff initial .revert).mpr (.inr ⟨prepared,prepared_source,
      (joined_halt_iff prepared.st .revert).mpr (.inr ⟨loopOut,wrapped_source,
        (joined_halt_iff loopOut.st .revert).mpr (.inl argument_source)⟩)⟩)
  · exact (joined_halt_iff initial .revert).mpr (.inr ⟨prepared,prepared_source,
      (joined_halt_iff prepared.st .revert).mpr (.inr ⟨loopOut,wrapped_source,
        (joined_halt_iff loopOut.st .revert).mpr (.inl stale_source)⟩)⟩)

end Solidity.Backend.Passes.LoopCallFailures

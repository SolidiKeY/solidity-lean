import Solidity.Backend.Passes.FixedBooleanFailure
import Solidity.Backend.Passes.ReindexedMemory

/-! Actual population and provisioning select two correlated maps before
the Boolean body's saved-tail quantifier. No stale population map is used
in place of the initializer's selected output map. -/
namespace Solidity.Backend.Passes.FreshBooleanPrefix
open Evm Evm.Memory Evm.Compiler
open Controls.Fixture
open FixedBooleanSequence
open ReferenceControls (Γb state initializeBool branchThenRead)

theorem population_tail (tail : List Word) :
    run population.code {initialMachine with stack := tail} =
      .ok {populatedTarget with stack := tail} 0 := by
  have h := run_tail population.code initialMachine tail (by rw [population_target]; intro h; cases h)
  simpa only [population_target,appendOut,appendTail,show initialMachine.stack = [] from rfl,
    populated_stack,List.nil_append] using h

theorem initializer_tail (b : Bool) (tail : List Word) :
    run (initializer b).code {populatedTarget with stack := tail} =
      .ok {(runtimeInput b) with stack := tail} 0 := by
  simpa only [runtimeInput,writeMachine] using initialize_target b {populatedTarget with stack := tail}

def provisioner (b : Bool) : Memory.CompiledProg 1 population.frag (initializeBool b) :=
  memory_reindex population_fragment (initializer b)

theorem provisioner_code (b : Bool) : (provisioner b).code = (initializer b).code :=
  memory_reindex_code population_fragment (initializer b)

theorem population_initializer_link (b : Bool) (tail : List Word) :
    MappedBoundaryLink (.memory population) (.memory (provisioner b)) 1 128 initialBase initial
      {initialMachine with stack := tail} :=
  memory_nonallocating_mapped_link population (provisioner b)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)

theorem initializer_receiver_link (b : Bool) (base : Nat → Fin W) (tail : List Word) :
    MappedBoundaryLink (.memory (initializer b)) (.memory receiver) 1 128 base σ
      {populatedTarget with stack := tail} :=
  memory_nonallocating_mapped_link (initializer b) receiver (by decide +kernel) (by decide +kernel)

/-- This map is selected by the actual initializer certificate/run, not
chosen later merely to represent an intended receiver result. -/
theorem initialized_output {base : Nat → Fin W}
    (hp : MappedOutput (.memory population) 1 128 initialBase initial initialMachine σ populatedTarget base)
    (b : Bool) :
    ∃ ib, MappedOutput (.memory (initializer b)) 1 128 base σ populatedTarget
      (state b) (runtimeInput b) ib := by
  obtain ⟨m,ht,_,hr⟩ := compilation_success (.memory (initializer b))
    (initializer_input hp b) (by cases b <;> decide +kernel) (initialized_source b)
  have actual : run (initializer b).code populatedTarget = .ok (runtimeInput b) 0 :=
    initialize_target b populatedTarget
  have same : m = runtimeInput b := (Evm.Out.ok.inj (ht.symm.trans actual)).1
  subst m
  simpa only [show Evm.Prog.pushes (initializeBool b) = 0 from by cases b <;> decide +kernel,
    Nat.add_zero] using (mapped_output_iff (.memory (initializer b)) _ _ _ _ _ _ _).mp hr

/-- Inhabited starting at the ORIGINAL fresh state/machine. Both selected
maps precede forall tail; the population map also precedes the Boolean. -/
theorem provisioning_shared :
    ∃ pb : Nat → Fin W, ∀ b : Bool, ∃ ib : Nat → Fin W, ∀ tail,
      (Compilation.memory population).Input 1 128 initialBase initial {initialMachine with stack := tail} ∧
      run population.code {initialMachine with stack := tail} = .ok {populatedTarget with stack := tail} 0 ∧
      MappedOutput (.memory population) 1 128 initialBase initial {initialMachine with stack := tail}
        σ {populatedTarget with stack := tail} pb ∧
      MappedBoundaryLink (.memory population) (.memory (provisioner b)) 1 128 initialBase initial
        {initialMachine with stack := tail} ∧
      (Compilation.memory (initializer b)).Input 1 128 pb σ {populatedTarget with stack := tail} ∧
      run (initializer b).code {populatedTarget with stack := tail} =
        .ok {(runtimeInput b) with stack := tail} 0 ∧
      MappedOutput (.memory (initializer b)) 1 128 pb σ {populatedTarget with stack := tail}
        (state b) {(runtimeInput b) with stack := tail} ib ∧
      MappedBoundaryLink (.memory (initializer b)) (.memory receiver) 1 128 pb σ
        {populatedTarget with stack := tail} ∧
      (Compilation.memory receiver).Input 1 128 ib (state b) {(runtimeInput b) with stack := tail} := by
  obtain ⟨pb,hp⟩ := reached_population
  refine ⟨pb,?_⟩
  intro b
  obtain ⟨ib,hm⟩ := initialized_output hp b
  refine ⟨ib,?_⟩
  intro tail
  have pop : MappedOutput (.memory population) 1 128 initialBase initial {initialMachine with stack := tail}
      σ {populatedTarget with stack := tail} pb := mapped_output_stack (.memory population) hp tail tail
  have init : MappedOutput (.memory (initializer b)) 1 128 pb σ {populatedTarget with stack := tail}
      (state b) {(runtimeInput b) with stack := tail} ib :=
    mapped_output_stack (.memory (initializer b)) hm tail tail
  have ip : (Compilation.memory (initializer b)).Input 1 128 pb σ {populatedTarget with stack := tail} := by
    have aligned := population_initializer_link b tail sourcePopulation {populatedTarget with stack := tail}
      pb population_source (population_tail tail) pop
    have plain := (memory_reindex_input_iff population_fragment (initializer b) pb σ
      {populatedTarget with stack := tail}).mp aligned
    simpa only [population.cert.pushes_zero,Nat.add_zero] using plain
  have ri : (Compilation.memory receiver).Input 1 128 ib (state b) {(runtimeInput b) with stack := tail} := by
    simpa only [(initializer b).cert.pushes_zero,Nat.add_zero] using
      initializer_receiver_link b pb tail ⟨state b,List.prefix_refl _⟩ {(runtimeInput b) with stack := tail}
        ib (initialized_source b) (initializer_tail b tail) init
  exact ⟨compilation_input_stack (.memory population) population_input tail,population_tail tail,
    pop,population_initializer_link b tail,ip,initializer_tail b tail,init,
    initializer_receiver_link b pb tail,ri⟩

end Solidity.Backend.Passes.FreshBooleanPrefix

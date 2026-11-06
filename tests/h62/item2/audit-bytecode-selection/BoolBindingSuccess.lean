import Solidity.Backend.AbiEntry.BoolBinding

/-! Guards the regression that an inhabited Boolean-binding compiler certificate
is mistaken for successful supported execution, allowing reject-all/revert-all
implementations. Joint witnesses retain the actual selected program and initial
word/size representation. These are gasless intrinsic IR observations, not a
native byte loader, Source adequacy, charged execution or fork acceptance. -/
namespace Solidity.H62.BytecodeSelection.BoolBindingFixture
open Solidity.Evm Solidity.Backend.AbiEntry
open Solidity.Backend.AbiEntry.Interface

def seeded (base : Nat) (word size : Fin W) (machine : Machine) : Machine :=
  {machine with mem := fun cell =>
    if cell = base then .val word else
    if cell = base + 1 then .val size else machine.mem cell}

private theorem seeded_word (base : Nat) (word size : Fin W) (machine : Machine) :
    (seeded base word size machine).mem base = .val word := by
  simp only [seeded, ite_true]

private theorem seeded_size (base : Nat) (word size : Fin W) (machine : Machine) :
    (seeded base word size machine).mem (base + 1) = .val size := by
  have distinct : base + 1 ≠ base := Nat.ne_of_gt (Nat.lt_succ_self base)
  simp only [seeded, if_neg distinct, ite_true]

/-- Supported Boolean words use the actual selected compiler result. -/
theorem full_valid_success (C : Solidity.Contract) (base : Nat) (label word : Fin W)
    (machine : Machine) (valid : Solidity.AbiEntry.Kind.bool.valid word.val = true) :
    run (BoolBinding.compiled C base label).code (seeded base word (wmod 36) machine) =
      .ok (boolBoundMachine base label word (seeded base word (wmod 36) machine)) 0 := by
  rw [BoolBinding.executed C base label _ (BoolBinding.selected C base label)
    (seeded base word (wmod 36) machine) word (wmod 36)
    (seeded_word base word (wmod 36) machine) (seeded_size base word (wmod 36) machine)]
  have full : ¬ (wmod 36).val < 36 := by decide
  simp only [boolBindingOutcome, if_neg full, if_pos valid]

/-- All certificate, selection and execution hypotheses coexist with success. -/
theorem certificate_and_execution_jointWitness :
    ∃ (program : (C : Solidity.Contract) → Fin W → Solidity.Prog C RouteCtx BoolBoundCtx)
      (_certificate : BoolBindingCertificate program) (C : Solidity.Contract)
      (base : Nat) (label : Fin W)
      (result : Compiler.Compilation base (Frag.init RouteCtx) (program C label)),
      program = BoolBinding.program ∧
      Compiler.compile base (Frag.init RouteCtx) (program C label) = some result ∧
      ∃ (machine : Machine) (word size : Fin W),
        ¬ size.val < 36 ∧ Solidity.AbiEntry.Kind.bool.valid word.val = true ∧
        machine.mem base = .val word ∧ machine.mem (base + 1) = .val size ∧
        run result.code machine = .ok (boolBoundMachine base label word machine) 0 := by
  exact ⟨BoolBinding.program, BoolBinding.certificate, {vars := []}, 7, wmod 13,
    BoolBinding.compiled {vars := []} 7 (wmod 13), rfl,
    BoolBinding.selected {vars := []} 7 (wmod 13),
    seeded 7 (wmod 1) (wmod 36) Machine.init, wmod 1, wmod 36, by decide, by decide,
    seeded_word 7 (wmod 1) (wmod 36) Machine.init,
    seeded_size 7 (wmod 1) (wmod 36) Machine.init,
    full_valid_success {vars := []} 7 (wmod 13) (wmod 1) Machine.init (by decide)⟩

/-- The successful local contains the validated raw bit, not a supplied payload. -/
theorem validated_local (base : Nat) (label word : Fin W) (machine : Machine)
    (valid : Solidity.AbiEntry.Kind.bool.valid word.val = true) :
    (boolBoundMachine base label word machine).mem (base + 2) = .val word := by
  change upd (upd machine.mem (base + 1) (.val label)) (base + 2)
    (.val (boolValueWord word)) (base + 2) = .val word
  rw [upd_same, BoolBinding.validated_word word valid]

/-- Reject-all disagrees with actual supported-family selection. -/
theorem reject_all_fails_selection (C : Solidity.Contract) (base : Nat) (label : Fin W) :
    (none : Option (Compiler.Compilation base (Frag.init RouteCtx) (BoolBinding.program C label))) ≠
      Compiler.compile base (Frag.init RouteCtx) (BoolBinding.program C label) := by
  rw [BoolBinding.selected]
  intro impossible
  cases impossible

/-- Revert-all disagrees with actual supported-family observable success. -/
theorem always_revert_fails_success (C : Solidity.Contract) (base : Nat)
    (label word : Fin W) (machine : Machine)
    (valid : Solidity.AbiEntry.Kind.bool.valid word.val = true) :
    run [.revert] (seeded base word (wmod 36) machine) ≠
      run (BoolBinding.compiled C base label).code (seeded base word (wmod 36) machine) := by
  rw [full_valid_success C base label word machine valid]
  intro impossible
  cases impossible

/-- The same selected program reverts on a dirty Boolean word. -/
theorem dirty_word_reverts (C : Solidity.Contract) (base : Nat)
    (label : Fin W) (machine : Machine) :
    run (BoolBinding.compiled C base label).code (seeded base (wmod 2) (wmod 36) machine) =
      .revert := by
  rw [BoolBinding.executed C base label _ (BoolBinding.selected C base label)
    (seeded base (wmod 2) (wmod 36) machine) (wmod 2) (wmod 36)
    (seeded_word base (wmod 2) (wmod 36) machine) (seeded_size base (wmod 2) (wmod 36) machine)]
  have full : ¬ (wmod 36).val < 36 := by decide
  have dirty : ¬ Solidity.AbiEntry.Kind.bool.valid (wmod 2).val = true := by decide
  simp only [boolBindingOutcome, if_neg full, if_neg dirty]

/-- Short-head rejection precedes any validation of the word to be bound. -/
theorem short_head_reverts (C : Solidity.Contract) (base : Nat)
    (label word : Fin W) (machine : Machine) :
    run (BoolBinding.compiled C base label).code (seeded base word (wmod 35) machine) =
      .revert := by
  rw [BoolBinding.executed C base label _ (BoolBinding.selected C base label)
    (seeded base word (wmod 35) machine) word (wmod 35)
    (seeded_word base word (wmod 35) machine) (seeded_size base word (wmod 35) machine)]
  have short : (wmod 35).val < 36 := by decide
  simp only [boolBindingOutcome, if_pos short]

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.full_valid_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_valid_success
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.certificate_and_execution_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate_and_execution_jointWitness
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.validated_local' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms validated_local
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.reject_all_fails_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reject_all_fails_selection
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.always_revert_fails_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms always_revert_fails_success
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.dirty_word_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_word_reverts
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.short_head_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_head_reverts
end Solidity.H62.BytecodeSelection.BoolBindingFixture

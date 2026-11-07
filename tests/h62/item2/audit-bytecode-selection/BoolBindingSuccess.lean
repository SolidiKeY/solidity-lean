import Solidity.Backend.AbiEntry.BoolBinding

/-! Guards the regression that an inhabited Boolean-binding compiler certificate
is mistaken for successful supported execution, allowing reject-all/revert-all
implementations. Joint witnesses retain the actual selected program and initial
word/size representation. These are gasless intrinsic IR observations, not a
native byte loader, Source adequacy, charged execution or fork acceptance.
The generic fuel controls also guard against dropping the decoder fuel offset. -/
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

/-- Finite-word size representation is possible exactly below the word modulus. -/
theorem word_size_representable_iff (n : Nat) :
    (∃ size : Fin W, size.val = n) ↔ n < W := by
  constructor
  · rintro ⟨size, same⟩
    exact same ▸ size.isLt
  · intro small
    exact ⟨⟨n, small⟩, rfl⟩


/-- Every representable semantic input has a joint frame/selection witness for
the existing rejection-equivalence field. Native loading is not supplied here. -/
theorem represented_entry_jointWitness (C : Solidity.Contract) (base : Nat)
    (label : Fin W) (input : Solidity.AbiEntry.Input) (fuel : Nat)
    (machine : Machine) (small : input.size < W) :
    ∃ (_certificate : BoolBindingCertificate BoolBinding.program)
      (result : Compiler.Compilation base (Frag.init RouteCtx) (BoolBinding.program C label))
      (prepared : Machine) (size : Fin W),
      Compiler.compile base (Frag.init RouteCtx) (BoolBinding.program C label) = some result ∧
      size.val = input.size ∧ prepared.mem base = .val (rawArgumentWord input) ∧
      prepared.mem (base + 1) = .val size ∧
      (run result.code prepared = .revert ↔
        Solidity.AbiEntry.entry input (fuel + 2) (singleWordParams .bool) = .error .revert) := by
  let size : Fin W := ⟨input.size, small⟩
  let prepared : Machine := seeded base (rawArgumentWord input) size machine
  refine ⟨BoolBinding.certificate, BoolBinding.compiled C base label, prepared, size,
    BoolBinding.selected C base label, rfl, ?_, ?_, ?_⟩
  · exact seeded_word base (rawArgumentWord input) size machine
  · exact seeded_size base (rawArgumentWord input) size machine
  · exact BoolBinding.entry_rejection C base label _ (BoolBinding.selected C base label)
      input fuel prepared size (seeded_word base (rawArgumentWord input) size machine)
      (seeded_size base (rawArgumentWord input) size machine) rfl

/-- A concrete short input inhabits all rejection-equivalence hypotheses.
This is feasibility of a refusal theorem, not a supported-success claim. -/
theorem entry_rejection_hypotheses_jointWitness :
    ∃ (input : Solidity.AbiEntry.Input) (fuel : Nat),
      input.data = [] ∧ input.free = 0 ∧ input.size < W ∧
      ∃ (_certificate : BoolBindingCertificate BoolBinding.program)
        (result : Compiler.Compilation 7 (Frag.init RouteCtx)
          (BoolBinding.program {vars := []} (wmod 13)))
        (prepared : Machine) (size : Fin W),
        Compiler.compile 7 (Frag.init RouteCtx)
          (BoolBinding.program {vars := []} (wmod 13)) = some result ∧
        size.val = input.size ∧ prepared.mem 7 = .val (rawArgumentWord input) ∧
        prepared.mem 8 = .val size ∧
        (run result.code prepared = .revert ↔
          Solidity.AbiEntry.entry input (fuel + 2) (singleWordParams .bool) = .error .revert) := by
  let input : Solidity.AbiEntry.Input := {data := [], free := 0}
  have small : input.size < W := by decide
  refine ⟨input, 0, rfl, rfl, small, ?_⟩
  exact represented_entry_jointWitness {vars := []} 7 (wmod 13) input 0 Machine.init small

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.represented_entry_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms represented_entry_jointWitness
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.entry_rejection_hypotheses_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_rejection_hypotheses_jointWitness

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.word_size_representable_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms word_size_representable_iff


/-- Existing semantic decoder success and selected IR execution share the same
represented input and validated local; no native load provenance is supplied. -/
theorem decoded_input_success_jointWitness (C : Solidity.Contract) (base : Nat)
    (label : Fin W) (input : Solidity.AbiEntry.Input) (fuel : Nat)
    (machine : Machine) (small : input.size < W) (full : ¬ input.size < 36)
    (valid : Solidity.AbiEntry.Kind.bool.valid (Solidity.AbiEntry.load input.data 4) = true) :
    ∃ (_certificate : BoolBindingCertificate BoolBinding.program)
      (result : Compiler.Compilation base (Frag.init RouteCtx) (BoolBinding.program C label))
      (prepared : Machine) (size : Fin W) (value : Solidity.AbiEntry.Word .bool),
      Compiler.compile base (Frag.init RouteCtx) (BoolBinding.program C label) = some result ∧
      size.val = input.size ∧ prepared.mem base = .val (rawArgumentWord input) ∧
      prepared.mem (base + 1) = .val size ∧
      Solidity.AbiEntry.entry input (fuel + 2) (singleWordParams .bool) =
        .ok (.cons (.val (.word value)) .nil) ∧
      run result.code prepared =
        .ok (boolBoundMachine base label (rawArgumentWord input) prepared) 0 ∧
      (boolBoundMachine base label (rawArgumentWord input) prepared).mem
        (cellOf base (.here : Solidity.Idx BoolBoundCtx (.val .bool))) =
          .val ⟨value.val, value.lt⟩ := by
  let size : Fin W := ⟨input.size, small⟩
  let prepared : Machine := seeded base (rawArgumentWord input) size machine
  obtain ⟨value, decoded, executed, localValue⟩ :=
    BoolBinding.decoded_and_bound C base label _ (BoolBinding.selected C base label)
      input fuel prepared size (seeded_word base (rawArgumentWord input) size machine)
      (seeded_size base (rawArgumentWord input) size machine) rfl full valid
  exact ⟨BoolBinding.certificate, BoolBinding.compiled C base label, prepared, size, value,
    BoolBinding.selected C base label, rfl,
    seeded_word base (rawArgumentWord input) size machine,
    seeded_size base (rawArgumentWord input) size machine, decoded, executed, localValue⟩

/-- Concrete byte data inhabits all semantic-success and representation facts.
This is a modeled ABI/IR success control, not a native or whole-Source call. -/
theorem zero_word_input_success_jointWitness :
    ∃ input : Solidity.AbiEntry.Input,
      input.data = List.replicate 36 (0 : UInt8) ∧ input.free = 0 ∧ input.size < W ∧
      ¬ input.size < 36 ∧
      Solidity.AbiEntry.Kind.bool.valid (Solidity.AbiEntry.load input.data 4) = true ∧
      ∃ (_certificate : BoolBindingCertificate BoolBinding.program)
        (result : Compiler.Compilation 7 (Frag.init RouteCtx)
          (BoolBinding.program {vars := []} (wmod 13)))
        (prepared : Machine) (size : Fin W) (value : Solidity.AbiEntry.Word .bool),
        Compiler.compile 7 (Frag.init RouteCtx)
          (BoolBinding.program {vars := []} (wmod 13)) = some result ∧
        size.val = input.size ∧ prepared.mem 7 = .val (rawArgumentWord input) ∧
        prepared.mem 8 = .val size ∧
        Solidity.AbiEntry.entry input 2 (singleWordParams .bool) =
          .ok (.cons (.val (.word value)) .nil) ∧
        run result.code prepared =
          .ok (boolBoundMachine 7 (wmod 13) (rawArgumentWord input) prepared) 0 ∧
        (boolBoundMachine 7 (wmod 13) (rawArgumentWord input) prepared).mem
          (cellOf 7 (.here : Solidity.Idx BoolBoundCtx (.val .bool))) =
            .val ⟨value.val, value.lt⟩ := by
  let input : Solidity.AbiEntry.Input := {data := List.replicate 36 (0 : UInt8), free := 0}
  have small : input.size < W := by decide
  have full : ¬ input.size < 36 := by decide
  have valid : Solidity.AbiEntry.Kind.bool.valid (Solidity.AbiEntry.load input.data 4) = true := by decide
  refine ⟨input, rfl, rfl, small, full, valid, ?_⟩
  exact decoded_input_success_jointWitness {vars := []} 7 (wmod 13) input 0 Machine.init small full valid

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.decoded_input_success_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decoded_input_success_jointWitness
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.zero_word_input_success_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_word_input_success_jointWitness

/-- Every modeled kind shares one selected gate and simultaneously represented
execution hypotheses. Validity is an explicit per-input domain, not a claim
that every kind has an inhabitant. -/
theorem single_word_success_jointWitness (C : Solidity.Contract) (base : Nat)
    (kind : Solidity.AbiEntry.Kind) (label word : Fin W) (machine : Machine)
    (valid : kind.valid word.val = true) :
    ∃ (_certificate : SingleWordGateCertificate SingleWordGate.program)
      (result : Compiler.Compilation base (Frag.init RouteCtx)
        (SingleWordGate.program C kind label)) (prepared : Machine) (size : Fin W),
      Compiler.compile base (Frag.init RouteCtx)
        (SingleWordGate.program C kind label) = some result ∧
      prepared.mem base = .val word ∧ prepared.mem (base + 1) = .val size ∧
      ¬ size.val < 36 ∧
      run result.code prepared =
        .ok {prepared with mem := upd prepared.mem (base + 1) (.val label)} 0 := by
  let size : Fin W := wmod 36
  let prepared : Machine := seeded base word size machine
  have full : ¬ size.val < 36 := by decide
  refine ⟨SingleWordGate.certificate, SingleWordGate.compiled C base kind label,
    prepared, size, SingleWordGate.selected C base kind label,
    seeded_word base word size machine, seeded_size base word size machine, full, ?_⟩
  rw [SingleWordGate.executed C base kind label _
    (SingleWordGate.selected C base kind label) prepared word size
    (seeded_word base word size machine) (seeded_size base word size machine)]
  simp only [singleWordOutcome, if_neg full, wordGateOutcome, if_pos valid]

/-- A globally inhabited generic certificate does not manufacture a valid
input for the modeled empty-enumeration domain. This is an intentional domain
control, not a claim that Source admits an empty enum. -/
theorem empty_enum_has_no_valid_word :
    ¬ ∃ word : Fin W, (Solidity.AbiEntry.Kind.enumBelow 0).valid word.val = true := by
  intro witness
  obtain ⟨word, valid⟩ := witness
  change decide (word.val < 0) = true at valid
  have impossible : ¬ word.val < 0 := Nat.not_lt_zero word.val
  simp only [impossible, decide_false, Bool.false_eq_true] at valid

/-- A positive domain instance accompanies the empty-domain negative control. -/
theorem generic_gate_positive_domain :
    ∃ kind : Solidity.AbiEntry.Kind, ∃ word : Fin W, kind.valid word.val = true := by
  exact ⟨.bool, wmod 1, by decide⟩

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.single_word_success_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms single_word_success_jointWitness
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.empty_enum_has_no_valid_word' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms empty_enum_has_no_valid_word
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.generic_gate_positive_domain' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms generic_gate_positive_domain

/-- The generic rejection field has simultaneous representation hypotheses
for every representable semantic input, independently of word validity. -/
theorem generic_entry_rejection_jointWitness (C : Solidity.Contract) (base : Nat)
    (kind : Solidity.AbiEntry.Kind) (label : Fin W) (input : Solidity.AbiEntry.Input)
    (fuel : Nat) (machine : Machine) (small : input.size < W) :
    ∃ (_certificate : SingleWordGateCertificate SingleWordGate.program)
      (result : Compiler.Compilation base (Frag.init RouteCtx)
        (SingleWordGate.program C kind label)) (prepared : Machine) (size : Fin W),
      Compiler.compile base (Frag.init RouteCtx) (SingleWordGate.program C kind label) = some result ∧
      size.val = input.size ∧ prepared.mem base = .val (rawArgumentWord input) ∧
      prepared.mem (base + 1) = .val size ∧
      (run result.code prepared = .revert ↔
        Solidity.AbiEntry.entry input (fuel + 2) (singleWordParams kind) = .error .revert) := by
  let size : Fin W := ⟨input.size, small⟩
  let prepared : Machine := seeded base (rawArgumentWord input) size machine
  exact ⟨SingleWordGate.certificate, SingleWordGate.compiled C base kind label,
    prepared, size, SingleWordGate.selected C base kind label, rfl,
    seeded_word base (rawArgumentWord input) size machine,
    seeded_size base (rawArgumentWord input) size machine,
    SingleWordGate.entry_rejection C base kind label _ (SingleWordGate.selected C base kind label)
      input fuel prepared size (seeded_word base (rawArgumentWord input) size machine)
      (seeded_size base (rawArgumentWord input) size machine) rfl⟩

/-- Semantic decoding and selected IR success use the same raw input for any
modeled kind. No decoded payload or favorable execution is a premise. -/
theorem generic_decoded_success_jointWitness (C : Solidity.Contract) (base : Nat)
    (kind : Solidity.AbiEntry.Kind) (label : Fin W) (input : Solidity.AbiEntry.Input)
    (fuel : Nat) (machine : Machine) (small : input.size < W)
    (full : ¬ input.size < 36)
    (valid : kind.valid (Solidity.AbiEntry.load input.data 4) = true) :
    ∃ (_certificate : SingleWordGateCertificate SingleWordGate.program)
      (result : Compiler.Compilation base (Frag.init RouteCtx)
        (SingleWordGate.program C kind label)) (prepared : Machine) (size : Fin W)
      (value : Solidity.AbiEntry.Word kind),
      Compiler.compile base (Frag.init RouteCtx) (SingleWordGate.program C kind label) = some result ∧
      size.val = input.size ∧ prepared.mem base = .val (rawArgumentWord input) ∧
      prepared.mem (base + 1) = .val size ∧
      value.val = Solidity.AbiEntry.load input.data 4 ∧
      Solidity.AbiEntry.entry input (fuel + 2) (singleWordParams kind) =
        .ok (.cons (.val (.word value)) .nil) ∧
      run result.code prepared =
        .ok {prepared with mem := upd prepared.mem (base + 1) (.val label)} 0 := by
  let size : Fin W := ⟨input.size, small⟩
  let prepared : Machine := seeded base (rawArgumentWord input) size machine
  let value : Solidity.AbiEntry.Word kind :=
    ⟨Solidity.AbiEntry.load input.data 4, Solidity.AbiEntry.load_lt _ _, valid⟩
  refine ⟨SingleWordGate.certificate, SingleWordGate.compiled C base kind label,
    prepared, size, value, SingleWordGate.selected C base kind label, rfl,
    seeded_word base (rawArgumentWord input) size machine,
    seeded_size base (rawArgumentWord input) size machine, rfl,
    SingleWordGate.entry_success input fuel kind full valid, ?_⟩
  rw [SingleWordGate.executed C base kind label _ (SingleWordGate.selected C base kind label)
    prepared (rawArgumentWord input) size (seeded_word base (rawArgumentWord input) size machine)
    (seeded_size base (rawArgumentWord input) size machine)]
  simp only [singleWordOutcome, wordGateOutcome, rawArgumentWord, size, if_neg full, if_pos valid]

/-- The same selected generic family actually rejects a short frame for every
kind, including kinds with no valid words; no word-validity premise is hidden. -/
theorem generic_short_frame_reverts (C : Solidity.Contract) (base : Nat)
    (kind : Solidity.AbiEntry.Kind) (label word : Fin W) (machine : Machine) :
    run (SingleWordGate.compiled C base kind label).code
      (seeded base word (wmod 35) machine) = .revert := by
  exact SingleWordGate.short_before_word C base kind label
    (seeded base word (wmod 35) machine) (wmod 35)
    (seeded_size base word (wmod 35) machine) (by decide)

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.generic_entry_rejection_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generic_entry_rejection_jointWitness
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.generic_decoded_success_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generic_decoded_success_jointWitness
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.generic_short_frame_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generic_short_frame_reverts

/-- The same successful selected gate cannot justify success of an unfueled
semantic decoder. This is a fuel-boundary control, not a producer defect. -/
theorem generic_fuel_boundary_jointWitness (C : Solidity.Contract) (base : Nat)
    (kind : Solidity.AbiEntry.Kind) (label : Fin W) (input : Solidity.AbiEntry.Input)
    (machine : Machine) (small : input.size < W) (full : ¬ input.size < 36)
    (valid : kind.valid (Solidity.AbiEntry.load input.data 4) = true) :
    ∃ (_certificate : SingleWordGateCertificate SingleWordGate.program)
      (result : Compiler.Compilation base (Frag.init RouteCtx)
        (SingleWordGate.program C kind label)) (prepared : Machine) (size : Fin W)
      (value : Solidity.AbiEntry.Word kind),
      Compiler.compile base (Frag.init RouteCtx) (SingleWordGate.program C kind label) = some result ∧
      size.val = input.size ∧ prepared.mem base = .val (rawArgumentWord input) ∧
      prepared.mem (base + 1) = .val size ∧
      value.val = Solidity.AbiEntry.load input.data 4 ∧
      run result.code prepared =
        .ok {prepared with mem := upd prepared.mem (base + 1) (.val label)} 0 ∧
      Solidity.AbiEntry.entry input 2 (singleWordParams kind) =
        .ok (.cons (.val (.word value)) .nil) ∧
      Solidity.AbiEntry.entry input 0 (singleWordParams kind) = .error .fuel ∧
      Solidity.AbiEntry.entry input 1 (singleWordParams kind) = .error .fuel ∧
      ¬ (run result.code prepared =
          .ok {prepared with mem := upd prepared.mem (base + 1) (.val label)} 0 ↔
        ∃ values, Solidity.AbiEntry.entry input 0 (singleWordParams kind) = .ok values) := by
  obtain ⟨certificate, result, prepared, size, value, selected, represented,
    initialWord, initialSize, rawValue, decoded, executed⟩ :=
    generic_decoded_success_jointWitness C base kind label input 0 machine small full valid
  have low :
      Solidity.AbiEntry.entry input 0 (singleWordParams kind) = .error .fuel ∧
      Solidity.AbiEntry.entry input 1 (singleWordParams kind) = .error .fuel :=
    SingleWordGate.insufficient_fuel input kind full
  refine ⟨certificate, result, prepared, size, value, selected, represented,
    initialWord, initialSize, rawValue, executed, decoded, low.1, low.2, ?_⟩
  intro unshifted
  obtain ⟨values, success⟩ := unshifted.mp executed
  rw [low.1] at success
  cases success

/-- Concrete zero-byte Boolean data inhabits all fuel-boundary hypotheses;
this is not a conditional assertion over an empty supported-input domain. -/
theorem fuel_boundary_input_inhabited :
    ∃ input : Solidity.AbiEntry.Input,
      input.data = List.replicate 36 (0 : UInt8) ∧ input.free = 0 ∧
      input.size < W ∧ ¬ input.size < 36 ∧
      Solidity.AbiEntry.Kind.bool.valid (Solidity.AbiEntry.load input.data 4) = true := by
  exact ⟨{data := List.replicate 36 (0 : UInt8), free := 0},
    rfl, rfl, by decide, by decide, by decide⟩

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.generic_fuel_boundary_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generic_fuel_boundary_jointWitness
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.fuel_boundary_input_inhabited' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fuel_boundary_input_inhabited

/-- Exact success feasibility for the generic head guard, including its
actual selected program and a jointly represented frame. A global certificate
alone does not make an unrepresentable semantic extent feasible. -/
theorem head_gate_actual_success_iff (C : Solidity.Contract) (base : Nat)
    (parameters : List Solidity.AbiEntry.Param) (label : Fin W) (machine : Machine) :
    (∃ (_certificate : HeadGateCertificate HeadGate.program)
      (result : Compiler.Compilation base (Frag.init RouteCtx)
        (HeadGate.program C parameters label)) (prepared : Machine) (size : Fin W),
      Compiler.compile base (Frag.init RouteCtx) (HeadGate.program C parameters label) = some result ∧
      prepared = seeded base (wmod 0) size machine ∧
      prepared.mem (base + 1) = .val size ∧
      run result.code prepared =
        .ok {prepared with mem := upd prepared.mem (base + 1) (.val label)} 0) ↔
      HeadCheck.need parameters < W := by
  constructor
  · rintro ⟨certificate, result, prepared, size, selected, initialFrame, initialSize, executed⟩
    have full : ¬ size.val < HeadCheck.need parameters := by
      intro short
      have rejected : run result.code prepared = .revert :=
        (HeadGate.rejected_iff C base parameters label result selected prepared size initialSize).2 short
      rw [rejected] at executed
      cases executed
    exact Nat.lt_of_le_of_lt (Nat.le_of_not_gt full) size.isLt
  · intro fits
    let size : Fin W := ⟨HeadCheck.need parameters, fits⟩
    let prepared : Machine := seeded base (wmod 0) size machine
    refine ⟨HeadGate.certificate, HeadGate.compiled C base parameters label, prepared, size,
      HeadGate.selected C base parameters label, rfl,
      seeded_size base (wmod 0) size machine, ?_⟩
    rw [HeadGate.executed C base parameters label _ (HeadGate.selected C base parameters label)
      prepared size (seeded_size base (wmod 0) size machine)]
    have full : ¬ size.val < HeadCheck.need parameters := Nat.lt_irrefl _
    simp only [headGateOutcome, if_neg full]

/-- Every represented target size refuses a semantic head extent beyond the
word range. The required size does not wrap into an admissible immediate. -/
theorem head_gate_unrepresentable_refuses (C : Solidity.Contract) (base : Nat)
    (parameters : List Solidity.AbiEntry.Param) (label size : Fin W) (machine : Machine)
    (large : W ≤ HeadCheck.need parameters) :
    run (HeadGate.compiled C base parameters label).code
      (seeded base (wmod 0) size machine) = .revert := by
  exact (HeadGate.rejected_iff C base parameters label _ (HeadGate.selected C base parameters label)
    (seeded base (wmod 0) size machine) size (seeded_size base (wmod 0) size machine)).2
      (Nat.lt_of_lt_of_le size.isLt large)

/-- A concrete nonempty parameter layout inhabits the complete head-guard
certificate/selection/frame/success domain, rather than only a numeric bound. -/
theorem head_gate_nonempty_jointWitness :
    ∃ (_certificate : HeadGateCertificate HeadGate.program)
      (result : Compiler.Compilation 7 (Frag.init RouteCtx)
        (HeadGate.program {vars := []} (singleWordParams .bool) (wmod 13)))
      (prepared : Machine) (size : Fin W),
      Compiler.compile 7 (Frag.init RouteCtx)
        (HeadGate.program {vars := []} (singleWordParams .bool) (wmod 13)) = some result ∧
      prepared = seeded 7 (wmod 0) size Machine.init ∧ prepared.mem 8 = .val size ∧
      run result.code prepared =
        .ok {prepared with mem := upd prepared.mem 8 (.val (wmod 13))} 0 := by
  exact (head_gate_actual_success_iff {vars := []} 7 (singleWordParams .bool)
    (wmod 13) Machine.init).2 (by decide)

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.head_gate_actual_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_gate_actual_success_iff
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.head_gate_unrepresentable_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_gate_unrepresentable_refuses
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.head_gate_nonempty_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_gate_nonempty_jointWitness

/-- Modeled oversized fixed-array metadata inhabits the negative domain.
Its low-word remainder is small, yet every represented frame still refuses;
this neither admits a Source layout nor allocates its semantic extent. -/
theorem head_gate_oversized_jointWitness (C : Solidity.Contract) (base : Nat)
    (label : Fin W) (machine : Machine) :
    ∃ parameters : List Solidity.AbiEntry.Param,
      HeadGateCertificate HeadGate.program ∧ W ≤ HeadCheck.need parameters ∧
      HeadCheck.need parameters % W = 4 ∧
      ∀ size : Fin W,
        run (HeadGate.compiled C base parameters label).code
          (seeded base (wmod 0) size machine) = .revert := by
  let parameters : List Solidity.AbiEntry.Param :=
    [{shape := .fixed (.word (.uint 256)) W, loc := .memory}]
  have large : W ≤ HeadCheck.need parameters := by decide
  have remainder : HeadCheck.need parameters % W = 4 := by decide
  exact ⟨parameters, HeadGate.certificate, large, remainder,
    fun size => head_gate_unrepresentable_refuses C base parameters label size machine large⟩

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.head_gate_oversized_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_gate_oversized_jointWitness

/-- Bare primitive-guard success is feasible on exactly its validated-word
input domain, with actual selection, global certificate and one common frame. -/
theorem word_gate_actual_success_iff (C : Solidity.Contract) (base : Nat)
    (kind : Solidity.AbiEntry.Kind) (label word : Fin W) (machine : Machine) :
    (∃ (_certificate : WordGateCertificate WordGate.program)
      (result : Compiler.Compilation base (Frag.init RouteCtx)
        (WordGate.program C kind label)) (prepared : Machine),
      Compiler.compile base (Frag.init RouteCtx) (WordGate.program C kind label) = some result ∧
      prepared = seeded base word (wmod 0) machine ∧ prepared.mem base = .val word ∧
      run result.code prepared =
        .ok {prepared with mem := upd prepared.mem (base + 1) (.val label)} 0) ↔
      kind.valid word.val = true := by
  constructor
  · rintro ⟨certificate, result, prepared, selected, initialFrame, initialWord, executed⟩
    cases validity : kind.valid word.val with
    | false =>
      have rejected : run result.code prepared = .revert :=
        (WordGate.rejected_iff C base kind label result selected prepared word initialWord).2 validity
      rw [rejected] at executed
      cases executed
    | true => rfl
  · intro valid
    let prepared : Machine := seeded base word (wmod 0) machine
    refine ⟨WordGate.certificate, WordGate.compiled C base kind label, prepared,
      WordGate.selected C base kind label, rfl, seeded_word base word (wmod 0) machine, ?_⟩
    rw [WordGate.executed C base kind label _ (WordGate.selected C base kind label)
      prepared word (seeded_word base word (wmod 0) machine)]
    simp only [wordGateOutcome, if_pos valid]

/-- The generic certificate coexists with a modeled empty success domain.
Every represented word is actually rejected; this asserts no Source enum admission. -/
theorem word_gate_empty_enum_jointWitness (C : Solidity.Contract) (base : Nat)
    (label : Fin W) (machine : Machine) :
    ∃ _certificate : WordGateCertificate WordGate.program,
      ∀ word : Fin W,
        run (WordGate.compiled C base (.enumBelow 0) label).code
          (seeded base word (wmod 0) machine) = .revert := by
  refine ⟨WordGate.certificate, ?_⟩
  intro word
  have invalid : (Solidity.AbiEntry.Kind.enumBelow 0).valid word.val = false := by
    cases validity : (Solidity.AbiEntry.Kind.enumBelow 0).valid word.val with
    | false => exact validity
    | true => exact False.elim (empty_enum_has_no_valid_word ⟨word, validity⟩)
  exact (WordGate.rejected_iff C base (.enumBelow 0) label _
    (WordGate.selected C base (.enumBelow 0) label)
    (seeded base word (wmod 0) machine) word (seeded_word base word (wmod 0) machine)).2 invalid

/-- A valid Boolean word inhabits the full bare-guard success domain. -/
theorem word_gate_positive_jointWitness :
    ∃ (_certificate : WordGateCertificate WordGate.program)
      (result : Compiler.Compilation 7 (Frag.init RouteCtx)
        (WordGate.program {vars := []} .bool (wmod 13))) (prepared : Machine),
      Compiler.compile 7 (Frag.init RouteCtx)
        (WordGate.program {vars := []} .bool (wmod 13)) = some result ∧
      prepared = seeded 7 (wmod 1) (wmod 0) Machine.init ∧ prepared.mem 7 = .val (wmod 1) ∧
      run result.code prepared =
        .ok {prepared with mem := upd prepared.mem 8 (.val (wmod 13))} 0 := by
  exact (word_gate_actual_success_iff {vars := []} 7 .bool (wmod 13)
    (wmod 1) Machine.init).2 (by decide)

/-- The primitive cval comparison's loaded-word, frame and selection hypotheses
coexist at every offset. Zero-padded abstract loads are not native provenance
and this does not assert an ABI entry-span check or successful decoding. -/
theorem word_gate_cval_jointWitness (C : Solidity.Contract) (base : Nat)
    (kind : Solidity.AbiEntry.Kind) (label : Fin W) (input : Solidity.AbiEntry.Input)
    (offset fuel len : Nat) (machine : Machine) :
    ∃ (_certificate : WordGateCertificate WordGate.program)
      (result : Compiler.Compilation base (Frag.init RouteCtx)
        (WordGate.program C kind label)) (prepared : Machine) (word : Fin W),
      Compiler.compile base (Frag.init RouteCtx) (WordGate.program C kind label) = some result ∧
      word.val = Solidity.AbiEntry.load input.data offset ∧
      prepared = seeded base word (wmod 0) machine ∧ prepared.mem base = .val word ∧
      (run result.code prepared = .revert ↔
        Solidity.AbiEntry.cval input (fuel + 1) (.word kind) offset len = .error .revert) := by
  let word : Fin W := ⟨Solidity.AbiEntry.load input.data offset, Solidity.AbiEntry.load_lt _ _⟩
  let prepared : Machine := seeded base word (wmod 0) machine
  exact ⟨WordGate.certificate, WordGate.compiled C base kind label, prepared, word,
    WordGate.selected C base kind label, rfl, rfl, seeded_word base word (wmod 0) machine,
    WordGate.correspondence C base kind label _ (WordGate.selected C base kind label)
      prepared word (seeded_word base word (wmod 0) machine) input offset fuel len rfl⟩

/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.word_gate_actual_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_gate_actual_success_iff
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.word_gate_empty_enum_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_gate_empty_enum_jointWitness
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.word_gate_positive_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_gate_positive_jointWitness
/-- info: 'Solidity.H62.BytecodeSelection.BoolBindingFixture.word_gate_cval_jointWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_gate_cval_jointWitness

end Solidity.H62.BytecodeSelection.BoolBindingFixture

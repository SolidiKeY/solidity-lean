import Solidity.Backend.Passes.SourceCallProducer
import Solidity.Backend.WorldCalls.PaymentControl

/-! Controls for the G42.02 reached-call/frame producer on an actual invocation
(`PaymentControl.origin`): the produced raw outcome is the kernel-observed one,
the step is inhabited on a concrete machine, and spoofed identities, raw
outcomes and target results are refused. No RETURNDATA witness is given. -/
namespace Solidity.Backend.Passes.SourceCallProducerControls
open Solidity.Source
open Solidity.Backend.WorldCalls
open Solidity.Backend.Passes.SourceCallProducer

abbrev origin := PaymentControl.origin

/-- The produced outcome agrees with the independently computed control. -/
theorem produced_raw : raw origin = .ok (.success []) ∧ final origin = PaymentControl.sourceFinal :=
  origin.raw_unique _ _ _ _ (rawAt origin) PaymentControl.source_raw

theorem inhabited : (premises origin).Step (identity origin) PaymentControl.initial
    (.ok (.success [])) PaymentControl.sourceFinal (Evm.run (code origin).full PaymentControl.initial) := by
  rw [← produced_raw.1, ← produced_raw.2]
  exact step_total origin PaymentControl.initial

theorem call_reached :
    (code origin).full[(fetchedCall origin PaymentControl.initial).pc]? = some Evm.Instr.call :=
  (fetchedCall origin PaymentControl.initial).instruction

theorem frame_restored : ∃ machine, Evm.run (code origin).full PaymentControl.initial = .ok machine 0 ∧
    machine.stack = PaymentControl.initial.stack ∧ machine.store = PaymentControl.initial.store ∧
    machine.mem = PaymentControl.initial.mem ∧ machine.self = PaymentControl.initial.self :=
  returns origin PaymentControl.initial

theorem spoofed_mode_refused (m : Evm.Machine) (out : Evm.Out) :
    ¬ (premises origin).Step {identity origin with static := true} m
      (raw origin) (final origin) out := by
  intro h
  have eq := congrArg Identity.static (step_unique origin h).1
  change true = false at eq
  cases eq

theorem unrelated_raw_refused (m : Evm.Machine) (out : Evm.Out) :
    ¬ (premises origin).Step (identity origin) m (.ok (.success [1])) (final origin) out := by
  intro h
  have eq := (step_unique origin h).2.1.trans produced_raw.1
  cases eq

theorem unrelated_target_refused :
    ¬ (premises origin).Step (identity origin) PaymentControl.initial (raw origin) (final origin) .revert := by
  intro h
  obtain ⟨machine, run, _⟩ := returns origin PaymentControl.initial
  have eq := h.2.2.2.trans run
  cases eq

/-- Disclosure, not a witness: `ReturndataDuty` inherits the unconstrained
`FetchedPremises.Returndata` relation, so the trivial relation meets it. Any
`FetchedPremises` built from it carries no RETURNDATA content. -/
def trivial_duty : ReturndataDuty origin := ⟨fun _ _ _ _ _ => True, fun _ => trivial⟩

end Solidity.Backend.Passes.SourceCallProducerControls

/-- info: 'Solidity.Backend.Passes.SourceCallProducerControls.produced_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerControls.produced_raw

/-- info: 'Solidity.Backend.Passes.SourceCallProducerControls.inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerControls.inhabited

/-- info: 'Solidity.Backend.Passes.SourceCallProducerControls.call_reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerControls.call_reached

/-- info: 'Solidity.Backend.Passes.SourceCallProducerControls.frame_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerControls.frame_restored

/-- info: 'Solidity.Backend.Passes.SourceCallProducerControls.spoofed_mode_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerControls.spoofed_mode_refused

/-- info: 'Solidity.Backend.Passes.SourceCallProducerControls.unrelated_raw_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerControls.unrelated_raw_refused

/-- info: 'Solidity.Backend.Passes.SourceCallProducerControls.unrelated_target_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.SourceCallProducerControls.unrelated_target_refused

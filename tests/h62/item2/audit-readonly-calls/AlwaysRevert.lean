import Solidity.Backend.WorldCalls.ExternalCalls
import Solidity.Backend.WorldCalls.PaymentControl

/-! Negative contract control, NOT a producer implementation or target-success
claim. It supplies simultaneous hypotheses for three exact frozen consumers. The exact frozen consumer types permit a reached target
CALL followed by unconditional REVERT to be related to actual Source success.
No reference P10 relation or native correctness is claimed for this relation. -/
namespace Solidity.H62.ReadonlyAudit.AlwaysRevert
open Solidity.Source Solidity.Source.SemanticsExamples Solidity.Roadmap
open Solidity.Backend.WorldCalls
open Solidity.Lowering.Readonly

def code : Code := ⟨[], PaymentControl.code.full ++ [.revert], []⟩

theorem executed : Evm.run code.full PaymentControl.initial = .revert := by rfl

def step (key : Identity) (initial : Evm.Machine) (raw : Except Halt Outcome)
    (final : St EB) (target : Evm.Out) : Prop :=
  key = identity PaymentControl.origin ∧ initial = PaymentControl.initial ∧ raw = .ok (.success []) ∧
    final = PaymentControl.sourceFinal ∧ target = .revert

def premises : Premises PaymentControl.origin where
  code := code
  Observed := fun key _ target raw => key = identity PaymentControl.origin ∧ target = .revert ∧ raw = .ok (.success [])
  Step := step
  bound _ _ _ _ _ h := h.1
  execution key initial raw final target h := by
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact executed
  observed key initial raw final target h := ⟨h.1, h.2.2.2.2, h.2.2.1⟩
  sourceRaw key initial raw final target h := by
    rw [h.2.2.1, h.2.2.2.1]
    exact PaymentControl.source_raw
  p2History key initial raw final target h := by
    rw [h.2.2.2.1]
    exact .start _ _

def call : FetchedCall code.full PaymentControl.initial where
  pc := 3
  reached := PaymentControl.fetched_call.reached
  result := PaymentControl.fetched_call.result
  instruction := by rfl
  prefixRun := by rfl
  execute := PaymentControl.fetched_call.execute

def fetchedPremises : FetchedPremises PaymentControl.origin premises where
  -- This elementary relation deliberately does NOT authenticate P10 adequacy.
  Returndata := fun key {_initial} _call target raw =>
    key = identity PaymentControl.origin ∧ target = .revert ∧ raw = .ok (.success [])
  Fetched := fun initial raw final target => step (identity PaymentControl.origin) initial raw final target
  fetch initial raw final target h := by
    rw [h.2.1]
    exact call
  returndata initial raw final target h := ⟨rfl, h.2.2.2.2, h.2.2.1⟩
  step _ _ _ _ h := h

theorem nonempty_fetched :
    fetchedPremises.Fetched PaymentControl.initial (.ok (.success [])) PaymentControl.sourceFinal .revert :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Exact original fetched contract applies despite target failure. -/
theorem accepted_fetched :
    (∃ reached : FetchedCall premises.code.full PaymentControl.initial,
      fetchedPremises.Returndata (identity PaymentControl.origin) reached .revert (.ok (.success []))) ∧
    Evm.run premises.code.full PaymentControl.initial = .revert ∧ PaymentControl.origin.RawAt (.ok (.success [])) PaymentControl.sourceFinal :=
  ExternalCalls.fetched premises fetchedPremises PaymentControl.initial _ PaymentControl.sourceFinal .revert nonempty_fetched

/-- Exact original declared-return contract also accepts this nonempty client. -/
theorem accepted_declared_return :
    (evalE PaymentControl.origin.global PaymentControl.origin.frame (PaymentControl.origin.horizon + 1)
      (.extCall PaymentControl.origin.target PaymentControl.origin.declaration PaymentControl.origin.signature
        PaymentControl.origin.value PaymentControl.origin.arguments)).run PaymentControl.origin.before =
      (extReturn [] (.success [])).run (PaymentControl.origin.after.1, PaymentControl.sourceFinal) :=
  ExternalCalls.declared_return premises fetchedPremises PaymentControl.initial (.success []) PaymentControl.sourceFinal .revert nonempty_fetched

/-- Actual Source decoding succeeds while the fetched target always reverts. -/
theorem accepted_decoded :
    (evalE PaymentControl.origin.global PaymentControl.origin.frame (PaymentControl.origin.horizon + 1)
      (.extCall PaymentControl.origin.target PaymentControl.origin.declaration PaymentControl.origin.signature
        PaymentControl.origin.value PaymentControl.origin.arguments)).run PaymentControl.origin.before =
      (.ok RVal.unit, (PaymentControl.origin.after.1, PaymentControl.sourceFinal)) :=
  ExternalCalls.decoded premises fetchedPremises PaymentControl.initial (.success []) PaymentControl.sourceFinal .revert
    nonempty_fetched (.ok RVal.unit) (PaymentControl.origin.after.1, PaymentControl.sourceFinal) (by rfl)

theorem target_never_succeeds (machine : Evm.Machine) : Evm.run code.full PaymentControl.initial ≠ .ok machine 0 := by
  rw [executed]
  intro impossible
  cases impossible

/-- An inhabited global boundary may still reject every input. This is a
negative control, never counted as an invocation-hypothesis witness. -/
def rejectAll : Premises PaymentControl.origin where
  code := ⟨[], [.revert], []⟩
  Observed := fun _ _ _ _ => False
  Step := fun _ _ _ _ _ => False
  bound _ _ _ _ _ h := False.elim h
  execution _ _ _ _ _ h := False.elim h
  observed _ _ _ _ _ h := False.elim h
  sourceRaw _ _ _ _ _ h := False.elim h
  p2History _ _ _ _ _ h := False.elim h

def rejectAllFetched : FetchedPremises PaymentControl.origin rejectAll where
  Returndata := fun _ {_initial} _ _ _ => False
  Fetched := fun _ _ _ _ => False
  fetch _ _ _ _ h := False.elim h
  returndata _ _ _ _ h := False.elim h
  step _ _ _ _ h := False.elim h

theorem reject_all_global_inhabited : Nonempty (Premises PaymentControl.origin) ∧
    Nonempty (FetchedPremises PaymentControl.origin rejectAll) :=
  ⟨⟨rejectAll⟩, ⟨rejectAllFetched⟩⟩

theorem reject_all_input_infeasible :
    ¬ ∃ initial raw final target, rejectAllFetched.Fetched initial raw final target := by
  rintro ⟨initial, raw, final, target, impossible⟩
  exact impossible

#print axioms reject_all_global_inhabited
#print axioms reject_all_input_infeasible
#print axioms accepted_fetched
#print axioms accepted_declared_return
#print axioms accepted_decoded
#print axioms target_never_succeeds
end Solidity.H62.ReadonlyAudit.AlwaysRevert

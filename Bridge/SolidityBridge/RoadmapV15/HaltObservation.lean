import Solidity.Roadmap.Evm
import Solidity.Backend.Failure.Observe
import SolidityBridge.RoadmapV15.PrefixTransport

/-!
Exact consumers of the published G06 completed-frame observer. These conversions
choose a canonical representative of an observation; they construct no execution,
EvmYul dispatch, resource adequacy or source-exhaustion observation. In particular,
exceptional and empty REVERT share the approved observation, not the halt itself.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Roadmap

/-- Consume the existing Bool/byte observation, preserving every payload byte. -/
def outcomeOfHalt (h : Evm.Halt) : Outcome :=
  if h.observe.1 then .success h.observe.2 else .revert h.observe.2

/-- Canonical completed-halt representative, not an interpreter. -/
def haltOfOutcome : Outcome → Evm.Halt
  | .success d => .success d
  | .revert d => .revert d

theorem outcomeOfHalt_section (o : Outcome) : outcomeOfHalt (haltOfOutcome o) = o := by
  cases o <;> rfl

theorem haltOfOutcome_observe (h : Evm.Halt) :
    (haltOfOutcome (outcomeOfHalt h)).observe = h.observe := by
  cases h <;> rfl

/-- The conversion identifies exactly the already-approved observations. -/
theorem outcomeOfHalt_eq_iff (a b : Evm.Halt) :
    outcomeOfHalt a = outcomeOfHalt b ↔ a.observe = b.observe := by
  constructor
  · intro h
    have he := congrArg (fun o => (haltOfOutcome o).observe) h
    simpa only [haltOfOutcome_observe] using he
  · intro h
    unfold outcomeOfHalt
    rw [h]

theorem outcomeOfHalt_success_iff (h : Evm.Halt) (d : Evm.Bytes) :
    outcomeOfHalt h = .success d ↔ h = .success d := by
  change outcomeOfHalt h = outcomeOfHalt (.success d) ↔ h = .success d
  rw [outcomeOfHalt_eq_iff]
  exact Evm.Halt.observe_success

theorem outcomeOfHalt_revert_iff (h : Evm.Halt) (d : Evm.Bytes) :
    outcomeOfHalt h = .revert d ↔ h = .revert d ∨ (h = .exceptional ∧ d = []) := by
  cases h <;> simp only [outcomeOfHalt, Evm.Halt.observe, ↓reduceIte,
    Outcome.revert.injEq, Evm.Halt.revert.injEq, reduceCtorEq, false_or,
    false_and, or_false, true_and, eq_comm]

/-- Existing payload encoders (including panic/reason) are consumed unchanged. -/
theorem input_halt_payload (i : Backend.Failure.Input) :
    (haltOfOutcome i.observation).observe.2 = i.bytes := by
  cases i <;> rfl

/-- Agree with the existing emitter's actual terminal classification. -/
theorem input_halt_terminal (i : Backend.Failure.Input) :
    (haltOfOutcome i.observation).observe.1 =
      (match i.terminal with | .RETURN => true | _ => false) := by
  cases i <;> rfl

/-- A completed finite prefix retains every existing event and exact payload. -/
theorem halt_prefix_completed (p : Prefix Event Evm.Halt) (h : Evm.Halt)
    (finished : p.final = some h) :
    mapPrefix id outcomeOfHalt p = ⟨p.events, some (outcomeOfHalt h)⟩ := by
  simp only [mapPrefix, List.map_id, finished, Option.map_some]

/-- Only the owner's existing finite intrinsic-result adapter is accepted.
This supplies an observation representative, not evidence of EVM execution. -/
theorem finite_intrinsic_halt_observation (t : TRes (List UInt8))
    (i : Backend.Failure.Input) (finite : Backend.Failure.inputOfResult t = some i) :
    Backend.Failure.ResultObserves id t (outcomeOfHalt (haltOfOutcome i.observation)) := by
  rw [outcomeOfHalt_section]
  exact Backend.Failure.inputOfResult_sound t i finite

end SolidityBridge.RoadmapV15

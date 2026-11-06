import Solidity.Lowering.V08.SourceCallPhase
import Solidity.Lowering.V08.SourceCustomErrorControls

namespace Solidity.Lowering.V08.SourceCallPhaseControls
open Solidity Source SourceCallPhase SourceCustomErrorControls

def receiver : Roadmap.Address := ⟨9, by decide +kernel⟩
def request : Request := ⟨receiver, ⟨0, by decide +kernel⟩, [0,255,128], false⟩
def staticFrame : Fr := { frame with static := true }
def answering (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) : Glob E :=
  { global pipeline with hasCode := fun _ _ => true, callee := fun _ => .answer out }
def after (out : Roadmap.Outcome) : Source.St E :=
  { populated with events := populated.events ++
    [.call receiver request.value request.input true, .answer out none] }

/-- Actual no-instance execution: code-presence is separately true, inherited
static reaches the request, and all raw bytes survive before caller decoding. -/
theorem actual_raw {Γ : RCtx} (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome)
    (l : Source.Locals E.layout Γ) :
    (raw (answering pipeline out) staticFrame 2 request).run (l, populated) =
      (.ok out, (l, after out)) := by
  cases out <;> rfl

theorem actual_capture (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) :
    (capture (answering pipeline out) staticFrame 2 request).run (locals, populated) =
      (.ok (out, after out), (locals, after out)) := by
  rw [capture_run (point := ⟨staticFrame,locals,populated⟩), actual_raw]

/-- A real caller-side expression changes its local before this same call. -/
def prefixed (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) :
    Source.EM E [.bool] (Roadmap.Outcome × Source.St E) := do
  let _ ← Source.evalE (answering pipeline out) staticFrame 3 setFalse
  capture (answering pipeline out) staticFrame 2 request

theorem actual_prefix (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) :
    (prefixed pipeline out).run (locals, populated) =
      (.ok (out, after out), (.cons (.bool false) .nil, after out)) := by
  change (capture (answering pipeline out) staticFrame 2 request).run
    (.cons (.bool false) .nil, populated) = _
  rw [capture_run (point := ⟨staticFrame,.cons (.bool false) .nil,populated⟩), actual_raw]

/-- The old object, saved world/transient writes, caller identity and journal
prefix are observed separately from the new ordered call/answer history. -/
theorem retained (out : Roadmap.Outcome) :
    (after out).heap.get 0 = some ⟨.bytes .memory, .bytes [0,255]⟩ ∧
    (after out).heap.next = 1 ∧
    (after out).ex.world.accounts self = populated.ex.world.accounts self ∧
    (after out).ex.transient = populated.ex.transient ∧
    (after out).ex.journal = populated.ex.journal ∧
    (after out).fnLocals = populated.fnLocals ∧
    (after out).logs = populated.logs := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def declared : List STy := [.int IntTy.u256]

theorem one_byte_caller_failure (pipeline : Roadmap.Pipeline) :
    ((do let out ← raw (answering pipeline (.success [1])) staticFrame 2 request
         consume declared out) : Source.EM E [.bool] _).run (locals,populated) =
      (.error (.revert []), (locals,after (.success [1]))) := by
  rw [consume_run, actual_raw]
  exact short_success declared [1] (by decide +kernel) locals _

/-- Empty declared demand is observably different; never substitute it for the
callee's declared return types just because caller binders are empty. -/
theorem no_demand_success (pipeline : Roadmap.Pipeline) :
    ((do let out ← raw (answering pipeline (.success [1])) staticFrame 2 request
         consume [] out) : Source.EM E [.bool] _).run (locals,populated) =
      (.ok RVal.unit, (locals,after (.success [1]))) := by
  rw [consume_run, actual_raw]
  rfl

theorem revert_payload (pipeline : Roadmap.Pipeline) :
    ((do let out ← raw (answering pipeline (.revert [1,0,255])) staticFrame 2 request
         consume declared out) : Source.EM E [.bool] _).run (locals,populated) =
      (.error (.revert [1,0,255]), (locals,after (.revert [1,0,255]))) := by
  rw [consume_run, actual_raw]
  exact callee_revert _ _ _ _

theorem unfinished (pipeline : Roadmap.Pipeline) :
    (capture (answering pipeline (.success [1])) staticFrame 0 request).run (locals,populated) =
      (.error .timeout, (locals,populated)) := rfl

theorem static_value_refusal (pipeline : Roadmap.Pipeline) :
    (capture (answering pipeline (.success [1])) staticFrame 2
      {request with value := ⟨1,by decide +kernel⟩}).run (locals,populated) =
      (.error (.revert []), (locals,populated)) := rfl

theorem wrong_order : request.input ≠ [128,255,0] := by decide +kernel
theorem wrong_mode : effectiveStatic staticFrame request ≠ false := by decide +kernel
theorem wrong_outcome : Roadmap.Outcome.success [1] ≠ .revert [1] := by decide +kernel

end Solidity.Lowering.V08.SourceCallPhaseControls

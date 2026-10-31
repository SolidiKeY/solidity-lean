import Solidity.Backend.Failure.Checkpoint
import Solidity.Backend.Failure.Correct

/-! Actual checked payload execution followed by the independent local
checkpoint rules. Store updates before emission are explicit live inputs. -/
namespace Solidity.Backend.Failure.Local

variable {P T : Type}

/-- The bytes are obtained before restoration. Caller memory restoration
cannot replace or erase this immutable return/revert payload. -/
def execute (c : Checkpoint P T) (a : Nat) (i : Input) (live : Journal P T) :
    Option (Journal P T × Roadmap.Outcome) := do
  let (m, outcome) ← Slice.checkedRun (emit a i) live.machine
  match outcome with
  | none => none
  | some o => some (finish c o { live with machine := m }, o)

theorem execute_emitter (c : Checkpoint P T) (a : Nat) (i : Input) (live : Journal P T)
    (hf : Fits a i.bytes) (hs : live.machine.stack.length + 2 ≤ 1024) :
    execute c a i live = some
      (finish c i.observation
        { live with machine := { live.machine with memory := Slice.putBytes live.machine.memory a i.bytes } },
       i.observation) := by
  unfold execute
  rw [show Slice.checkedRun (emit a i) live.machine =
    some ({ live.machine with memory := Slice.putBytes live.machine.memory a i.bytes }, some i.observation) from
      by simpa only [List.append_nil] using checkedRun_emit_suffix a i [] live.machine hf hs]
  rfl

theorem execute_checkpoint (c : Checkpoint P T) (a : Nat) (i : Input) (live : Journal P T)
    (hf : Fits a i.bytes) (hs : live.machine.stack.length + 2 ≤ 1024) :
    let emitted := { live with machine :=
      { live.machine with memory := Slice.putBytes live.machine.memory a i.bytes } }
    execute c a i live = some (finish c i.observation emitted, i.observation) ∧
    CheckpointRel c i.observation emitted (finish c i.observation emitted) :=
  ⟨execute_emitter c a i live hf hs, finish_rel c i.observation _⟩

theorem execute_failure (c : Checkpoint P T) (a : Nat) (d : List UInt8) (live : Journal P T)
    (hf : Fits a d) (hs : live.machine.stack.length + 2 ≤ 1024) :
    execute c a (.custom d) live = some (restore c, .revert d) :=
  execute_emitter c a (.custom d) live hf hs

theorem execute_return (c : Checkpoint P T) (a : Nat) (d : List UInt8) (live : Journal P T)
    (hf : Fits a d) (hs : live.machine.stack.length + 2 ≤ 1024) :
    execute c a (.returned d) live = some
      ({ live with machine := { live.machine with memory := Slice.putBytes live.machine.memory a d } }, .success d) :=
  execute_emitter c a (.returned d) live hf hs

/-- Nested failed emissions with an explicit local continuation. This is a
component witness constructor, not an implementation of Solidity catch. -/
def nested (outer inner : Checkpoint P T) (a b : Nat) (di do' : List UInt8)
    (resume : Journal P T → Journal P T) (deep : Journal P T) :
    Option (Journal P T × Roadmap.Outcome × Roadmap.Outcome) := do
  let (middle, oi) ← execute inner a (.custom di) deep
  let (final, oo) ← execute outer b (.custom do') (resume middle)
  pure (final, oi, oo)

theorem nested_failure (outer inner : Checkpoint P T) (a b : Nat) (di do' : List UInt8)
    (resume : Journal P T → Journal P T) (deep : Journal P T)
    (hi : Fits a di) (ho : Fits b do')
    (hs : deep.machine.stack.length + 2 ≤ 1024)
    (hr : (resume (restore inner)).machine.stack.length + 2 ≤ 1024) :
    nested outer inner a b di do' resume deep =
      some (restore outer, .revert di, .revert do') := by
  unfold nested
  rw [execute_failure inner a di deep hi hs]
  change (do
    let (final, oo) ← execute outer b (.custom do') (resume (restore inner))
    pure (final, Roadmap.Outcome.revert di, oo)) = _
  rw [execute_failure outer b do' (resume (restore inner)) ho hr]
  rfl

end Solidity.Backend.Failure.Local

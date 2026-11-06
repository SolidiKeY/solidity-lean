import Solidity.Yul.World.Raw

/-!
# Separate G01 log/emit observation extension (YQ6)

No change to G01's existing Event or its correctness theorem. Both origins
produce exactly the same log observation; no origin tag is observable. An emit
adapter must prove the indexed-topic/data encoding, including anonymous events.
-/
namespace Solidity.Yul.World
open Solidity.Roadmap (Address Word Bytes Event)

/-- Exactly 0–4 topics; their order is observable. -/
structure Log where
  emitter : Address
  count : Fin 5
  topics : Vector Word count.val
  data : Bytes
  deriving DecidableEq, Repr

/-- Extended observations retain every old event and add full EVM logs. -/
inductive Observation where
  | event (value : Event)
  | log (value : Log)
  deriving DecidableEq, Repr

/-- Compilation must use this same observation for Solidity emit and Yul LOGn. -/
def observeYul (log : Log) : Observation := .log log
def observeEmit (log : Log) : Observation := .log log

theorem emit_yul_agree (log : Log) : observeEmit log = observeYul log := rfl

theorem log_exact (a b : Log) : Observation.log a = .log b ↔ a = b :=
  by simp only [Observation.log.injEq]

/-- Old events remain distinguishable and cannot be confused with logs. -/
theorem event_injective (a b : Event) : Observation.event a = .event b ↔ a = b :=
  by simp only [Observation.event.injEq]

theorem event_ne_log (event : Event) (log : Log) : Observation.event event ≠ .log log := by
  intro h
  cases h

/-- A separate extension contract. Both sides must produce full observations;
erasing logs is deliberately not an available correctness premise. -/
structure ObservationAgreement (Source Target : Type) where
  source : Source → List Observation
  target : Target → List Observation
  related : Source → Target → Prop
  exact_observations : ∀ s t, related s t → source s = target t

/-- Only committed logs are observations. Interaction events of a failed frame
are retained, since the environment already observed them. -/
def discardLogs : List Observation → List Observation
  | [] => []
  | .event e :: rest => .event e :: discardLogs rest
  | .log _ :: rest => discardLogs rest

def interactionEvents : List Observation → List Event
  | [] => []
  | .event e :: rest => e :: interactionEvents rest
  | .log _ :: rest => interactionEvents rest

def committedLogs : List Observation → List Log
  | [] => []
  | .event _ :: rest => committedLogs rest
  | .log l :: rest => l :: committedLogs rest

/-- Rollback keeps the caller prefix verbatim and drops only failed-frame logs.
The adapter must supply the actual prefix/suffix split at source frame entry. -/
def rollbackTrace (callerPrefix calleeSuffix : List Observation) : List Observation :=
  callerPrefix ++ discardLogs calleeSuffix

theorem events_append (xs ys : List Observation) :
    interactionEvents (xs ++ ys) = interactionEvents xs ++ interactionEvents ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [List.cons_append, interactionEvents, ih, List.cons_append]

theorem logs_append (xs ys : List Observation) :
    committedLogs (xs ++ ys) = committedLogs xs ++ committedLogs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [List.cons_append, committedLogs, ih, List.cons_append]

theorem discard_events (xs : List Observation) :
    interactionEvents (discardLogs xs) = interactionEvents xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [discardLogs, interactionEvents, ih]

theorem discard_logs (xs : List Observation) : committedLogs (discardLogs xs) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [discardLogs, committedLogs, ih]

/-- No interaction event is erased by a log rollback. -/
theorem rollback_events (xs ys : List Observation) :
    interactionEvents (rollbackTrace xs ys) = interactionEvents (xs ++ ys) := by
  simp only [rollbackTrace, events_append, discard_events]

/-- No callee log survives a failed frame; every caller log survives. -/
theorem rollback_logs (xs ys : List Observation) :
    committedLogs (rollbackTrace xs ys) = committedLogs xs := by
  simp only [rollbackTrace, logs_append, discard_logs, List.append_nil]

/-- LOGn and emit share the same static restriction in this extension. -/
def appendLog (static : Bool) (trace : List Observation) (log : Log) : Option (List Observation) :=
  if static then none else some (trace ++ [.log log])

theorem appendLog_static (trace : List Observation) (log : Log) :
    appendLog true trace log = none := rfl

/-! ## Complete ordered trace laws, without reachable-outcome assumptions -/

theorem discardLogs_append (xs ys : List Observation) :
    discardLogs (xs ++ ys) = discardLogs xs ++ discardLogs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp only [List.cons_append, discardLogs, ih, List.cons_append]

theorem discardLogs_idempotent (xs : List Observation) :
    discardLogs (discardLogs xs) = discardLogs xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [discardLogs, ih]

/-- Arbitrary caller observations are retained verbatim, with full ordering. -/
theorem rollbackTrace_append_prefix (callerPrefix prior suffix : List Observation) :
    rollbackTrace (callerPrefix ++ prior) suffix = callerPrefix ++ rollbackTrace prior suffix := by
  simp only [rollbackTrace, List.append_assoc]

/-- Composing failed suffixes keeps every interaction in its original order. -/
theorem rollbackTrace_append_suffix (callerPrefix first second : List Observation) :
    rollbackTrace callerPrefix (first ++ second) =
      rollbackTrace (rollbackTrace callerPrefix first) second := by
  simp only [rollbackTrace, discardLogs_append, List.append_assoc]

theorem rollbackTrace_idempotent (callerPrefix suffix : List Observation) :
    rollbackTrace callerPrefix (discardLogs suffix) = rollbackTrace callerPrefix suffix := by
  simp only [rollbackTrace, discardLogs_idempotent]

theorem discardLogs_rollbackTrace (callerPrefix suffix : List Observation) :
    discardLogs (rollbackTrace callerPrefix suffix) = discardLogs callerPrefix ++ discardLogs suffix := by
  simp only [rollbackTrace, discardLogs_append, discardLogs_idempotent]

/-- A child's failed logs already removed cannot reappear or change event
order when the parent also reverts. The result is the FULL observation list. -/
theorem rollbackTrace_nested (callerPrefix outer inner : List Observation) :
    rollbackTrace callerPrefix (rollbackTrace outer inner) = rollbackTrace callerPrefix (outer ++ inner) := by
  simp only [rollbackTrace, discardLogs_append, discardLogs_idempotent]

/-- A successful child is part of the caller prefix of a subsequent failed
frame. The enclosing prefix retains even that successful child's logs. -/
theorem rollbackTrace_success_then_revert (callerPrefix committed failed : List Observation) :
    rollbackTrace (callerPrefix ++ committed) failed =
      callerPrefix ++ (committed ++ discardLogs failed) := by
  simp only [rollbackTrace, List.append_assoc]

/-- An enclosing failure removes committed-child logs too, while preserving
all interactions from the enclosing frame, child and later suffix in order. -/
theorem rollbackTrace_enclosing (callerPrefix outer committed later : List Observation) :
    rollbackTrace callerPrefix ((outer ++ committed) ++ later) =
      rollbackTrace (rollbackTrace (rollbackTrace callerPrefix outer) committed) later := by
  rw [rollbackTrace_append_suffix, rollbackTrace_append_suffix]

end Solidity.Yul.World

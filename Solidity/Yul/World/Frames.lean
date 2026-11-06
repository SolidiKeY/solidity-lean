import Solidity.Yul.World.Observations
import Solidity.Source.World

/-!
# Raw source-frame completion over the existing typed journal

Operation lists are explicit outcome assumptions, not an environment semantics
or a G42 adequacy theorem. Interaction events are distinct from committed logs:
callee revert removes its logs but retains the caller's prefix. Returndata is
caller-local and is overwritten even on failure; a fresh child starts empty.
-/
namespace Solidity.Yul.World
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Source
variable {D : Layout} {L T : Address → SPath → STy}

/-- Only the effects owned by this preparation layer. No physical state copy. -/
structure Effects (D : Layout) (L T : Address → SPath → STy) where
  execution : ExecState D L T
  logs : List Log
  returndata : Bytes

/-- A fresh child has no previous call's returndata. The journal and log
prefix are shared until completion/rollback; physical memory is VY2's input. -/
def freshChild (entry : Effects D L T) : Effects D L T :=
  { entry with returndata := [] }

theorem freshChild_data (entry : Effects D L T) : (freshChild entry).returndata = [] := rfl

/-- Context selection is shared by known and environment execution adapters. -/
inductive CallKind where
  | call | staticcall | delegatecall
  deriving DecidableEq, Repr

/-- No CALLCODE constructor, and no gas/MSIZE/PC/own-code observations. -/
def childContext (s : ExecState D L T) (parent : CallFrame) (kind : CallKind)
    (callee : Address) (value : Word) (input : Bytes) : CallFrame :=
  match kind with
  | .call => s.enter callee parent.this value input parent.static
  | .staticcall => s.enter callee parent.this ⟨0, by decide⟩ input true
  | .delegatecall => s.enter parent.this parent.caller parent.value input parent.static

/-- DELEGATECALL retains caller storage address, sender and value. -/
theorem delegate_context (s : ExecState D L T) (p : CallFrame) (a : Address) (v : Word) (i : Bytes) :
    (childContext s p .delegatecall a v i).this = p.this ∧
    (childContext s p .delegatecall a v i).caller = p.caller ∧
    (childContext s p .delegatecall a v i).value = p.value := ⟨rfl, rfl, rfl⟩

/-- Descendants cannot clear a static context. This does not claim that
arbitrary supplied operation lists respect static restrictions. -/
theorem child_static (s : ExecState D L T) (p : CallFrame) (k : CallKind)
    (a : Address) (v : Word) (i : Bytes) (h : p.static = true) :
    (childContext s p k a v i).static = true := by
  cases k <;> simp only [childContext, ExecState.enter, h]

/-- Completion given actual callee operations/logs and outcome. The adapter
must justify which operations, logs and outcome are possible. -/
def complete (entry : Effects D L T) (this caller : Address) (value : Word) (input : Bytes)
    (static : Bool) (ops : List (Op D L T)) (logs : List Log) (outcome : Outcome) : Effects D L T :=
  let after := entry.execution.run ops
  match outcome with
  | .success data => ⟨after, entry.logs ++ logs, data⟩
  | .revert data => ⟨(entry.execution.enter this caller value input static).rollback after,
      entry.logs, data⟩

/-- Actual journal rollback restores the entry, while exposing failure data. -/
theorem complete_revert (entry : Effects D L T) (a c : Address) (v : Word) (i : Bytes)
    (st : Bool) (ops : List (Op D L T)) (logs : List Log) (data : Bytes) :
    complete entry a c v i st ops logs (.revert data) =
      ⟨entry.execution, entry.logs, data⟩ := by
  simp only [complete, rollback_run]

/-- Caller prefix preserved, including when the caller already journaled
writes. No assumption of an empty journal or an empty log prefix. -/
theorem nested_revert (entry : Effects D L T) (priorOps inner : List (Op D L T))
    (prefixLogs innerLogs : List Log) (a c : Address) (v : Word) (i data : Bytes) (st : Bool) :
    complete ⟨entry.execution.run priorOps, entry.logs ++ prefixLogs, entry.returndata⟩
      a c v i st inner innerLogs (.revert data) =
      ⟨entry.execution.run priorOps, entry.logs ++ prefixLogs, data⟩ :=
  complete_revert _ _ _ _ _ _ _ _ _

/-- A later completion overwrites earlier returndata, independently of the
callee outcome. -/
theorem complete_data (entry : Effects D L T) (a c : Address) (v : Word) (i : Bytes)
    (st : Bool) (ops : List (Op D L T)) (logs : List Log) (outcome : Outcome) :
    (complete entry a c v i st ops logs outcome).returndata = returnData outcome := by
  cases outcome <;> rfl

end Solidity.Yul.World

import Solidity.Backend.Transient.CallbackObservation
import Solidity.Backend.Transient.SourceFrames

/-! G39 selected-slot sharing under supplied source frames. All target bodies
execute the existing P7 run; observations are taken before finish restores the
caller stack. This does not establish G42 call-entry/code/account reachability. -/
namespace Solidity.Backend.FailurePaths.TransientSharing
open Source

/-- Observe the actual framed body before caller restoration. -/
def observed (frame : Fr) (code : Backend.Program) (entry : Transient.State) :
    Transient.Result × Option Evm.Word :=
  let body := Transient.run frame.this frame.static code
    {entry with machine := Transient.frameMachine frame entry.machine}
  (Transient.finish entry body, match body with
    | .ok child => child.machine.stack.head?
    | .error _ _ => none)

theorem load_observed (frame : Fr) (key : Transient.Word) (entry : Transient.State) :
    observed frame (Transient.loadCode key) entry =
      (.ok entry, some (.val (entry.bank frame.this key))) := by
  simp only [observed, Transient.load_code, Transient.finish, Evm.Machine.push,
    Transient.frameMachine]
  rfl

def source {E : Source.Env} {Γ : RCtx} (slot : Transient.BoolSlot E)
    (parent child : Fr) (value : Bool) : EM E Γ (Source.Val E.layout .bool) := do
  Source.writeAt parent slot.path (.bool value)
  Source.readAt child slot.path .bool

/-- Initial read, executed write and later same-owner read, with genuine initial
representation. A supplied child frame may have a different sender/static flag;
sharing is justified by its SAME owner, not by an arbitrary target pairing. -/
theorem self_share {E : Source.Env} {Γ : RCtx} (slot : Transient.BoolSlot E)
    (parent child : Fr) (normal : parent.static = false) (sameOwner : child.this = parent.this)
    (value : Bool) (state : Source.EMState E Γ) (target : Transient.State)
    (initial : Transient.Represents slot parent.this state target) :
    ∃ old,
      (Source.readAt parent slot.path .bool).run state = (.ok (.bool old), state) ∧
      observed parent (Transient.loadCode slot.key) target = (.ok target, some (.val (Transient.boolWord old))) ∧
      (source slot parent child value).run state =
        (.ok (.bool value), (state.1, Transient.sourceWrite slot parent.this value state.2)) ∧
      Transient.callbackInFrame parent (Transient.storeCode slot.key (Transient.boolWord value)) target =
        .ok (Transient.write target parent.this slot.key (Transient.boolWord value)) ∧
      observed child (Transient.loadCode slot.key)
        (Transient.write target parent.this slot.key (Transient.boolWord value)) =
        (.ok (Transient.write target parent.this slot.key (Transient.boolWord value)),
          some (.val (Transient.boolWord value))) ∧
      Transient.Represents slot child.this
        (state.1, Transient.sourceWrite slot parent.this value state.2)
        (Transient.write target parent.this slot.key (Transient.boolWord value)) := by
  obtain ⟨old, found, word⟩ := initial
  have after : Transient.Represents slot parent.this
      (state.1, Transient.sourceWrite slot parent.this value state.2)
      (Transient.write target parent.this slot.key (Transient.boolWord value)) :=
    Transient.write_represents slot parent.this value state target
  have written : ((Transient.sourceWrite slot parent.this value state.2).ex.transient.cells parent.this).read
      slot.path = some (Transient.boolValue slot value) := by
    change ((state.2.ex.transient.set parent.this
      ((state.2.ex.transient.cells parent.this).write slot.path (Transient.boolValue slot value))).cells parent.this).read _ = _
    simp only [Source.Transient.set, dif_pos, Source.Storage.write_read]
  refine ⟨old, Transient.read_actual slot parent state old found, ?_, ?_,
    Transient.framed_store parent normal slot.key (Transient.boolWord value) target, ?_, ?_⟩
  · rw [load_observed, word]
  · rw [source, Source.Hoare.run_bind, Transient.write_actual slot parent normal value state]
    exact Transient.read_actual slot child (state.1, Transient.sourceWrite slot parent.this value state.2)
      value (by rw [sameOwner]; exact written)
  · rw [load_observed, sameOwner]
    simp only [Transient.write, Transient.put_same]
  · simpa only [sameOwner] using after

/-- An executable sequence of two actual framed bodies. -/
def execute (parent child : Fr) (key value : Transient.Word) (entry : Transient.State) :
    Transient.Result × Option Evm.Word :=
  match Transient.callbackInFrame parent (Transient.storeCode key value) entry with
  | .ok next => observed child (Transient.loadCode key) next
  | .error why dirty => (.error why dirty, none)

theorem execute_shared (parent child : Fr) (normal : parent.static = false)
    (sameOwner : child.this = parent.this) (key value : Transient.Word) (entry : Transient.State) :
    execute parent child key value entry =
      (.ok (Transient.write entry parent.this key value), some (.val value)) := by
  simp only [execute, Transient.framed_store parent normal, load_observed, sameOwner,
    Transient.write, Transient.put_same]

theorem execute_static (parent child : Fr) (static : parent.static = true)
    (key value : Transient.Word) (entry : Transient.State) :
    execute parent child key value entry = (.error .staticWrite entry, none) := by
  rw [execute, Transient.framed_static_store parent static]

theorem source_static {E : Source.Env} {Γ : RCtx} (slot : Transient.BoolSlot E)
    (parent child : Fr) (static : parent.static = true) (value : Bool) (state : Source.EMState E Γ) :
    (source slot parent child value).run state = (.error (.revert []), state) := by
  rw [source, Source.Hoare.run_bind, Transient.write_static slot parent static value state]

/-- Reset is sequenced AFTER an executed callback; it is not a rewrite of a
hypothetical write state. Reset preserves the complete ordinary target machine. -/
def writeReset (frame : Fr) (key value : Transient.Word) (entry : Transient.State) : Option Transient.State :=
  match Transient.callbackInFrame frame (Transient.storeCode key value) entry with
  | .ok child => some (Transient.endTx child)
  | .error _ _ => none

theorem write_reset (frame : Fr) (normal : frame.static = false)
    (key value : Transient.Word) (entry : Transient.State) :
    writeReset frame key value entry = some (Transient.endTx entry) := by
  simp only [writeReset, Transient.framed_store frame normal, Transient.endTx, Transient.write]

/-- Actual Source reset and target reset restore the typed default relation.
This preserves source world/heap and target persistent/memory machine fields. -/
theorem reset_relation {E : Source.Env} {Γ : RCtx} (slot : Transient.BoolSlot E)
    (parent : Fr) (value : Bool) (state : Source.EMState E Γ) (target : Transient.State) :
    let next := Transient.sourceWrite slot parent.this value state.2
    let targetNext := Transient.write target parent.this slot.key (Transient.boolWord value)
    Transient.Represents slot parent.this (state.1, {next with ex := next.ex.endTx}) (Transient.endTx targetNext) ∧
    next.ex.endTx.world = state.2.ex.world ∧ next.heap = state.2.heap ∧
    (Transient.endTx targetNext).machine = target.machine :=
  ⟨Transient.end_represents slot parent.this _ _, rfl, rfl, rfl⟩

#print axioms load_observed
#print axioms self_share
#print axioms write_reset
#print axioms reset_relation
#print axioms execute_shared
#print axioms execute_static
#print axioms source_static
end Solidity.Backend.FailurePaths.TransientSharing

import Solidity.Backend.Transient.Frames
namespace Solidity.Backend.Transient
/-- Observe the successful body's stack before finish restores the caller. -/
def callbackObserved (owner : Roadmap.Address) (static : Bool)
    (code : List Backend.Instr) (entry : State) : Result × Option Evm.Word :=
  let body := run owner static code {entry with machine := {entry.machine with stack := []}}
  (finish entry body, match body with
    | .ok child => child.machine.stack.head?
    | .error _ _ => none)
theorem callbackObserved_result (owner : Roadmap.Address) (static : Bool) (code : List Backend.Instr) (entry : State) :
    (callbackObserved owner static code entry).1 = callback owner static code entry := by rfl
theorem callbackObserved_load (owner : Roadmap.Address) (static : Bool) (k : Word) (entry : State) :
    callbackObserved owner static (loadCode k) entry =
      (.ok entry, some (.val (entry.bank owner k))) := by
  simp only [callbackObserved, load_code, finish, Evm.Machine.push]
  rfl
theorem callback_store_endTx (owner : Roadmap.Address) (k v : Word) (entry : State) :
    (match callback owner false (storeCode k v) entry with
      | .ok child => some (endTx child)
      | .error _ _ => none) = some (endTx entry) := by
  simp only [callback_store, endTx, write]
/-- Pre-write agreement is required: observing the initial selected cell is
not justified by the relation that a write establishes afterwards. This is a
selected full-word compiler port, not a packed-layout simulation. -/
theorem callbackObserved_source_write {E : Source.Env} {Γ : Source.RCtx}
    (slot : BoolSlot E) (F : Source.Fr) (normal : F.static = false)
    (s : Source.EMState E Γ) (target : State)
    (before : Represents slot F.this s target) (value : Bool) :
    ∃ old,
      (Source.readAt F slot.path .bool).run s = (.ok (.bool old), s) ∧
      callbackObserved F.this F.static (loadCode slot.key) target =
        (.ok target, some (.val (boolWord old))) ∧
      (Source.writeAt F slot.path (.bool value)).run s =
        (.ok (), (s.1, sourceWrite slot F.this value s.2)) ∧
      callback F.this false (storeCode slot.key (boolWord value)) target =
        .ok (write target F.this slot.key (boolWord value)) ∧
      Represents slot F.this (s.1, sourceWrite slot F.this value s.2)
        (write target F.this slot.key (boolWord value)) := by
  obtain ⟨old, found, word⟩ := before
  refine ⟨old, read_actual slot F s old found, ?_,
    write_actual slot F normal value s, callback_store F.this _ _ target,
    write_represents slot F.this value s target⟩
  simp only [callbackObserved_load, word]

end Solidity.Backend.Transient

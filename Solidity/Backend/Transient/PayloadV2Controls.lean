import Solidity.Backend.Transient.PayloadV2
import Solidity.Backend.Transient.Controls

/-! Guards dropped/nonempty payloads, dirty-byte truncation, static-write
misclassification and loss of an inhabited caller journal/symbolic stack.
Reuses the existing populated transient fixture. No Source/world/coherent
word/byte-memory or arbitrary-payload adequacy is inferred from these controls. -/
namespace Solidity.Backend.Transient.PayloadV2Controls

def entry : State :=
  {Controls.target with machine := {Controls.target.machine with
    stack := [.slot (.root 99),.val ⟨0xa5,by decide⟩]}}
def memory : PayloadV2.Memory := fun a =>
  if a=64 then 0x33 else if a=65 then 0x44 else 0x55
def key : Word := ⟨9,by decide⟩
def stored : Word := ⟨7,by decide⟩
def offset : Word := ⟨64,by decide⟩
def dirtyByte : Word := ⟨0x1ab,by decide⟩
def code : Program := storeCode key stored ++ PayloadV2.byteRevertCode offset dirtyByte

theorem nonempty_prefix : entry.journal.length=1 := by rfl

theorem actual_write_changes :
    (write entry Controls.owner key stored).bank Controls.owner key=stored ∧
    entry.bank Controls.owner key=⟨0,by decide⟩ := by
  exact ⟨Transient.put_same entry.bank Controls.owner key stored,rfl⟩

/-- The raw executed byte body preserves even a symbolic older stack tail. -/
theorem raw_byte_tail :
    PayloadV2.run Controls.owner false (PayloadV2.byteRevertCode offset dirtyByte) entry memory =
      .exit (.revert [0xab]) entry (Failure.Slice.putByte memory 64 0xab) := by
  exact PayloadV2.byte_revert_run Controls.owner false entry memory offset dirtyByte

/-- Complete caller state and memory, including its prior other-owner journal. -/
theorem actual_nonempty_rollback :
    PayloadV2.callback Controls.owner false code entry memory =
      .exit (.revert [0xab]) entry memory := by
  exact PayloadV2.callback_store_byte_revert Controls.owner entry memory key stored offset dirtyByte

theorem static_refusal :
    PayloadV2.callback Controls.owner true code entry memory =
      .error .staticWrite entry memory := by
  exact PayloadV2.callback_static_store_suffix Controls.owner entry memory key stored _

theorem not_unsupported :
    PayloadV2.callback Controls.owner false code entry memory ≠
      .error .unsupported entry memory := by
  rw [actual_nonempty_rollback]
  intro impossible
  cases impossible

theorem wrong_payload :
    PayloadV2.callback Controls.owner false code entry memory ≠
      .exit (.revert [0]) entry memory := by
  rw [actual_nonempty_rollback]
  intro impossible
  have outcome := (PayloadV2.Result.exit.inj impossible).1
  have payload := Roadmap.Outcome.revert.inj outcome
  have byte := (List.cons.inj payload).1
  exact (by decide : (0xab : UInt8) ≠ 0) byte

theorem empty_payload_refused :
    PayloadV2.callback Controls.owner false code entry memory ≠
      .exit (.revert []) entry memory := by
  rw [actual_nonempty_rollback]
  intro impossible
  have payload := Roadmap.Outcome.revert.inj (PayloadV2.Result.exit.inj impossible).1
  cases payload

theorem lost_prefix_refused :
    PayloadV2.callback Controls.owner false code entry memory ≠
      .exit (.revert [0xab]) Controls.base memory := by
  rw [actual_nonempty_rollback]
  intro impossible
  have same := (PayloadV2.Result.exit.inj impossible).2.1
  have lengths := congrArg (fun state : State => state.journal.length) same
  change (1:Nat)=0 at lengths
  omega


/-- info: 'Solidity.Backend.Transient.PayloadV2Controls.actual_nonempty_rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_nonempty_rollback
/-- info: 'Solidity.Backend.Transient.PayloadV2Controls.static_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms static_refusal
/-- info: 'Solidity.Backend.Transient.PayloadV2Controls.wrong_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_payload
end Solidity.Backend.Transient.PayloadV2Controls

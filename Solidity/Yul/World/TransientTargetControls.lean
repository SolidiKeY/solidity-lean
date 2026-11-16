import Solidity.Yul.World.TransientTargetPort
import Solidity.Yul.Views.TransientSlotControls
namespace Solidity.Yul.World.TransientTarget.Controls
open Views Solidity.Backend
open Views.Controls Views.TransientSlotControls

def target : Transient.State := Transient.write
  ⟨{Evm.Machine.init with stack := [.val ⟨0x99, by decide⟩]},
    fun _ _ => ⟨0xbeef0000, by decide⟩, []⟩ 2 99 rawMax

def completed := (transientSlotStore? (ps:=ps) (ts:=ts) frame 0 rawB caller.1.2 caller.2).get (by decide)

theorem loaded_full_word : (transientSlotLoad ts callerCore account 0,
    Transient.callbackObserved account false (Transient.loadCode 0)
      (Transient.write target account 0 rawA)) =
      (some rawA, (.ok (Transient.write target account 0 rawA), some (.val rawA))) := by
  simp only [caller_full_readback.1, Transient.callbackObserved_load, Transient.write, Transient.put_same]

theorem executed_store : store (ps:=ps) (ts:=ts) frame 0 rawB caller.1.2 caller.2 target =
    some (completed, .ok (Transient.write target account 0 rawB)) := by
  rfl

theorem typed_complement_and_journals : (completed.1.2.2.ex.transient.cells account).read (rootPath "temp") =
    some (.int 0xabcd (by decide)) ∧
    completed.2.cells (complementKey true account 0) = 0xb6b60000 ∧
    completed.1.2.2.ex.journal.length = 3 ∧ completed.2.journal.length = 3 := by
  exact ⟨rfl, by decide, rfl, rfl⟩

theorem static_both_carriers : store (ps:=ps) (ts:=ts) {frame with static:=true} 0 rawB caller.1.2 caller.2 target =
    some (((.error (.revert []),caller.1.2),caller.2), .error .staticWrite target) := by
  exact store_static (ps:=ps) (ts:=ts) {frame with static:=true} 0 rawB caller.1.2 caller.2 target rfl (by decide)

theorem dirty_padding_required : transientSlotLoad ts callerCore account 0 ≠ some ⟨0x1234, by decide⟩ := by
  decide

theorem other_target_preserved : (Transient.write target account 0 rawB).bank 2 99 = rawMax := by
  decide

theorem reset_unowned_slot : transientSlotLoad ts (companionEndTx childCore) account 99 =
    some ((Transient.endTx target).bank account 99) := by
  exact reset_readback_zero ts childCore target actual_zero_defaults account 99
theorem initially_mismatched_view : transientSlotLoad ts callerCore account 0 ≠ some (target.bank account 0) := by
  decide
theorem actual_stored_load : (transientSlotLoad ts ⟨completed.1.2.2.ex,completed.2⟩ account 0,
    Transient.callbackObserved account false (Transient.loadCode 0)
      (Transient.write target account 0 rawB)) =
    (some rawB,(.ok (Transient.write target account 0 rawB),some (.val rawB))) := by
  exact stored_load_readback frame 0 rawB caller.1.2 caller.2 target completed
    (Option.some_get (by decide)).symm rfl rootTempChecked.separated

end Solidity.Yul.World.TransientTarget.Controls

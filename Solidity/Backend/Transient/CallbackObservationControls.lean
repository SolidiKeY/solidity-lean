import Solidity.Backend.Transient.CallbackObservation
import Solidity.Backend.Transient.Controls
/-! Distinct owners and a nonempty caller stack/history come from Controls.
These controls observe the loaded word before finish restores the caller. -/
namespace Solidity.Backend.Transient.Controls
theorem owner_load_observed : callbackObserved owner true (loadCode slot.key) target =
    (.ok target, some (.val ⟨0, by decide⟩)) := by
  simp only [callbackObserved_load]
  rfl
theorem other_load_observed : callbackObserved other true (loadCode slot.key) target =
    (.ok target, some (.val ⟨0xcc, by decide⟩)) := by
  simp only [callbackObserved_load]
  rfl
theorem wrong_owner_observation : (callbackObserved owner true (loadCode slot.key) target).2 ≠
    (callbackObserved other true (loadCode slot.key) target).2 := by
  simp only [callbackObserved_load]
  decide
theorem written_load_observed : callbackObserved owner false (loadCode slot.key)
    (write target owner slot.key (boolWord true)) =
      (.ok (write target owner slot.key (boolWord true)), some (.val (boolWord true))) := by
  simp only [callbackObserved_load, write, put_same]
theorem executed_callback_reset : (match callback owner false (storeCode slot.key (boolWord true)) target with
    | .ok child => some (endTx child)
    | .error _ _ => none) = some (endTx target) := by
  rfl
end Solidity.Backend.Transient.Controls

import Solidity.Backend.FailurePaths.TransientSharing
import Solidity.Backend.Transient.SourceCallback

/-! Selected-cell consumer of the actual registered Source callback fixture.
Initial agreement and observed before/after values are explicit. Target code
is the ported local store body, not compilation of the complete CALL protocol;
external strategy, code/account admission and full G42/EVM adequacy remain open. -/
namespace Solidity.Backend.FailurePaths.TransientCallback
open Source
open Transient.SourceCallback

/-- Real Source callback execution, actual framed target store, and actual
caller-side readback. Arbitrary outer bytes remain the supplied Source strategy
answer, not bytes manufactured by the fallback or by the target store. -/
theorem cell_port (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (target : Transient.State)
    (initial : Transient.Represents slot Transient.Controls.owner before target) :
    ∃ old,
      (Source.readAt (child false) slot.path .bool).run before = (.ok (.bool old), before) ∧
      TransientSharing.observed (child false) (Transient.loadCode slot.key) target =
        (.ok target, some (.val (Transient.boolWord old))) ∧
      (run pipeline (.success bytes) false 10).run before =
        (.ok (.success bytes), after (.success bytes) false) ∧
      Transient.callbackInFrame (child false) (Transient.storeCode slot.key (Transient.boolWord true)) target =
        .ok (Transient.write target Transient.Controls.owner slot.key (Transient.boolWord true)) ∧
      (Source.readAt (child false) slot.path .bool).run (after (.success bytes) false) =
        (.ok (.bool true), after (.success bytes) false) ∧
      TransientSharing.observed (child false) (Transient.loadCode slot.key)
        (Transient.write target Transient.Controls.owner slot.key (Transient.boolWord true)) =
        (.ok (Transient.write target Transient.Controls.owner slot.key (Transient.boolWord true)),
          some (.val (Transient.boolWord true))) ∧
      Transient.Represents slot Transient.Controls.owner (after (.success bytes) false)
        (Transient.write target Transient.Controls.owner slot.key (Transient.boolWord true)) := by
  obtain ⟨old, found, word⟩ := initial
  obtain ⟨actualSource, actualTarget, represented⟩ := source_target pipeline bytes target
  refine ⟨old, Transient.read_actual slot (child false) before old found, ?_,
    actualSource, actualTarget, ?_, ?_, represented⟩
  · rw [TransientSharing.load_observed]
    change (Transient.Result.ok target, some (Evm.Word.val (target.bank Transient.Controls.owner slot.key))) = _
    rw [word]
  · exact Transient.read_actual slot (child false) _ true (by rfl)
  · rw [TransientSharing.load_observed]
    simp only [child, Transient.write, Transient.put_same]

/-- The actual Source callback preserves its concrete memory invariant. This
is neither an initial full target representation nor a general callback proof. -/
theorem source_memory (bytes : Roadmap.Bytes) :
    Source.MemOK env before.2.heap.ty before ∧
    Source.MemOK env before.2.heap.ty (after (.success bytes) false) :=
  ⟨before_memOK, after_memOK _ _⟩

#print axioms cell_port
#print axioms source_memory
end Solidity.Backend.FailurePaths.TransientCallback

import Solidity.Backend.FailurePaths.TransientComposition
import Solidity.Backend.FailurePaths.TransientCallback

/-! Nonempty-prefix sharing, reset, mixed-root and refusal controls. These
exercise selected P7 ports, not a full source-to-EVM call compiler. -/
namespace Solidity.Backend.FailurePaths.TransientSharingControls
open Source Transient.Controls

def child : Fr := {frame with sender := owner, static := true}

theorem share (value : Bool) :
    (TransientSharing.source slot frame child value).run prefixedSource =
      (.ok (.bool value), (prefixedSource.1, Transient.sourceWrite slot owner value prefixedSource.2)) ∧
    TransientSharing.execute frame child slot.key (Transient.boolWord value) target =
      (.ok (Transient.write target owner slot.key (Transient.boolWord value)), some (.val (Transient.boolWord value))) := by
  obtain ⟨_, _, _, actual, _, _, _⟩ :=
    TransientSharing.self_share slot frame child rfl rfl value prefixedSource target initial_relation
  exact ⟨actual, TransientSharing.execute_shared frame child rfl rfl slot.key (Transient.boolWord value) target⟩

theorem wrong_owner_observed :
    (TransientSharing.observed {child with this := other} (Transient.loadCode slot.key)
      (Transient.write target owner slot.key (Transient.boolWord true))).2 ≠
    (TransientSharing.observed child (Transient.loadCode slot.key)
      (Transient.write target owner slot.key (Transient.boolWord true))).2 := by
  rw [TransientSharing.load_observed, TransientSharing.load_observed]
  decide +kernel

theorem static_source :
    (TransientSharing.source slot {frame with static := true} child true).run prefixedSource =
      (.error (.revert []), prefixedSource) :=
  TransientSharing.source_static slot _ child rfl true prefixedSource

theorem static_target :
    TransientSharing.execute {frame with static := true} child slot.key (Transient.boolWord true) target =
      (.error .staticWrite target, none) :=
  TransientSharing.execute_static _ child rfl _ _ target

theorem reset_after_execution :
    TransientSharing.writeReset frame slot.key (Transient.boolWord true) target = some (Transient.endTx target) :=
  TransientSharing.write_reset frame rfl _ _ target

theorem mixed_reset :
    TransientComposition.mixedReset frame child slot.key (Transient.boolWord true) target =
      some (Transient.endTx (TransientComposition.reached frame slot.key (Transient.boolWord true) target)) ∧
    (Transient.endTx (TransientComposition.reached frame slot.key (Transient.boolWord true) target)).machine.store (.root 7) = 0x5566 ∧
    (Transient.endTx (TransientComposition.reached frame slot.key (Transient.boolWord true) target)).machine.mem 3 = .val ⟨0xa1ff, by decide⟩ ∧
    (Transient.endTx (TransientComposition.reached frame slot.key (Transient.boolWord true) target)).bank owner slot.key = ⟨0, by decide⟩ ∧
    (Transient.endTx (TransientComposition.reached frame slot.key (Transient.boolWord true) target)).journal = [] :=
  ⟨TransientComposition.mixed_reset_run frame child rfl rfl _ _ target,
    TransientComposition.reset_distinct_roots frame slot.key (Transient.boolWord true) target⟩

theorem callback_initial :
    Transient.Represents Transient.SourceCallback.slot owner Transient.SourceCallback.before target := ⟨false, rfl, rfl⟩

theorem registered_callback (pipeline : Roadmap.Pipeline) :
    (Transient.SourceCallback.run pipeline (.success [0xa1,0,0xfe]) false 10).run Transient.SourceCallback.before =
      (.ok (.success [0xa1,0,0xfe]), Transient.SourceCallback.after (.success [0xa1,0,0xfe]) false) ∧
    TransientSharing.observed (Transient.SourceCallback.child false)
      (Transient.loadCode Transient.SourceCallback.slot.key)
      (Transient.write target owner Transient.SourceCallback.slot.key (Transient.boolWord true)) =
      (.ok (Transient.write target owner Transient.SourceCallback.slot.key (Transient.boolWord true)),
        some (.val (Transient.boolWord true))) := by
  obtain ⟨_, _, _, actual, _, _, loaded, _⟩ :=
    TransientCallback.cell_port pipeline [0xa1,0,0xfe] target callback_initial
  exact ⟨actual, loaded⟩

def sourceValue : Option Bool :=
  match (TransientSharing.source slot frame child true).run prefixedSource |>.1 with
  | .ok (.bool b) => some b
  | .error _ => none

def targetValue : Option Nat :=
  match (TransientSharing.execute frame child slot.key (Transient.boolWord true) target).2 with
  | some (.val w) => some w.val
  | _ => none

#eval (Transient.SourceCallback.run .legacy (.success [0xa1,0,0xfe]) false 10).run Transient.SourceCallback.before |>.1
#eval (Transient.SourceCallback.run .viaIR (.success [0xa1,0,0xfe]) false 10).run Transient.SourceCallback.before |>.1
#eval sourceValue
#eval targetValue
#print axioms share
#print axioms wrong_owner_observed
#print axioms mixed_reset
#print axioms registered_callback
end Solidity.Backend.FailurePaths.TransientSharingControls

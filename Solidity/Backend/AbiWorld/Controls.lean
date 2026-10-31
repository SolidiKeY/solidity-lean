import Solidity.Backend.AbiWorld.ErrorControls
import Solidity.Backend.AbiWorld.ErrorEmission
import Solidity.Backend.AbiWorld.WorldFrames

/-! Inhabited emitter/catch and typed persistent/transient rollback combinations. -/
namespace Solidity.Backend.AbiWorld.Controls
open Semantics Failure

private def machine : Slice.Machine := ⟨[], fun _ => 0xee⟩

/-- A nonzero address, nonempty multiword reason, exact REVERT and reason catch. -/
theorem emitted_catch_combination :
    Slice.checkedRun (emitError 31 (List.replicate 33 0xa5)) machine =
      some ({ machine with memory := (Slice.putBytes machine.memory 31 (encodeError (List.replicate 33 0xa5))) },
        some (.revert (encodeError (List.replicate 33 0xa5)))) ∧
    CatchKind.reason.decode (encodeError (List.replicate 33 0xa5)) =
      some (List.replicate 33 0xa5) := by
  constructor
  · simpa only [List.append_nil] using
      execute_error 31 (List.replicate 33 0xa5) [] machine
        (by unfold Fits; decide +kernel) (by decide)
  · exact catch_error _ (by decide +kernel)

/-- Wrong error class reaches neither the Error reason decoder nor a fake success. -/
theorem panic_not_error : CatchKind.reason.decode (encodePanic 1) = none := by decide +kernel

open Source Roadmap
private def layout : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
private def types : Address → Source.SPath → STy := fun _ _ => .bool
private def owner : Address := ⟨7, by decide⟩
private def path : Source.SPath := ⟨⟨none, "flag"⟩, []⟩
private def initial : ExecState layout types types :=
  ⟨⟨fun _ => Account.empty _⟩, Transient.empty, []⟩
private def operations : List (Source.Op layout types types) :=
  [.account owner (fun a => { a with nonce := a.nonce + 1 }),
   .transient owner (fun s => s.write path (.bool true))]

/-- The witness actually changes both the persistent account and transient cell. -/
theorem live_writes :
    ((initial.run operations).world.accounts owner).nonce = 1 ∧
      ((initial.run operations).transient.cells owner).read path = some (.bool true) := by
  simp only [initial, operations, ExecState.run, ExecState.apply, World.set_get,
    Account.empty, Transient.set, Transient.empty, dite_true, Storage.write_read]
  trivial

/-- Panic words cover zero and the largest code; trailing bytes retain strict rejection. -/
theorem panic_boundary_controls :
    (decodePanic (encodePanic 0)).map (fun w => w.1.toNat) = some 0 ∧
    (decodePanic (encodePanic (2 ^ 256 - 1))).map (fun w => w.1.toNat) = some (2 ^ 256 - 1) ∧
    decodePanic (encodePanic 1 ++ [0]) = none := by decide +kernel

/-- The codec word bound is exact: the largest word reads back and the next wraps. -/
theorem word_boundary_control :
    bytesNat (wordBytes (256 ^ 32 - 1)) = 256 ^ 32 - 1 ∧
      bytesNat (wordBytes (256 ^ 32)) = 0 := by
  constructor
  · exact read_word _ (by decide)
  · decide +kernel

private def otherOperations : List (Source.Op layout types types) :=
  [.account Address.zero (fun a => { a with nonce := a.nonce + 1 }),
   .transient Address.zero (fun s => s.write path (.bool true))]

/-- A different owner really changes while both observations of owner 7 are framed. -/
theorem other_owner_control :
    (((initial.run otherOperations).world.accounts owner,
      (initial.run otherOperations).transient.cells owner) =
      (initial.world.accounts owner, initial.transient.cells owner)) ∧
    ((initial.run otherOperations).world.accounts Address.zero).nonce = 1 := by
  constructor
  · apply unrelated_world_frame
    intro o ho
    simp only [otherOperations, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with he | he <;> subst o <;> decide +kernel
  · simp only [otherOperations, initial, ExecState.run, ExecState.apply, World.set_get, Account.empty]

/-- Rollback restores the whole typed state, including both stores and the journal. -/
theorem both_stores_rollback :
    (initial.enter owner Address.zero ⟨0, by decide⟩ [1, 2] false).rollback
      (initial.run operations) = initial :=
  rollback_run _ _ _ _ _ _ _

/-- Omitting rollback is observably wrong, despite retaining exactly typed states. -/
theorem missing_rollback_negative : initial.run operations ≠ initial := by
  intro he
  have hn : ((initial.run operations).world.accounts owner).nonce = 0 := by
    rw [he]
    rfl
  have hc : ((initial.run operations).world.accounts owner).nonce = 1 := live_writes.1
  omega

/-- Different calldata, identities and static flags do not alter journal restoration. -/
theorem callback_metadata_combination :
    let outer := initial.enter owner Address.zero ⟨0, by decide⟩ [1] false
    let inner := (initial.run operations).enter Address.zero owner ⟨0, by decide⟩ [2, 3] true
    inner.rollback ((initial.run operations).run operations) = initial.run operations ∧
      outer.rollback (inner.rollback ((initial.run operations).run operations)) = initial :=
  heterogeneous_callback_rollback _ _ _ _ _ rfl rfl

/-- Complete prefixes cannot be extended merely by claiming a longer event list. -/
theorem final_prefix_negative :
    ¬ (⟨[1], some true⟩ : Prefix Nat Bool).Le ⟨[1, 2], some true⟩ := by
  intro h
  rcases h.2 with hn | he
  · cases hn
  · have bad : ([1, 2] : List Nat) = [1] := congrArg Prefix.events he
    cases bad

/-- info: 'Solidity.Backend.AbiWorld.Controls.emitted_catch_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emitted_catch_combination
/-- info: 'Solidity.Backend.AbiWorld.Controls.both_stores_rollback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms both_stores_rollback
/-- info: 'Solidity.Backend.AbiWorld.Controls.callback_metadata_combination' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms callback_metadata_combination
end Solidity.Backend.AbiWorld.Controls

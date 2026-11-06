import Solidity.Yul.Composition.PhysicalFrames
import Solidity.Yul.Composition.PhysicalBytes
import Solidity.Yul.Views.OwnedBoolDeclarationControls

/-! Same committed VY2 ownedOrigin source action, now composed with actual
child success/outer rollback, world execution and physical-byte/target copying.
Logical bool truth does not stand in for the original owned byte or padding. -/
namespace Solidity.Yul.Composition.PhysicalControls
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls

/-- The first write is the producer witness, not a replaced store action. -/
def childRequest : PackedSlotRequest := ⟨false,account,43,⟨0xcd000003,by decide⟩⟩
def childPrepared := prepareRepresentedSlot originRegistry originTempRegistry childRequest ownedOriginRun.2
theorem child_prepared : childPrepared.isSome := by decide +kernel
def childPlan := childPrepared.get child_prepared
def childRun := representedSourceStep originRegistry originTempRegistry childRequest ownedOriginRun.2
  packedStepFrame childPlan ownedOriginRun.1.1.2 ownedOriginRun.1.2

def firstCore : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership :=
  ⟨ownedOriginRun.1.1.2.2.ex,ownedOriginRun.1.2⟩
def childCore : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership :=
  ⟨childRun.1.1.2.2.ex,childRun.1.2⟩
def outerEntry : ResidualCompanion originEnv.layout originEnv.lay originEnv.lay complementCarrierOwnership :=
  ⟨ownedOriginState.2.ex,ownedOriginResidual⟩
def revertedChild := companionRollback (companionEnter firstCore account account 0 [] false) childCore
def revertedOuter := companionRollback (companionEnter outerEntry account account 0 [] false)
  (companionCommit (companionEnter firstCore account account 0 [] false) childCore)
def restoredEncoding := boolEncodingRollback boolEncodingInitial.journal.length childRun.2

theorem first_checked_MemOK_and_raw :
    representedFrameWrite? originRegistry originTempRegistry packedStepFrame false 43 ownedOriginRequest.raw
      boolEncodingInitial ownedOriginState ownedOriginResidual = some ownedOriginRun ∧
    Source.MemOK originEnv ownedOriginState.2.heap.ty ownedOriginRun.1.1.2 ∧
    reencodePersistentSlot (representedBanks originRegistry false ownedOriginRun.2) firstCore account 43 =
      some ownedOriginRequest.raw :=
  prepared_persistent_source originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan (Option.some_get owned_origin_prepared).symm rfl ownedOriginState
    ownedOriginResidual _ owned_origin_initial_MemOK rfl rfl originChecked.separated

theorem child_logical_truth :
    (childRun.1.1.2.2.ex.world.accounts account).storage.read (originPath "c") = some (.bool true) := rfl

theorem child_full_raw :
    reencodePersistentSlot (representedBanks originRegistry false childRun.2) childCore account 43 = some childRequest.raw :=
  represented_step_persistent_at_request packedStepFrame childPlan ownedOriginRun.1.1.2 ownedOriginRun.1.2
    rfl rfl originChecked.separated

theorem child_MemOK : Source.MemOK originEnv ownedOriginState.2.heap.ty childRun.1.1.2 :=
  representedSourceStep_MemOK _ packedStepFrame childPlan _ _ first_checked_MemOK_and_raw.2.1

/-- Actual committed child effects remain in all three journals until the
outer rollback; source equality alone would lose raw byte/padding information. -/
theorem all_journals_outer_restore : revertedOuter = outerEntry ∧ restoredEncoding = boolEncodingInitial :=
  physical_child_outer_rollback originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan ownedOriginState ownedOriginResidual childRequest childPlan rfl []

theorem complete_source_outer_restore :
    (childRun.1.1.2.1,{childRun.1.1.2.2 with ex := revertedOuter.source}) = ownedOriginState :=
  physical_child_state_rollback originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan ownedOriginState ownedOriginResidual childRequest childPlan rfl []

/-- No fallback word on absent encoding; the bytes really come from the
coupled source/complement/owned-byte result. -/
def firstRaw := reencodePersistentSlot (representedBanks originRegistry false ownedOriginRun.2) firstCore account 43
def childRaw := reencodePersistentSlot (representedBanks originRegistry false childRun.2) childCore account 43
def payload (raw : Solidity.Roadmap.Word) : Solidity.Roadmap.Bytes := readBytes (mstore (fun _ => 0) 0 raw) 0 32
def firstPayload := firstRaw.map payload
def childPayload := childRaw.map payload

def target : Solidity.Backend.Environment.Slice := ⟨[Solidity.uintOfNat 99],fun _ => 0xee⟩
def callerLog : Solidity.Yul.World.Log := ⟨account,⟨0,by decide⟩,#v[],[0x11]⟩
def copiedFirst := firstPayload.bind fun data =>
  completeAndCopy (physicalExecution ownedOriginState [callerLog] [0xff])
    packedStepFrame.this packedStepFrame.sender packedStepFrame.value [] packedStepFrame.static
    [ownedOriginPlan.packed.sourceOp] [] (.success data) 28 4 31 target

def copiedBytes := copiedFirst.map fun result => readBytes result.2.memory 30 6

theorem actual_physical_payload : firstPayload.bind (fun data => Solidity.Yul.World.returnWindow data 28 4) =
    some [0xab,0,0,2] := by
  unfold firstPayload
  rw [show firstRaw = some ownedOriginRequest.raw from owned_origin_actual_fullword]
  decide +kernel

theorem actual_target_bytes : copiedBytes = some [0xee,0xab,0,0,2,0xee] := by
  unfold copiedBytes copiedFirst firstPayload
  rw [show firstRaw = some ownedOriginRequest.raw from owned_origin_actual_fullword]
  decide +kernel

/-- The target realizes the same physical-byte snapshot copy, with the real
source and destination nonwrapping premises discharged for this witness. -/
theorem physical_target_window :
    Solidity.Backend.Environment.runData (Solidity.Backend.Environment.materialize 31 [0xab,0,0,2]) target =
      some {target with memory := copyBytes target.memory (mstore (fun _ => 0) 0 ownedOriginRequest.raw) 31 28 4} :=
  (physical_window_target (mstore (fun _ => 0) 0 ownedOriginRequest.raw) target 0 32 28 4 31 [0xab,0,0,2]
    (by decide +kernel) (Or.inr (by decide)) (by decide)).1

/-- Both physical journals restore the first raw word on a child revert. -/
theorem child_inner_all_restore : revertedChild = firstCore ∧
    boolEncodingRollback ownedOriginRun.2.journal.length childRun.2 = ownedOriginRun.2 :=
  represented_step_rollback packedStepFrame childPlan ownedOriginRun.1.1.2 ownedOriginRun.1.2 rfl

theorem outer_full_raw :
    reencodePersistentSlot (representedBanks originRegistry false restoredEncoding) revertedOuter account 43 = some 0 := by
  rw [all_journals_outer_restore.1,all_journals_outer_restore.2]
  decide +kernel

/-- The nested VY4 successes use exactly the two actual source plan actions,
with the second full physical payload replacing the stale/first buffer. -/
theorem nested_world_projection :
    Solidity.Yul.World.complete
      (Solidity.Yul.World.complete (physicalExecution ownedOriginState [callerLog] [0xff])
        packedStepFrame.this packedStepFrame.sender packedStepFrame.value [] packedStepFrame.static
        [ownedOriginPlan.packed.sourceOp] [] (.success (payload ownedOriginRequest.raw)))
      packedStepFrame.this packedStepFrame.sender packedStepFrame.value [] packedStepFrame.static
      [childPlan.packed.sourceOp] [] (.success (payload childRequest.raw)) =
      ⟨childRun.1.1.2.2.ex,[callerLog],payload childRequest.raw⟩ :=
  physical_two_success_projection originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan ownedOriginState ownedOriginResidual childRequest childPlan rfl
    [callerLog] [0xff] [] (payload ownedOriginRequest.raw) (payload childRequest.raw)


/-- Logical true without the matching owned byte is observably the wrong word. -/
example : reencodePersistentSlot (representedBanks originRegistry false boolEncodingInitial) firstCore account 43 =
    some (⟨0xab000001,by decide⟩ : Solidity.Roadmap.Word) := by decide +kernel
example : reencodePersistentSlot (representedBanks originRegistry false ownedOriginRun.2)
    ⟨ownedOriginRun.1.1.2.2.ex,ownedOriginResidual⟩ account 43 = some (2 : Solidity.Roadmap.Word) := by decide +kernel

/-- Child rollback with a stale child-owned byte or stale child padding
keeps logical truth but fails exact raw-word restoration. -/
example : reencodePersistentSlot (representedBanks originRegistry false childRun.2) revertedChild account 43 =
    some (⟨0xab000003,by decide⟩ : Solidity.Roadmap.Word) := by decide +kernel
example : reencodePersistentSlot (representedBanks originRegistry false ownedOriginRun.2)
    ⟨revertedChild.source,childRun.1.2⟩ account 43 = some (⟨0xcd000002,by decide⟩ : Solidity.Roadmap.Word) := by decide +kernel

def wrongOwner : Source.Fr := {packedStepFrame with this := ⟨2,by decide⟩}
def wrongOwnerRun := representedFrameWrite? originRegistry originTempRegistry wrongOwner false 43 ownedOriginRequest.raw
  boolEncodingInitial ownedOriginState ownedOriginResidual
def wrongSlotRun := representedFrameWrite? originRegistry originTempRegistry packedStepFrame false 42 ownedOriginRequest.raw
  boolEncodingInitial ownedOriginState ownedOriginResidual
example : ownedOriginRequest.address ≠ wrongOwner.this := by decide
example : (wrongOwnerRun.map fun out =>
    (out.1.1.2.2.ex.world.accounts account).storage.read (originPath "c")) = some (some (.bool false)) := rfl
example : (wrongSlotRun.map fun out =>
    (out.1.1.2.2.ex.world.accounts account).storage.read (originPath "c")) = some (some (.bool false)) := rfl
example : representedSourceStep originRegistry originTempRegistry childRequest ownedOriginRun.2
    {packedStepFrame with static := true} childPlan ownedOriginRun.1.1.2 ownedOriginRun.1.2 =
    (((.error (.revert []),ownedOriginRun.1.1.2),ownedOriginRun.1.2),ownedOriginRun.2) :=
  representedSourceStep_static _ _ _ _ rfl

#print axioms first_checked_MemOK_and_raw
#print axioms child_logical_truth
#print axioms child_full_raw
#print axioms child_MemOK
#print axioms all_journals_outer_restore
#print axioms complete_source_outer_restore
#print axioms actual_physical_payload
#print axioms actual_target_bytes
#print axioms physical_target_window
#print axioms child_inner_all_restore
#print axioms outer_full_raw
#print axioms nested_world_projection
end Solidity.Yul.Composition.PhysicalControls

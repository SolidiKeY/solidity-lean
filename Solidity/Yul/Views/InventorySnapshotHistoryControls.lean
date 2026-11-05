import Solidity.Yul.Views.InventorySnapshotHistory
import Solidity.Yul.Views.NominalInventoryDynamicControls
import Solidity.Yul.Views.NominalInventorySequentialControls

/-! Changing nominal snapshots through actual Source writes: both retained aliases,
original-capacity regrowth, nonzero tails and unsupported late preparation.
Synthetic byte seeds are separate from compiler/EVM observations. -/
namespace Solidity.Yul.Views.NominalInventory.SnapshotControls
open Solidity.Yul.Views
open Solidity.Yul.Views.NominalMemory.RetainedControls

def cursor : SnapshotCursor placement state := ⟨placement,.initial,[DynamicControls.originalEntry]⟩
def changedRaw : ByteView := mstore (mstore regrownRaw 160 ⟨2^256-32768,by decide⟩) 192 0
def invalidRaw : ByteView := mstore changedRaw 160 65535

def cycle : SnapshotProgress (Γ:=[arrayTy,arrayTy]) placement := runSnapshots placement state cursor [shrunkRaw,regrownRaw,changedRaw]
def stopInputs : List ByteView := [shrunkRaw,regrownRaw,changedRaw,invalidRaw,raw]
def stopped : SnapshotProgress (Γ:=[arrayTy,arrayTy]) placement := runSnapshots placement state cursor stopInputs
def firstStop : SnapshotProgress (Γ:=[arrayTy,arrayTy]) placement := runSnapshots placement state cursor [invalidRaw,shrunkRaw,regrownRaw]

/-- A real initial Source write, not a manually supplied output-view equation. -/
theorem actual_shrink : ∃ next,snapshotStep placement state cursor shrunkRaw=some next ∧
    next.1=shrunkState := by
  have actual := (snapshotStep_source placement state cursor shrunkRaw).trans DynamicControls.inventory_shrink
  obtain ⟨next,step,output⟩ := Option.map_eq_some_iff.mp actual
  exact ⟨next,step,congrArg Prod.snd output⟩

/-- Every initial typing survives ANY finite input sequence from this inhabited
state. Keeping the list abstract avoids normalizing concrete byte functions. -/
theorem snapshots_MemOK (ms : List ByteView) (H : Source.HeapTy)
    (ok : Source.MemOK env H state) :
    Source.MemOK env H (runSnapshots placement state cursor ms).current.1 :=
  runSnapshots_MemOK placement state cursor ms H ok

theorem actual_snapshots_MemOK (ms : List ByteView) :
    Source.MemOK env heap.ty (runSnapshots placement state cursor ms).current.1 :=
  snapshots_MemOK ms heap.ty actual_MemOK

/-- Complete nonheap state, not merely alias projections, is preserved. -/
theorem snapshots_administration (ms : List ByteView) :
    (runSnapshots placement state cursor ms).current.1=
      withSourceHeap state (runSnapshots placement state cursor ms).current.1.2.heap :=
  (runSnapshots_preserves placement state cursor ms).1

/-- info: (0, 2, 3) -/
#guard_msgs in #eval (cycle.pending.length,stopped.pending.length,firstStop.pending.length)
/-- info: true -/
#guard_msgs in #eval decide
  (aliasRead stopped.current.1 .here 0=some ⟨2^256-32768,by decide⟩ ∧
   aliasRead stopped.current.1 (.there .here) 0=some ⟨2^256-32768,by decide⟩ ∧
   aliasRead stopped.current.1 (.there .here) 1=some 0)
/-- info: true -/
#guard_msgs in #eval decide
  (aliasRead firstStop.current.1 .here 0=some ⟨2^256-1,by decide⟩ ∧
   stopped.current.1.2.heap.next=1 ∧ cycle.current.2.placement.free.val=256 ∧
   stopped.current.2.placement.shape 0=.array true 2 ∧
   changedRaw 240=165 ∧ mload shrunkRaw 160=⟨2^256-1,by decide⟩)

/-- info: true -/
#guard_msgs in #eval (snapshotStep placement stopped.current.1 stopped.current.2 invalidRaw).isNone

/- Distinct mixed roots are retained across changing snapshots, not just one array. -/
def mixedCursor : SnapshotCursor UnchangedControls.placement UnchangedControls.state :=
  ⟨UnchangedControls.placement,.initial,UnchangedControls.entries⟩
def mixedBad : ByteView := mstore SequentialControls.beyondRaw 128 0
def mixed := runSnapshots UnchangedControls.placement UnchangedControls.state mixedCursor
  [SequentialControls.mixedRaw,SequentialControls.lateRaw,mixedBad,SequentialControls.mixedRaw]
/-- info: true -/
#guard_msgs in #eval decide (mixed.pending.length=2 ∧
  NominalMemory.Controls.aliasRead mixed.current.1 .here 0=some ⟨2^256-32768,by decide⟩ ∧
  (snapshotStep UnchangedControls.placement mixed.current.1 mixed.current.2 mixedBad).isNone=true)

/- If the failed mixed snapshot were partly executed, the nominal alias would
read zero; if its suffix ran, the alias would read -1. Both must remain -32768. -/
/-- info: true -/
#guard_msgs in #eval match mixed.current.2.entries with
  | e::_ => (update UnchangedControls.placement mixed.current.2.placement
      mixed.current.2.entries e mixedBad).isSome
  | [] => false

def zero := runSnapshots placement state cursor [shrunkRaw]
/-- info: true -/
#guard_msgs in #eval (snapshotStep zero.current.2.placement zero.current.1
  ⟨zero.current.2.placement,.initial,zero.current.2.entries⟩ regrownRaw).isNone

/-- info: true -/
#guard_msgs in #eval decide (readBytes (encodeMixedHeap stopped.current.2.placement
  stopped.current.2.entries changedRaw) 0 256=readBytes changedRaw 0 256)

/-- info: (none, 0) -/
#guard_msgs in #eval let reversed := runSnapshots placement state cursor [changedRaw,shrunkRaw]
  (aliasRead reversed.current.1 .here 0,reversed.pending.length)

def repeatedCursor : SnapshotCursor UnchangedControls.placement UnchangedControls.state :=
  ⟨UnchangedControls.placement,.initial,UnchangedControls.repeatedEntries⟩
def repeated := runSnapshots UnchangedControls.placement UnchangedControls.state repeatedCursor
  [SequentialControls.mixedRaw,SequentialControls.lateRaw]
/-- info: (0, 2) -/
#guard_msgs in #eval (repeated.pending.length,repeated.current.1.2.heap.next)

end Solidity.Yul.Views.NominalInventory.SnapshotControls

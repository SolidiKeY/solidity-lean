import Solidity.Backend.StorageOps.TargetArrayCopyTail

/-! Complete ordered symbolic-word observations for the actual two-loop copy.
These raw target controls do not assert Source typing or a physical hash layout. -/
namespace Solidity.Backend.StorageOps.TargetArrayCopyControls
open Evm
private def src : Evm.Slot := .root 0
private def dst : Evm.Slot := .root 1
private def store (sourceLength oldLength : Nat) : Evm.WordStore := .ofFn fun slot =>
  if slot = src then sourceLength else if slot = dst then oldLength else
  if slot = .data src 0 then 7 else if slot = .data src 1 then 9 else
  if slot = .data src 2 then 11 else if slot = .data src 3 then 13 else
  if slot = .data dst 0 then 21 else if slot = .data dst 1 then 22 else
  if slot = .data dst 2 then 23 else if slot = .data dst 3 then 24 else
  if slot = .data dst 4 then 25 else if slot = .root 9 then 99 else 0
private def tail : List Evm.Word := [.val ⟨17,by decide⟩,.slot (.root 9)]
private def machine (sourceLength oldLength : Nat) : Evm.Machine :=
  { stack := tail, store := store sourceLength oldLength, mem := fun _ => .val ⟨31,by decide⟩,
    bal := fun _ => 41, bal₀ := fun _ => 43, self := ⟨47,by decide⟩,
    caller := ⟨53,by decide⟩, callvalue := ⟨59,by decide⟩, timestamp := ⟨61,by decide⟩,
    accepts := fun _ _ => false }
private def slots : List Evm.Slot := [src,dst,.data src 0,.data src 1,.data src 2,.data src 3,
  .data dst 0,.data dst 1,.data dst 2,.data dst 3,.data dst 4,.root 9]
private def view (m : Evm.Machine) : List Nat := slots.map (fun slot => m.store slot)
private def context (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.bal ⟨0,by decide⟩,m.bal₀ ⟨0,by decide⟩,m.self,m.caller,m.callvalue,m.timestamp,m.accepts ⟨0,by decide⟩ ⟨0,by decide⟩)
private def copied (sourceLength oldLength : Nat) :=
  TargetArrayCopyTail.afterCopy (machine sourceLength oldLength) tail src dst

/-- Shrink clears only former live tail, preserving the older shadow at 3. -/
theorem shrink :
    Evm.run TargetArrayCopy.code { machine 2 3 with stack := .slot src :: .slot dst :: tail } = .ok (copied 2 3) 0 ∧
    (view (machine 2 3),view (copied 2 3),context (copied 2 3)) =
      ([2,3,7,9,11,13,21,22,23,24,25,99],[2,2,7,9,11,13,7,9,0,24,25,99],context (machine 2 3)) := by
  exact ⟨TargetArrayCopyTail.run_current _ _ _ _,rfl⟩

/-- Growth and empty inputs discriminate both actual header-controlled loops. -/
theorem grow_empty :
    Evm.run TargetArrayCopy.code { machine 3 1 with stack := .slot src :: .slot dst :: tail } = .ok (copied 3 1) 0 ∧
    Evm.run TargetArrayCopy.code { machine 0 3 with stack := .slot src :: .slot dst :: tail } = .ok (copied 0 3) 0 ∧
    Evm.run TargetArrayCopy.code { machine 0 0 with stack := .slot src :: .slot dst :: tail } = .ok (copied 0 0) 0 ∧
    (view (copied 3 1),view (copied 0 3),view (copied 0 0),context (copied 3 1),context (copied 0 3),context (copied 0 0)) =
      ([3,3,7,9,11,13,7,9,11,24,25,99],[0,0,7,9,11,13,0,0,0,24,25,99],
       [0,0,7,9,11,13,21,22,23,24,25,99],context (machine 3 1),context (machine 0 3),context (machine 0 0)) := by
  exact ⟨TargetArrayCopyTail.run_current _ _ _ _,TargetArrayCopyTail.run_current _ _ _ _,
    TargetArrayCopyTail.run_current _ _ _ _,rfl⟩

private def selfResult := TargetArrayCopyTail.afterCopy (machine 2 3) tail src src
/-- Self-copy consumes both operands and preserves all observed words/context. -/
theorem self_copy :
    Evm.run TargetArrayCopy.code { machine 2 3 with stack := .slot src :: .slot src :: tail } = .ok selfResult 0 ∧
    (view selfResult,context selfResult) = (view (machine 2 3),context (machine 2 3)) := by
  exact ⟨TargetArrayCopyTail.run_current _ _ _ _,rfl⟩

private def overlapSource : Evm.Slot := .data dst 0
private def overlapStore : Evm.WordStore := .ofFn fun slot =>
  if slot = overlapSource then 2 else if slot = dst then 3 else
  if slot = .data overlapSource 0 then 7 else if slot = .data overlapSource 1 then 9 else
  if slot = .data dst 1 then 22 else if slot = .data dst 2 then 23 else
  if slot = .data dst 3 then 24 else if slot = .root 9 then 99 else 0
private def overlapMachine : Evm.Machine := { machine 2 3 with store := overlapStore }
private def overlapSlots : List Evm.Slot := [dst,overlapSource,.data overlapSource 0,
  .data overlapSource 1,.data dst 1,.data dst 2,.data dst 3,.root 9]
private def overlapView (m : Evm.Machine) := overlapSlots.map (fun slot => m.store slot)
private def overlapResult := TargetArrayCopyTail.afterCopy overlapMachine tail overlapSource dst
private def overlapPrefix (n : Nat) : Evm.Machine :=
  { overlapMachine with store := TargetArrayCopy.copyPrefix overlapStore overlapSource dst n }

/-- The first copy changes the CURRENT source header from 2 to 7. Capturing
that header before the loop avoids the wrong incremental-source limit. These
are raw symbolic aliases, with no ordinary Source array typing claimed. -/
theorem overlapping_header :
    Evm.run TargetArrayCopy.code { overlapMachine with stack := .slot overlapSource :: .slot dst :: tail } = .ok overlapResult 0 ∧
    (overlapView overlapMachine,overlapView (overlapPrefix 1),overlapView (overlapPrefix 2),overlapView overlapResult,context overlapResult) =
      ([3,2,7,9,22,23,24,99],[3,7,7,9,22,23,24,99],[3,7,7,9,9,23,24,99],
       [2,7,7,9,9,0,24,99],context overlapMachine) := by
  exact ⟨TargetArrayCopyTail.run_current _ _ _ _,rfl⟩

private def wrongCondition : List Evm.Instr := [.dup 3,.sload,.dup 2,.lt]
private def atEnd : Evm.Machine :=
  TargetArrayCopy.iterationMachine overlapMachine tail overlapSource dst ⟨3,by decide⟩ ⟨2,by decide⟩ ⟨2,by decide⟩
private def flag (out : Evm.Out) : Option Nat :=
  match out with
  | .ok m _ => match m.stack with | .val v :: _ => some v.val | _ => none
  | _ => none

/-- ACTUAL incorrect current-header condition keeps copying after index 2. -/
theorem incremental_source_negative :
    (flag (Evm.run TargetArrayCopy.condition atEnd),flag (Evm.run wrongCondition atEnd),overlapView atEnd) =
      (some 0,some 1,[3,7,7,9,9,23,24,99]) := by
  rfl

private def wrongClear := TargetArrayClear.afterClear (overlapPrefix 2) tail dst
/-- Clearing the whole old live prefix after copying destroys copied payloads. -/
theorem whole_prefix_clear_negative :
    Evm.run TargetArrayClear.code { overlapPrefix 2 with stack := .slot dst :: tail } = .ok wrongClear 0 ∧
    (overlapView wrongClear,overlapView overlapResult,context wrongClear) =
      ([0,0,7,9,0,0,24,99],[2,7,7,9,9,0,24,99],context overlapMachine) := by
  exact ⟨TargetArrayClear.run_current _ _ _,rfl⟩

/-- Kernel result is inhabited at every runtime word length, with no lmax or
fixed traversal cap. This family does not assert representation coverage. -/
theorem all_lengths (sourceLength oldLength : Fin Evm.W) :
    Evm.run TargetArrayCopy.code { machine sourceLength.val oldLength.val with stack := .slot src :: .slot dst :: tail } =
      .ok (copied sourceLength.val oldLength.val) 0 :=
  TargetArrayCopyTail.run_current _ _ _ _

/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyControls.shrink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms shrink
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyControls.grow_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms grow_empty
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyControls.self_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_copy
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyControls.overlapping_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlapping_header
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyControls.incremental_source_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms incremental_source_negative
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyControls.whole_prefix_clear_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms whole_prefix_clear_negative
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyControls.all_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms all_lengths

end Solidity.Backend.StorageOps.TargetArrayCopyControls

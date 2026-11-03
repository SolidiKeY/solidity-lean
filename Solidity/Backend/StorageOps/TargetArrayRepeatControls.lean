import Solidity.Backend.StorageOps.TargetArrayRepeat

/-! Actual structured target executions, entire context, complete ordered store
observations and non-refusing unsafe controls. No Source typing, physical hash
interpretation, bytecode/gas or reachable-world rollback is asserted. -/
namespace Solidity.Backend.StorageOps.TargetArrayRepeatControls
open Evm TargetArrayCopyTail TargetArrayRepeat
private def src : Evm.Slot := .root 0
private def dst : Evm.Slot := .root 1
private def tail : List Evm.Word := [.val ⟨17,by decide⟩,.slot (.root 9)]
private def store (live old : Nat) : Evm.WordStore := .ofFn fun slot =>
 if slot=src then live else if slot=dst then old else
 if slot=.data src 0 then 7 else if slot=.data src 1 then 17 else if slot=.data src 2 then 23 else
 if slot=.data src 3 then 53 else if slot=.data src 4 then 71 else if slot=.data src 5 then 113 else if slot=.data src 6 then 127 else
 if slot=.data dst 0 then 31 else if slot=.data dst 1 then 37 else if slot=.data dst 2 then 41 else if slot=.data dst 3 then 43 else
 if slot=.data dst 4 then 99 else if slot=.data dst 5 then 151 else if slot=.data dst 6 then 157 else
 if slot=.root 9 then 211 else if slot=.root 8 then 223 else 0
private def machine (live old : Nat) : Evm.Machine :=
 {stack:=tail,store:=store live old,mem:=fun _ => .val ⟨31,by decide⟩,
  bal:=fun _ => 41,bal₀:=fun _ => 43,self:=⟨47,by decide⟩,caller:=⟨53,by decide⟩,
  callvalue:=⟨59,by decide⟩,timestamp:=⟨61,by decide⟩,accepts:=fun _ _ => false}
private def slots : List Evm.Slot := [src,dst,.data src 0,.data src 1,.data src 2,.data src 3,.data src 4,.data src 5,.data src 6,
 .data dst 0,.data dst 1,.data dst 2,.data dst 3,.data dst 4,.data dst 5,.data dst 6,.root 9,.root 8]
private def view (m : Evm.Machine) := slots.map (fun slot => m.store slot)
private def once (live old : Nat) := afterCopy (machine live old) tail src dst
private def twice (live old : Nat) := afterCopy (once live old) tail src dst
private def Context (old result : Evm.Machine) : Prop := result.stack=old.stack ∧ result.mem=old.mem ∧
 result.bal=old.bal ∧ result.bal₀=old.bal₀ ∧ result.self=old.self ∧ result.caller=old.caller ∧
 result.callvalue=old.callvalue ∧ result.timestamp=old.timestamp ∧ result.accepts=old.accepts
private theorem executed (m : Evm.Machine) (s d : Evm.Slot) :
 Evm.run (code s d) m=.ok (afterCopy m m.stack s d) 0 := by
 have pushes : Evm.run [.push (.slot d),.push (.slot s)] m=.ok {m with stack:=.slot s :: .slot d :: m.stack} 0 := by rfl
 unfold code
 rw [Evm.run_append_ok pushes]
 exact run_current _ _ _ _
private theorem safeShrink : src=dst ∨ ∀ w∈writes (machine 2 4) src dst,∀ r∈reads (machine 2 4) src,w≠r := Or.inr (by decide)

/-- Actual TWO complete programs; the second re-reads current headers. -/
theorem shrinking_runs : Evm.run (code src dst++code src dst) (machine 2 4)=.ok (once 2 4) 0 ∧
 twice 2 4=once 2 4 := TargetArrayRepeat.complete (machine 2 4) src dst safeShrink
/-- COMPLETE18word OLD/once/twice fixture observations. -/
theorem shrinking_ordered : (view (machine 2 4),view (once 2 4),view (twice 2 4))=
 ([2,4,7,17,23,53,71,113,127,31,37,41,43,99,151,157,211,223],
  [2,2,7,17,23,53,71,113,127,7,17,0,0,99,151,157,211,223],
  [2,2,7,17,23,53,71,113,127,7,17,0,0,99,151,157,211,223]) := by rfl
/-- ALL nonstore context functions/fields, not just sampled cells. -/
theorem full_context : Context (machine 2 4) (once 2 4) ∧ Context (machine 2 4) (twice 2 4) := by repeat' constructor
/-- Independently varying runtime lengths exercise both loops and zero turns. -/
theorem growth_empty_runs :
 Evm.run (code src dst++code src dst) (machine 4 1)=.ok (once 4 1) 0 ∧
 Evm.run (code src dst++code src dst) (machine 0 3)=.ok (once 0 3) 0 ∧
 Evm.run (code src dst++code src dst) (machine 0 0)=.ok (once 0 0) 0 := by
 exact ⟨(TargetArrayRepeat.complete (machine 4 1) src dst (Or.inr (by decide))).1,
  (TargetArrayRepeat.complete (machine 0 3) src dst (Or.inr (by decide))).1,
  (TargetArrayRepeat.complete (machine 0 0) src dst (Or.inr (by decide))).1⟩
/-- COMPLETE growth/empty/zero-turn OLD/once/twice observations. -/
theorem growth_empty_ordered :
 (view (machine 4 1),view (once 4 1),view (twice 4 1),
  view (machine 0 3),view (once 0 3),view (twice 0 3),
  view (machine 0 0),view (once 0 0),view (twice 0 0))=
 ([4,1,7,17,23,53,71,113,127,31,37,41,43,99,151,157,211,223],
  [4,4,7,17,23,53,71,113,127,7,17,23,53,99,151,157,211,223],
  [4,4,7,17,23,53,71,113,127,7,17,23,53,99,151,157,211,223],
  [0,3,7,17,23,53,71,113,127,31,37,41,43,99,151,157,211,223],
  [0,0,7,17,23,53,71,113,127,0,0,0,43,99,151,157,211,223],
  [0,0,7,17,23,53,71,113,127,0,0,0,43,99,151,157,211,223],
  [0,0,7,17,23,53,71,113,127,31,37,41,43,99,151,157,211,223],
  [0,0,7,17,23,53,71,113,127,31,37,41,43,99,151,157,211,223],
  [0,0,7,17,23,53,71,113,127,31,37,41,43,99,151,157,211,223]) := by rfl
private def selfOnce := afterCopy (machine 2 4) tail src src
private def selfTwice := afterCopy selfOnce tail src src
/-- Self aliases are supported explicitly, without separation. -/
theorem self_runs : Evm.run (code src src++code src src) (machine 2 4)=.ok selfOnce 0 ∧
 selfTwice=selfOnce ∧ view selfOnce=view (machine 2 4) ∧ view selfTwice=view (machine 2 4) ∧ Context (machine 2 4) selfTwice := by
 exact ⟨(TargetArrayRepeat.complete (machine 2 4) src src (Or.inl rfl)).1,
  (TargetArrayRepeat.complete (machine 2 4) src src (Or.inl rfl)).2,rfl,rfl,by repeat' constructor⟩

private def nested : Evm.Slot := .data dst 0
private def badStore : Evm.WordStore := .ofFn fun slot => if slot=dst then 3 else if slot=nested then 2 else
 if slot=.data nested 0 then 7 else if slot=.data nested 1 then 17 else
 if slot=.data dst 1 then 31 else if slot=.data dst 2 then 99 else if slot=.data dst 3 then 43 else
 if slot=.data dst 4 then 151 else if slot=.data dst 5 then 157 else if slot=.data dst 6 then 163 else if slot=.root 9 then 211 else 0
private def bad := {machine 2 4 with store:=badStore}
private def badOnce := afterCopy bad tail nested dst
private def badTwice := afterCopy badOnce tail nested dst
private def badSlots : List Evm.Slot := [dst,nested,.data nested 0,.data nested 1,.data nested 2,.data nested 3,.data nested 4,.data nested 5,.data nested 6,
 .data dst 1,.data dst 2,.data dst 3,.data dst 4,.data dst 5,.data dst 6,.root 9]
private def badView (m : Evm.Machine) := badSlots.map (fun slot => m.store slot)
/-- Unsafe aliasing still executes BOTH actual programs successfully. No source
profile exclusion or refusal is introduced to force the repetition theorem. -/
theorem unsafe_runs : Evm.run (code nested dst) bad=.ok badOnce 0 ∧
 Evm.run (code nested dst++code nested dst) bad=.ok badTwice 0 := by
 refine ⟨executed bad nested dst,?_⟩
 rw [Evm.run_append_ok (executed bad nested dst)]
 exact executed badOnce nested dst
/-- COMPLETE16word unsafe OLD/once/twice observations and entire context. -/
theorem unsafe_ordered : (badView bad,badView badOnce,badView badTwice)=
 ([3,2,7,17,0,0,0,0,0,31,99,43,151,157,163,211],
  [2,7,7,17,0,0,0,0,0,17,0,43,151,157,163,211],
  [7,7,7,17,0,0,0,0,0,17,0,0,0,0,0,211]) ∧ Context bad badTwice := by
 exact ⟨rfl,by repeat' constructor⟩
/-- The first copy clobbers the source header2->7; actual results differ. -/
theorem unsafe_rejected :
 ¬ (nested=dst ∨ ∀ w∈writes bad nested dst,∀ r∈reads bad nested,w≠r) ∧ badTwice≠badOnce := by
 refine ⟨by decide,?_⟩
 intro same
 have headers : 7=2 := congrArg (fun m : Evm.Machine => m.store dst) same
 exact (by decide : 7≠2) headers
/-- Reversed operand pushes execute the opposite copy, changing the SOURCE. -/
theorem wrong_push_order : Evm.run (code dst src) (machine 2 4)=
 .ok (afterCopy (machine 2 4) tail dst src) 0 ∧
 (view (machine 2 4),view (once 2 4),view (afterCopy (machine 2 4) tail dst src))=
 ([2,4,7,17,23,53,71,113,127,31,37,41,43,99,151,157,211,223],
  [2,2,7,17,23,53,71,113,127,7,17,0,0,99,151,157,211,223],
  [4,4,31,37,41,43,71,113,127,31,37,41,43,99,151,157,211,223]) := by
 exact ⟨executed _ _ _,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.shrinking_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shrinking_runs
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.shrinking_ordered' does not depend on any axioms -/
#guard_msgs in #print axioms shrinking_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.full_context' does not depend on any axioms -/
#guard_msgs in #print axioms full_context
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.growth_empty_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms growth_empty_runs
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.growth_empty_ordered' does not depend on any axioms -/
#guard_msgs in #print axioms growth_empty_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.self_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_runs
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.unsafe_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms unsafe_runs
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.unsafe_ordered' does not depend on any axioms -/
#guard_msgs in #print axioms unsafe_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.unsafe_rejected' does not depend on any axioms -/
#guard_msgs in #print axioms unsafe_rejected
/-- info: 'Solidity.Backend.StorageOps.TargetArrayRepeatControls.wrong_push_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_push_order
end Solidity.Backend.StorageOps.TargetArrayRepeatControls

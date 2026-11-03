import Solidity.Backend.StorageOps.TargetNestedArrayRuntime

/-! Complete ordered ACTUAL two-level target observations. These do not claim
ordinary Source/independent graph/PUBLIC numeric correspondence. -/
namespace Solidity.Backend.StorageOps.TargetNestedArrayControls
private def word (n : Fin 128) : Fin Evm.W := ⟨n.val,by
  have bound := n.isLt
  have wide : 128 < Evm.W := by decide
  omega⟩
private def src : Evm.Slot := .root 0
private def dst : Evm.Slot := .root 1
private def tail : List Evm.Word := [.val (word 97),.slot (.root 9)]
private def machine (sourceOuter oldOuter inner : Fin 3) : Evm.Machine :=
  { stack := tail,store := Evm.WordStore.ofFn (fun slot =>
      if slot = src then sourceOuter.val else if slot = dst then oldOuter.val else
      if slot = .data src 0 then inner.val else if slot = .data (.data src 0) 0 then 7 else
      if slot = .data (.data src 0) 1 then 11 else if slot = .data (.data src 0) 2 then 13 else
      if slot = .data src 1 then 1 else if slot = .data (.data src 1) 0 then 17 else if slot = .data (.data src 1) 1 then 19 else
      if slot = .data src 2 then 1 else if slot = .data (.data src 2) 0 then 71 else
      if slot = .data dst 0 then 3 else if slot = .data (.data dst 0) 0 then 23 else if slot = .data (.data dst 0) 1 then 29 else
      if slot = .data (.data dst 0) 2 then 31 else if slot = .data (.data dst 0) 3 then 37 else
      if slot = .data dst 1 then 2 else if slot = .data (.data dst 1) 0 then 41 else if slot = .data (.data dst 1) 1 then 43 else
      if slot = .data (.data dst 1) 2 then 47 else if slot = .data dst 2 then 2 else
      if slot = .data (.data dst 2) 0 then 53 else if slot = .data (.data dst 2) 1 then 59 else if slot = .data (.data dst 2) 2 then 61 else
      if slot = .root 7 then 73 else 0),mem := fun _ => .val (word 79),bal := fun _ => 13,bal₀ := fun _ => 17,
    self := ⟨5,by decide⟩,caller := ⟨7,by decide⟩,callvalue := ⟨11,by decide⟩,timestamp := ⟨19,by decide⟩,accepts := fun _ _ => false }
private def copied (m : Evm.Machine) := TargetNestedArrayCopyLoop.prefixMachine m src dst (m.store src)
private def copyMachine (m : Evm.Machine) := TargetNestedArrayCopyLoop.iterationMachine m tail src dst (m.store.cells dst) (m.store.cells src) (m.store.cells src)
private def clearMachine (m : Evm.Machine) := TargetNestedArrayClearLoop.iterationMachine (copied m) tail dst (m.store src)
  (m.store.cells src) (m.store.cells dst) (TargetNestedArrayClearLoop.finalIndex (m.store.cells src) (m.store.cells dst))
private def result (m : Evm.Machine) := TargetNestedArrayRuntime.afterCopy m tail src dst
private def view (m : Evm.Machine) : List Nat :=
  [m.store src,m.store dst,m.store (.data src 0),m.store (.data (.data src 0) 0),m.store (.data (.data src 0) 1),m.store (.data (.data src 0) 2),
   m.store (.data src 1),m.store (.data (.data src 1) 0),m.store (.data (.data src 1) 1),m.store (.data src 2),m.store (.data (.data src 2) 0),
   m.store (.data dst 0),m.store (.data (.data dst 0) 0),m.store (.data (.data dst 0) 1),m.store (.data (.data dst 0) 2),m.store (.data (.data dst 0) 3),
   m.store (.data dst 1),m.store (.data (.data dst 1) 0),m.store (.data (.data dst 1) 1),m.store (.data (.data dst 1) 2),
   m.store (.data dst 2),m.store (.data (.data dst 2) 0),m.store (.data (.data dst 2) 1),m.store (.data (.data dst 2) 2),m.store (.root 7)]
private def context (m : Evm.Machine) := (m.stack,m.mem,m.bal,m.bal₀,m.self,m.accepts,m.caller,m.callvalue,m.timestamp)
private def copyStack (m : Evm.Machine) : List Evm.Word :=
  .val (m.store.cells src) :: .val (m.store.cells src) :: .slot src :: .slot dst :: .val (m.store.cells dst) :: tail
private def clearStack (m : Evm.Machine) : List Evm.Word :=
  .val (TargetNestedArrayClearLoop.finalIndex (m.store.cells src) (m.store.cells dst)) :: .val (m.store.cells dst) :: .slot dst :: .val (m.store.cells src) :: tail
private def observation (m : Evm.Machine) :=
  (view m,view (copyMachine m),view (clearMachine m),view (result m),context m,context (copyMachine m),context (clearMachine m),context (result m))

/-- The SAME actual code consumes varying runtime outer/inner header words.
These finite test parameters are inhabited witnesses, not source restrictions. -/
theorem runtime_header_family (sourceOuter oldOuter inner : Fin 3) :
    Evm.run TargetNestedArrayCopy.code { machine sourceOuter oldOuter inner with stack := .slot src :: .slot dst :: tail } =
      .ok (result (machine sourceOuter oldOuter inner)) 0 := TargetNestedArrayRuntime.run_current _ _ _ _

/-- COMPLETE before/copy/clear/final storage and full actual phase-stack/context observations. -/
theorem shrinking_ordered : observation (machine 1 2 2) =
      ([1,2,2,7,11,13,1,17,19,1,71,3,23,29,31,37,2,41,43,47,2,53,59,61,73],
       [1,2,2,7,11,13,1,17,19,1,71,2,7,11,0,37,2,41,43,47,2,53,59,61,73],
       [1,2,2,7,11,13,1,17,19,1,71,2,7,11,0,37,0,0,0,47,2,53,59,61,73],
       [1,1,2,7,11,13,1,17,19,1,71,2,7,11,0,37,0,0,0,47,2,53,59,61,73],
       context (machine 1 2 2),context { machine 1 2 2 with stack := copyStack (machine 1 2 2) },
       context { machine 1 2 2 with stack := clearStack (machine 1 2 2) },context (machine 1 2 2)) := by rfl

/-- COMPLETE before/copy/clear/final storage and full actual phase-stack/context observations. -/
theorem growing_ordered : observation (machine 2 1 1) =
      ([2,1,1,7,11,13,1,17,19,1,71,3,23,29,31,37,2,41,43,47,2,53,59,61,73],
       [2,1,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],
       [2,1,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],
       [2,2,1,7,11,13,1,17,19,1,71,1,7,0,0,37,1,17,0,47,2,53,59,61,73],
       context (machine 2 1 1),context { machine 2 1 1 with stack := copyStack (machine 2 1 1) },
       context { machine 2 1 1 with stack := clearStack (machine 2 1 1) },context (machine 2 1 1)) := by rfl

/-- COMPLETE before/copy/clear/final storage and full actual phase-stack/context observations. -/
theorem empty_source_ordered : observation (machine 0 2 2) =
      ([0,2,2,7,11,13,1,17,19,1,71,3,23,29,31,37,2,41,43,47,2,53,59,61,73],
       [0,2,2,7,11,13,1,17,19,1,71,3,23,29,31,37,2,41,43,47,2,53,59,61,73],
       [0,2,2,7,11,13,1,17,19,1,71,0,0,0,0,37,0,0,0,47,2,53,59,61,73],
       [0,0,2,7,11,13,1,17,19,1,71,0,0,0,0,37,0,0,0,47,2,53,59,61,73],
       context (machine 0 2 2),context { machine 0 2 2 with stack := copyStack (machine 0 2 2) },
       context { machine 0 2 2 with stack := clearStack (machine 0 2 2) },context (machine 0 2 2)) := by rfl

/-- COMPLETE before/copy/clear/final storage and full actual phase-stack/context observations. -/
theorem retained_reuse_ordered : observation (machine 2 0 0) =
      ([2,0,0,7,11,13,1,17,19,1,71,3,23,29,31,37,2,41,43,47,2,53,59,61,73],
       [2,0,0,7,11,13,1,17,19,1,71,0,0,0,0,37,1,17,0,47,2,53,59,61,73],
       [2,0,0,7,11,13,1,17,19,1,71,0,0,0,0,37,1,17,0,47,2,53,59,61,73],
       [2,2,0,7,11,13,1,17,19,1,71,0,0,0,0,37,1,17,0,47,2,53,59,61,73],
       context (machine 2 0 0),context { machine 2 0 0 with stack := copyStack (machine 2 0 0) },
       context { machine 2 0 0 with stack := clearStack (machine 2 0 0) },context (machine 2 0 0)) := by rfl

private def shrink := machine 1 2 2
private def badCleared := TargetNestedArrayClearLoop.prefixMachine (copied shrink) dst 0 2
private def badAfter := { badCleared with stack := tail,store := Evm.WordStore.write badCleared.store dst 1 }

/-- ACTUAL wrong phase starts its counter at ZERO, clearing a newly copied
live child. Complete target/context observations distinguish the corruption. -/
theorem wrong_outer_start :
    Evm.run ([.loop TargetArrayClear.condition TargetNestedArrayCopy.clearBody] ++ TargetArrayCopy.finish)
      { copied shrink with stack := .val (word 0) :: .val (word 2) :: .slot dst :: .val (word 1) :: tail } = .ok badAfter 0 ∧
    (view (result shrink),view badAfter,context (result shrink),context badAfter) =
      ([1,1,2,7,11,13,1,17,19,1,71,2,7,11,0,37,0,0,0,47,2,53,59,61,73],[1,1,2,7,11,13,1,17,19,1,71,0,0,0,0,37,0,0,0,47,2,53,59,61,73],context shrink,context shrink) := by
  have loop := TargetNestedArrayClearLoop.run_loop_from (copied shrink) tail dst 0 (word 1) (word 2) (word 0) (by decide) (by decide)
  have actual : Evm.run ([.loop TargetArrayClear.condition TargetNestedArrayCopy.clearBody] ++ TargetArrayCopy.finish)
      { copied shrink with stack := .val (word 0) :: .val (word 2) :: .slot dst :: .val (word 1) :: tail } = .ok badAfter 0 := by
    change Evm.run _ (TargetNestedArrayClearLoop.iterationMachine (copied shrink) tail dst 0 (word 1) (word 2) (word 0)) = _
    rw [Evm.run_append_ok loop]
    change Evm.run TargetArrayCopy.finish { badCleared with stack := .val (word 2) :: .val (word 2) :: .slot dst :: .val (word 1) :: tail } = _
    exact TargetArrayCopyTail.run_finish badCleared tail dst (word 2) (word 2) (word 1)
  exact ⟨actual,rfl⟩

private def olderSlot : Evm.Slot := .data (.data dst 0) 3
private def badOlderCode : List Evm.Instr := TargetNestedArrayCopy.code ++ [.push (.val (word 0)),.push (.slot olderSlot),.sstore]
private def badOlder := { result shrink with store := Evm.WordStore.write (result shrink).store olderSlot 0 }
/-- An ACTUAL extra SSTORE destroys older inner shadow37 despite otherwise
correct runtime traversal. The entire ordered cell/context result is pinned. -/
theorem wrong_older_shadow_clear :
    Evm.run badOlderCode { shrink with stack := .slot src :: .slot dst :: tail } = .ok badOlder 0 ∧
    (view (result shrink),view badOlder,context (result shrink),context badOlder) =
      ([1,1,2,7,11,13,1,17,19,1,71,2,7,11,0,37,0,0,0,47,2,53,59,61,73],[1,1,2,7,11,13,1,17,19,1,71,2,7,11,0,0,0,0,0,47,2,53,59,61,73],context shrink,context shrink) := by
  have executed := TargetNestedArrayRuntime.run_current shrink tail src dst
  have actual : Evm.run badOlderCode { shrink with stack := .slot src :: .slot dst :: tail } = .ok badOlder 0 := by
    rw [badOlderCode,Evm.run_append_ok executed]
    rfl
  exact ⟨actual,rfl⟩

/-- Same-root aliases execute both actual levels without dropping any observed
live/retained child, payload, older shadow or nontrivial context field. -/
theorem self_alias :
    Evm.run TargetNestedArrayCopy.code { machine 2 1 2 with stack := .slot src :: .slot src :: tail } =
      .ok (TargetNestedArrayRuntime.afterCopy (machine 2 1 2) tail src src) 0 ∧
    (view (machine 2 1 2),view (TargetNestedArrayRuntime.afterCopy (machine 2 1 2) tail src src),
      context (TargetNestedArrayRuntime.afterCopy (machine 2 1 2) tail src src)) =
      ([2,1,2,7,11,13,1,17,19,1,71,3,23,29,31,37,2,41,43,47,2,53,59,61,73],
       [2,1,2,7,11,13,1,17,19,1,71,3,23,29,31,37,2,41,43,47,2,53,59,61,73],context (machine 2 1 2)) := by
  exact ⟨TargetNestedArrayRuntime.run_current _ _ _ _,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayControls.runtime_header_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms runtime_header_family
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayControls.shrinking_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms shrinking_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayControls.growing_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms growing_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayControls.empty_source_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_source_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayControls.retained_reuse_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms retained_reuse_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayControls.wrong_outer_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_outer_start
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayControls.wrong_older_shadow_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_older_shadow_clear
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayControls.self_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_alias

end Solidity.Backend.StorageOps.TargetNestedArrayControls

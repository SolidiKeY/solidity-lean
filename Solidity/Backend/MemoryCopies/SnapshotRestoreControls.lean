import Solidity.Backend.MemoryCopies.SnapshotRestore

/-! Inhabited empty, nonempty and long captures. A real SSTORE changes the
reached old length before restoration. An actual memory write refutes the
memory-preservation premise; that negative does not assert copy refusal. -/
namespace Solidity.Backend.MemoryCopies.SnapshotRestoreControls
open Evm Evm.Memory
private def H : HTy := [.array (.prim .uint)]
private def reference : HRef H (.array (.prim .uint)) := ⟨0,rfl⟩
private theorem wide : 1024 < W := by decide
private def heap (n : Nat) (bounded : n < 128) : Heap H :=
  (⟨List.replicate n (indexValue (wmod 7)),by rw [List.length_replicate]; exact Nat.lt_trans bounded (by decide)⟩,())
private def destination : Slot := .root 1
private def before (n : Nat) : Machine := {Machine.init with
  stack := [w[77]], mem := fun a => if a = 16 then .val (wmod n) else w[7],
  store := ⟨fun slot => match slot with
    | .root 1 => wmod 1
    | .data (.root 1) _ => wmod 99
    | .root 2 => wmod 77
    | _ => wmod 0⟩}
private def changed (n : Nat) : Machine :=
  {before n with store := WordStore.write (before n).store destination 4}
private def intervention : List Instr := [.push w[4],.push (.slot destination),.sstore]
private def old : SVal (.ref (.array (.prim .uint))) :=
  .array (SVec.ofList (List.replicate 4 (.prim (indexValue (wmod 99))))) .nil (by decide)

private theorem count (n : Nat) (bounded : n < 128) : (heap n bounded).len reference .dyn = n := by
  simp only [heap,reference,Heap.len,Heap.get,H,Objs.get,MObj.elems_dyn,List.length_replicate]

private theorem captured (n : Nat) (bounded : n < 128) :
    Evm.Memory.ArrayRepr (heap n bounded) reference (wmod 16) (before n) := by
  refine ⟨?_,?_,?_⟩
  · rw [count]
    change 16+1+n ≤ W
    have enough : 1024 < W := wide
    omega
  · rw [count]
    rfl
  · intro i item selected
    simp only [heap,reference,Heap.get,H,Objs.get,MObj.elems_dyn] at selected
    have same : item = indexValue (wmod 7) := (List.mem_replicate.mp (List.mem_of_getElem? selected)).2
    subst item
    have notHeader : 16+1+i ≠ 16 := by omega
    change ReprV .uint (indexValue (wmod 7)) (if 16+1+i = 16 then .val (wmod n) else w[7])
    rw [if_neg notHeader]
    exact ReprV.uint_of rfl

private theorem executed (n : Nat) :
    run intervention ((before n).push w[16]) = .ok ((changed n).push w[16]) 0 := rfl

private theorem reached (n : Nat) :
    ReprAt (changed n).store 128 (.ref (.array (.prim .uint))) destination old := by
  refine .array ?_ (by decide) ?_
  · exact WordStore.write_same_of_lt _ _ _ (by decide)
  · intro i item selected
    rw [SVec.toList_ofList] at selected
    have same : item = SVal.prim (indexValue (wmod 99)) := (List.mem_replicate.mp (List.mem_of_getElem? selected)).2
    subst item
    simp only [size_prim,Nat.mul_one]
    refine .prim (ReprV.uint_of ?_)
    have unchanged : (changed n).store (.data destination i) = 99 := by
      change (WordStore.write (before n).store destination 4) (.data destination i) = 99
      rw [WordStore.write_other _ _ (Ne.symm (Slot.ne_data destination i))]
      rfl
    change (99 : Int) = (((changed n).store (.data destination i)) : Int)
    rw [unchanged]
    rfl

private theorem restored (n : Nat) (bounded : n < 128) :
    SnapshotRestoreResult (heap n bounded) reference (wmod 16) (before n) (changed n) intervention destination 128 old :=
  snapshot_restore_correct _ _ _ _ _ _ _ _ _ (captured n bounded) (executed n) rfl (reached n) (by rw [count]; exact bounded)

private def final (n : Nat) : Machine := {changed n with store := arrayCopyStore (changed n).store destination n (fun _ => wmod 7)}

private theorem observations (n : Nat) (bounded : n < 128) :
    run (snapshotRestoreCode intervention destination) ((before n).push w[16]) = .ok (final n) 0 ∧
    (before n).store destination = 1 ∧ (changed n).store destination = 4 ∧
    (final n).store destination = n ∧
    (∀ i, i < n → (final n).store (.data destination i) = 7) ∧
    (∀ i, n ≤ i → i < 4 → (final n).store (.data destination i) = 0) ∧
    (final n).store (.root 2) = 77 ∧ (final n).stack = [w[77]] := by
  have result : SnapshotRestoreResult (heap n bounded) reference (wmod 16) (before n) (changed n) intervention destination 128 old := restored n bounded
  have words : (fun i => payloadWord ((before n).mem ((wmod 16).val+1+i))) = (fun _ => wmod 7) := by
    funext i
    change payloadWord (if 16+1+i = 16 then .val (wmod n) else w[7]) = wmod 7
    rw [if_neg (show 16+1+i ≠ 16 by omega)]
    rfl
  have word (i : Nat) : payloadWord ((before n).mem ((wmod 16).val+1+i)) = wmod 7 := congrFun words i
  simp only [SnapshotRestoreResult,count,word] at result
  obtain ⟨whole,copy,typed,length,live,tail,frame,memory,stack⟩ := result
  refine ⟨whole,rfl,WordStore.write_same_of_lt _ _ _ (by decide),length,?_,tail,?_,rfl⟩
  · intro i within
    exact live i within
  · have outside : ¬ Occ (.ref (.array (.prim .uint))) destination (.root 2) := by
      intro occurrence
      cases occurrence with
      | elem i occurrence => cases occurrence
    change (arrayCopyStore (changed n).store destination n (fun _ => wmod 7)) (.root 2) = 77
    rw [frame (.root 2) outside]
    change (WordStore.write (before n).store destination 4) (.root 2) = 77
    rw [WordStore.write_other _ _ (by decide)]
    rfl

theorem empty_capture_restored :
    run (snapshotRestoreCode intervention destination) ((before 0).push w[16]) = .ok (final 0) 0 ∧
    (final 0).store (.data destination 3) = 0 :=
  ⟨(observations 0 (by decide)).1,(observations 0 (by decide)).2.2.2.2.2.1 3 (by decide) (by decide)⟩

theorem pair_capture_restored :
    run (snapshotRestoreCode intervention destination) ((before 2).push w[16]) = .ok (final 2) 0 ∧
    (before 2).store destination = 1 ∧ (changed 2).store destination = 4 ∧
    (final 2).store (.data destination 0) = 7 ∧ (final 2).store (.data destination 3) = 0 ∧
    (final 2).store (.root 2) = 77 := by
  obtain ⟨whole,initialLength,reachedLength,length,live,tail,sentinel,stack⟩ := observations 2 (by decide)
  exact ⟨whole,initialLength,reachedLength,live 0 (by decide),tail 3 (by decide) (by decide),sentinel⟩

theorem long_capture_restored :
    run (snapshotRestoreCode intervention destination) ((before 64).push w[16]) = .ok (final 64) 0 ∧
    (final 64).store (.data destination 63) = 7 :=
  ⟨(observations 64 (by decide)).1,(observations 64 (by decide)).2.2.2.2.1 63 (by decide)⟩

private def corruptCode : List Instr := [.push w[99],.push w[17],.mstoreAt]
private def corrupted : Machine := {before 2 with mem := fun a => if a = 17 then w[99] else (before 2).mem a}

theorem captured_memory_write_refutes_preservation :
    run corruptCode ((before 2).push w[16]) = .ok (corrupted.push w[16]) 0 ∧
    corrupted.mem ≠ (before 2).mem := by
  refine ⟨rfl,?_⟩
  intro equal
  have atPayload : w[99] = w[7] := congrFun equal 17
  cases atPayload

/--
info: 'Solidity.Backend.MemoryCopies.SnapshotRestoreControls.empty_capture_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_capture_restored
/--
info: 'Solidity.Backend.MemoryCopies.SnapshotRestoreControls.pair_capture_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pair_capture_restored
/--
info: 'Solidity.Backend.MemoryCopies.SnapshotRestoreControls.long_capture_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_capture_restored
/--
info: 'Solidity.Backend.MemoryCopies.SnapshotRestoreControls.captured_memory_write_refutes_preservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms captured_memory_write_refutes_preservation

end Solidity.Backend.MemoryCopies.SnapshotRestoreControls

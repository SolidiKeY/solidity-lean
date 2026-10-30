import Solidity.Backend.MemoryOps.CalldataTransfer
import Solidity.Backend.MemoryOps.CalldataRead

/-! Executed decoded-object transfers. Byte input is intentionally unconstrained;
these kernel controls establish no ABI decoder or emitted EVM behavior. -/
namespace Solidity.Backend.MemoryOps.TransferControls
private def D : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B, P]
private def dst : HRef H B := ⟨0, rfl⟩
private def parent : HRef H P := ⟨1, rfl⟩
private def hp : Heap H := (⟨[true, true, true, true, true], by decide⟩,
  ⟨[dst, dst], rfl⟩, ())
private def output : Heap H := (⟨[true, false, true, false, true], by decide⟩,
  ⟨[dst, dst], rfl⟩, ())
private def input (bs : List Bool) : Source.Calldata D :=
  ⟨[], fun off => if off = 7 then
    some ⟨.array .calldata .bool none, decodedBools bs⟩ else none⟩
private def bs : List Bool := [true, false, true, false, true]
private theorem repr : DecodedArrayAt (n := none) (input bs) 7 bs.length
    (fun _ h => by cases h) (fun i => .val (.bool bs[i])) := rfl

/-- Populated nonuniform source drives the operation; payload is not supplied. -/
theorem ordered : checkedCalldataBools (input bs) 7 hp dst .dyn 1 4 1 = some output := by
  simp only [checkedCalldataBools, calldataBools, calldataBoolPayload, calldataBool, input, decodedBools, bs, hp, dst, output, Heap.get, Heap.set, Objs.get, Objs.set, Heap.len, MObj.elems_dyn, overwriteSlice, withElems, replaceSlice, Bind.bind, Option.bind, ↓reduceIte, List.ofFn_succ, List.ofFn_zero]
  simp only [Nat.reduceLeDiff, List.length_cons, List.length_nil, Nat.reduceAdd, Fin.isValue,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.getElem_fin, Nat.zero_add,
      and_self, ↓reduceDIte, Nat.add_one_sub_one, Nat.reducePow, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero, List.cons_append, List.nil_append, Option.some.injEq]

  apply Prod.ext
  · apply Subtype.ext
    change @Eq (List Bool) _ _
    simp only [Fin.isValue, List.cons.injEq, and_true, true_and]
    simp only [MVal, PrimTy.Denote]
    decide
  · rfl

theorem actual_reads : ∃ b, (MObj.elems .dyn (output.get dst))[1]? = some b ∧
    DecodedArrayRead (input bs) 7 .bool none 1 (.val (.bool b)) :=
  checkedCalldataBools_read repr hp dst .dyn 1 4 1 output ordered 0 (by decide)

/-- Wrong payload order/value differs, not merely equal uniform fixtures. -/
theorem discriminating :
    MObj.elems .dyn (output.get dst) ≠ [true, true, false, true, true] ∧
    (MObj.elems .dyn (output.get dst))[1]? ≠ some true ∧
    output.get parent = hp.get parent := by
  constructor
  · simp only [MObj.elems_dyn]
    change [true, false, true, false, true] ≠ [true, true, false, true, true]
    decide
  · refine ⟨?_, checkedCalldataBools_frame repr hp dst .dyn 1 4 1 output ordered parent (by decide)⟩
    simp only [MObj.elems_dyn]; decide

theorem exterior :
    (MObj.elems .dyn (output.get dst))[0]? = (MObj.elems .dyn (hp.get dst))[0]? ∧
    (MObj.elems .dyn (output.get dst))[4]? = (MObj.elems .dyn (hp.get dst))[4]? := by
  exact ⟨checkedCalldataBools_outside repr hp dst .dyn 1 4 1 output ordered 0 (by decide),
    checkedCalldataBools_outside repr hp dst .dyn 1 4 1 output ordered 4 (by decide)⟩

/-- Each check fails independently on the actual operation. -/
theorem bounds :
    checkedCalldataBools (input bs) 7 hp dst .dyn 4 1 0 = none ∧
    checkedCalldataBools (input bs) 7 hp dst .dyn 5 6 0 = none ∧
    checkedCalldataBools (input bs) 7 hp dst .dyn 0 2 4 = none := by
  simp only [checkedCalldataBools, calldataBools, calldataBoolPayload, calldataBool, input, decodedBools, bs, hp, dst, Heap.get, Objs.get, Heap.len, MObj.elems_dyn, Bind.bind, Option.bind, ↓reduceIte, List.ofFn_succ, List.ofFn_zero]
  simp only [Nat.reduceLeDiff, List.length_cons, List.length_nil, Nat.reduceAdd, Fin.isValue,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.getElem_fin, Nat.zero_add,
      and_true, ↓reduceDIte, and_false, Nat.zero_le, and_self, Nat.sub_zero]

theorem empty_end :
    checkedCalldataBools (input bs) 7 hp dst .dyn 5 5 5 = some hp ∧
    checkedCalldataBools (input []) 7 hp dst .dyn 0 0 5 = some hp := by
  simp only [checkedCalldataBools, calldataBools, calldataBoolPayload, calldataBool, input, decodedBools, bs, hp, dst, Heap.get, Heap.set, Objs.get, Objs.set, Heap.len, MObj.elems_dyn, overwriteSlice, withElems, replaceSlice, Bind.bind, Option.bind, ↓reduceIte, List.ofFn_succ, List.ofFn_zero]
  simp only [Nat.le_refl, List.length_cons, List.length_nil, Nat.reduceAdd, Fin.isValue,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Fin.getElem_fin, Nat.zero_add,
      and_self, ↓reduceDIte, Nat.sub_self, Nat.add_zero, Nat.reducePow, List.take_succ_cons,
      List.take_nil, List.drop_succ_cons, List.drop_nil, List.append_nil]

private def fixedInput : Source.Calldata D :=
  ⟨[], fun _ => some ⟨.array .calldata .bool (some 3),
    .array 3 (fun _ h => (Option.some.inj h).symm) (fun i => .val (.bool (i.val == 1)))⟩⟩
private abbrev F : RefTy := .fixed (.prim .bool) 5
private def fixedDst : HRef [F] F := ⟨0, rfl⟩
private def fixedHp : Heap [F] := (⟨[true, true, true, true, true], rfl⟩, ())
private def fixedOut : Heap [F] := (⟨[true, false, true, false, true], rfl⟩, ())
theorem fixed_transfer :
    checkedCalldataBools fixedInput 0 fixedHp fixedDst .fixed 0 3 1 = some fixedOut := by
  simp only [checkedCalldataBools, calldataBools, calldataBoolPayload, calldataBool, fixedInput, fixedHp, fixedDst, fixedOut, Heap.get, Heap.set, Objs.get, Objs.set, Heap.len, MObj.elems_fixed, overwriteSlice, withElems, replaceSlice, Bind.bind, Option.bind, List.ofFn_succ, List.ofFn_zero]
  simp only [Nat.zero_le, Fin.isValue, Fin.val_zero, Nat.reduceBEq, Fin.succ_zero_eq_one,
      Fin.val_one, BEq.rfl, Fin.succ_one_eq_two, Fin.val_two, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd, Nat.le_refl, and_self, ↓reduceDIte, Nat.sub_zero, Nat.reduceLeDiff,
      List.take_succ_cons, List.take_zero, List.drop_zero, List.take_nil, List.drop_succ_cons,
      List.cons_append, List.nil_append]

private def wrongType : Source.Calldata D := ⟨[], fun _ => some ⟨.bytes .calldata, .bytes [1]⟩⟩
private def wrongLocation : Source.Calldata D := ⟨[], fun _ => some ⟨.array .memory .bool none,
  .array 1 (fun _ h => by cases h) (fun _ => .val (.bool true))⟩⟩
private def pointer : Source.Calldata D := ⟨[], fun _ => some ⟨.array .calldata .bool none,
  .val (.cdRef rfl 7)⟩⟩
theorem lookup_failures :
    checkedCalldataBools (input bs) 8 hp dst .dyn 0 1 0 = none ∧
    checkedCalldataBools wrongType 7 hp dst .dyn 0 1 0 = none ∧
    checkedCalldataBools wrongLocation 7 hp dst .dyn 0 1 0 = none ∧
    checkedCalldataBools pointer 7 hp dst .dyn 0 1 0 = none := ⟨rfl, rfl, rfl, rfl⟩

/-- Arbitrary runtime payload length, with nonuniform selected value. -/
theorem runtime_transfer (n : Nat) (hn : n < 2 ^ 256) :
    ∃ out : Heap [.array (.prim .bool)],
      checkedCalldataBools (H := [B]) (input ((List.range n).map (fun i => i == 32))) 7
        ((⟨List.replicate n false, by simp only [List.length_replicate]; exact hn⟩, ()) : Heap [B])
        (⟨0, rfl⟩ : HRef [B] B) .dyn 0 n 0 = some out := by
  let vals := (List.range n).map (fun i => i == 32)
  have hc : DecodedArrayAt (n := none) (input vals) 7 vals.length
      (fun _ h => by cases h) (fun i => .val (.bool vals[i])) := rfl
  have hs : SliceBounds vals.length 0 n := ⟨Nat.zero_le _, by simp only [vals, List.length_map, List.length_range]; exact Nat.le_refl _⟩
  refine ⟨_, checkedCalldataBools_some hc _ _ .dyn 0 n 0 hs ?_⟩
  simp only [Heap.len, MObj.elems_dyn]
  change 0 + (n - 0) ≤ (List.replicate n false).length
  simp only [List.length_replicate, Nat.sub_zero, Nat.zero_add, Nat.le_refl]

private def boundaryHp : Heap [B] := (⟨List.replicate 34 false, by decide⟩, ())
private def boundaryDst : HRef [B] B := ⟨0, rfl⟩
private def boundaryOut : Heap [B] := (⟨List.replicate 32 false ++ [true, false], by decide⟩, ())
/-- Indices32/33 are element boundaries; no physical byte encoding claim. -/
theorem boundary : checkedCalldataBools
    (input ((List.range 34).map (fun i => i == 32))) 7 boundaryHp boundaryDst .dyn 0 34 0 = some boundaryOut := by
  simp only [checkedCalldataBools, calldataBools, calldataBoolPayload, calldataBool, input, decodedBools, boundaryHp, boundaryDst, boundaryOut, Heap.get, Heap.set, Objs.get, Objs.set, Heap.len, MObj.elems_dyn, overwriteSlice, withElems, replaceSlice, Bind.bind, Option.bind, ↓reduceIte, List.ofFn_succ, List.ofFn_zero]
  simp only [Nat.zero_le, Fin.isValue, List.map_cons, Nat.reduceBEq, List.map_nil, List.length_cons,
      List.length_nil, Nat.reduceAdd, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc,
      Nat.zero_add, Nat.le_refl, and_self, ↓reduceDIte, Nat.sub_zero, List.reduceReplicate,
      Nat.reducePow, List.take_zero, List.drop_zero, List.take_succ_cons, List.take_nil,
      List.drop_succ_cons, List.drop_nil, List.append_nil, List.nil_append, List.cons_append,
      Option.some.injEq]

  apply Prod.ext
  · apply Subtype.ext
    change @Eq (List Bool) _ _
    simp only [Fin.isValue, List.cons.injEq, and_true]
    simp only [MVal, PrimTy.Denote]
    decide
  · rfl

/-- info: 'Solidity.Backend.MemoryOps.TransferControls.ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.actual_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_reads
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.discriminating' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms discriminating
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.exterior' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exterior
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bounds
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.fixed_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixed_transfer
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.lookup_failures' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lookup_failures
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.runtime_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runtime_transfer
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms boundary
/-- An actual allocator discharges the growth premise; fresh alias fields are
framed although their old Boolean child acquires the transferred contents. -/
theorem allocated_transfer :
    let obj : MObj H P := ⟨[dst, dst], rfl⟩
    let g := hp.alloc obj
    let e := List.prefix_append H [P]
    ∃ out', checkedCalldataBools (input bs) 7 g.1 (dst.wk e) .dyn 1 4 1 = some out' ∧
      Heap.Keeps e output out' ∧ out'.get g.2 = g.1.get g.2 ∧
      (MObj.elems .dyn (out'.get (dst.wk e)))[1]? = some false := by
  dsimp only
  let obj : MObj H P := ⟨[dst, dst], rfl⟩
  let e := List.prefix_append H [P]
  obtain ⟨out', ho, hk⟩ := checkedCalldataBools_keeps repr e (Heap.keeps_alloc hp obj) dst .dyn 1 4 1 output ordered
  refine ⟨out', ho, hk, checkedCalldataBools_frame repr _ (dst.wk e) .dyn 1 4 1 out' ho (hp.alloc obj).2 (by decide), ?_⟩
  rw [hk dst, MObj.elems_wk]
  simp only [MObj.elems_dyn]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.TransferControls.allocated_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allocated_transfer
private def wrongElement : Source.Calldata D :=
  ⟨[], fun _ => some ⟨.array .calldata (.bytes .calldata) none,
    .array 1 (fun _ h => by cases h) (fun _ => .bytes [1])⟩⟩
/-- A decoded array with the wrong element type is rejected before copying. -/
theorem wrong_element : checkedCalldataBools wrongElement 7 hp dst .dyn 0 1 0 = none := rfl
/-- info: 'Solidity.Backend.MemoryOps.TransferControls.wrong_element' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrong_element
end Solidity.Backend.MemoryOps.TransferControls

import Solidity.Backend.MemoryOps.CalldataUintTransfer

/-! Exact uint256 decoded transfers, including the maximum value. No ABI bytes,
truncation/target word encoding or Source execution is supplied or claimed. -/
namespace Solidity.Backend.MemoryOps.UintTransferControls
private def D : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
private abbrev U := PrimTy.uint.Denote
private def zero : U := ⟨0, by decide⟩
private def seven : U := ⟨7, by decide⟩
private def twelve : U := ⟨12, by decide⟩
private def one : U := ⟨1, by decide⟩
private def maximum : U := ⟨((2 ^ 256 - 1 : Nat) : Int), by decide⟩
private abbrev A : RefTy := .array (.prim .uint)
private abbrev P : RefTy := .fixed (.ref A) 2
private abbrev H : HTy := [A, P]
private def dst : HRef H A := ⟨0, rfl⟩
private def parent : HRef H P := ⟨1, rfl⟩
private def hp : Heap H := (⟨[zero, zero, zero, zero, zero], by decide⟩, ⟨[dst, dst], rfl⟩, ())
private def bs : List U := [maximum, seven, zero, twelve, one]
private def input (values : List U) : Source.Calldata D :=
  ⟨[], fun off => if off = 9 then some ⟨.array .calldata (.int .u256) none,
    .array values.length (fun _ h => by cases h)
      (fun i => .val (sourceUint values[i]))⟩ else none⟩
private theorem repr (values : List U) : DecodedArrayAt (n := none) (input values) 9 values.length
    (fun _ h => by cases h) (fun i => .val (sourceUint values[i])) := rfl
private theorem space : 1 + ((bs.drop 0).take (3 - 0)).length ≤ hp.len dst .dyn := by
  simp only [Heap.len, MObj.elems_dyn]
  decide
private def out := overwriteSlice hp dst .dyn 1 ((bs.drop 0).take (3 - 0)) space

theorem checked : checkedCalldataUints (input bs) 9 hp dst .dyn 0 3 1 = some out := by
  have h := checkedCalldataUints_some (repr bs) hp dst .dyn 0 3 1
    (show SliceBounds bs.length 0 3 from ⟨by decide, by decide⟩)
    (by simp only [Heap.len, MObj.elems_dyn]; decide)
  simpa only [calldataUint_values] using h

/-- Complete nonuniform ordered output includes uint256's maximum unmodified. -/
theorem ordered : (MObj.elems .dyn (out.get dst)).map (fun v : U => v.val) =
    [0, ((2 ^ 256 - 1 : Nat) : Int), 7, 0, 0] := by
  rw [out, overwriteSlice_elems]
  simp only [MObj.elems_dyn]
  rfl

theorem immutable_read : ∃ v, (MObj.elems .dyn (out.get dst))[1]? = some v ∧
    DecodedArrayRead (input bs) 9 (.int .u256) none 0 (.val (sourceUint v)) :=
  checkedCalldataUints_read (repr bs) hp dst .dyn 0 3 1 out checked 0 (by decide)

theorem wrong_order : (MObj.elems .dyn (out.get dst)).map (fun v : U => v.val) ≠
    [0, 7, ((2 ^ 256 - 1 : Nat) : Int), 0, 0] := by
  rw [ordered]
  decide

theorem frames : out.get parent = hp.get parent ∧
    (MObj.elems .dyn (out.get dst))[0]? = (MObj.elems .dyn (hp.get dst))[0]? ∧
    (MObj.elems .dyn (out.get dst))[4]? = (MObj.elems .dyn (hp.get dst))[4]? :=
  ⟨checkedCalldataUints_frame (repr bs) hp dst .dyn 0 3 1 out checked parent (by decide),
    checkedCalldataUints_outside (repr bs) hp dst .dyn 0 3 1 out checked 0 (by decide),
    checkedCalldataUints_outside (repr bs) hp dst .dyn 0 3 1 out checked 4 (by decide)⟩

theorem bounds : checkedCalldataUints (input bs) 9 hp dst .dyn 3 1 0 = none ∧
    checkedCalldataUints (input bs) 9 hp dst .dyn 5 6 0 = none ∧
    checkedCalldataUints (input bs) 9 hp dst .dyn 0 2 4 = none := by
  constructor
  · exact (checkedCalldataUints_none_iff (repr bs) hp dst .dyn 3 1 0).mpr (Or.inl (by decide))
  · constructor
    · exact (checkedCalldataUints_none_iff (repr bs) hp dst .dyn 5 6 0).mpr (Or.inr (Or.inl (by decide)))
    · apply (checkedCalldataUints_none_iff (repr bs) hp dst .dyn 0 2 4).mpr
      right; right
      simp only [Heap.len, MObj.elems_dyn]; decide

/-- Runtime lists are read from their typed immutable entries without an extra
payload bound. The destination's own capacity supplies the only size premise. -/
theorem runtime (values : List U) {K : HTy} {R : RefTy}
    (heap : Heap K) (r : HRef K R) (a : ArrTy R (.prim .uint))
    (hcap : values.length ≤ heap.len r a) :
    ∃ output, checkedCalldataUints (input values) 9 heap r a 0 values.length 0 = some output := by
  exact ⟨_, checkedCalldataUints_some (repr values) heap r a 0 values.length 0
    ⟨Nat.zero_le _, Nat.le_refl _⟩ (by simpa only [Nat.sub_zero, Nat.zero_add] using hcap)⟩

/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.immutable_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms immutable_read
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.wrong_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrong_order
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.frames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms frames
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bounds
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.runtime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runtime
theorem empty_end : checkedCalldataUints (input bs) 9 hp dst .dyn 5 5 5 = some hp ∧
    checkedCalldataUints (input []) 9 hp dst .dyn 0 0 5 = some hp := by
  constructor
  · exact checkedCalldataUints_empty (repr bs) hp dst .dyn 5 5 (by decide)
      (by simp only [Heap.len, MObj.elems_dyn]; decide)
  · exact checkedCalldataUints_empty (repr []) hp dst .dyn 0 5 (by decide)
      (by simp only [Heap.len, MObj.elems_dyn]; decide)

private def wrongWidth : Source.Calldata D := ⟨[], fun _ =>
  some ⟨.array .calldata (.int .u8) none,
    .array 1 (fun _ h => by cases h) (fun _ => .val (.int 7 (by decide)))⟩⟩
private def signed : Source.Calldata D := ⟨[], fun _ =>
  some ⟨.array .calldata (.int ⟨true, 256, by decide⟩) none,
    .array 1 (fun _ h => by cases h) (fun _ => .val (.int (-1) (by decide)))⟩⟩
private def pointer : Source.Calldata D := ⟨[], fun _ =>
  some ⟨.array .calldata (.int .u256) none, .val (.cdRef rfl 9)⟩⟩
/-- Other numeric families are unsupported here, not newly forbidden in Source. -/
theorem family_negatives :
    checkedCalldataUints wrongWidth 9 hp dst .dyn 0 1 0 = none ∧
    checkedCalldataUints signed 9 hp dst .dyn 0 1 0 = none ∧
    checkedCalldataUints pointer 9 hp dst .dyn 0 1 0 = none ∧
    checkedCalldataUints (input bs) 10 hp dst .dyn 0 1 0 = none := ⟨rfl, rfl, rfl, rfl⟩

private def fixedValues : List U := [zero, maximum, seven]
private def fixedInput : Source.Calldata D := ⟨[], fun _ =>
  some ⟨.array .calldata (.int .u256) (some 3),
    .array 3 (fun _ h => (Option.some.inj h).symm)
      (fun i => .val (sourceUint fixedValues[i]))⟩⟩
private abbrev F : RefTy := .fixed (.prim .uint) 5
private def fixedDst : HRef [F] F := ⟨0, rfl⟩
private def fixedHp : Heap [F] := (⟨[zero, zero, zero, zero, zero], rfl⟩, ())
theorem fixed_transfer : ∃ output, checkedCalldataUints fixedInput 0 fixedHp fixedDst .fixed 0 3 1 = some output ∧
    (MObj.elems .fixed (output.get fixedDst)).map (fun v : U => v.val) =
      [0, 0, ((2 ^ 256 - 1 : Nat) : Int), 7, 0] := by
  have hc : DecodedArrayAt (n := some 3) fixedInput 0 3
      (fun _ h => (Option.some.inj h).symm) (fun i => .val (sourceUint fixedValues[i])) := rfl
  have hs : SliceBounds 3 0 3 := ⟨by decide, by decide⟩
  have hd : 1 + (3 - 0) ≤ fixedHp.len fixedDst .fixed := by
    simp only [Heap.len, MObj.elems_fixed]; decide
  refine ⟨_, checkedCalldataUints_some hc fixedHp fixedDst .fixed 0 3 1 hs hd, ?_⟩
  rw [overwriteSlice_elems]
  change (replaceSlice (MObj.elems .fixed (fixedHp.get fixedDst)) 1
    ((List.ofFn (fun i : Fin fixedValues.length => calldataUint (.val (sourceUint (D := D) fixedValues[i])))).drop 0 |>.take (3 - 0))).map (fun v : U => v.val) = _
  rw [calldataUint_values]
  simp only [MObj.elems_fixed]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.family_negatives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms family_negatives
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.fixed_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fixed_transfer
/-- Actual allocation discharges growth and frames a fresh alias-containing
parent while the old child receives the maximum numeric value. -/
theorem allocated_transfer :
    let obj : MObj H P := ⟨[dst, dst], rfl⟩
    let g := hp.alloc obj
    let e := List.prefix_append H [P]
    ∃ output, checkedCalldataUints (input bs) 9 g.1 (dst.wk e) .dyn 0 3 1 = some output ∧
      Heap.Keeps e out output ∧ output.get g.2 = g.1.get g.2 ∧
      (MObj.elems .dyn (output.get (dst.wk e)))[1]? = some maximum := by
  dsimp only
  let obj : MObj H P := ⟨[dst, dst], rfl⟩
  let e := List.prefix_append H [P]
  obtain ⟨output, ho, hk⟩ := checkedCalldataUints_keeps (repr bs) e (Heap.keeps_alloc hp obj) dst .dyn 0 3 1 out checked
  refine ⟨output, ho, hk, checkedCalldataUints_frame (repr bs) _ (dst.wk e) .dyn 0 3 1 output ho (hp.alloc obj).2 (by decide), ?_⟩
  have hm : (MObj.elems .dyn (out.get dst))[1]? = some maximum := by
    change (MObj.elems .dyn (out.get dst))[1 + 0]? = some maximum
    rw [out, overwriteSlice_inside]
    · rfl
    · decide
  rw [hk dst, MObj.elems_wk, List.map_id'' (f := MVal.wk e (.prim .uint)) (fun _ => rfl)]
  exact hm

private def zeroHp : Heap [A] := (⟨[], by decide⟩, ())
private def zeroDst : HRef [A] A := ⟨0, rfl⟩
theorem empty_destination : checkedCalldataUints (input []) 9 zeroHp zeroDst .dyn 0 0 0 = some zeroHp :=
  checkedCalldataUints_empty (repr []) zeroHp zeroDst .dyn 0 0 (by decide)
    (by simp only [Heap.len, MObj.elems_dyn]; decide)

private def boundaryValues : List U := List.replicate 32 zero ++ [maximum, seven]
private def boundaryHp : Heap [A] := (⟨List.replicate 34 zero, by decide⟩, ())
private def boundaryDst : HRef [A] A := ⟨0, rfl⟩
/-- Runtime slice crosses element31/32/33, with no physical-byte claim. -/
theorem boundary : ∃ output,
    checkedCalldataUints (input boundaryValues) 9 boundaryHp boundaryDst .dyn 31 34 0 = some output ∧
    (MObj.elems .dyn (output.get boundaryDst)).map (fun v : U => v.val) =
      [0, ((2 ^ 256 - 1 : Nat) : Int), 7] ++ List.replicate 31 0 := by
  have hs : SliceBounds boundaryValues.length 31 34 := ⟨by decide, by decide⟩
  have hd : 0 + (34 - 31) ≤ boundaryHp.len boundaryDst .dyn := by
    simp only [Heap.len, MObj.elems_dyn]; decide
  refine ⟨_, checkedCalldataUints_some (repr boundaryValues) boundaryHp boundaryDst .dyn 31 34 0 hs hd, ?_⟩
  rw [overwriteSlice_elems, calldataUint_values]
  simp only [MObj.elems_dyn]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.allocated_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allocated_transfer
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.empty_destination' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_destination
/-- info: 'Solidity.Backend.MemoryOps.UintTransferControls.boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms boundary
end Solidity.Backend.MemoryOps.UintTransferControls

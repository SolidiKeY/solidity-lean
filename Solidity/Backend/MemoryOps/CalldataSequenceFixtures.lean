import Solidity.Backend.MemoryOps.MixedCalldataSequence

/-! Concrete decoded primitive fixture tables only; no ABI decoder or Source
execution judgment. The operations themselves still accept no payload list. -/
namespace Solidity.Backend.MemoryOps.SequenceFixtures
def D : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
/-- Retain the 4.24 generated length-witness interface. -/
theorem bools._proof_1 (bs : List Bool) (x : Nat) (h : (none : Option Nat) = some x) :
    x = bs.length := by cases h
/-- Retain the 4.24 generated index-bound interface. -/
theorem bools._proof_2 (bs : List Bool) (i : Fin bs.length) : i.val < bs.length := i.isLt
def bools (bs : List Bool) : Source.Calldata D := ⟨[], fun off => if off = 7 then
  some ⟨.array .calldata .bool none, .array bs.length (bools._proof_1 bs)
    (fun i => .val (.bool (bs[i.val]'(bools._proof_2 bs i))))⟩ else none⟩
theorem bool_repr (bs : List Bool) : DecodedArrayAt (n := none) (bools bs) 7 bs.length
    (fun _ h => by cases h) (fun i => .val (.bool bs[i])) := rfl
theorem bool_values (bs : List Bool) : List.ofFn (fun i : Fin bs.length =>
    calldataBool (Source.Data.val (Source.Val.bool (D := D) bs[i]))) = bs := by
  apply List.ext_getElem
  · exact List.length_ofFn
  · intro i hi hj
    simp only [List.getElem_ofFn, calldataBool, Fin.getElem_fin]
abbrev U := PrimTy.uint.Denote
def zero : U := ⟨0, by decide⟩
def seven : U := ⟨7, by decide⟩
def one : U := ⟨1, by decide⟩
def maximum : U := ⟨((2^256-1 : Nat) : Int), by decide⟩
/-- Retain the 4.24 generated unsigned-table length witness. -/
theorem uints._proof_1 (bs : List U) (x : Nat) (h : (none : Option Nat) = some x) :
    x = bs.length := by cases h
/-- Retain the 4.24 generated unsigned-table index bound. -/
theorem uints._proof_2 (bs : List U) (i : Fin bs.length) : i.val < bs.length := i.isLt
def uints (bs : List U) : Source.Calldata D := ⟨[], fun off => if off = 9 then
  some ⟨.array .calldata (.int .u256) none, .array bs.length (uints._proof_1 bs)
    (fun i => .val (sourceUint (bs[i.val]'(uints._proof_2 bs i))))⟩ else none⟩
theorem uint_repr (bs : List U) : DecodedArrayAt (n := none) (uints bs) 9 bs.length
    (fun _ h => by cases h) (fun i => .val (sourceUint bs[i])) := rfl
/-- info: 'Solidity.Backend.MemoryOps.SequenceFixtures.bool_repr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bool_repr
/-- info: 'Solidity.Backend.MemoryOps.SequenceFixtures.bool_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bool_values
/-- info: 'Solidity.Backend.MemoryOps.SequenceFixtures.uint_repr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uint_repr
end Solidity.Backend.MemoryOps.SequenceFixtures

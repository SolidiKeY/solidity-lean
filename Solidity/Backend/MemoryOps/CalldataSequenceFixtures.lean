import Solidity.Backend.MemoryOps.MixedCalldataSequence

/-! Concrete decoded primitive fixture tables only; no ABI decoder or Source
execution judgment. The operations themselves still accept no payload list. -/
namespace Solidity.Backend.MemoryOps.SequenceFixtures
def D : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
def bools (bs : List Bool) : Source.Calldata D := ⟨[], fun off => if off = 7 then
  some ⟨.array .calldata .bool none, .array bs.length (fun _ h => by cases h)
    (fun i => .val (.bool bs[i]))⟩ else none⟩
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
def uints (bs : List U) : Source.Calldata D := ⟨[], fun off => if off = 9 then
  some ⟨.array .calldata (.int .u256) none, .array bs.length (fun _ h => by cases h)
    (fun i => .val (sourceUint bs[i]))⟩ else none⟩
theorem uint_repr (bs : List U) : DecodedArrayAt (n := none) (uints bs) 9 bs.length
    (fun _ h => by cases h) (fun i => .val (sourceUint bs[i])) := rfl
/-- info: 'Solidity.Backend.MemoryOps.SequenceFixtures.bool_repr' depends on axioms: [propext] -/
#guard_msgs in #print axioms bool_repr
/-- info: 'Solidity.Backend.MemoryOps.SequenceFixtures.bool_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bool_values
/-- info: 'Solidity.Backend.MemoryOps.SequenceFixtures.uint_repr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uint_repr
end Solidity.Backend.MemoryOps.SequenceFixtures

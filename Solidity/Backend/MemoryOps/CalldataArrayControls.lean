import Solidity.Backend.MemoryOps.CalldataArrayRead
import Solidity.Backend.MemoryOps.CalldataRead

/-! Static decoded arrays containing calldata references and nested contents.
Offsets are retained as existing Source.Val.cdRef identities; no ABI decoder,
child lookup semantics, or translation to memory references is inferred. -/
namespace Solidity.Backend.MemoryOps.ArrayControls
private def D : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
private abbrev T : Source.STy := .array .calldata .bool none
private def ref (off : Nat) : Source.Data D T := .val (.cdRef rfl off)
private def xs (i : Fin 3) : Source.Data D T := ref (if i.val = 1 then 42 else 37)
private theorem fixed_len : ∀ m, (some 3 : Option Nat) = some m → m = 3 := by
  intro m h
  exact (Option.some.inj h).symm
private def c : Source.Calldata D := ⟨[], fun off => if off = 11 then
  some ⟨.array .calldata T (some 3), .array 3 fixed_len xs⟩ else none⟩
private theorem lookup : DecodedArrayAt c 11 3 fixed_len xs := rfl

/-- A nonzero-offset static array has typed reference contents, not Bool leaves. -/
theorem reference_slice : decodedArraySlice xs 1 3 = [ref 42, ref 37] := rfl

/-- Generic slice/read transport applies to an actual static reference array. -/
theorem reference_read :
    ∃ v, (decodedArraySlice xs 1 3)[0]? = some v ∧
      DecodedArrayRead c 11 T (some 3) 1 v :=
  decodedArraySlice_read lookup ⟨by decide, by decide⟩ (by decide)

/-- Repeated child identities remain repeated in the immutable decoded object. -/
theorem shared_identity :
    DecodedArrayRead c 11 T (some 3) 0 (ref 37) ∧
    DecodedArrayRead c 11 T (some 3) 2 (ref 37) :=
  ⟨(decodedArrayRead_iff lookup _).mpr ⟨by decide, rfl⟩,
    (decodedArrayRead_iff lookup _).mpr ⟨by decide, rfl⟩⟩

/-- A different calldata offset is not silently accepted as an alias. -/
theorem wrong_reference : ¬ DecodedArrayRead c 11 T (some 3) 0 (ref 38) := by
  intro h
  obtain ⟨hi, hv⟩ := (decodedArrayRead_iff lookup _).mp h
  change ref 37 = ref 38 at hv
  cases hv

theorem endpoint_failure : ¬ DecodedArrayRead c 11 T (some 3) 3 (ref 37) :=
  decodedArrayRead_overrun lookup (by decide) _

theorem empty_end : decodedArraySlice xs 3 3 = [] := rfl

theorem nested_coordinates :
    ((decodedArraySlice xs 0 3).drop 1).take (3 - 1) = decodedArraySlice xs 1 3 :=
  decodedArraySlice_compose xs ⟨by decide, by decide⟩ ⟨by decide, by decide⟩

private theorem dynamic_len (len : Nat) : ∀ m, (none : Option Nat) = some m → m = len := by
  intro m h
  cases h
private def row (b : Bool) : Source.Data D T :=
  .array 2 (dynamic_len 2) (fun i => .val (.bool (if i.val = 0 then b else false)))
private def rows (i : Fin 2) : Source.Data D T := row (i.val = 0)
private def nested : Source.Calldata D := ⟨[], fun off => if off = 23 then
  some ⟨.array .calldata T none, .array 2 (dynamic_len 2) rows⟩ else none⟩
private theorem nested_lookup : DecodedArrayAt nested 23 2 (dynamic_len 2) rows := rfl

/-- Generic reads also preserve an actual nested typed array constructor. -/
theorem nested_contents :
    decodedArraySlice rows 0 2 = [row true, row false] ∧
    DecodedArrayRead nested 23 T none 0 (row true) :=
  ⟨rfl, (decodedArrayRead_iff nested_lookup _).mpr ⟨by decide, rfl⟩⟩

private def noElems : Fin 0 → Source.Data D T := Fin.elim0
private def emptyInput : Source.Calldata D := ⟨[], fun _ =>
  some ⟨.array .calldata T none, .array 0 (dynamic_len 0) noElems⟩⟩
theorem empty_source :
    decodedArraySlice noElems 0 0 = [] ∧
    ¬ DecodedArrayRead emptyInput 0 T none 0 (ref 37) :=
  ⟨rfl, decodedArrayRead_overrun
    (show DecodedArrayAt emptyInput 0 0 (dynamic_len 0) noElems from rfl) (by decide) _⟩

/-- The earlier Boolean observation is definitionally the generic observation;
this extension introduces no competing read semantics. -/
theorem bool_observation_compatibility {D' : Source.Layout} (input : Source.Calldata D')
    (off i : Nat) (b : Bool) :
    DecodedBoolRead input off i b ↔
      DecodedArrayRead input off .bool none i (.val (.bool b)) := Iff.rfl

/-- info: 'Solidity.Backend.MemoryOps.ArrayControls.bool_observation_compatibility' does not depend on any axioms -/
#guard_msgs in #print axioms bool_observation_compatibility
/-- info: 'Solidity.Backend.MemoryOps.ArrayControls.reference_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reference_read
/-- info: 'Solidity.Backend.MemoryOps.ArrayControls.shared_identity' does not depend on any axioms -/
#guard_msgs in #print axioms shared_identity
/-- info: 'Solidity.Backend.MemoryOps.ArrayControls.wrong_reference' depends on axioms: [propext] -/
#guard_msgs in #print axioms wrong_reference
/-- info: 'Solidity.Backend.MemoryOps.ArrayControls.endpoint_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms endpoint_failure
/-- info: 'Solidity.Backend.MemoryOps.ArrayControls.nested_coordinates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nested_coordinates
/-- info: 'Solidity.Backend.MemoryOps.ArrayControls.nested_contents' does not depend on any axioms -/
#guard_msgs in #print axioms nested_contents
/-- info: 'Solidity.Backend.MemoryOps.ArrayControls.empty_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_source
end Solidity.Backend.MemoryOps.ArrayControls

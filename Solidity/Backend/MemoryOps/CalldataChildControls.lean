import Solidity.Backend.MemoryOps.CalldataChildExtension

/-! Inhabited arbitrary-length reference families, repeated aliases and failures
of initial-to-final correspondence when the destination is a represented child. -/
namespace Solidity.Backend.MemoryOps.ChildControls
private def D : Source.Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
private abbrev B := BoolChildRef
private abbrev P : RefTy := .array (.ref B)
private abbrev H : HTy := [B, B, P]
private def first : HRef H B := ⟨0, rfl⟩
private def second : HRef H B := ⟨1, rfl⟩
private def parent : HRef H P := ⟨2, rfl⟩
private def address (i : Nat) := if i = 0 then 37 else if i = 1 then 42 else 70
private def sourceRef (off : Nat) : Source.Data D BoolChildTy := .val (.cdRef rfl off)
private def input (values : List (HRef H B)) : Source.Calldata D := ⟨[], fun off =>
  if off = 7 then some ⟨RefChildTy, decodedChildRefs address values⟩ else
  if off = 37 then some ⟨BoolChildTy, decodedBools [true]⟩ else
  if off = 42 then some ⟨BoolChildTy, decodedBools [false]⟩ else none⟩
private def heap (values : List (HRef H B)) (hv : values.length < 2 ^ 256) : Heap H :=
  (⟨[true], by decide⟩, ⟨[false], by decide⟩,
    ⟨List.replicate values.length first, by simpa only [List.length_replicate] using hv⟩, ())
private theorem refs (r : HRef H B) : r = first ∨ r = second := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact .inl rfl
  | succ i => cases i with
    | zero => cases hi; exact .inr rfl
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases hi
private theorem child_repr (values : List (HRef H B)) (hv : values.length < 2 ^ 256)
    (r : HRef H B) : BoolChildRepr (input values) address (heap values hv)
      (sourceRef (address r.id)) r := by
  rcases refs r with rfl | rfl <;> constructor
  all_goals first | rfl | simp only [MObj.elems_dyn]; rfl
private theorem space (values : List (HRef H B)) (hv : values.length < 2 ^ 256) :
    0 + ((values.drop 0).take (values.length - 0)).length ≤ (heap values hv).len parent .dyn := by
  simp only [Heap.len, MObj.elems_dyn, List.drop_zero,
    Nat.sub_zero, List.take_length, Nat.zero_add]
  change values.length ≤ (List.replicate values.length first).length
  rw [List.length_replicate]
  exact Nat.le_refl _
private def out (values : List (HRef H B)) (hv : values.length < 2 ^ 256) :=
  overwriteSlice (heap values hv) parent .dyn 0 ((values.drop 0).take (values.length - 0)) (space values hv)

/-- An inhabited family for every existing typed-array length, not just two
constants; representation and separation premises are proved for all elements. -/
theorem arbitrary_family (values : List (HRef H B)) (hv : values.length < 2 ^ 256)
    (i : Nat) (hi : i < values.length) :
    (MObj.elems .dyn ((out values hv).get parent))[i]? = some values[i] ∧
    BoolChildRepr (input values) address (out values hv) (sourceRef (address values[i].id)) values[i] := by
  have h := decodedBoolChildren_overwrite
    (show DecodedArrayAt (input values) 7 values.length (fun _ h => by cases h)
      (fun j => sourceRef (address values[j].id)) from rfl)
    (heap values hv) parent .dyn values rfl (fun j => child_repr values hv values[j])
    0 0 values.length ⟨Nat.zero_le _, Nat.le_refl _⟩ (space values hv)
    i (by simpa only [Nat.sub_zero] using hi)
  simpa only [Nat.zero_add] using h.2

private theorem address_injective (r q : HRef H B) (he : address r.id = address q.id) : r.id = q.id := by
  rcases refs r with rfl | rfl <;> rcases refs q with rfl | rfl
  · rfl
  · change 37 = 42 at he; cases he
  · change 42 = 37 at he; cases he
  · rfl
/-- Alias equivalence is inhabited for arbitrary lists with this independently
injective address assignment, including repeated positions. -/
theorem family_alias_iff (values : List (HRef H B)) (hv : values.length < 2 ^ 256)
    (i j : Nat) (hi : i < values.length) (hj : j < values.length) :
    sourceRef (address values[i].id) = sourceRef (address values[j].id) ↔ values[i].id = values[j].id :=
  ((arbitrary_family values hv i hi).2).alias_iff (arbitrary_family values hv j hj).2 address_injective

private def extensionObject : MObj H B := ⟨[false, true], by decide⟩
/-- Published allocation discharges growth for every represented output element;
the old child remains distinct from a fresh object of the same type. -/
theorem family_allocation (values : List (HRef H B)) (hv : values.length < 2 ^ 256)
    (i : Nat) (hi : i < values.length) :
    BoolChildRepr (input values) address ((out values hv).alloc extensionObject).1
      (sourceRef (address values[i].id)) (values[i].wk (List.prefix_append H [B])) ∧
    (values[i].wk (List.prefix_append H [B])).id ≠ ((out values hv).alloc extensionObject).2.id :=
  ⟨((arbitrary_family values hv i hi).2).grow _ (Heap.keeps_alloc _ _),
    old_ne_fresh (out values hv) extensionObject values[i]⟩
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.family_allocation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms family_allocation

private def sample : List (HRef H B) := [second, first, second]
private theorem sample_size : sample.length < 2 ^ 256 := by decide
/-- The nonempty parent genuinely changes and retains a repeated shared child. -/
theorem changed_shared :
    (MObj.elems .dyn ((heap sample sample_size).get parent)).map HRef.id = [0, 0, 0] ∧
    (MObj.elems .dyn ((out sample sample_size).get parent)).map HRef.id = [1, 0, 1] ∧
    BoolChildRepr (input sample) address (out sample sample_size) (sourceRef 42) second := by
  refine ⟨?_, ?_, (arbitrary_family sample sample_size 0 (by decide)).2⟩
  · simp only [MObj.elems_dyn]; rfl
  · rw [out, overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl

theorem repeated_identity :
    BoolChildRepr (input sample) address (out sample sample_size) (sourceRef 42) sample[0] ∧
    BoolChildRepr (input sample) address (out sample sample_size) (sourceRef 42) sample[2] :=
  ⟨(arbitrary_family sample sample_size 0 (by decide)).2,
    (arbitrary_family sample sample_size 2 (by decide)).2⟩

theorem empty_and_end :
    out [] (by decide) = heap [] (by decide) ∧
    overwriteSlice (heap sample sample_size) parent .dyn 3 ((sample.drop 3).take (3 - 3))
      (by simp only [Nat.sub_self, List.take_zero, List.length_nil, Nat.add_zero, Heap.len, MObj.elems_dyn]; decide) =
      heap sample sample_size := by
  constructor
  · exact referenceSlice_empty (heap [] (by decide)) parent .dyn [] 0 0 (Nat.zero_le _)
  · exact referenceSlice_empty (heap sample sample_size) parent .dyn sample 3 3
      (by simp only [Heap.len, MObj.elems_dyn]; decide)

private def missing : Source.Calldata D := ⟨[], fun off => if off = 42 then none else (input sample).objects off⟩
theorem missing_child : ¬ BoolChildRepr missing address (heap sample sample_size) (sourceRef 42) second := by
  intro h
  have ho := h.2
  change none = some _ at ho
  cases ho

theorem wrong_offset : ¬ BoolChildRepr (input sample) address (heap sample sample_size) (sourceRef 37) second := by
  intro h
  have he := h.1
  change sourceRef 37 = sourceRef 42 at he
  cases he
private def wrong : Source.Calldata D := ⟨[], fun off => if off = 42 then some ⟨BoolChildTy, decodedBools [true]⟩ else (input sample).objects off⟩
theorem wrong_contents : ¬ BoolChildRepr wrong address (heap sample sample_size) (sourceRef 42) second := by
  intro h
  have hr := decodedBoolArray_read (show DecodedBoolArray wrong 42 [true] from rfl) 0 (by decide)
  have he := (h.read_iff 0 true).mp hr
  simp only [MObj.elems_dyn] at he
  change some false = some true at he
  cases he

private abbrev AliasH : HTy := [B]
private def aliasRef : HRef AliasH B := ⟨0, rfl⟩
private def aliasHeap : Heap AliasH := (⟨[true], by decide⟩, ())
private def aliasInput : Source.Calldata D := ⟨[], fun _ => some ⟨BoolChildTy, decodedBools [true]⟩⟩
private def aliasOut := overwriteSlice aliasHeap aliasRef .dyn 0 [false]
  (by simp only [Heap.len, MObj.elems_dyn]; decide)
/-- Same-object writes may invalidate child contents: initial correspondence
alone cannot establish output correspondence. This remains an admitted case. -/
theorem aliased_destination_negative :
    BoolChildRepr aliasInput (fun _ => 37) aliasHeap (sourceRef 37) aliasRef ∧
    ¬ BoolChildRepr aliasInput (fun _ => 37) aliasOut (sourceRef 37) aliasRef := by
  constructor
  · constructor
    · rfl
    · simp only [MObj.elems_dyn]; rfl
  · intro h
    have hr := decodedBoolArray_read (show DecodedBoolArray aliasInput 37 [true] from rfl) 0 (by decide)
    have he := (h.read_iff 0 true).mp hr
    rw [aliasOut, overwriteSlice_elems] at he
    simp only [MObj.elems_dyn] at he
    change some false = some true at he
    cases he

private def collisionHeap : Heap H :=
  (⟨[true], by decide⟩, ⟨[true], by decide⟩, ⟨[], by decide⟩, ())
private def collisionInput : Source.Calldata D := ⟨[], fun _ => some ⟨BoolChildTy, decodedBools [true]⟩⟩
/-- Without injectivity, equal source offsets can correspond to distinct heap
identities even though both content relations hold. -/
theorem collision_negative :
    BoolChildRepr collisionInput (fun _ => 37) collisionHeap (sourceRef 37) first ∧
    BoolChildRepr collisionInput (fun _ => 37) collisionHeap (sourceRef 37) second ∧ first.id ≠ second.id := by
  refine ⟨?_, ?_, by decide⟩
  all_goals constructor
  all_goals first | rfl | simp only [MObj.elems_dyn]; rfl

/-- info: 'Solidity.Backend.MemoryOps.ChildControls.family_alias_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms family_alias_iff
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.collision_negative' depends on axioms: [propext] -/
#guard_msgs in #print axioms collision_negative

/-- Child failures are isolated: both perturbed tables retain the valid root. -/
theorem root_retained : missing.objects 7 = (input sample).objects 7 ∧
    wrong.objects 7 = (input sample).objects 7 ∧
    missing.objects 37 = (input sample).objects 37 := ⟨rfl, rfl, rfl⟩
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.root_retained' depends on axioms: [propext] -/
#guard_msgs in #print axioms root_retained

/-- info: 'Solidity.Backend.MemoryOps.ChildControls.arbitrary_family' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms arbitrary_family
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.changed_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms changed_shared
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.repeated_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms repeated_identity
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.empty_and_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_and_end
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.missing_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms missing_child
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.wrong_offset' depends on axioms: [propext] -/
#guard_msgs in #print axioms wrong_offset
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.wrong_contents' depends on axioms: [propext] -/
#guard_msgs in #print axioms wrong_contents
/-- info: 'Solidity.Backend.MemoryOps.ChildControls.aliased_destination_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms aliased_destination_negative
end Solidity.Backend.MemoryOps.ChildControls

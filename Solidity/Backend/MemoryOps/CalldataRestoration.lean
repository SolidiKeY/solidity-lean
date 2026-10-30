import Solidity.Backend.MemoryOps.OverwriteRestoration

/-! Exact restoration for the EXISTING decoded Boolean sequence. Payloads and
both reached capacities come from actual operation success, never caller
conversion certificates. Intermediate child mutation is allowed. -/
namespace Solidity.Backend.MemoryOps

/-- Initial reads compared only with the actual immutable table extractions. -/
def BoolSequenceRestores {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d u v f : Nat) : Prop :=
  match calldataBools c off, calldataBools c' off' with
  | some bs, some cs => LastWriteAgrees (MObj.elems a (hp.get r))
      d ((bs.drop s).take (t-s)) f ((cs.drop u).take (v-u))
  | _, _ => False

/-- Both real payloads and bounds are reconstructed from the actual reached
heaps. The second capacity is derived back to the unchanged initial length. -/
theorem boolSequence_same_result_lookup {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d u v f : Nat)
    (out : Heap H)
    (ho : checkedBoolSequence c off c' off' hp r a s t d r a u v f = some out) :
    ∃ bs cs : List Bool, calldataBools c off = some bs ∧ calldataBools c' off' = some cs ∧
      ∃ (_hs : SliceBounds bs.length s t) (_hu : SliceBounds cs.length u v)
        (hd : d+((bs.drop s).take (t-s)).length ≤ hp.len r a)
        (he : f+((cs.drop u).take (v-u)).length ≤ hp.len r a),
        out = overwriteIntervals hp r a d ((bs.drop s).take (t-s)) hd f ((cs.drop u).take (v-u)) he := by
  obtain ⟨mid,hfirst,hsecond⟩ := (checkedBoolSequence_some_iff c off c' off' hp r a s t d r a u v f out).mp ho
  obtain ⟨bs,hb,hs,hd,rfl⟩ := boolTransfer_result_lookup c off hp r a s t d mid hfirst
  obtain ⟨cs,hc,hu,he,rfl⟩ := boolTransfer_result_lookup c' off' _ r a u v f out hsecond
  have he' : f+((cs.drop u).take (v-u)).length ≤ hp.len r a := by
    rw [overwriteSlice_len] at he; exact he
  exact ⟨bs,cs,hb,hc,hs,hu,hd,he',rfl⟩

theorem boolSequence_target_restore_iff {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d u v f : Nat)
    (out : Heap H)
    (ho : checkedBoolSequence c off c' off' hp r a s t d r a u v f = some out) :
    out.get r = hp.get r ↔ BoolSequenceRestores c off c' off' hp r a s t d u v f := by
  obtain ⟨bs,cs,hb,hc,_,_,hd,he,rfl⟩ := boolSequence_same_result_lookup c off c' off' hp r a s t d u v f out ho
  unfold BoolSequenceRestores
  rw [hb,hc]
  exact overwriteIntervals_target_eq_iff hp r a d _ hd f _ he

theorem boolSequence_heap_restore_iff {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d u v f : Nat)
    (out : Heap H)
    (ho : checkedBoolSequence c off c' off' hp r a s t d r a u v f = some out) :
    out = hp ↔ BoolSequenceRestores c off c' off' hp r a s t d u v f := by
  obtain ⟨bs,cs,hb,hc,_,_,hd,he,rfl⟩ := boolSequence_same_result_lookup c off c' off' hp r a s t d u v f out ho
  unfold BoolSequenceRestores
  rw [hb,hc]
  exact overwriteIntervals_eq_self_iff hp r a d _ hd f _ he

theorem boolSequence_same_frame_lookup {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d u v f : Nat)
    (out : Heap H)
    (ho : checkedBoolSequence c off c' off' hp r a s t d r a u v f = some out)
    (q : HRef H Q) (hne : r.id ≠ q.id) : out.get q = hp.get q := by
  obtain ⟨_,_,_,_,_,_,hd,he,rfl⟩ := boolSequence_same_result_lookup c off c' off' hp r a s t d u v f out ho
  exact overwriteIntervals_frame hp r a d _ hd f _ he q hne

/-- Exact final correspondence, without requiring correspondence at mid. -/
theorem BoolChildRepr.sequence_restore_iff {D : Source.Layout} {H : HTy}
    {table : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {child : HRef H BoolChildRef}
    (hi : BoolChildRepr table address hp sv child)
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (s t d u v f : Nat) (out : Heap H)
    (ho : checkedBoolSequence c off c' off' hp child .dyn s t d child .dyn u v f = some out) :
    BoolChildRepr table address out sv child ↔ BoolSequenceRestores c off c' off' hp child .dyn s t d u v f := by
  rw [hi.at_heap_iff out]
  exact boolSequence_target_restore_iff c off c' off' hp child .dyn s t d u v f out ho

/-- Local leaf framing OR actual final restoration permits a selected alias. -/
theorem BoolChildRepr.sequence_frame_restore {D : Source.Layout} {H : HTy} {R : RefTy}
    {table : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {child : HRef H BoolChildRef}
    (hi : BoolChildRepr table address hp sv child)
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d u v f : Nat) (out : Heap H)
    (ho : checkedBoolSequence c off c' off' hp r a s t d r a u v f = some out)
    (hlocal : r.id ≠ child.id ∨ BoolSequenceRestores c off c' off' hp r a s t d u v f) :
    BoolChildRepr table address out sv child := by
  rcases hlocal with hne | ha
  · exact ⟨hi.1,by rw [boolSequence_same_frame_lookup c off c' off' hp r a s t d u v f out ho child hne]; exact hi.2⟩
  · rw [(boolSequence_heap_restore_iff c off c' off' hp r a s t d u v f out ho).mpr ha]
    exact hi

/-- The initial reference-root table and repeated old leaf identities survive
at the final heap. A selected alias may be broken at mid and restored later. -/
theorem RefChildRepr.sequence_restore {D : Source.Layout} {H : HTy} {R : RefTy}
    {table : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D RefChildTy} {root : HRef H RefChildRef}
    (hi : RefChildRepr table address hp sv root)
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d u v f : Nat) (out : Heap H)
    (ho : checkedBoolSequence c off c' off' hp r a s t d r a u v f = some out)
    (hleaves : ∀ leaf ∈ MObj.elems .dyn (hp.get root),
      r.id ≠ leaf.id ∨ BoolSequenceRestores c off c' off' hp r a s t d u v f) :
    RefChildRepr table address out sv root := by
  have hf : out.get root = hp.get root := boolSequence_same_frame_lookup c off c' off' hp r a s t d u v f out ho root
    (primitiveTransfer_ref_root_ne r a root)
  refine ⟨hi.1,?_,?_⟩
  · rw [hf]; exact hi.2.1
  · intro leaf hl
    rw [hf] at hl
    exact (hi.2.2 leaf hl).sequence_frame_restore c off c' off' r a s t d u v f out ho (hleaves leaf hl)

/-- info: 'Solidity.Backend.MemoryOps.boolSequence_same_result_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms boolSequence_same_result_lookup
/-- info: 'Solidity.Backend.MemoryOps.boolSequence_target_restore_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolSequence_target_restore_iff
/-- info: 'Solidity.Backend.MemoryOps.boolSequence_heap_restore_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolSequence_heap_restore_iff
/-- info: 'Solidity.Backend.MemoryOps.boolSequence_same_frame_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms boolSequence_same_frame_lookup
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.sequence_restore_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.sequence_restore_iff
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.sequence_frame_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.sequence_frame_restore
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.sequence_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.sequence_restore
end Solidity.Backend.MemoryOps

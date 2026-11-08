import Solidity.Backend.MemoryOps.MixedCalldataSequence
import Solidity.Backend.MemoryOps.CalldataNestedChildren

/-! Existing immutable child-table correspondence at actual sequence outputs.
Initial relations are inhabited separately; no fresh Source entries or reverse
address injectivity are assumed. Alias writes are supported, including an empty
aliased transfer; nonempty aliased mutation need not preserve correspondence. -/
namespace Solidity.Backend.MemoryOps

set_option backward.isDefEq.respectTransparency false in
/-- Distinct object or empty interval is sufficient for actual object framing. -/
theorem boolTransfer_frame_or_empty {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (out : Heap H)
    (ho : checkedCalldataBools c off hp r a s t d = some out)
    (q : HRef H Q) (hsep : r.id ≠ q.id ∨ s = t) : out.get q = hp.get q := by
  obtain ⟨_,_,_,hd,rfl⟩ := boolTransfer_result_lookup c off hp r a s t d out ho
  rcases hsep with hne | he
  · exact overwriteSlice_frame hp r q a d _ hd hne
  · cases he
    simp only [Nat.sub_self,List.take_zero,overwriteSlice_empty]

set_option backward.isDefEq.respectTransparency false in
theorem uintTransfer_frame_or_empty {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (s t d : Nat) (out : Heap H)
    (ho : checkedCalldataUints c off hp r a s t d = some out)
    (q : HRef H Q) (hsep : r.id ≠ q.id ∨ s = t) : out.get q = hp.get q := by
  obtain ⟨_,_,_,hd,rfl⟩ := uintTransfer_result_lookup c off hp r a s t d out ho
  rcases hsep with hne | he
  · exact overwriteSlice_frame hp r q a d _ hd hne
  · cases he
    simp only [Nat.sub_self,List.take_zero,overwriteSlice_empty]

/-- No initial decoded-array premise is needed: actual success reconstructs
both actual operations before framing any typed observation. -/
theorem mixedTransfer_frame_or_empty {D : Source.Layout} {H : HTy} {R Q T : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H)
    (ho : checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out)
    (k : HRef H T) (hr : r.id ≠ k.id ∨ s = t) (hq : q.id ≠ k.id ∨ u = v) :
    out.get k = hp.get k := by
  obtain ⟨mid,hfirst,hsecond⟩ := (checkedBoolUintSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  exact (uintTransfer_frame_or_empty c' off' mid q b u v f out hsecond k hq).trans
    (boolTransfer_frame_or_empty c off hp r a s t d mid hfirst k hr)

/-- Primitive targets cannot be an existing reference-array root. -/
theorem primitiveTransfer_ref_root_ne {H : HTy} {R : RefTy} {p : PrimTy}
    (r : HRef H R) (a : ArrTy R (.prim p)) (root : HRef H RefChildRef) : r.id ≠ root.id := by
  intro he
  have ht := (HRef.heq_of_id r root he).1
  cases a <;> cases ht

/-- Correspondence is about the final heap, derived from the real sequence
frame. The Boolean destination may alias the child if its interval is empty. -/
theorem BoolChildRepr.mixedSequence {D : Source.Layout} {H : HTy} {R Q : RefTy}
    {childTable : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {child : HRef H BoolChildRef}
    (hi : BoolChildRepr childTable address hp sv child)
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H)
    (ho : checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out)
    (hsep : r.id ≠ child.id ∨ s = t) :
    BoolChildRepr childTable address out sv child := by
  refine ⟨hi.1,?_⟩
  rw [mixedTransfer_frame_or_empty c off c' off' hp r a s t d q b u v f out ho child hsep
    (Or.inl (bool_uint_transfer_ne child .dyn q b).symm)]
  exact hi.2

/-- Arbitrary runtime child lists and repeated aliases retain final-heap
contents. Root separation is type-derived; each Boolean leaf must be framed or
the first interval empty. This local sufficient case is not a Source exclusion. -/
theorem RefChildRepr.mixedSequence {D : Source.Layout} {H : HTy} {R Q : RefTy}
    {childTable : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D RefChildTy} {root : HRef H RefChildRef}
    (hi : RefChildRepr childTable address hp sv root)
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H)
    (ho : checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out)
    (hleaves : ∀ leaf ∈ MObj.elems .dyn (hp.get root), r.id ≠ leaf.id ∨ s = t) :
    RefChildRepr childTable address out sv root := by
  have hf : out.get root = hp.get root := mixedTransfer_frame_or_empty c off c' off' hp r a s t d q b u v f out ho root
    (Or.inl (primitiveTransfer_ref_root_ne r a root)) (Or.inl (primitiveTransfer_ref_root_ne q b root))
  refine ⟨hi.1,?_,?_⟩
  · rw [hf]; exact hi.2.1
  · intro leaf hl
    rw [hf] at hl
    exact (hi.2.2 leaf hl).mixedSequence c off c' off' r a s t d q b u v f out ho (hleaves leaf hl)

/-- info: 'Solidity.Backend.MemoryOps.boolTransfer_frame_or_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms boolTransfer_frame_or_empty
/-- info: 'Solidity.Backend.MemoryOps.uintTransfer_frame_or_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uintTransfer_frame_or_empty
/-- info: 'Solidity.Backend.MemoryOps.mixedTransfer_frame_or_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mixedTransfer_frame_or_empty
/-- info: 'Solidity.Backend.MemoryOps.primitiveTransfer_ref_root_ne' does not depend on any axioms -/
#guard_msgs in #print axioms primitiveTransfer_ref_root_ne
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.mixedSequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.mixedSequence
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.mixedSequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.mixedSequence
end Solidity.Backend.MemoryOps

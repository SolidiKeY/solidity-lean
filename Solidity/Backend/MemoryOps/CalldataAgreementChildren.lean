import Solidity.Backend.MemoryOps.OverwriteAgreement

/-! Refine actual child footprint transport with INITIAL computed-payload
agreement. Nonempty aliases are supported; changed-payload aliases need not
preserve correspondence. Reverse order reuses existing full-heap commutation. -/
namespace Solidity.Backend.MemoryOps

theorem boolTransfer_frame_agrees {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (out : Heap H)
    (ho : checkedCalldataBools c off hp r a s t d = some out)
    (q : HRef H Q)
    (hs : r.id ≠ q.id ∨ s = t ∨ BoolTransferAgrees c off hp r a s t d) : out.get q = hp.get q := by
  rcases hs with hne | he | ha
  · exact boolTransfer_frame_or_empty c off hp r a s t d out ho q (Or.inl hne)
  · exact boolTransfer_frame_or_empty c off hp r a s t d out ho q (Or.inr he)
  · rw [boolTransfer_eq_self_of_agrees c off hp r a s t d out ho ha]

theorem mixedTransfer_frame_agrees {D : Source.Layout} {H : HTy} {R Q T : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H)
    (ho : checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out)
    (k : HRef H T)
    (hr : r.id ≠ k.id ∨ s = t ∨ BoolTransferAgrees c off hp r a s t d)
    (hq : q.id ≠ k.id ∨ u = v) : out.get k = hp.get k := by
  obtain ⟨mid,hfirst,hsecond⟩ := (checkedBoolUintSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  exact (uintTransfer_frame_or_empty c' off' mid q b u v f out hsecond k hq).trans
    (boolTransfer_frame_agrees c off hp r a s t d mid hfirst k hr)

theorem BoolChildRepr.mixedSequence_agrees {D : Source.Layout} {H : HTy} {R Q : RefTy}
    {childTable : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {child : HRef H BoolChildRef}
    (hi : BoolChildRepr childTable address hp sv child)
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H)
    (ho : checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out)
    (hs : r.id ≠ child.id ∨ s = t ∨ BoolTransferAgrees c off hp r a s t d) :
    BoolChildRepr childTable address out sv child := by
  refine ⟨hi.1,?_⟩
  rw [mixedTransfer_frame_agrees c off c' off' hp r a s t d q b u v f out ho child hs
    (Or.inl (bool_uint_transfer_ne child .dyn q b).symm)]
  exact hi.2

theorem RefChildRepr.mixedSequence_agrees {D : Source.Layout} {H : HTy} {R Q : RefTy}
    {childTable : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D RefChildTy} {root : HRef H RefChildRef}
    (hi : RefChildRepr childTable address hp sv root)
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H)
    (ho : checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out)
    (hleaves : ∀ leaf ∈ MObj.elems .dyn (hp.get root),
      r.id ≠ leaf.id ∨ s = t ∨ BoolTransferAgrees c off hp r a s t d) :
    RefChildRepr childTable address out sv root := by
  have hf : out.get root = hp.get root := mixedTransfer_frame_or_empty c off c' off' hp r a s t d q b u v f out ho root
    (Or.inl (primitiveTransfer_ref_root_ne r a root)) (Or.inl (primitiveTransfer_ref_root_ne q b root))
  refine ⟨hi.1,?_,?_⟩
  · rw [hf]; exact hi.2.1
  · intro leaf hl
    rw [hf] at hl
    exact (hi.2.2 leaf hl).mixedSequence_agrees c off c' off' r a s t d q b u v f out ho (hleaves leaf hl)

/-- Actual reverse success supplies the source/target bounds required by the
EXISTING mixed commutation law. No second interpreter or commutation proof. -/
theorem checkedReverse_as_forward {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H)
    (ho : checkedUintBoolSequence c' off' c off hp q b u v f r a s t d = some out) :
    checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out := by
  obtain ⟨mid,hfirst,hsecond⟩ := (checkedUintBoolSequence_some_iff c' off' c off hp q b u v f r a s t d out).mp ho
  obtain ⟨hu,hdu,_⟩ := checkedCalldataUints_result hc' hp q b u v f mid hfirst
  obtain ⟨hs,hdb,_⟩ := checkedCalldataBools_result hc mid r a s t d out hsecond
  have hd : d+(t-s) ≤ hp.len r a := by
    rw [←uintTransfer_all_len c' off' hp q b u v f mid hfirst r a,←calldataBools_slice_length xs hs]
    exact hdb
  have he : f+(v-u) ≤ hp.len q b := by
    rw [←calldataUints_slice_length ys hu]
    exact hdu
  exact (checkedBoolUintSequence_comm hc hc' hp r a s t d q b u v f hs hd hu he).trans ho

theorem RefChildRepr.reverseMixedSequence_agrees {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} {hp : Heap H} {childTable : Source.Calldata D} {address : Nat → Nat}
    {sv : Source.Data D RefChildTy} {root : HRef H RefChildRef}
    (hi : RefChildRepr childTable address hp sv root)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H)
    (ho : checkedUintBoolSequence c' off' c off hp q b u v f r a s t d = some out)
    (hleaves : ∀ leaf ∈ MObj.elems .dyn (hp.get root),
      r.id ≠ leaf.id ∨ s = t ∨ BoolTransferAgrees c off hp r a s t d) :
    RefChildRepr childTable address out sv root :=
  hi.mixedSequence_agrees c off c' off' r a s t d q b u v f out
    (checkedReverse_as_forward hc hc' hp r a s t d q b u v f out ho) hleaves

/-- info: 'Solidity.Backend.MemoryOps.boolTransfer_frame_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolTransfer_frame_agrees
/-- info: 'Solidity.Backend.MemoryOps.mixedTransfer_frame_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mixedTransfer_frame_agrees
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.mixedSequence_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.mixedSequence_agrees
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.mixedSequence_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.mixedSequence_agrees
/-- info: 'Solidity.Backend.MemoryOps.checkedReverse_as_forward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedReverse_as_forward
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.reverseMixedSequence_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.reverseMixedSequence_agrees
end Solidity.Backend.MemoryOps

import Solidity.Yul.Views.ActualScalarReset
import Solidity.Source.WellTyped

/-! Preserve every original owner heap typing through actual typed writes,
including static refusal. Exact locals/heap preservation is separate from
retained-path coverage and physical/source adequacy, which are not inferred. -/
namespace Solidity.Yul.Views

theorem actualScalarWrite_MemOK {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (actualScalarWrite F path codec slot value raw s).1.2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  have safe := Source.writeAt_mem (H:=H) F path value s ok
  change Source.MemOK E H ((Source.writeAt F path value).run s).2
  cases actual : (Source.writeAt F path value).run s with
  | mk result after =>
    rw [actual] at safe
    cases result <;> exact safe

theorem actualScalarWrite_locals_heap {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ) :
    (actualScalarWrite F path codec slot value raw s).1.2.1=s.1 ∧
      (actualScalarWrite F path codec slot value raw s).1.2.2.heap=s.2.heap := by
  first | (simp only;done) | decide | omega | rfl | skip
  change ((Source.writeAt F path value).run s).2.1=s.1 ∧
    ((Source.writeAt F path value).run s).2.2.heap=s.2.heap
  cases bank : E.transientRoot path <;> cases mode : F.static <;>
    simp only [Source.writeAt,dite_true,Source.setCell,bank,Source.applyOp,mode,
      Bool.false_eq_true,if_false,if_true] <;> exact ⟨rfl,rfl⟩

/-- Execute the second actual write only if the first Source write succeeds. -/
def actualScalarWritePair {E Γ f g} (F K : Source.Fr) (path other : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (nextCodec : ScalarCodec E.layout (E.cellTy other) g)
    (slot nextSlot : Roadmap.Word) (value : Source.Val E.layout (E.cellTy path))
    (next : Source.Val E.layout (E.cellTy other)) (raw : SlotView) (s : Source.EMState E Γ) :=
  let first := actualScalarWrite F path codec slot value raw s
  match first.1.1 with
  | .error _ => first
  | .ok _ => actualScalarWrite K other nextCodec nextSlot next first.2 first.1.2

theorem actualScalarWritePair_source {E Γ f g} (F K : Source.Fr) (path other : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (nextCodec : ScalarCodec E.layout (E.cellTy other) g)
    (slot nextSlot : Roadmap.Word) (value : Source.Val E.layout (E.cellTy path))
    (next : Source.Val E.layout (E.cellTy other)) (raw : SlotView) (s : Source.EMState E Γ) :
    (actualScalarWritePair F K path other codec nextCodec slot nextSlot value next raw s).1=
      (do Source.writeAt F path value; Source.writeAt K other next).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [Source.Hoare.run_bind]
  unfold actualScalarWritePair actualScalarWrite
  cases actual : (Source.writeAt F path value).run s with
  | mk result after => cases result <;> rfl

/-- Every original H is retained through the actual short-circuiting pair. -/
theorem actualScalarWritePair_MemOK {E Γ f g} (F K : Source.Fr) (path other : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (nextCodec : ScalarCodec E.layout (E.cellTy other) g)
    (slot nextSlot : Roadmap.Word) (value : Source.Val E.layout (E.cellTy path))
    (next : Source.Val E.layout (E.cellTy other)) (raw : SlotView) (s : Source.EMState E Γ)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (actualScalarWritePair F K path other codec nextCodec slot nextSlot value next raw s).1.2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  have first := actualScalarWrite_MemOK F path codec slot value raw s H ok
  unfold actualScalarWritePair
  dsimp only
  split
  · exact first
  · exact actualScalarWrite_MemOK K other nextCodec nextSlot next _ _ H first
end Solidity.Yul.Views

import Solidity.Yul.Views.PathScalarSeparation
import Solidity.Yul.Views.ScalarDynamicValues

namespace Solidity.Yul.Views

/-- Actual source readback from a concrete successful scalar decoder. This is
not a caller-supplied inverse or read-adequacy law. -/
theorem PathScalarHeader.read_decoded {E root t cursor Γ} (h : PathScalarHeader E root t cursor)
    (F : Source.Fr) (s : Source.EMState E Γ) (fixed : Roadmap.Evm.Fixed) (i : Nat) (m : SlotView)
    (v : Source.Val E.layout (E.cellTy (h.elementPath i)))
    (decoded : (h.element fixed F.this i).codec.decode ((h.element fixed F.this i).field.findWord (m (h.element fixed F.this i).slot)) = some v)
    (bank : E.transientRoot (h.elementPath i) = false)
    (view : scalarPathView (h.element fixed F.this i).path (h.element fixed F.this i).codec
      (h.element fixed F.this i).slot (s.2.ex.world.accounts F.this).storage m) :
    (Source.readLoc F (Source.Loc.stor (τ := t.ty) (h.elementPath i))).run s =
      (.ok ((h.element_type i) ▸ v),s) := by
  obtain ⟨w,read,encoded⟩ := Option.map_eq_some_iff.mp view
  have inverse := (h.element fixed F.this i).codec.decode_encode w
  rw [encoded,decoded] at inverse
  have same := Option.some.inj inverse
  rw [← same] at read
  change (s.2.ex.world.accounts F.this).storage.read (h.elementPath i) = some v at read
  have raw : (Source.readCell F (h.elementPath i)).run s = (.ok v,s) := by
    unfold Source.readCell
    rw [Source.Hoare.run_bind,show (Source.EM.st (E := E) (Γ := Γ)).run s = (.ok s.2,s) from rfl]
    dsimp only
    rw [bank]
    simp only [Bool.false_eq_true,if_false,read]
    rfl
  have byRef : t.ty.byRef = false := by cases t <;> rfl
  simp only [Source.readLoc,byRef,Bool.false_eq_true,if_false]
  unfold Source.readAt
  rw [Source.Hoare.run_bind,raw]
  simp only [dif_pos (h.element_type i)]
  rfl

end Solidity.Yul.Views

import Solidity.Yul.Views.IntOwnershipBatch
import Solidity.Yul.Views.IntPayloadInverse
import Solidity.Yul.Views.PackedDynamicValues
import Solidity.Yul.Views.OwnershipElement

namespace Solidity.Yul.Views

def IntDynamicHeader.elementValue {E root t cursor} (h : IntDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) (m : Roadmap.Word) : Source.Val E.layout (E.cellTy (h.elementPath i)) :=
  have bound : ((h.element fixed a i).field.findWord m).val < 2^t.bits := by
    have bounded := ((h.element fixed a i).field.findWord m).isLt
    change ((h.element fixed a i).field.findWord m).val < (intField t ((i%h.perSlot)*h.byteWidth) (h.element_fits i)).modulus at bounded
    rw [intField_modulus] at bounded
    exact bounded
  Eq.mp (congrArg (Source.Val E.layout) (h.element_type i).symm)
    (integerStorageValue E.layout t _ bound)

theorem IntDynamicHeader.element_encode {E root t cursor} (h : IntDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) (m : Roadmap.Word) :
    (h.element fixed a i).codec.encode (h.elementValue fixed a i m) = (h.element fixed a i).field.findWord m := by
  have bound : ((h.element fixed a i).field.findWord m).val < 2^t.bits := by
    have bounded := ((h.element fixed a i).field.findWord m).isLt
    change ((h.element fixed a i).field.findWord m).val < (intField t ((i%h.perSlot)*h.byteWidth) (h.element_fits i)).modulus at bounded
    rw [intField_modulus] at bounded
    exact bounded
  have same := scalarCodec_transport_encode_mp (h.element_type i)
    (intCodec E.layout t ((i%h.perSlot)*h.byteWidth) (h.element_fits i))
    (integerStorageValue E.layout t _ bound)
  have transported : (h.element fixed a i).codec.encode (h.elementValue fixed a i m) =
      (intCodec E.layout t ((i%h.perSlot)*h.byteWidth) (h.element_fits i)).encode
        (integerStorageValue E.layout t _ bound) := same
  apply Fin.ext
  rw [transported]
  change intPayload t (readIntPayload t ((h.element fixed a i).field.findWord m).val) = ((h.element fixed a i).field.findWord m).val
  exact intPayload_readIntPayload t _ bound

theorem IntDynamicHeader.view_element_cell {E root t cursor} (h : IntDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) (s : Source.Storage E.layout (E.lay a)) (m : SlotView)
    (view : scalarPathView (h.element fixed a i).path (h.element fixed a i).codec (h.element fixed a i).slot s m) :
    s.read (h.elementPath i) = some (h.elementValue fixed a i (m (h.element fixed a i).slot)) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp view
  have same := (h.element fixed a i).codec.encode_injective (encoded.trans (h.element_encode fixed a i _).symm)
  rw [same] at read
  exact read

theorem IntDynamicHeader.read_element {E root t cursor Γ} (h : IntDynamicHeader E root t cursor)
    (F : Source.Fr) (s : Source.EMState E Γ) (fixed : Roadmap.Evm.Fixed) (i : Nat) (m : SlotView)
    (bank : E.transientRoot (h.elementPath i) = false)
    (view : scalarPathView (h.element fixed F.this i).path (h.element fixed F.this i).codec
      (h.element fixed F.this i).slot (s.2.ex.world.accounts F.this).storage m) :
    (Source.readLoc F (Source.Loc.stor (τ := .int t) (h.elementPath i))).run s =
      (.ok ((h.element_type i) ▸ h.elementValue fixed F.this i (m (h.element fixed F.this i).slot)),s) := by
  have cell := h.view_element_cell fixed F.this i _ m view
  have raw : (Source.readCell F (h.elementPath i)).run s =
      (.ok (h.elementValue fixed F.this i (m (h.element fixed F.this i).slot)),s) := by
    unfold Source.readCell
    rw [Source.Hoare.run_bind,show (Source.EM.st (E := E) (Γ := Γ)).run s = (.ok s.2,s) from rfl]
    dsimp only
    rw [bank]
    simp only [Bool.false_eq_true,if_false,cell]
    rfl
  change (Source.readAt F (h.elementPath i) (.int t)).run s = _
  unfold Source.readAt
  rw [Source.Hoare.run_bind,raw]
  simp only [dif_pos (h.element_type i)]
  rfl

end Solidity.Yul.Views

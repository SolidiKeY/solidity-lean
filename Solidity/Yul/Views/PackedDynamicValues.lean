import Solidity.Yul.Views.PackedOwnershipBatch
import Solidity.Yul.Views.OwnershipElement

namespace Solidity.Yul.Views

theorem scalarCodec_transport_encode_mp {D τ σ field} (e : τ = σ)
    (codec : ScalarCodec D σ field) (v : Source.Val D σ) :
    (Eq.mp (congrArg (fun t => ScalarCodec D t field) e.symm) codec).encode
      (Eq.mp (congrArg (Source.Val D) e.symm) v) = codec.encode v := by cases e; rfl

def unsignedStorageValue (D : Source.Layout) (t : Source.IntTy) (unsigned : t.signed = false)
    (n : Nat) (bound : n < 2^t.bits) : Source.Val D (.int t) :=
  .int n (by simp only [Source.IntTy.lo,Source.IntTy.hi,unsigned,Bool.false_eq_true,if_false]; omega)

def PackedDynamicHeader.elementValue {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) (m : Roadmap.Word) : Source.Val E.layout (E.cellTy (h.elementPath i)) :=
  have bound : ((h.element fixed a i).field.findWord m).val < 2^t.bits := by
    have bounded := ((h.element fixed a i).field.findWord m).isLt
    change ((h.element fixed a i).field.findWord m).val < (intField t ((i%h.perSlot)*h.byteWidth) (h.element_fits i)).modulus at bounded
    rw [intField_modulus] at bounded
    exact bounded
  Eq.mp (congrArg (Source.Val E.layout) (h.element_type i).symm)
    (unsignedStorageValue E.layout t h.unsigned _ bound)

theorem PackedDynamicHeader.element_encode {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) (m : Roadmap.Word) :
    (h.element fixed a i).codec.encode (h.elementValue fixed a i m) = (h.element fixed a i).field.findWord m := by
  have bound : ((h.element fixed a i).field.findWord m).val < 2^t.bits := by
    have bounded := ((h.element fixed a i).field.findWord m).isLt
    change ((h.element fixed a i).field.findWord m).val < (intField t ((i%h.perSlot)*h.byteWidth) (h.element_fits i)).modulus at bounded
    rw [intField_modulus] at bounded
    exact bounded
  have same := scalarCodec_transport_encode_mp (h.element_type i)
    (intCodec E.layout t ((i%h.perSlot)*h.byteWidth) (h.element_fits i))
    (unsignedStorageValue E.layout t h.unsigned _ bound)
  have transported : (h.element fixed a i).codec.encode (h.elementValue fixed a i m) =
      (intCodec E.layout t ((i%h.perSlot)*h.byteWidth) (h.element_fits i)).encode
        (unsignedStorageValue E.layout t h.unsigned _ bound) := same
  apply Fin.ext
  rw [transported]
  change intPayload t ((((h.element fixed a i).field.findWord m).val : Nat) : Int) = ((h.element fixed a i).field.findWord m).val
  have nonnegative : ¬((((h.element fixed a i).field.findWord m).val : Nat) : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg _)
  simp only [intPayload,if_neg nonnegative,Int.toNat_natCast]

theorem PackedDynamicHeader.view_element_cell {E root t cursor} (h : PackedDynamicHeader E root t cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) (s : Source.Storage E.layout (E.lay a)) (m : SlotView)
    (view : scalarPathView (h.element fixed a i).path (h.element fixed a i).codec (h.element fixed a i).slot s m) :
    s.read (h.elementPath i) = some (h.elementValue fixed a i (m (h.element fixed a i).slot)) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp view
  have same := (h.element fixed a i).codec.encode_injective (encoded.trans (h.element_encode fixed a i _).symm)
  rw [same] at read
  exact read

theorem PackedDynamicHeader.read_element {E root t cursor Γ} (h : PackedDynamicHeader E root t cursor)
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

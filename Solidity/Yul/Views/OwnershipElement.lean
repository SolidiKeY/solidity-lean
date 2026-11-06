import Solidity.Yul.Views.OwnershipBatch

namespace Solidity.Yul.Views

theorem scalarCodec_transport_encode {D τ σ field} (e : τ = σ)
    (codec : ScalarCodec D σ field) (v : Source.Val D σ) :
    (e.symm ▸ codec).encode (e.symm ▸ v) = codec.encode v := by cases e; rfl

def DynamicHeader.elementValue {E root cursor} (h : DynamicHeader E root cursor) (i : Nat) (n : Roadmap.Word) :
    Source.Val E.layout (E.cellTy (h.elementPath i)) := (h.element_type i).symm ▸ uintValueOfWord E.layout n

theorem DynamicHeader.element_encode {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat) (n : Roadmap.Word) :
    (h.element fixed a i).codec.encode (h.elementValue i n) = (h.element fixed a i).field.findWord n := by
  have same := scalarCodec_transport_encode (h.element_type i) (intCodec E.layout .u256 0 (by decide)) (uintValueOfWord E.layout n)
  apply Fin.ext
  rw [show (h.element fixed a i).codec.encode (h.elementValue i n) =
    (intCodec E.layout .u256 0 (by decide)).encode (uintValueOfWord E.layout n) from same]
  change intPayload .u256 (n.val : Int) = n.val / 256^0 % 256^32
  have power : 256^32 = 2^256 := by decide
  have nonnegative : ¬(n.val : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg _)
  simp only [intPayload,if_neg nonnegative,Int.toNat_natCast,Nat.pow_zero,Nat.div_one,power,Nat.mod_eq_of_lt n.isLt]

theorem DynamicHeader.view_element_cell {E root cursor} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address) (i : Nat)
    (s : Source.Storage E.layout (E.lay a)) (m : SlotView)
    (view : scalarPathView (h.element fixed a i).path (h.element fixed a i).codec (h.element fixed a i).slot s m) :
    s.read (h.elementPath i) = some (h.elementValue i (m (h.element fixed a i).slot)) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp view
  have same := (h.element fixed a i).codec.encode_injective (encoded.trans (h.element_encode fixed a i _).symm)
  rw [same] at read
  exact read

theorem DynamicHeader.read_element {E root cursor Γ} (h : DynamicHeader E root cursor)
    (F : Source.Fr) (s : Source.EMState E Γ) (fixed : Roadmap.Evm.Fixed) (i : Nat) (m : SlotView)
    (bank : E.transientRoot (h.elementPath i) = false)
    (view : scalarPathView (h.element fixed F.this i).path (h.element fixed F.this i).codec
      (h.element fixed F.this i).slot (s.2.ex.world.accounts F.this).storage m) :
    (Source.readLoc F (Source.Loc.stor (τ := .int .u256) (h.elementPath i))).run s =
      (.ok (uintValueOfWord E.layout (m (h.element fixed F.this i).slot)),s) := by
  have cell := h.view_element_cell fixed F.this i _ m view
  have raw : (Source.readCell F (h.elementPath i)).run s =
      (.ok (h.elementValue i (m (h.element fixed F.this i).slot)),s) := by
    unfold Source.readCell
    rw [Source.Hoare.run_bind,show (Source.EM.st (E := E) (Γ := Γ)).run s = (.ok s.2,s) from rfl]
    dsimp only
    rw [bank]
    simp only [Bool.false_eq_true,if_false,cell]
    rfl
  change (Source.readAt F (h.elementPath i) (.int .u256)).run s = _
  unfold Source.readAt
  rw [Source.Hoare.run_bind,raw]
  simp only [dif_pos (h.element_type i)]
  have cancel : (h.element_type i) ▸ h.elementValue i (m (h.element fixed F.this i).slot) =
      uintValueOfWord E.layout (m (h.element fixed F.this i).slot) := sourceVal_transport_cancel _ _
  change ((Except.ok ((h.element_type i) ▸ h.elementValue i (m (h.element fixed F.this i).slot)) : Except Source.Halt (Source.Val E.layout (.int .u256))),s) = _
  rw [cancel]

end Solidity.Yul.Views

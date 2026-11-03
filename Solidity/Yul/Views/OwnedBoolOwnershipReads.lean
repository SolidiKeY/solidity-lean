import Solidity.Yul.Views.OwnedBoolOwnershipFrame

namespace Solidity.Yul.Views

/-- Read the real Source location through the concrete physical codec. This
handles represented bool codecs without substituting the old canonical codec. -/
theorem representedScalar_readLoc {E Γ τ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (m : SlotView)
    (v : Source.Val E.layout (E.cellTy c.path))
    (decoded : c.codec.decode (c.field.findWord (m c.slot))=some v)
    (bank : E.transientRoot c.path=false) (typed : E.cellTy c.path=τ) (byValue : τ.byRef=false)
    (view : scalarPathView c.path c.codec c.slot (s.2.ex.world.accounts F.this).storage m) :
    (Source.readLoc F (Source.Loc.stor (τ:=τ) c.path)).run s=(.ok (typed ▸ v),s) := by
  obtain ⟨w,read,encoded⟩ := Option.map_eq_some_iff.mp view
  have inverse := c.codec.decode_encode w
  rw [encoded,decoded] at inverse
  have same := Option.some.inj inverse
  rw [← same] at read
  have raw : (Source.readCell F c.path).run s=(.ok v,s) := by
    unfold Source.readCell
    rw [Source.Hoare.run_bind,show (Source.EM.st (E:=E) (Γ:=Γ)).run s=(.ok s.2,s) from rfl]
    dsimp only
    rw [bank]
    simp only [Bool.false_eq_true,if_false,read]
    rfl
  simp only [Source.readLoc,byValue,Bool.false_eq_true,if_false]
  unfold Source.readAt
  rw [Source.Hoare.run_bind,raw]
  simp only [dif_pos typed]
  rfl

theorem representedBool_nonzero (D : Source.Layout) (field : Field) (width : field.width=1)
    (code : BoolTrueByte) (v : Source.Val D .bool)
    (nonzero : ((representedBoolCodec D field width code).encode v).val≠0) : v=.bool true := by
  cases v with
  | bool b =>
    cases b
    · exact False.elim (nonzero rfl)
    · rfl
  | memRef h _ | storRef h _ | cdRef h _ => cases h

end Solidity.Yul.Views

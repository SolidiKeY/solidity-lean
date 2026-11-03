import Solidity.Yul.Views.DynamicSource

namespace Solidity.Yul.Views

def DynamicHeader.lengthWrapped {E root cursor} (h : DynamicHeader E root cursor) (n : Nat) :
    Source.Val E.layout (E.cellTy ⟨root,[]⟩) :=
  (dynamic_header_cell h.declared).symm ▸ Source.intWrap (D := E.layout) .u256 n

/-- The actual persistent Source operation used by ordinary writeLen. Unlike
pure unchanged-view preparation this writes an explicit cell even for zero. -/
def DynamicHeader.lengthOp {E root cursor} (h : DynamicHeader E root cursor) (F : Source.Fr) (n : Nat) :
    Source.Op E.layout E.lay E.lay :=
  .account F.this (fun ac => {ac with storage := ac.storage.set ⟨root,[]⟩ (some (h.lengthWrapped n))})

theorem DynamicHeader.writeLen_run {E root cursor Γ} (h : DynamicHeader E root cursor)
    (F : Source.Fr) (s : Source.EMState E Γ) (n : Nat)
    (bank : E.transientRoot ⟨root,[]⟩ = false) :
    (Source.writeLen F ⟨root,[]⟩ n).run s =
      (if F.static then (.error (.revert []),s)
       else (.ok (),(s.1,{s.2 with ex := s.2.ex.apply (h.lengthOp F n)}))) := by
  rw [h.writeLen_operation]
  unfold Source.setCell
  rw [bank]
  simp only [Bool.false_eq_true,if_false]
  change (Source.applyOp F (h.lengthOp F n)).run s = _
  unfold Source.applyOp
  cases static : F.static <;> rfl

theorem DynamicHeader.writeLen_MemOK {E root cursor Γ} (h : DynamicHeader E root cursor)
    (F : Source.Fr) (s : Source.EMState E Γ) (n : Nat) (H : Source.HeapTy)
    (bank : E.transientRoot ⟨root,[]⟩ = false) (ok : Source.MemOK E H s) :
    Source.MemOK E H ((Source.writeLen F ⟨root,[]⟩ n).run s).2 := by
  rw [h.writeLen_run F s n bank]
  cases static : F.static
  · exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩
  · exact ok

theorem DynamicHeader.lengthOp_other {E root cursor} (h : DynamicHeader E root cursor)
    (F : Source.Fr) (s : Source.ExecState E.layout E.lay E.lay) (n : Nat) (q : Source.SPath)
    (different : q ≠ ⟨root,[]⟩) :
    ((s.apply (h.lengthOp F n)).world.accounts F.this).storage.cell q =
      (s.world.accounts F.this).storage.cell q := by
  change ((s.world.set F.this _).accounts F.this).storage.cell q = _
  rw [Source.World.set_get]
  simp only [Source.Storage.set,dif_neg different]

end Solidity.Yul.Views

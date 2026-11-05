import Solidity.Yul.Views.PackedDynamicElements

namespace Solidity.Yul.Views

def PackedDynamicHeader.lengthValue {E root t cursor} (h : PackedDynamicHeader E root t cursor) (n : Roadmap.Word) :
    Source.Val E.layout (E.cellTy ⟨root,[]⟩) := (packed_dynamic_header_cell h.declared).symm ▸ uintValueOfWord E.layout n

/-- Real source-cell premise, not assumed physical adequacy. Concrete
writeback instances below derive it from the checked canonical codec. -/
theorem PackedDynamicHeader.readLen {E root t cursor Γ} (h : PackedDynamicHeader E root t cursor)
    (F : Source.Fr) (s : Source.EMState E Γ) (n : Roadmap.Word)
    (bank : E.transientRoot ⟨root,[]⟩ = false)
    (read : (s.2.ex.world.accounts F.this).storage.read ⟨root,[]⟩ =
      some (h.lengthValue n)) :
    (Source.readLen F ⟨root,[]⟩).run s = (.ok n.val,s) := by
  have raw : (Source.readCell (E := E) F ⟨root,[]⟩).run s =
      (.ok (h.lengthValue n),s) := by
    unfold Source.readCell
    rw [Source.Hoare.run_bind,show (Source.EM.st (E := E) (Γ := Γ)).run s = (.ok s.2,s) from rfl]
    dsimp only
    rw [bank]
    simp only [Bool.false_eq_true,if_false,read]
    rfl
  have typed : (Source.readAt F ⟨root,[]⟩ (.int .u256)).run s = (.ok (uintValueOfWord E.layout n),s) := by
    unfold Source.readAt
    rw [Source.Hoare.run_bind,raw]
    simp only [dif_pos (packed_dynamic_header_cell h.declared)]
    have cancel : (packed_dynamic_header_cell h.declared) ▸ h.lengthValue n = uintValueOfWord E.layout n :=
      sourceVal_transport_cancel _ _
    change ((Except.ok ((packed_dynamic_header_cell h.declared) ▸ h.lengthValue n) : Except Source.Halt (Source.Val E.layout (.int .u256))),s) = _
    rw [cancel]
  unfold Source.readLen
  rw [Source.Hoare.run_bind,typed]
  rfl

def PackedDynamicHeader.reference {E root t cursor} (_ : PackedDynamicHeader E root t cursor) :
    Source.Val E.layout (.array .storage (.int t) none) := .storRef rfl ⟨root,[]⟩

theorem PackedDynamicHeader.indexLoc {E root t cursor Γ} (h : PackedDynamicHeader E root t cursor)
    (F : Source.Fr) (s : Source.EMState E Γ) (n : Roadmap.Word)
    (length : (Source.readLen F ⟨root,[]⟩).run s = (.ok n.val,s)) (i : Nat) :
    (Source.indexLoc F h.reference i).run s =
      (if i < n.val then (.ok (.stor ⟨root,[.index i]⟩),s) else (.error (.revert (Source.panicData .index)),s)) := by
  unfold Source.indexLoc Source.lengthOf PackedDynamicHeader.reference
  rw [Source.Hoare.run_bind,length]
  dsimp only
  by_cases bound : i < n.val
  · simp only [if_pos bound]; rfl
  · simp only [if_neg bound]; rfl

/-- No natural length cap is introduced. For the Source writeLen operation,
full administration is the ordinary writeAt/setCell operation, not canonical
view preparation's unchanged-none identity. -/
theorem PackedDynamicHeader.writeLen_operation {E root t cursor Γ} (h : PackedDynamicHeader E root t cursor)
    (F : Source.Fr) (s : Source.EMState E Γ) (n : Nat) :
    (Source.writeLen F ⟨root,[]⟩ n).run s =
      (Source.setCell F ⟨root,[]⟩ (some ((packed_dynamic_header_cell h.declared).symm ▸ Source.intWrap (D := E.layout) .u256 n))).run s := by
  unfold Source.writeLen Source.writeAt
  rw [dif_pos (packed_dynamic_header_cell h.declared).symm]

end Solidity.Yul.Views

import Solidity.Yul.Views.DynamicSeparation

namespace Solidity.Yul.Views

/-- Uses actual Source index/length/error behavior. A successful intrinsic
source location is paired with the existing Fixed-hash physical registration;
no owner lmax/artificial node bound is imposed on source index evaluation. -/
def DynamicHeader.prepareElement {E root cursor Γ} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (F : Source.Fr) (i : Nat) :
    Source.EM E Γ (ScalarPath E.layout (E.lay F.this)) := do
  let _ ← Source.indexLoc F h.reference i
  pure (h.element fixed F.this i)

theorem DynamicHeader.prepareElement_success {E root cursor Γ} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (F : Source.Fr) (s : Source.EMState E Γ) (n : Roadmap.Word)
    (length : (Source.readLen F ⟨root,[]⟩).run s = (.ok n.val,s)) (i : Nat) (valid : i < n.val) :
    (h.prepareElement fixed F i).run s = (.ok (h.element fixed F.this i),s) := by
  unfold prepareElement
  rw [Source.Hoare.run_bind,h.indexLoc F s n length i]
  simp only [if_pos valid]
  rfl

theorem DynamicHeader.prepareElement_error {E root cursor Γ} (h : DynamicHeader E root cursor)
    (fixed : Roadmap.Evm.Fixed) (F : Source.Fr) (s : Source.EMState E Γ) (n : Roadmap.Word)
    (length : (Source.readLen F ⟨root,[]⟩).run s = (.ok n.val,s)) (i : Nat) (invalid : ¬i < n.val) :
    (h.prepareElement fixed F i).run s = (.error (.revert (Source.panicData .index)),s) := by
  unfold prepareElement
  rw [Source.Hoare.run_bind,h.indexLoc F s n length i]
  simp only [if_neg invalid]

end Solidity.Yul.Views

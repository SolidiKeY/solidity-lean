import Solidity.Yul.Views.ScalarOwnershipFrame
import Solidity.Yul.Views.GenericFlow.Reads

namespace Solidity.Yul.Views

theorem ScalarOwnershipPlan.readLen {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.scalarFamilyTrace}) :
    (Source.readLen F ⟨entry.val.1,[]⟩).run p.step.1.2 =
      (.ok (p.nextRaw ((layout.scalarFamilyHeader entry).registration F.this).slot).val,p.step.1.2) := by
  let h := layout.scalarFamilyHeader entry
  have member := layout.scalarFamilyHeader_member entry
  have view := p.view static
  have header := view (h.registration F.this) (layout.scalarFamily_root_member fixed p.nextRaw _ member)
  exact h.readLen F _ _ (layout.bank_agreement _ member) (h.view_length_cell F.this _ _ header)

theorem ScalarOwnershipPlan.header_readLen {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.scalarFamilyTrace})
    (target : ((layout.scalarFamilyHeader entry).registration F.this).slot = written) :
    (Source.readLen F ⟨entry.val.1,[]⟩).run p.step.1.2 = (.ok value.val,p.step.1.2) := by
  exact GenericFlow.Reads.header_readLen (F := F) (s := p.step.1.2)
    (written := written) (value := value) p.raw _ _ (p.readLen static entry) target

theorem ScalarOwnershipPlan.account_other {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (b : Roadmap.Address)
    (different : b ≠ F.this) : p.after.source.world.accounts b = (s.2.ex.world.accounts b) := by
  exact GenericFlow.Reads.account_other p b different

theorem ScalarOwnershipPlan.unselected {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (q : Source.SPath)
    (outside : ∀ c ∈ p.next, q ≠ c.path) :
    (p.after.source.world.accounts F.this).storage.cell q = (s.2.ex.world.accounts F.this).storage.cell q := by
  exact GenericFlow.Reads.unselected p q outside

theorem ScalarOwnershipPlan.readCell {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (c : ScalarPath E.layout (E.lay F.this)) (member : c ∈ p.next) :
    ∃ v, (Source.readCell F c.path).run p.step.1.2 = (.ok v,p.step.1.2) ∧
      c.codec.encode v = c.field.findWord (p.nextRaw c.slot) := by
  exact GenericFlow.Reads.readCell p p.nextChecked static c member
    (layout.scalarFamily_bank_agreement fixed p.nextRaw c member)

theorem ScalarOwnershipPlan.dead_word {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (q : Roadmap.Word) (outside : ∀ c ∈ p.next, c.slot ≠ q) :
    p.step.2.cells (complementKey false F.this q) = p.nextRaw q := by
  exact GenericFlow.Reads.dead_word p static q outside

theorem ScalarOwnershipPlan.locals {E ds d active Γ F layout fixed written value s r}
    (p : @ScalarOwnershipPlan E ds d active Γ F layout fixed written value s r) : p.step.1.2.1 = s.1 := by
  exact GenericFlow.Reads.locals p

end Solidity.Yul.Views

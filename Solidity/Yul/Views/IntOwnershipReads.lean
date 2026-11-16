import Solidity.Yul.Views.IntOwnershipFrame
import Solidity.Yul.Views.GenericFlow.Reads

namespace Solidity.Yul.Views

theorem IntOwnershipPlan.readLen {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.integerTrace}) :
    (Source.readLen F ⟨entry.val.1,[]⟩).run p.step.1.2 =
      (.ok (p.nextRaw ((layout.integerHeader entry).registration F.this).slot).val,p.step.1.2) := by
  let h := layout.integerHeader entry
  have member := layout.integerHeader_member entry
  have view := p.view static
  have header := view (h.registration F.this) (layout.integer_root_member fixed p.nextRaw _ member)
  exact h.readLen F _ _ (layout.bank_agreement _ member) (h.view_length_cell F.this _ _ header)

theorem IntOwnershipPlan.header_readLen {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.integerTrace})
    (target : ((layout.integerHeader entry).registration F.this).slot = written) :
    (Source.readLen F ⟨entry.val.1,[]⟩).run p.step.1.2 = (.ok value.val,p.step.1.2) := by
  exact GenericFlow.Reads.header_readLen (F := F) (s := p.step.1.2)
    (written := written) (value := value) p.raw _ _ (p.readLen static entry) target

theorem IntOwnershipPlan.account_other {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (b : Roadmap.Address)
    (different : b ≠ F.this) : p.after.source.world.accounts b = (s.2.ex.world.accounts b) := by
  exact GenericFlow.Reads.account_other p b different

theorem IntOwnershipPlan.unselected {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (q : Source.SPath)
    (outside : ∀ c ∈ p.next, q ≠ c.path) :
    (p.after.source.world.accounts F.this).storage.cell q = (s.2.ex.world.accounts F.this).storage.cell q := by
  exact GenericFlow.Reads.unselected p q outside

theorem IntOwnershipPlan.readCell {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (c : ScalarPath E.layout (E.lay F.this)) (member : c ∈ p.next) :
    ∃ v, (Source.readCell F c.path).run p.step.1.2 = (.ok v,p.step.1.2) ∧
      c.codec.encode v = c.field.findWord (p.nextRaw c.slot) := by
  exact GenericFlow.Reads.readCell p p.nextChecked static c member
    (layout.integer_bank_agreement fixed p.nextRaw c member)

theorem IntOwnershipPlan.dead_word {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (q : Roadmap.Word) (outside : ∀ c ∈ p.next, c.slot ≠ q) :
    p.step.2.cells (complementKey false F.this q) = p.nextRaw q := by
  exact GenericFlow.Reads.dead_word p static q outside

theorem IntOwnershipPlan.locals {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) : p.step.1.2.1 = s.1 := by
  exact GenericFlow.Reads.locals p

end Solidity.Yul.Views

import Solidity.Yul.Views.PackedOwnershipFrame
import Solidity.Yul.Views.GenericFlow.Reads

namespace Solidity.Yul.Views

theorem PackedOwnershipPlan.readLen {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.unsignedTrace}) :
    (Source.readLen F ⟨entry.val.1,[]⟩).run p.step.1.2 =
      (.ok (p.nextRaw ((layout.unsignedHeader entry).registration F.this).slot).val,p.step.1.2) := by
  let h := layout.unsignedHeader entry
  have member := layout.unsignedHeader_member entry
  have view := p.view static
  have header := view (h.registration F.this) (layout.unsigned_root_member fixed p.nextRaw _ member)
  exact h.readLen F _ _ (layout.bank_agreement _ member) (h.view_length_cell F.this _ _ header)

theorem PackedOwnershipPlan.header_readLen {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.unsignedTrace})
    (target : ((layout.unsignedHeader entry).registration F.this).slot = written) :
    (Source.readLen F ⟨entry.val.1,[]⟩).run p.step.1.2 = (.ok value.val,p.step.1.2) := by
  exact GenericFlow.Reads.header_readLen (F := F) (s := p.step.1.2)
    (written := written) (value := value) p.raw _ _ (p.readLen static entry) target

theorem PackedOwnershipPlan.account_other {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (b : Roadmap.Address)
    (different : b ≠ F.this) : p.after.source.world.accounts b = (s.2.ex.world.accounts b) := by
  exact GenericFlow.Reads.account_other p b different

theorem PackedOwnershipPlan.unselected {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (q : Source.SPath)
    (outside : ∀ c ∈ p.next, q ≠ c.path) :
    (p.after.source.world.accounts F.this).storage.cell q = (s.2.ex.world.accounts F.this).storage.cell q := by
  exact GenericFlow.Reads.unselected p q outside

theorem PackedOwnershipPlan.readCell {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (c : ScalarPath E.layout (E.lay F.this)) (member : c ∈ p.next) :
    ∃ v, (Source.readCell F c.path).run p.step.1.2 = (.ok v,p.step.1.2) ∧
      c.codec.encode v = c.field.findWord (p.nextRaw c.slot) := by
  exact GenericFlow.Reads.readCell p p.nextChecked static c member
    (layout.unsigned_bank_agreement fixed p.nextRaw c member)

theorem PackedOwnershipPlan.dead_word {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (q : Roadmap.Word) (outside : ∀ c ∈ p.next, c.slot ≠ q) :
    p.step.2.cells (complementKey false F.this q) = p.nextRaw q := by
  exact GenericFlow.Reads.dead_word p static q outside

theorem PackedOwnershipPlan.locals {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) : p.step.1.2.1 = s.1 := by
  exact GenericFlow.Reads.locals p

end Solidity.Yul.Views

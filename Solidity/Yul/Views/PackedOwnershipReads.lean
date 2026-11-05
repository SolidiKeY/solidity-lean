import Solidity.Yul.Views.PackedOwnershipFrame

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
  have read := p.readLen static entry
  change (Source.readLen F ⟨entry.val.1,[]⟩).run p.step.1.2 =
    (.ok ((saveSlot p.raw written value) ((layout.unsignedHeader entry).registration F.this).slot).val,p.step.1.2) at read
  rw [target,find_saveSlot] at read
  exact read

theorem PackedOwnershipPlan.account_other {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (b : Roadmap.Address)
    (different : b ≠ F.this) : p.after.source.world.accounts b = (s.2.ex.world.accounts b) := by
  cases static : F.static
  · have ready := p.prepared
    obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp ready
    unfold PackedOwnershipPlan.after
    rw [p.nonstatic static]
    change ((s.2.ex.apply p.sourceOp).world.accounts b) = _
    rw [← same]
    exact Source.World.set_other _ different _
  · unfold PackedOwnershipPlan.after
    rw [p.static static]

theorem PackedOwnershipPlan.unselected {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (q : Source.SPath)
    (outside : ∀ c ∈ p.next, q ≠ c.path) :
    (p.after.source.world.accounts F.this).storage.cell q = (s.2.ex.world.accounts F.this).storage.cell q := by
  cases static : F.static
  · unfold PackedOwnershipPlan.after
    rw [p.nonstatic static]
    exact finiteAccountWrite_other F.this p.next p.nextRaw s.2.ex p.sourceOp p.prepared q outside
  · unfold PackedOwnershipPlan.after
    rw [p.static static]

theorem PackedOwnershipPlan.readCell {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (c : ScalarPath E.layout (E.lay F.this)) (member : c ∈ p.next) :
    ∃ v, (Source.readCell F c.path).run p.step.1.2 = (.ok v,p.step.1.2) ∧
      c.codec.encode v = c.field.findWord (p.nextRaw c.slot) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp (p.view static c member)
  refine ⟨v,?_,encoded⟩
  unfold Source.readCell
  rw [Source.Hoare.run_bind,show (Source.EM.st (E := E) (Γ := Γ)).run p.step.1.2 = (.ok p.step.1.2.2,p.step.1.2) from rfl]
  dsimp only
  rw [layout.unsigned_bank_agreement fixed p.nextRaw c member]
  simp only [Bool.false_eq_true,if_false,read]
  rfl

theorem PackedOwnershipPlan.dead_word {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (q : Roadmap.Word) (outside : ∀ c ∈ p.next, c.slot ≠ q) :
    p.step.2.cells (complementKey false F.this q) = p.nextRaw q := by
  have same := congrFun (p.complement static) q
  exact same.trans (packedMask_unowned_slot p.next p.nextRaw q outside)

theorem PackedOwnershipPlan.locals {E ds d active Γ F layout fixed written value s r}
    (p : @PackedOwnershipPlan E ds d active Γ F layout fixed written value s r) : p.step.1.2.1 = s.1 := by
  cases static : F.static
  · rw [p.nonstatic static]
  · rw [p.static static]

end Solidity.Yul.Views

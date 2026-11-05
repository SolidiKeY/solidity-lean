import Solidity.Yul.Views.RecursiveOwnershipFrame

namespace Solidity.Yul.Views

theorem RecursiveOwnershipPlan.readLen {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.headerTrace}) :
    (Source.readLen F entry.val.1).run p.step.1.2 =
      (.ok (p.nextRaw ((layout.header entry).registration F.this).slot).val,p.step.1.2) := by
  let h := layout.header entry
  have member := layout.header_member entry
  have bank := layout.bank_agreement _ member
  rw [PathPrimitiveHeader.registration_path] at bank
  exact h.readLen_view F _ _ bank (p.view static _ (layout.snapshot_root_member fixed p.nextRaw _ member))

theorem RecursiveOwnershipPlan.header_readLen {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (entry : {entry // entry ∈ layout.headerTrace})
    (target : ((layout.header entry).registration F.this).slot = written) :
    (Source.readLen F entry.val.1).run p.step.1.2 = (.ok value.val,p.step.1.2) := by
  have read := p.readLen static entry
  change (Source.readLen F entry.val.1).run p.step.1.2 =
    (.ok ((saveSlot p.raw written value) ((layout.header entry).registration F.this).slot).val,p.step.1.2) at read
  rw [target,find_saveSlot] at read
  exact read

theorem RecursiveOwnershipPlan.account_other {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (b : Roadmap.Address)
    (different : b ≠ F.this) : p.after.source.world.accounts b = (s.2.ex.world.accounts b) := by
  cases static : F.static
  · have ready := p.prepared
    obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp ready
    unfold RecursiveOwnershipPlan.after
    rw [p.nonstatic static]
    change ((s.2.ex.apply p.sourceOp).world.accounts b) = _
    rw [← same]
    exact Source.World.set_other _ different _
  · unfold RecursiveOwnershipPlan.after
    rw [p.static static]

theorem RecursiveOwnershipPlan.unselected {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (q : Source.SPath)
    (outside : ∀ c ∈ p.next, q ≠ c.path) :
    (p.after.source.world.accounts F.this).storage.cell q = (s.2.ex.world.accounts F.this).storage.cell q := by
  cases static : F.static
  · unfold RecursiveOwnershipPlan.after
    rw [p.nonstatic static]
    exact finiteAccountWrite_other F.this p.next p.nextRaw s.2.ex p.sourceOp p.prepared q outside
  · unfold RecursiveOwnershipPlan.after
    rw [p.static static]

theorem RecursiveOwnershipPlan.readCell {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (c : ScalarPath E.layout (E.lay F.this)) (member : c ∈ p.next) :
    ∃ v, (Source.readCell F c.path).run p.step.1.2 = (.ok v,p.step.1.2) ∧
      c.codec.encode v = c.field.findWord (p.nextRaw c.slot) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp (p.view static c member)
  refine ⟨v,?_,encoded⟩
  unfold Source.readCell
  rw [Source.Hoare.run_bind,show (Source.EM.st (E := E) (Γ := Γ)).run p.step.1.2 = (.ok p.step.1.2.2,p.step.1.2) from rfl]
  dsimp only
  rw [layout.snapshot_bank fixed p.nextRaw c member]
  simp only [Bool.false_eq_true,if_false,read]
  rfl

theorem RecursiveOwnershipPlan.dead_word {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false)
    (q : Roadmap.Word) (outside : ∀ c ∈ p.next, c.slot ≠ q) :
    p.step.2.cells (complementKey false F.this q) = p.nextRaw q := by
  have same := congrFun (p.complement static) q
  exact same.trans (packedMask_unowned_slot p.next p.nextRaw q outside)

theorem RecursiveOwnershipPlan.locals {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) : p.step.1.2.1 = s.1 := by
  cases static : F.static
  · rw [p.nonstatic static]
  · rw [p.static static]

end Solidity.Yul.Views

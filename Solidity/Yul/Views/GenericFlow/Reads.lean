import Solidity.Yul.Views.Generic.Plan

namespace Solidity.Yul.Views.GenericFlow.Reads

variable {E : Source.Env} {Γ : Source.RCtx} {F : Source.Fr}
variable {interface : Generic.OwnershipInterface E Γ F} {layout : interface.Layout}
variable {fixed : Roadmap.Evm.Fixed} {written value : Roadmap.Word}
variable {s : Source.EMState E Γ} {r : ResidualJournal complementCarrierOwnership}
variable {check : List (ScalarPath E.layout (E.lay F.this)) → Bool}

/-- Account preservation follows from the actual checked account operation. -/
theorem account_other
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check)
    (b : Roadmap.Address) (different : b ≠ F.this) :
    p.step.1.2.2.ex.world.accounts b = s.2.ex.world.accounts b := by
  cases static : F.static
  · have ready := p.prepared
    obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp ready
    rw [p.nonstatic static]
    change ((s.2.ex.apply p.sourceOp).world.accounts b) = _
    rw [← same]
    exact Source.World.set_other _ different _
  · rw [p.static static]

theorem unselected
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check)
    (q : Source.SPath) (outside : ∀ c ∈ p.next, q ≠ c.path) :
    (p.step.1.2.2.ex.world.accounts F.this).storage.cell q =
      (s.2.ex.world.accounts F.this).storage.cell q := by
  cases static : F.static
  · rw [p.nonstatic static]
    exact finiteAccountWrite_other F.this p.next p.nextRaw s.2.ex p.sourceOp p.prepared q outside
  · rw [p.static static]

theorem readCell
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check)
    (checked : packedSeparationCheck p.next = true) (static : F.static = false)
    (c : ScalarPath E.layout (E.lay F.this)) (member : c ∈ p.next)
    (bank : E.transientRoot c.path = false) :
    ∃ v, (Source.readCell F c.path).run p.step.1.2 = (.ok v,p.step.1.2) ∧
      c.codec.encode v = c.field.findWord (p.nextRaw c.slot) := by
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp (p.view checked static c member)
  refine ⟨v,?_,encoded⟩
  unfold Source.readCell
  rw [Source.Hoare.run_bind,show (Source.EM.st (E := E) (Γ := Γ)).run p.step.1.2 = (.ok p.step.1.2.2,p.step.1.2) from rfl]
  dsimp only
  rw [bank]
  simp only [Bool.false_eq_true,if_false,read]
  rfl

theorem dead_word
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check)
    (static : F.static = false) (q : Roadmap.Word)
    (outside : ∀ c ∈ p.next, c.slot ≠ q) :
    p.step.2.cells (complementKey false F.this q) = p.nextRaw q := by
  have same := congrFun (p.complement static) q
  exact same.trans (packedMask_unowned_slot p.next p.nextRaw q outside)

theorem locals
    (p : Generic.OwnershipPlan F interface layout fixed written value s r check) :
    p.step.1.2.1 = s.1 := by
  cases static : F.static
  · rw [p.nonstatic static]
  · rw [p.static static]

/-- A read of the saved header slot returns the actual written word. -/
theorem header_readLen (m : SlotView) (slot : Roadmap.Word) (path : Source.SPath)
    (read : (Source.readLen F path).run s =
      (.ok ((saveSlot m written value) slot).val,s))
    (target : slot = written) :
    (Source.readLen F path).run s = (.ok value.val,s) := by
  rw [target,find_saveSlot] at read
  exact read

end Solidity.Yul.Views.GenericFlow.Reads

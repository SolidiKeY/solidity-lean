import Solidity.Yul.Views.RecursiveOwnershipReads

namespace Solidity.Yul.Views

/-- Reuse PROVED actual output provenance, without evaluating the preceding
source/residual journals again. The theorem below identifies this with fresh
preparation at the exact resulting state, not a second semantics. -/
def RecursiveOwnershipPlan.following? {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word) :
    Option (RecursiveOwnershipPlan F layout fixed q v p.step.1.2 p.step.2) :=
  have roots : finiteView layout.registrations (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw :=
    fun c member => p.view static c (layout.snapshot_root_member fixed p.nextRaw c member)
  if checked : packedSeparationCheck (layout.snapshot fixed (saveSlot p.nextRaw q v)) = true then
    match prepared : finiteAccountWrite? F.this (layout.snapshot fixed (saveSlot p.nextRaw q v)) (saveSlot p.nextRaw q v) with
    | none => none
    | some op => some ⟨p.next,layout.sourceInventory_view F fixed p.step.1.2 p.nextRaw roots,
        p.nextRaw,p.reencode static,p.nextChecked,checked,op,prepared⟩
  else none

theorem RecursiveOwnershipPlan.following_fresh {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word) :
    p.following? static q v = prepareRecursiveOwnership? F layout fixed q v p.step.1.2 p.step.2 := by
  have roots : finiteView layout.registrations (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw :=
    fun c member => p.view static c (layout.snapshot_root_member fixed p.nextRaw c member)
  unfold prepareRecursiveOwnership?
  split
  next missing =>
    have found := layout.sourceInventory_view F fixed p.step.1.2 p.nextRaw roots
    rw [missing] at found
    cases found
  next old found =>
    have same := Option.some.inj (found.symm.trans (layout.sourceInventory_view F fixed p.step.1.2 p.nextRaw roots))
    subst old
    split
    next missing =>
      have encoded := p.reencode static
      change finiteEncode (layout.snapshot fixed p.nextRaw) _ _ = some p.nextRaw at encoded
      rw [missing] at encoded
      cases encoded
    next raw encoded =>
      have same := Option.some.inj (encoded.symm.trans (p.reencode static))
      subst raw
      split
      next checked =>
        unfold following?
        split <;> rfl
      next rejected => exact False.elim (rejected p.nextChecked)

theorem RecursiveOwnershipPlan.following_ready {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r)
    (static : F.static = false) (q v : Roadmap.Word)
    (checked : packedSeparationCheck (layout.snapshot fixed (saveSlot p.nextRaw q v)) = true)
    (decoded : (finiteAccountWrite? (T := E.lay) F.this (layout.snapshot fixed (saveSlot p.nextRaw q v)) (saveSlot p.nextRaw q v)).isSome) :
    (p.following? static q v).isSome := by
  unfold following?
  rw [dif_pos checked]
  split
  next missing => rw [missing] at decoded; cases decoded
  next op found => rfl

theorem RecursiveOwnershipPlan.prepare_eq {E ds d active Γ F layout fixed written value s r}
    (p : @RecursiveOwnershipPlan E ds d active Γ F layout fixed written value s r) :
    prepareRecursiveOwnership? F layout fixed written value s r = some p := by
  unfold prepareRecursiveOwnership?
  split
  next absent => have found := p.oldComputed; rw [absent] at found; cases found
  next old found =>
    have same := Option.some.inj (found.symm.trans p.oldComputed)
    subst old
    split
    next absent => have encoded := p.encoded; rw [absent] at encoded; cases encoded
    next raw encoded =>
      have same := Option.some.inj (encoded.symm.trans p.encoded)
      subst raw
      split
      next checked =>
        split
        next checkedNext =>
          split
          next absent => have ready := p.prepared; rw [absent] at ready; cases ready
          next op prepared =>
            have same := Option.some.inj (prepared.symm.trans p.prepared)
            subst op
            rfl
        next rejected => exact False.elim (rejected p.nextChecked)
      next rejected => exact False.elim (rejected p.oldChecked)

end Solidity.Yul.Views

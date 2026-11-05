import Solidity.Yul.Views.RetainedOwnershipRefresh

namespace Solidity.Yul.Views

/-- Proved output provenance avoids re-evaluating preceding journals. New
header geometry/decoding are still the actual checked computations. -/
def RetainedOwnershipPlan.following? {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    (static : F.static=false) (q v : Roadmap.Word) :
    Option (RetainedOwnershipPlan F layout fixed history q v p.step.1.2 p.step.2) :=
  have roots : finiteView p.nextImage.registrations (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw :=
    fun c member => p.view static c (p.nextImage.snapshot_roots p.nextRaw c member)
  match nextImageComputed : prepareRetainedArrayImage? layout fixed history ((saveSlot p.nextRaw q v) layout.header.slot) with
  | none => none
  | some image => if checked : packedSeparationCheck (image.snapshot (saveSlot p.nextRaw q v))=true then
      match prepared : finiteAccountWrite? F.this (image.snapshot (saveSlot p.nextRaw q v)) (saveSlot p.nextRaw q v) with
      | none => none
      | some op => some ⟨p.nextRaw layout.header.slot,layout.sourceLength_view (F := F) p.step.1.2 p.nextRaw (roots _ List.mem_cons_self),
          p.nextImage,p.nextImageComputed,p.next,p.nextImage.source_view (F := F) p.step.1.2 p.nextRaw roots,
          p.nextRaw,p.reencode static,p.nextChecked,image,nextImageComputed,checked,op,prepared⟩
    else none

theorem RetainedOwnershipPlan.following_ready {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    (static : F.static=false) (q v : Roadmap.Word)
    (image : RetainedArrayImage layout fixed history ((saveSlot p.nextRaw q v) layout.header.slot))
    (computed : prepareRetainedArrayImage? layout fixed history ((saveSlot p.nextRaw q v) layout.header.slot)=some image)
    (checked : packedSeparationCheck (image.snapshot (saveSlot p.nextRaw q v))=true)
    (decoded : (finiteAccountWrite? (T := E.lay) F.this (image.snapshot (saveSlot p.nextRaw q v)) (saveSlot p.nextRaw q v)).isSome) :
    (p.following? static q v).isSome := by
  unfold following?
  dsimp only
  split
  next absent => rw [absent] at computed; cases computed
  next image' found =>
    have same := Option.some.inj (found.symm.trans computed)
    subst image'
    split
    next accepted =>
      split
      next absent => rw [absent] at decoded; cases decoded
      next op prepared => rfl
    next rejected => exact False.elim (rejected checked)

theorem RetainedOwnershipPlan.prepare_eq {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) :
    prepareRetainedOwnership? F layout fixed history written value s r=some p := by
  unfold prepareRetainedOwnership?
  split
  next absent => have h := p.lengthComputed; rw [absent] at h; cases h
  next n found =>
    have same := Option.some.inj (found.symm.trans p.lengthComputed)
    subst n
    split
    next absent => have h := p.oldImageComputed; rw [absent] at h; cases h
    next image found =>
      have same := Option.some.inj (found.symm.trans p.oldImageComputed)
      subst image
      split
      next absent => have h := p.oldComputed; rw [absent] at h; cases h
      next old found =>
        have same := Option.some.inj (found.symm.trans p.oldComputed)
        subst old
        split
        next absent => have h := p.encoded; rw [absent] at h; cases h
        next raw found =>
          have same := Option.some.inj (found.symm.trans p.encoded)
          subst raw
          split
          next checked =>
            split
            next absent => have h := p.nextImageComputed; rw [absent] at h; cases h
            next image found =>
              have same := Option.some.inj (found.symm.trans p.nextImageComputed)
              subst image
              split
              next checkedNext =>
                split
                next absent => have h := p.prepared; rw [absent] at h; cases h
                next op found =>
                  have same := Option.some.inj (found.symm.trans p.prepared)
                  subst op
                  rfl
              next rejected => exact False.elim (rejected p.nextChecked)
          next rejected => exact False.elim (rejected p.oldChecked)

theorem RetainedOwnershipPlan.following_raw {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r)
    (static : F.static=false) (q v : Roadmap.Word) (next : RetainedOwnershipPlan F layout fixed history q v p.step.1.2 p.step.2)
    (computed : p.following? static q v=some next) : next.raw=p.nextRaw := by
  unfold following? at computed
  dsimp only at computed
  split at computed
  · cases computed
  · split at computed
    · split at computed
      · cases computed
      · cases computed; rfl
    · cases computed

/-- Static context changes no source read or typed ownership computation;
actual Source.applyOp still supplies its exact refusal. -/
def RetainedOwnershipPlan.withStatic {E τ b child active Γ F layout fixed history written value s r}
    (p : @RetainedOwnershipPlan E τ b child active Γ F layout fixed history written value s r) (static : Bool) :
    RetainedOwnershipPlan {F with static:=static} layout fixed history written value s r := by
  have view := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp p.oldChecked) p.encoded
  have roots : finiteView p.oldImage.registrations (s.2.ex.world.accounts F.this).storage p.raw :=
    fun c member => view c (p.oldImage.source_roots s _ p.oldComputed c member)
  have oldLen := layout.sourceLength_view (F := F) s p.raw (roots _ List.mem_cons_self)
  have newLen := layout.sourceLength_view (F := {F with static:=static}) s p.raw (roots _ List.mem_cons_self)
  have sourceNew : p.oldImage.sourceInventory? (F := {F with static:=static}) s=some p.old :=
    (p.oldImage.source_view (F := {F with static:=static}) s p.raw roots).trans (congrArg some p.old_agrees.symm)
  exact ⟨p.oldLength,newLen.trans (oldLen.symm.trans p.lengthComputed),p.oldImage,p.oldImageComputed,
    p.old,sourceNew,p.raw,p.encoded,p.oldChecked,p.nextImage,p.nextImageComputed,p.nextChecked,p.sourceOp,p.prepared⟩

end Solidity.Yul.Views

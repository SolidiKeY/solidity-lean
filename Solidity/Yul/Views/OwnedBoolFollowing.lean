import Solidity.Yul.Views.OwnedBoolOwnershipLaws

namespace Solidity.Yul.Views

theorem RepresentedOwnershipPlan.reencode_current {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false) :
    finiteEncode (representedRegistry (layout.primitiveSnapshot fixed p.nextRaw) false F.this p.step.2)
      (p.step.1.1.2.2.ex.world.accounts F.this).storage
      (fun q => p.step.1.2.cells (complementKey false F.this q))=some p.nextRaw := by
  have same : p.step.2=p.nextEncoding := congrArg Prod.snd (p.nonstatic static)
  rw [same]
  exact p.reencode static

/-- Efficient reuse of actual successful provenance, proved equal to fresh
source/readLen/encode preparation below. Not a second source semantics. -/
def RepresentedOwnershipPlan.following? {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    (static : F.static=false) (q v : Roadmap.Word) :
    Option (RepresentedOwnershipPlan F layout fixed q v p.step.1.1.2 p.step.1.2 p.step.2) :=
  if checked : packedSeparationCheck (layout.primitiveSnapshot fixed (saveSlot p.nextRaw q v))=true then
    match prepared : finiteAccountWrite? F.this
      (representedRegistry (layout.primitiveSnapshot fixed (saveSlot p.nextRaw q v)) false F.this
        (primitiveEncodingNext layout fixed (saveSlot p.nextRaw q v) p.step.2)) (saveSlot p.nextRaw q v) with
    | none => none
    | some op => some ⟨layout.primitiveSnapshot fixed p.nextRaw,p.refreshed static,p.nextRaw,p.reencode_current static,
        p.nextChecked,checked,op,prepared⟩
  else none

theorem RepresentedOwnershipPlan.following_fresh {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding)
    (static : F.static=false) (q v : Roadmap.Word) :
    p.following? static q v=prepareRepresentedOwnership? F layout fixed q v p.step.1.1.2 p.step.1.2 p.step.2 := by
  unfold prepareRepresentedOwnership?
  split
  next missing => have found:=p.refreshed static; rw [missing] at found; cases found
  next old found =>
    have same := Option.some.inj (found.symm.trans (p.refreshed static))
    subst old
    split
    next missing => have encoded:=p.reencode_current static; rw [missing] at encoded; cases encoded
    next raw encoded =>
      have same:=Option.some.inj (encoded.symm.trans (p.reencode_current static))
      subst raw
      split
      next checked => unfold following?; split <;> rfl
      next rejected => exact False.elim (rejected p.nextChecked)

theorem RepresentedOwnershipPlan.prepare_eq {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) :
    prepareRepresentedOwnership? F layout fixed written value s r encoding=some p := by
  unfold prepareRepresentedOwnership?
  split
  next absent => have found:=p.oldComputed; rw [absent] at found; cases found
  next old found =>
    have same:=Option.some.inj (found.symm.trans p.oldComputed)
    subst old
    split
    next absent => have encoded:=p.encoded; rw [absent] at encoded; cases encoded
    next raw encoded =>
      have same:=Option.some.inj (encoded.symm.trans p.encoded)
      subst raw
      split
      next checked =>
        split
        next checkedNext =>
          split
          next absent => have ready:=p.prepared; rw [absent] at ready; cases ready
          next op ready =>
            have same:=Option.some.inj (ready.symm.trans p.prepared)
            subst op
            rfl
        next rejected => exact False.elim (rejected p.nextChecked)
      next rejected => exact False.elim (rejected p.oldChecked)

end Solidity.Yul.Views

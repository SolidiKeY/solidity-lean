import Solidity.Yul.Views.RetainedEntryImage
import Solidity.Yul.Views.RecursiveOwnershipFrame

namespace Solidity.Yul.Views

/-- All preparation fields are ACTUAL source/layout/codec computations. No
result-view/reencoding/frame law is assumed. The same observed scopes and witnessed history select
old and new indices, so outer shrink cannot revoke a retained child. -/
structure CapturedOwnershipPlan {E τ b child active Γ} (F : Source.Fr)
    (layout : @RetainedArrayLayout E τ b child active F.this) (fixed : Roadmap.Evm.Fixed)
    (history : RetainedIndexHistory layout) (scopes : List (EntryReferenceScope E)) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) where
  oldLength : Roadmap.Word
  lengthComputed : aggregateSourceLengths F s layout.header=some oldLength
  oldImage : CapturedArrayImage layout fixed history scopes oldLength
  oldImageComputed : prepareCapturedArrayImage? layout fixed history scopes oldLength=some oldImage
  old : List (ScalarPath E.layout (E.lay F.this))
  oldComputed : oldImage.sourceInventory? s=some old
  raw : SlotView
  encoded : finiteEncode old (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q))=some raw
  oldChecked : packedSeparationCheck old=true
  nextImage : CapturedArrayImage layout fixed history scopes ((saveSlot raw written value) layout.header.slot)
  nextImageComputed : prepareCapturedArrayImage? layout fixed history scopes ((saveSlot raw written value) layout.header.slot)=some nextImage
  nextChecked : packedSeparationCheck (nextImage.snapshot (saveSlot raw written value))=true
  sourceOp : Source.Op E.layout E.lay E.lay
  prepared : finiteAccountWrite? F.this (nextImage.snapshot (saveSlot raw written value)) (saveSlot raw written value)=some sourceOp

def prepareCapturedOwnership? {E τ b child active Γ} (F : Source.Fr)
    (layout : @RetainedArrayLayout E τ b child active F.this) (fixed : Roadmap.Evm.Fixed)
    (history : RetainedIndexHistory layout) (scopes : List (EntryReferenceScope E)) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :
    Option (CapturedOwnershipPlan F layout fixed history scopes written value s r) :=
  match lengthComputed : aggregateSourceLengths F s layout.header with
  | none => none
  | some n => match oldImageComputed : prepareCapturedArrayImage? layout fixed history scopes n with
    | none => none
    | some oldImage => match oldComputed : oldImage.sourceInventory? s with
      | none => none
      | some old => match encoded : finiteEncode old (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q)) with
        | none => none
        | some raw => if oldChecked : packedSeparationCheck old=true then
            match nextImageComputed : prepareCapturedArrayImage? layout fixed history scopes ((saveSlot raw written value) layout.header.slot) with
            | none => none
            | some nextImage => if nextChecked : packedSeparationCheck (nextImage.snapshot (saveSlot raw written value))=true then
                match prepared : finiteAccountWrite? F.this (nextImage.snapshot (saveSlot raw written value)) (saveSlot raw written value) with
                | none => none
                | some op => some ⟨n,lengthComputed,oldImage,oldImageComputed,old,oldComputed,raw,encoded,oldChecked,nextImage,nextImageComputed,nextChecked,op,prepared⟩
              else none
          else none

def CapturedOwnershipPlan.nextRaw {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) := saveSlot p.raw written value

def CapturedOwnershipPlan.next {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) := p.nextImage.snapshot p.nextRaw

def CapturedOwnershipPlan.updates {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) :=
  ownershipUpdates false F.this (ownershipSupport p.old p.next written) (packedMask p.next p.nextRaw)

def CapturedOwnershipPlan.step {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) :=
  let source := (Source.applyOp F p.sourceOp).run s
  (source,match source.1 with | .error _ => r | .ok _ => residualRun r p.updates)

theorem CapturedOwnershipPlan.old_agrees {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) : p.old=p.oldImage.snapshot p.raw := by
  have view := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp p.oldChecked) p.encoded
  exact Option.some.inj (p.oldComputed.symm.trans (p.oldImage.source_view s p.raw (fun c member => view c (p.oldImage.source_roots s _ p.oldComputed c member))))

theorem CapturedOwnershipPlan.static {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) (static : F.static=true) : p.step=((.error (.revert []),s),r) := by
  unfold step
  rw [actualApplyOp_run,static]
  rfl

theorem CapturedOwnershipPlan.nonstatic {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) (static : F.static=false) :
    p.step=((.ok (),(s.1,{s.2 with ex:=s.2.ex.apply p.sourceOp})),residualRun r p.updates) := by
  unfold step
  rw [actualApplyOp_run,static]
  rfl

theorem CapturedOwnershipPlan.view {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) (static : F.static=false) :
    finiteView p.next (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw := by
  rw [p.nonstatic static]
  exact finiteAccountWrite_view _ _ _ _ _ ((packedSeparationCheck_iff _).mp p.nextChecked) p.prepared

theorem CapturedOwnershipPlan.reencode {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) (static : F.static=false) :
    finiteEncode p.next (p.step.1.2.2.ex.world.accounts F.this).storage
      (fun q => p.step.2.cells (complementKey false F.this q))=some p.nextRaw := by
  have complement := ownership_transport_slice p.old p.next _ r false F.this p.raw p.encoded written value
  have slice : (fun q => p.step.2.cells (complementKey false F.this q))=packedMask p.next p.nextRaw := by
    rw [p.nonstatic static]
    exact complement
  rw [slice]
  exact finiteEncode_fromComplement _ _ _ ((packedSeparationCheck_iff _).mp p.nextChecked) (p.view static)

theorem CapturedOwnershipPlan.MemOK {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H p.step.1.2 := by
  cases static : F.static
  · rw [p.nonstatic static]
    exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩
  · rw [p.static static]
    exact ok

def CapturedOwnershipPlan.withStatic {E τ b child active Γ F layout fixed history scopes written value s r}
    (p : @CapturedOwnershipPlan E τ b child active Γ F layout fixed history scopes written value s r) (static : Bool) :
    CapturedOwnershipPlan {F with static:=static} layout fixed history scopes written value s r := by
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

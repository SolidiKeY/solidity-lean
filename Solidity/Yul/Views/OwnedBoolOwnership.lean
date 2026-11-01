import Solidity.Yul.Views.OwnedBoolHeaders

namespace Solidity.Yul.Views

/-- Real declared primitive inventory; every new true byte comes from the SAME
complete raw snapshot. Dropped keys retain their history until reused. -/
def primitiveEncodingNext {E ds d active a} (layout : @ComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (raw : SlotView) (encoding : BoolEncodingJournal) :=
  boolEncodingRun encoding (encodingWrites (layout.primitiveSnapshot fixed raw) false a raw encoding)

/-- Actual computation equations only. Before-source, complement and owned-byte
journal are indices; no final view, inverse or safety law is assumed. -/
structure RepresentedOwnershipPlan {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (written value : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (encoding : BoolEncodingJournal) where
  old : List (ScalarPath E.layout (E.lay F.this))
  oldComputed : layout.primitiveSourceInventory? F fixed s=some old
  raw : SlotView
  encoded : finiteEncode (representedRegistry old false F.this encoding)
    (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q))=some raw
  oldChecked : packedSeparationCheck old=true
  nextChecked : packedSeparationCheck (layout.primitiveSnapshot fixed (saveSlot raw written value))=true
  sourceOp : Source.Op E.layout E.lay E.lay
  prepared : finiteAccountWrite? F.this
    (representedRegistry (layout.primitiveSnapshot fixed (saveSlot raw written value)) false F.this
      (primitiveEncodingNext layout fixed (saveSlot raw written value) encoding))
    (saveSlot raw written value)=some sourceOp

def prepareRepresentedOwnership? {E ds d active Γ} (F : Source.Fr)
    (layout : @ComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (written value : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (encoding : BoolEncodingJournal) :
    Option (RepresentedOwnershipPlan F layout fixed written value s r encoding) :=
  match oldComputed : layout.primitiveSourceInventory? F fixed s with
  | none => none
  | some old => match encoded : finiteEncode (representedRegistry old false F.this encoding)
      (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q)) with
    | none => none
    | some raw =>
      if oldChecked : packedSeparationCheck old=true then
        if nextChecked : packedSeparationCheck (layout.primitiveSnapshot fixed (saveSlot raw written value))=true then
          match prepared : finiteAccountWrite? F.this
            (representedRegistry (layout.primitiveSnapshot fixed (saveSlot raw written value)) false F.this
              (primitiveEncodingNext layout fixed (saveSlot raw written value) encoding))
            (saveSlot raw written value) with
          | none => none
          | some op => some ⟨old,oldComputed,raw,encoded,oldChecked,nextChecked,op,prepared⟩
        else none
      else none

def RepresentedOwnershipPlan.nextRaw {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) := saveSlot p.raw written value

def RepresentedOwnershipPlan.nextEncoding {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) := primitiveEncodingNext layout fixed p.nextRaw encoding

def RepresentedOwnershipPlan.next {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) :=
  representedRegistry (layout.primitiveSnapshot fixed p.nextRaw) false F.this p.nextEncoding

def RepresentedOwnershipPlan.updates {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) :=
  ownershipUpdates false F.this (ownershipSupport (representedRegistry p.old false F.this encoding) p.next written)
    (packedMask p.next p.nextRaw)

def RepresentedOwnershipPlan.step {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) :=
  let source := (Source.applyOp F p.sourceOp).run s
  ((source,match source.1 with | .error _ => r | .ok _ => residualRun r p.updates),
    match source.1 with | .error _ => encoding | .ok _ => p.nextEncoding)

theorem RepresentedOwnershipPlan.old_agrees {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) :
    p.old=layout.primitiveSnapshot fixed p.raw := by
  have view := finiteEncode_view _ _ _ p.raw (representedRegistry_separated _ _ _ _ ((packedSeparationCheck_iff _).mp p.oldChecked)) p.encoded
  exact Option.some.inj (p.oldComputed.symm.trans (layout.primitiveInventory_represented F fixed s p.old encoding p.raw
    (fun c member => layout.primitiveSourceInventory_roots F fixed s p.old p.oldComputed c member) view))

theorem RepresentedOwnershipPlan.static {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=true) :
    p.step=(((.error (.revert []),s),r),encoding) := by
  unfold step
  rw [actualApplyOp_run,static]
  rfl

theorem RepresentedOwnershipPlan.nonstatic {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false) :
    p.step=(((.ok (),(s.1,{s.2 with ex:=s.2.ex.apply p.sourceOp})),residualRun r p.updates),p.nextEncoding) := by
  unfold step
  rw [actualApplyOp_run,static]
  rfl

theorem RepresentedOwnershipPlan.MemOK {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (H : Source.HeapTy)
    (ok : Source.MemOK E H s) : Source.MemOK E H p.step.1.1.2 := by
  cases static : F.static
  · rw [p.nonstatic static]
    exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩
  · rw [p.static static]
    exact ok

theorem RepresentedOwnershipPlan.complement {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false) :
    (fun q => p.step.1.2.cells (complementKey false F.this q))=packedMask p.next p.nextRaw := by
  rw [p.nonstatic static]
  exact ownership_transport_slice (representedRegistry p.old false F.this encoding) p.next _ r false F.this p.raw p.encoded written value

theorem RepresentedOwnershipPlan.view {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false) :
    finiteView p.next (p.step.1.1.2.2.ex.world.accounts F.this).storage p.nextRaw := by
  rw [p.nonstatic static]
  exact finiteAccountWrite_view F.this p.next p.nextRaw s.2.ex p.sourceOp
    (representedRegistry_separated _ _ _ _ ((packedSeparationCheck_iff _).mp p.nextChecked)) p.prepared

theorem RepresentedOwnershipPlan.reencode {E ds d active Γ F layout fixed written value s r encoding}
    (p : @RepresentedOwnershipPlan E ds d active Γ F layout fixed written value s r encoding) (static : F.static=false) :
    finiteEncode p.next (p.step.1.1.2.2.ex.world.accounts F.this).storage
      (fun q => p.step.1.2.cells (complementKey false F.this q))=some p.nextRaw := by
  rw [p.complement static]
  exact finiteEncode_fromComplement _ _ _
    (representedRegistry_separated _ _ _ _ ((packedSeparationCheck_iff _).mp p.nextChecked)) (p.view static)

end Solidity.Yul.Views

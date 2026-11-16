import Solidity.Yul.Views.OwnershipTransport

namespace Solidity.Yul.Views.Generic

/-- Intrinsic varying computations. Paths remain indexed by the source layout
and executing address; inventories read the actual typed initial state. -/
structure OwnershipInterface (E : Source.Env) (Γ : Source.RCtx) (F : Source.Fr) where
  Layout : Type
  inventory? : Layout → Roadmap.Evm.Fixed → Source.EMState E Γ →
    Option (List (ScalarPath E.layout (E.lay F.this)))
  snapshot : Layout → Roadmap.Evm.Fixed → SlotView → List (ScalarPath E.layout (E.lay F.this))
  check : List (ScalarPath E.layout (E.lay F.this)) → Bool

/-- State-indexed checked preparation, not another source state. All fields
are actual computation/input equations. No final view/inverse/frame law fields.
The explicit `check` is the effective checker. Its record-field default permits
callers to specialize the computation directly, avoiding repeated projection
reduction when elaborating concrete constructor certificates. -/
structure OwnershipPlan {E Γ} (F : Source.Fr) (interface : OwnershipInterface E Γ F) (layout : interface.Layout)
    (fixed : Roadmap.Evm.Fixed) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (check : List (ScalarPath E.layout (E.lay F.this)) → Bool := interface.check) where
  old : List (ScalarPath E.layout (E.lay F.this))
  oldComputed : interface.inventory? layout fixed s = some old
  raw : SlotView
  encoded : finiteEncode old (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q)) = some raw
  oldChecked : check old = true
  nextChecked : check (interface.snapshot layout fixed (saveSlot raw written value)) = true
  sourceOp : Source.Op E.layout E.lay E.lay
  prepared : finiteAccountWrite? F.this (interface.snapshot layout fixed (saveSlot raw written value)) (saveSlot raw written value) = some sourceOp

abbrev prepareOwnership? {E Γ} (F : Source.Fr) (interface : OwnershipInterface E Γ F) (layout : interface.Layout)
    (fixed : Roadmap.Evm.Fixed) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
    (check : List (ScalarPath E.layout (E.lay F.this)) → Bool := interface.check) :
    Option (OwnershipPlan F interface layout fixed written value s r check) :=
  match oldComputed : interface.inventory? layout fixed s with
  | none => none
  | some old => match encoded : finiteEncode old (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q)) with
    | none => none
    | some raw =>
      if oldChecked : check old = true then
        if nextChecked : check (interface.snapshot layout fixed (saveSlot raw written value)) = true then
          match prepared : finiteAccountWrite? F.this (interface.snapshot layout fixed (saveSlot raw written value)) (saveSlot raw written value) with
          | none => none
          | some op => some ⟨old,oldComputed,raw,encoded,oldChecked,nextChecked,op,prepared⟩
        else none
      else none

abbrev OwnershipPlan.nextRaw {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) := saveSlot p.raw written value

abbrev OwnershipPlan.next {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) := interface.snapshot layout fixed p.nextRaw

abbrev OwnershipPlan.updates {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) :=
  ownershipUpdates false F.this (ownershipSupport p.old p.next written) (packedMask p.next p.nextRaw)

def OwnershipPlan.step {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) :=
  let source := (Source.applyOp F p.sourceOp).run s
  (source,match source.1 with | .error _ => r | .ok _ => residualRun r p.updates)

theorem OwnershipPlan.old_agrees {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check)
    (checked : packedSeparationCheck p.old = true)
    (roots : List (ScalarPath E.layout (E.lay F.this)))
    (members : ∀ c ∈ roots, c ∈ p.old)
    (snapshot : ∀ m, finiteView roots (s.2.ex.world.accounts F.this).storage m →
      interface.inventory? layout fixed s = some (interface.snapshot layout fixed m)) :
    p.old = interface.snapshot layout fixed p.raw := by
  have view := finiteEncode_view p.old _ _ p.raw ((packedSeparationCheck_iff _).mp checked) p.encoded
  have roots_view : finiteView roots (s.2.ex.world.accounts F.this).storage p.raw := by
    intro c member
    exact view c (members c member)
  exact Option.some.inj (p.oldComputed.symm.trans (snapshot p.raw roots_view))

theorem OwnershipPlan.static {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) (static : F.static = true) :
    p.step = ((.error (.revert []),s),r) := by
  unfold step
  rw [actualApplyOp_run,static]
  rfl

theorem OwnershipPlan.nonstatic {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) (static : F.static = false) :
    p.step = ((.ok (),(s.1,{s.2 with ex := s.2.ex.apply p.sourceOp})),residualRun r p.updates) := by
  unfold step
  rw [actualApplyOp_run,static]
  rfl

theorem OwnershipPlan.MemOK {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H p.step.1.2 := by
  cases static : F.static
  · rw [p.nonstatic static]
    exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩
  · rw [p.static static]
    exact ok

theorem OwnershipPlan.complement {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) (static : F.static = false) :
    (fun q => p.step.2.cells (complementKey false F.this q)) = packedMask p.next p.nextRaw := by
  rw [p.nonstatic static]
  exact ownership_transport_slice p.old p.next _ r false F.this p.raw p.encoded written value

theorem OwnershipPlan.view {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) (checked : packedSeparationCheck p.next = true) (static : F.static = false) :
    finiteView p.next (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw := by
  rw [p.nonstatic static]
  exact finiteAccountWrite_view F.this p.next p.nextRaw s.2.ex p.sourceOp ((packedSeparationCheck_iff _).mp checked) p.prepared

theorem OwnershipPlan.reencode {E Γ F interface layout fixed written value s r check}
    (p : @OwnershipPlan E Γ F interface layout fixed written value s r check) (checked : packedSeparationCheck p.next = true) (static : F.static = false) :
    finiteEncode p.next (p.step.1.2.2.ex.world.accounts F.this).storage
      (fun q => p.step.2.cells (complementKey false F.this q)) = some p.nextRaw := by
  rw [p.complement static]
  exact finiteEncode_fromComplement _ _ _ ((packedSeparationCheck_iff _).mp checked) (p.view checked static)

end Solidity.Yul.Views.Generic

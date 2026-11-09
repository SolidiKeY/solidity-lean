import Solidity.Yul.Views.IntOwnershipInventory
import Solidity.Yul.Views.Generic.Plan

namespace Solidity.Yul.Views

/-- Intrinsic specialization of the shared preparation computations. -/
abbrev intOwnershipInterface {E ds} (d : StorageDeclarations E ds) (active : String)
    (Γ : Source.RCtx) (F : Source.Fr) : Generic.OwnershipInterface E Γ F where
  Layout := @ComputedStorage E ds d active F.this
  inventory? := fun layout fixed s => layout.integerSourceInventory? F fixed s
  snapshot := fun layout fixed m => layout.integerSnapshot fixed m
  check := packedSeparationCheck

abbrev IntOwnershipPlan {E ds d active Γ} (F : Source.Fr) (layout : @ComputedStorage E ds d active F.this)
    (fixed : Roadmap.Evm.Fixed) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :=
  Generic.OwnershipPlan F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck

abbrev prepareIntOwnership? {E ds d active Γ} (F : Source.Fr) (layout : @ComputedStorage E ds d active F.this)
    (fixed : Roadmap.Evm.Fixed) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :
    Option (IntOwnershipPlan F layout fixed written value s r) :=
  Generic.prepareOwnership? F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck

namespace IntOwnershipPlan
variable {E ds} {d : StorageDeclarations E ds} {active : String} {Γ : Source.RCtx} {F : Source.Fr}
    {layout : @ComputedStorage E ds d active F.this} {fixed : Roadmap.Evm.Fixed}
    {written value : Roadmap.Word} {s : Source.EMState E Γ}
    {r : ResidualJournal complementCarrierOwnership}

@[match_pattern]
abbrev mk := @Generic.OwnershipPlan.mk E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
@[elab_as_elim]
noncomputable abbrev rec := @Generic.OwnershipPlan.rec E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
@[elab_as_elim]
noncomputable abbrev recOn := @Generic.OwnershipPlan.recOn E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
@[elab_as_elim]
abbrev casesOn := @Generic.OwnershipPlan.casesOn E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
noncomputable abbrev noConfusion := @Generic.OwnershipPlan.noConfusion E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev noConfusionType := @Generic.OwnershipPlan.noConfusionType E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev ctorIdx := @Generic.OwnershipPlan.ctorIdx E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev mk.noConfusion := @Generic.OwnershipPlan.mk.noConfusion E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev mk.sizeOf_spec := @Generic.OwnershipPlan.mk.sizeOf_spec E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev mk.inj := @Generic.OwnershipPlan.mk.inj E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev mk.injEq := @Generic.OwnershipPlan.mk.injEq E Γ F (intOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck

variable (self : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r)

abbrev old : List (ScalarPath E.layout (E.lay F.this)) :=
  Generic.OwnershipPlan.old self
abbrev oldComputed : layout.integerSourceInventory? F fixed s = some (Solidity.Yul.Views.IntOwnershipPlan.old self) :=
  Generic.OwnershipPlan.oldComputed self
abbrev raw : SlotView :=
  Generic.OwnershipPlan.raw self
abbrev encoded : finiteEncode (Solidity.Yul.Views.IntOwnershipPlan.old self) (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q)) = some (Solidity.Yul.Views.IntOwnershipPlan.raw self) :=
  Generic.OwnershipPlan.encoded self
abbrev oldChecked : packedSeparationCheck (Solidity.Yul.Views.IntOwnershipPlan.old self) = true :=
  Generic.OwnershipPlan.oldChecked self
abbrev nextChecked : packedSeparationCheck (layout.integerSnapshot fixed (saveSlot (Solidity.Yul.Views.IntOwnershipPlan.raw self) written value)) = true :=
  Generic.OwnershipPlan.nextChecked self
abbrev sourceOp : Source.Op E.layout E.lay E.lay :=
  Generic.OwnershipPlan.sourceOp self
abbrev prepared : finiteAccountWrite? F.this (layout.integerSnapshot fixed (saveSlot (Solidity.Yul.Views.IntOwnershipPlan.raw self) written value)) (saveSlot (Solidity.Yul.Views.IntOwnershipPlan.raw self) written value) = some (Solidity.Yul.Views.IntOwnershipPlan.sourceOp self) :=
  Generic.OwnershipPlan.prepared self

variable (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r)

abbrev nextRaw := Generic.OwnershipPlan.nextRaw p
abbrev next := Generic.OwnershipPlan.next p
abbrev updates := Generic.OwnershipPlan.updates p
abbrev step := Generic.OwnershipPlan.step p

end IntOwnershipPlan

theorem IntOwnershipPlan.old_agrees {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) : p.old = layout.integerSnapshot fixed p.raw :=
  Generic.OwnershipPlan.old_agrees p p.oldChecked layout.registrations
    (fun c member => layout.integerSourceInventory_roots F fixed s p.old p.oldComputed c member)
    (fun m view => layout.integerSourceInventory_view F fixed s m view)

theorem IntOwnershipPlan.static {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = true) :
    p.step = ((.error (.revert []),s),r) :=
  Generic.OwnershipPlan.static p static

theorem IntOwnershipPlan.nonstatic {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    p.step = ((.ok (),(s.1,{s.2 with ex := s.2.ex.apply p.sourceOp})),residualRun r p.updates) :=
  Generic.OwnershipPlan.nonstatic p static

theorem IntOwnershipPlan.MemOK {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H p.step.1.2 :=
  Generic.OwnershipPlan.MemOK p H ok

theorem IntOwnershipPlan.complement {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    (fun q => p.step.2.cells (complementKey false F.this q)) = packedMask p.next p.nextRaw :=
  Generic.OwnershipPlan.complement p static

theorem IntOwnershipPlan.view {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteView p.next (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw :=
  Generic.OwnershipPlan.view p p.nextChecked static

theorem IntOwnershipPlan.reencode {E ds d active Γ F layout fixed written value s r}
    (p : @IntOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteEncode p.next (p.step.1.2.2.ex.world.accounts F.this).storage
      (fun q => p.step.2.cells (complementKey false F.this q)) = some p.nextRaw :=
  Generic.OwnershipPlan.reencode p p.nextChecked static

end Solidity.Yul.Views

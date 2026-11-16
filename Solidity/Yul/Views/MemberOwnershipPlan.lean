import Solidity.Yul.Views.MemberSourceInventory
import Solidity.Yul.Views.Generic.Plan

namespace Solidity.Yul.Views

/-- Intrinsic specialization of the shared preparation computations. -/
abbrev memberOwnershipInterface {E ds} (d : RootMemberDeclarations E ds) (active : String)
    (Γ : Source.RCtx) (F : Source.Fr) : Generic.OwnershipInterface E Γ F where
  Layout := @MemberComputedStorage E ds d active F.this
  inventory? := fun layout fixed s => layout.sourceInventory? F fixed s
  snapshot := fun layout fixed m => layout.snapshot fixed m
  check := packedSeparationCheck

abbrev MemberOwnershipPlan {E ds d active Γ} (F : Source.Fr) (layout : @MemberComputedStorage E ds d active F.this)
    (fixed : Roadmap.Evm.Fixed) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :=
  Generic.OwnershipPlan F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck

abbrev prepareMemberOwnership? {E ds d active Γ} (F : Source.Fr) (layout : @MemberComputedStorage E ds d active F.this)
    (fixed : Roadmap.Evm.Fixed) (written value : Roadmap.Word)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :
    Option (MemberOwnershipPlan F layout fixed written value s r) :=
  Generic.prepareOwnership? F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck

namespace MemberOwnershipPlan
variable {E ds} {d : RootMemberDeclarations E ds} {active : String} {Γ : Source.RCtx} {F : Source.Fr}
    {layout : @MemberComputedStorage E ds d active F.this} {fixed : Roadmap.Evm.Fixed}
    {written value : Roadmap.Word} {s : Source.EMState E Γ}
    {r : ResidualJournal complementCarrierOwnership}

@[match_pattern]
abbrev mk := @Generic.OwnershipPlan.mk E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
@[elab_as_elim]
noncomputable abbrev rec := @Generic.OwnershipPlan.rec E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
@[elab_as_elim]
noncomputable abbrev recOn := @Generic.OwnershipPlan.recOn E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
@[elab_as_elim]
abbrev casesOn := @Generic.OwnershipPlan.casesOn E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
noncomputable abbrev noConfusion := @Generic.OwnershipPlan.noConfusion E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev noConfusionType := @Generic.OwnershipPlan.noConfusionType E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev ctorIdx := @Generic.OwnershipPlan.ctorIdx E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev mk.noConfusion := @Generic.OwnershipPlan.mk.noConfusion E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev mk.sizeOf_spec := @Generic.OwnershipPlan.mk.sizeOf_spec E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev mk.inj := @Generic.OwnershipPlan.mk.inj E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck
abbrev mk.injEq := @Generic.OwnershipPlan.mk.injEq E Γ F (memberOwnershipInterface d active Γ F) layout fixed written value s r packedSeparationCheck

variable (self : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r)

abbrev old : List (ScalarPath E.layout (E.lay F.this)) :=
  Generic.OwnershipPlan.old self
abbrev oldComputed : layout.sourceInventory? F fixed s = some (Solidity.Yul.Views.MemberOwnershipPlan.old self) :=
  Generic.OwnershipPlan.oldComputed self
abbrev raw : SlotView :=
  Generic.OwnershipPlan.raw self
abbrev encoded : finiteEncode (Solidity.Yul.Views.MemberOwnershipPlan.old self) (s.2.ex.world.accounts F.this).storage (fun q => r.cells (complementKey false F.this q)) = some (Solidity.Yul.Views.MemberOwnershipPlan.raw self) :=
  Generic.OwnershipPlan.encoded self
abbrev oldChecked : packedSeparationCheck (Solidity.Yul.Views.MemberOwnershipPlan.old self) = true :=
  Generic.OwnershipPlan.oldChecked self
abbrev nextChecked : packedSeparationCheck (layout.snapshot fixed (saveSlot (Solidity.Yul.Views.MemberOwnershipPlan.raw self) written value)) = true :=
  Generic.OwnershipPlan.nextChecked self
abbrev sourceOp : Source.Op E.layout E.lay E.lay :=
  Generic.OwnershipPlan.sourceOp self
abbrev prepared : finiteAccountWrite? F.this (layout.snapshot fixed (saveSlot (Solidity.Yul.Views.MemberOwnershipPlan.raw self) written value)) (saveSlot (Solidity.Yul.Views.MemberOwnershipPlan.raw self) written value) = some (Solidity.Yul.Views.MemberOwnershipPlan.sourceOp self) :=
  Generic.OwnershipPlan.prepared self

variable (p : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r)

abbrev nextRaw := Generic.OwnershipPlan.nextRaw p
abbrev next := Generic.OwnershipPlan.next p
abbrev updates := Generic.OwnershipPlan.updates p
abbrev step := Generic.OwnershipPlan.step p

end MemberOwnershipPlan

theorem MemberOwnershipPlan.old_agrees {E ds d active Γ F layout fixed written value s r}
    (p : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r) : p.old = layout.snapshot fixed p.raw :=
  Generic.OwnershipPlan.old_agrees p p.oldChecked layout.registrations
    (fun c member => layout.sourceInventory_roots F fixed s p.old p.oldComputed c member)
    (fun m view => layout.sourceInventory_view F fixed s m view)

theorem MemberOwnershipPlan.static {E ds d active Γ F layout fixed written value s r}
    (p : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = true) :
    p.step = ((.error (.revert []),s),r) :=
  Generic.OwnershipPlan.static p static

theorem MemberOwnershipPlan.nonstatic {E ds d active Γ F layout fixed written value s r}
    (p : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    p.step = ((.ok (),(s.1,{s.2 with ex := s.2.ex.apply p.sourceOp})),residualRun r p.updates) :=
  Generic.OwnershipPlan.nonstatic p static

theorem MemberOwnershipPlan.MemOK {E ds d active Γ F layout fixed written value s r}
    (p : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H p.step.1.2 :=
  Generic.OwnershipPlan.MemOK p H ok

theorem MemberOwnershipPlan.complement {E ds d active Γ F layout fixed written value s r}
    (p : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    (fun q => p.step.2.cells (complementKey false F.this q)) = packedMask p.next p.nextRaw :=
  Generic.OwnershipPlan.complement p static

theorem MemberOwnershipPlan.view {E ds d active Γ F layout fixed written value s r}
    (p : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteView p.next (p.step.1.2.2.ex.world.accounts F.this).storage p.nextRaw :=
  Generic.OwnershipPlan.view p p.nextChecked static

theorem MemberOwnershipPlan.reencode {E ds d active Γ F layout fixed written value s r}
    (p : @MemberOwnershipPlan E ds d active Γ F layout fixed written value s r) (static : F.static = false) :
    finiteEncode p.next (p.step.1.2.2.ex.world.accounts F.this).storage
      (fun q => p.step.2.cells (complementKey false F.this q)) = some p.nextRaw :=
  Generic.OwnershipPlan.reencode p p.nextChecked static

end Solidity.Yul.Views

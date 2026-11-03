import Solidity.Yul.Views.DynamicSourceSequence

namespace Solidity.Yul.Views

/-- Physical transient read combines actual typed cells with the exact raw
complement (including fully unowned slots). Canonical preparation may fail;
None is not a source/Yul execution verdict. -/
def transientSlotLoad {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (s : ResidualCompanion D L T complementCarrierOwnership) (a : Roadmap.Address) (slot : Roadmap.Word) : Option Roadmap.Word :=
  reencodeTransientSlot ts s a slot

/-- Current frame/account binding and real Source.applyOp static rule are
retained; the same successful operation journals the exact raw complement. -/
def transientSlotStore? {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) :
    Option ((Except Source.Halt Unit × Source.EMState E Γ) × ResidualJournal complementCarrierOwnership) :=
  packedFrameWrite? (ps:=ps) (ts:=ts) F true slot raw s residual

theorem transientSlot_load_store {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (result)
    (step : transientSlotStore? (ps:=ps) (ts:=ts) F slot raw s r=some result)
    (static : F.static=false) (separate : finiteSeparated (ts F.this)) :
    transientSlotLoad ts ⟨result.1.2.2.ex,result.2⟩ F.this slot=some raw :=
  packedFrameWrite_transient_reencode F slot raw s r result step static separate

theorem transientSlot_static {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (static : F.static=true)
    (prepared : (preparePackedFrame (ps:=ps) (ts:=ts) F true slot raw).isSome) :
    transientSlotStore? (ps:=ps) (ts:=ts) F slot raw s r=some ((.error (.revert []),s),r) :=
  packedFrameWrite_static F true slot raw s r static prepared

theorem transientSlot_every_H {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (H : Source.HeapTy) (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (result)
    (step : transientSlotStore? (ps:=ps) (ts:=ts) F slot raw s r=some result) (ok : Source.MemOK E H s) :
    Source.MemOK E H result.1.2 := packedFrameWrite_MemOK H F true slot raw s r result step ok

/-- EVERY slot, owned or unowned, reads zero after the actual transaction
reset. Zero defaults are real codec facts, not a supplied whole-view law. -/
theorem transientSlot_endTx {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (s : ResidualCompanion D L T complementCarrierOwnership)
    (defaults : ∀ a c, c∈ts a → ∃ v, Source.Val.default D (T a c.path)=some v ∧ (c.codec.encode v).val=0)
    (a : Roadmap.Address) (slot : Roadmap.Word) : transientSlotLoad ts (companionEndTx s) a slot=some 0 := by
  apply packedEndTx_transient
  intro c member
  exact defaults a c ((selectedSlotPaths_mem (ts a) slot c).mp member).1

theorem transientSlot_endTx_journals {D L T} (s : ResidualCompanion D L T complementCarrierOwnership) :
    (companionEndTx s).source.world=s.source.world ∧ (companionEndTx s).source.journal=[] ∧
      (companionEndTx s).residual.journal=[] := ⟨rfl,rfl,rfl⟩

/-- Paired source/residual rollback is applied to the ACTUAL checked source
sequence; it is not a pair of independently supplied logical/raw runs. -/
theorem transientSlot_child_rollback {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (caller child : List (@PackedSlotPlan E.layout E.lay E.lay ps ts))
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) (static : F.static=false) :
    let outer:=runPackedSource F caller s r
    let inner:=runPackedSource F child outer.1.2 outer.2
    let before : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership:=⟨outer.1.2.2.ex,outer.2⟩
    companionRollback (companionEnter before F.this F.sender F.value [] false)
      ⟨inner.1.2.2.ex,inner.2⟩=before := by
  dsimp only
  rw [runPackedSource_companion F child _ _ static]
  exact packed_frame_rollback _ child _ _ _ _ _

theorem transientSlot_outer_rollback_after_commit {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (caller child : List (@PackedSlotPlan E.layout E.lay E.lay ps ts))
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) (static : F.static=false) :
    let outer:=runPackedSource F caller s r
    let inner:=runPackedSource F child outer.1.2 outer.2
    let initial : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership:=⟨s.2.ex,r⟩
    let before : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership:=⟨outer.1.2.2.ex,outer.2⟩
    companionRollback (companionEnter initial F.this F.sender F.value [] false)
      (companionCommit (companionEnter before F.this F.sender F.value [] false) ⟨inner.1.2.2.ex,inner.2⟩)=initial := by
  dsimp only
  rw [runPackedSource_companion F child _ _ static,runPackedSource_companion F caller _ _ static]
  exact packed_frame_outer_commit _ caller child _ _ _ _ _

/-- A transient plan preserves the whole persistent account bank, even when
its numeric slot equals a persistent slot. -/
theorem transientSlot_persistent_bank {D L T ps ts}
    (s : ResidualCompanion D L T complementCarrierOwnership) (plan : @PackedSlotPlan D L T ps ts)
    (transient : plan.request.transient=true) (a : Roadmap.Address) (slot : Roadmap.Word) :
    reencodePersistentSlot ps (applyPackedSlot s plan) a slot=reencodePersistentSlot ps s a slot := by
  have prepared:=plan.prepared
  unfold packedRequestOp? at prepared
  rw [transient] at prepared
  obtain ⟨store,_,_,world,_⟩:=finiteTransientWrite_actual _ _ _ s.source plan.sourceOp prepared
  have other : complementKey false a slot≠plan.residualUpdate.1 := by
    intro same
    have bank:=congrArg ResidualKey.transient same
    change false=plan.request.transient at bank
    rw [transient] at bank
    cases bank
  have bytes:=packed_other_complement s plan (complementKey false a slot) other
  unfold reencodePersistentSlot
  change (finiteEncode _ ((s.source.apply plan.sourceOp).world.accounts a).storage _).map _=_
  rw [world,bytes]

end Solidity.Yul.Views

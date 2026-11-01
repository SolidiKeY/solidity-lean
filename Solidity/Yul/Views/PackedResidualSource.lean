import Solidity.Yul.Views.PackedResidualWorld
import Solidity.Source.WellTyped

namespace Solidity.Yul.Views

/-- Actual Source.applyOp checks STATIC BEFORE any source/residual effect.
The residual advances ONLY on actual source success. No fabricated source
verdict is introduced for unsupported canonical preparation. -/
def packedSourceStep {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (F : Source.Fr) (p : @PackedSlotPlan E.layout E.lay E.lay ps ts)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :
    (Except Source.Halt Unit × Source.EMState E Γ) × ResidualJournal complementCarrierOwnership :=
  let source := (Source.applyOp F p.sourceOp).run s
  (source,match source.1 with | .error _ => r | .ok _ => residualWrite r p.residualUpdate)

def preparePackedFrame {E : Source.Env} {ps ts} (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word) :
    Option (@PackedSlotPlan E.layout E.lay E.lay ps ts) := preparePackedSlot ps ts ⟨transient,F.this,slot,raw⟩

theorem packedSourceStep_static {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (F : Source.Fr) (p : @PackedSlotPlan E.layout E.lay E.lay ps ts)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) (static : F.static = true) :
    packedSourceStep F p s r = ((.error (.revert []),s),r) := by
  unfold packedSourceStep Source.applyOp
  rw [static]
  rfl

theorem packedSourceStep_nonstatic {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (F : Source.Fr) (p : @PackedSlotPlan E.layout E.lay E.lay ps ts)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) (static : F.static = false) :
    packedSourceStep F p s r = ((.ok (),(s.1,{s.2 with ex := s.2.ex.apply p.sourceOp})),residualWrite r p.residualUpdate) := by
  unfold packedSourceStep Source.applyOp
  rw [static]
  rfl

/-- Exact bridge to the paired ExecState/journal operation, not an adequacy
assumption. Local/frame state is actual Source state, and static refusal above
is the existing empty-revert result even for unchanged writes. -/
theorem packedSourceStep_companion {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (F : Source.Fr) (p : @PackedSlotPlan E.layout E.lay E.lay ps ts)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) (static : F.static = false) :
    let result := packedSourceStep F p s r
    result.1.1 = .ok () ∧ result.1.2.1 = s.1 ∧ result.1.2.2.heap = s.2.heap ∧
      result.1.2.2.events = s.2.events ∧ result.1.2.2.logs = s.2.logs ∧
      (⟨result.1.2.2.ex,result.2⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership) = applyPackedSlot ⟨s.2.ex,r⟩ p := by
  rw [packedSourceStep_nonstatic F p s r static]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem packedSourceStep_MemOK {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (H : Source.HeapTy) (F : Source.Fr) (p : @PackedSlotPlan E.layout E.lay E.lay ps ts)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) (ok : Source.MemOK E H s) :
    Source.MemOK E H (packedSourceStep F p s r).1.2 := by
  cases static : F.static
  · rw [packedSourceStep_nonstatic F p s r static]
    exact ⟨⟨⟨ok.1.1.heap,ok.1.1.le⟩,ok.1.2⟩,ok.2.1,ok.2.2⟩
  · rw [packedSourceStep_static F p s r static]
    exact ok

theorem preparePackedFrame_address {E : Source.Env} {ps ts} (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word)
    (p : @PackedSlotPlan E.layout E.lay E.lay ps ts) (prepared : preparePackedFrame F transient slot raw = some p) :
    p.request.address = F.this := congrArg PackedSlotRequest.address (preparePackedSlot_request _ _ prepared)


theorem packedPersistent_other_path {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = false) (q : Source.SPath)
    (unselected : ∀ c ∈ selectedSlotPaths (ps p.request.address) p.request.slot, q ≠ c.path) :
    (((applyPackedSlot s p).source.world.accounts p.request.address).storage).cell q =
      ((s.source.world.accounts p.request.address).storage).cell q := by
  have prepared := p.prepared
  unfold packedRequestOp? at prepared
  rw [tr] at prepared
  exact finiteAccountWrite_other _ _ _ s.source p.sourceOp prepared q unselected

theorem packedTransient_other_path {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = true) (q : Source.SPath)
    (unselected : ∀ c ∈ selectedSlotPaths (ts p.request.address) p.request.slot, q ≠ c.path) :
    ((applyPackedSlot s p).source.transient.cells p.request.address).cell q = (s.source.transient.cells p.request.address).cell q := by
  have prepared := p.prepared
  unfold packedRequestOp? at prepared
  rw [tr] at prepared
  exact finiteTransientWrite_other _ _ _ s.source p.sourceOp prepared q unselected

theorem packed_other_complement {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (k : ResidualKey complementCarrierOwnership) (different : k ≠ p.residualUpdate.1) :
    (applyPackedSlot s p).residual.cells k = s.residual.cells k := residualSave_other _ _ _ _ different

theorem packedEndTx_persistent {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy} (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (s : ResidualCompanion D L T complementCarrierOwnership) (a : Roadmap.Address) (q : Roadmap.Word) :
    reencodePersistentSlot ps (companionEndTx s) a q = reencodePersistentSlot ps s a q := rfl

/-- Default-zero is a REAL individual codec/layout premise, not a supplied
whole-view theorem; it is discharged by the concrete canonical registrations. -/
theorem packedEndTx_transient {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy} (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (s : ResidualCompanion D L T complementCarrierOwnership) (a : Roadmap.Address) (q : Roadmap.Word)
    (zeroDefault : ∀ c ∈ selectedSlotPaths (ts a) q, ∃ v, Source.Val.default D (T a c.path) = some v ∧ (c.codec.encode v).val = 0) :
    reencodeTransientSlot ts (companionEndTx s) a q = some 0 := by
  have view : finiteView (selectedSlotPaths (ts a) q) (Source.Storage.empty : Source.Storage D (T a)) (fun _ => 0) := by
    intro c member
    obtain ⟨v,default,zero⟩ := zeroDefault c member
    change (Source.Val.default D (T a c.path)).map c.codec.encode = some _
    rw [default,Option.map_some]
    apply congrArg some
    apply Fin.ext
    simpa only [Field.findWord,Field.find,Fin.val_zero,Nat.zero_div,Nat.zero_mod] using zero
  change (finiteEncode _ Source.Storage.empty (fun _ => 0)).map _ = _
  rw [finiteEncode_unchanged _ _ _ view]
  rfl

end Solidity.Yul.Views

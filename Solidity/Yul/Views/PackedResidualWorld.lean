import Solidity.Yul.Views.PackedResidualInvariant

namespace Solidity.Yul.Views

theorem finiteEncode_congr_at {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m n : SlotView) (q : Roadmap.Word) (sameSlot : ∀ c ∈ cs, c.slot = q) (same : m q = n q) :
    (finiteEncode cs s m).map (fun out => out q) = (finiteEncode cs s n).map (fun out => out q) := by
  induction cs generalizing m n with
  | nil => exact congrArg some same
  | cons c cs ih =>
    unfold finiteEncode encodeScalarPath
    cases read : s.read c.path with
    | none => rfl
    | some value =>
      simp only [Option.map_some,Option.bind_some]
      apply ih
      · intro d member; exact sameSlot d (List.mem_cons_of_mem _ member)
      · rw [show c.slot = q from sameSlot c List.mem_cons_self]
        simp only [patchScalarSlot,find_saveSlot,same]

/-- The selected typed fields are decoded from exactly the request's raw word. -/
theorem packedPersistent_view {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = false) (sep : finiteSeparated (ps p.request.address)) :
    finiteView (selectedSlotPaths (ps p.request.address) p.request.slot)
      (((applyPackedSlot s p).source.world.accounts p.request.address).storage) (fun _ => p.request.raw) := by
  have prepared := p.prepared
  unfold packedRequestOp? at prepared
  rw [tr] at prepared
  exact finiteAccountWrite_view _ _ _ s.source p.sourceOp (selectedSlotPaths_separated _ _ sep) prepared

theorem packedTransient_view {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = true) (sep : finiteSeparated (ts p.request.address)) :
    finiteView (selectedSlotPaths (ts p.request.address) p.request.slot)
      ((applyPackedSlot s p).source.transient.cells p.request.address) (fun _ => p.request.raw) := by
  have prepared := p.prepared
  unfold packedRequestOp? at prepared
  rw [tr] at prepared
  exact finiteTransientWrite_view _ _ _ s.source p.sourceOp (selectedSlotPaths_separated _ _ sep) prepared

def reencodePersistentSlot {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy} (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (s : ResidualCompanion D L T complementCarrierOwnership) (a : Roadmap.Address) (q : Roadmap.Word) : Option Roadmap.Word :=
  (finiteEncode (selectedSlotPaths (ps a) q) (s.source.world.accounts a).storage
    (fun _ => s.residual.cells (complementKey false a q))).map (fun out => out q)

def reencodeTransientSlot {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy} (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (s : ResidualCompanion D L T complementCarrierOwnership) (a : Roadmap.Address) (q : Roadmap.Word) : Option Roadmap.Word :=
  (finiteEncode (selectedSlotPaths (ts a) q) (s.source.transient.cells a)
    (fun _ => s.residual.cells (complementKey true a q))).map (fun out => out q)

/-- Complete post-write slot equality includes ALL unowned bits from the raw
word, not merely equal field projections or a caller-supplied result view. -/
theorem packedPersistent_reencode {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = false) (sep : finiteSeparated (ps p.request.address)) :
    reencodePersistentSlot ps (applyPackedSlot s p) p.request.address p.request.slot = some p.request.raw := by
  let cs := selectedSlotPaths (ps p.request.address) p.request.slot
  let outStore := ((applyPackedSlot s p).source.world.accounts p.request.address).storage
  have view := packedPersistent_view s p tr sep
  have encoded := finiteEncode_fromComplement cs outStore (fun _ => p.request.raw) (selectedSlotPaths_separated _ _ sep) view
  have input : (applyPackedSlot s p).residual.cells (complementKey false p.request.address p.request.slot) =
      packedMask cs (fun _ => p.request.raw) p.request.slot := by
    have keyeq : p.residualUpdate.1 = complementKey false p.request.address p.request.slot := by
      change complementKey p.request.transient _ _ = _
      rw [tr]
    change residualSave s.residual.cells p.residualUpdate.1 p.residualUpdate.2 _ = _
    rw [← keyeq,residualSave_get]
    change complementWord (packedCarrierOwns ps ts p.residualUpdate.1) p.request.raw = complementWord (packedOwnsByte cs p.request.slot) p.request.raw
    congr 1
    funext i
    change (if p.request.transient then _ else packedOwnsByte (ps p.request.address) p.request.slot i) = _
    rw [tr]
    exact (selectedSlotPaths_owns _ _ i).symm
  have congruent := finiteEncode_congr_at cs outStore
    (fun _ => (applyPackedSlot s p).residual.cells (complementKey false p.request.address p.request.slot))
    (packedMask cs (fun _ => p.request.raw)) p.request.slot
    (fun c member => ((selectedSlotPaths_mem _ _ c).mp member).2) input
  change (finiteEncode cs outStore _).map _ = _
  rw [congruent,encoded]
  rfl

theorem packedTransient_reencode {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = true) (sep : finiteSeparated (ts p.request.address)) :
    reencodeTransientSlot ts (applyPackedSlot s p) p.request.address p.request.slot = some p.request.raw := by
  let cs := selectedSlotPaths (ts p.request.address) p.request.slot
  let outStore := (applyPackedSlot s p).source.transient.cells p.request.address
  have view := packedTransient_view s p tr sep
  have encoded := finiteEncode_fromComplement cs outStore (fun _ => p.request.raw) (selectedSlotPaths_separated _ _ sep) view
  have input : (applyPackedSlot s p).residual.cells (complementKey true p.request.address p.request.slot) =
      packedMask cs (fun _ => p.request.raw) p.request.slot := by
    have keyeq : p.residualUpdate.1 = complementKey true p.request.address p.request.slot := by
      change complementKey p.request.transient _ _ = _
      rw [tr]
    change residualSave s.residual.cells p.residualUpdate.1 p.residualUpdate.2 _ = _
    rw [← keyeq,residualSave_get]
    change complementWord (packedCarrierOwns ps ts p.residualUpdate.1) p.request.raw = complementWord (packedOwnsByte cs p.request.slot) p.request.raw
    congr 1
    funext i
    change (if p.request.transient then packedOwnsByte (ts p.request.address) p.request.slot i else _) = _
    rw [tr]
    exact (selectedSlotPaths_owns _ _ i).symm
  have congruent := finiteEncode_congr_at cs outStore
    (fun _ => (applyPackedSlot s p).residual.cells (complementKey true p.request.address p.request.slot))
    (packedMask cs (fun _ => p.request.raw)) p.request.slot
    (fun c member => ((selectedSlotPaths_mem _ _ c).mp member).2) input
  change (finiteEncode cs outStore _).map _ = _
  rw [congruent,encoded]
  rfl

end Solidity.Yul.Views

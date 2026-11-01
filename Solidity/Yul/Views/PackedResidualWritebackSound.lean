import Solidity.Yul.Views.PackedResidualWriteback

namespace Solidity.Yul.Views

theorem packedUnchanged_persistent_reencode {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = false) (sep : finiteSeparated (ps p.request.address))
    (unchanged : packedRequestUnchanged s p = true) : reencodePersistentSlot ps s p.request.address p.request.slot = some p.request.raw := by
  have conditions := unchanged
  simp only [packedRequestUnchanged,tr,Bool.false_eq_true,if_false,Bool.and_eq_true,beq_iff_eq] at conditions
  have prepared := p.prepared
  unfold packedRequestOp? at prepared
  rw [tr] at prepared
  have storeSame := finiteAccountWrite_unchanged _ _ _ s.source p.sourceOp prepared ((finiteViewBool_iff _ _ _).mp conditions.1)
  have residualSame : (applyPackedSlot s p).residual.cells (complementKey false p.request.address p.request.slot) = s.residual.cells (complementKey false p.request.address p.request.slot) := by
    have keyeq : p.residualUpdate.1 = complementKey false p.request.address p.request.slot := by change complementKey p.request.transient _ _ = _; rw [tr]
    rw [← keyeq]
    change residualSave s.residual.cells p.residualUpdate.1 p.residualUpdate.2 p.residualUpdate.1 = _
    rw [residualSave_get,conditions.2]
  have encoded := packedPersistent_reencode s p tr sep
  unfold reencodePersistentSlot at encoded ⊢
  rw [show ((applyPackedSlot s p).source.world.accounts p.request.address).storage = (s.source.world.accounts p.request.address).storage from storeSame,residualSame] at encoded
  exact encoded

theorem packedUnchanged_transient_reencode {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = true) (sep : finiteSeparated (ts p.request.address))
    (unchanged : packedRequestUnchanged s p = true) : reencodeTransientSlot ts s p.request.address p.request.slot = some p.request.raw := by
  have conditions := unchanged
  simp only [packedRequestUnchanged,tr,if_true,Bool.and_eq_true,beq_iff_eq] at conditions
  have prepared := p.prepared
  unfold packedRequestOp? at prepared
  rw [tr] at prepared
  have storeSame := finiteTransientWrite_unchanged _ _ _ s.source p.sourceOp prepared ((finiteViewBool_iff _ _ _).mp conditions.1)
  have residualSame : (applyPackedSlot s p).residual.cells (complementKey true p.request.address p.request.slot) = s.residual.cells (complementKey true p.request.address p.request.slot) := by
    have keyeq : p.residualUpdate.1 = complementKey true p.request.address p.request.slot := by change complementKey p.request.transient _ _ = _; rw [tr]
    rw [← keyeq]
    change residualSave s.residual.cells p.residualUpdate.1 p.residualUpdate.2 p.residualUpdate.1 = _
    rw [residualSave_get,conditions.2]
  have encoded := packedTransient_reencode s p tr sep
  unfold reencodeTransientSlot at encoded ⊢
  rw [show (applyPackedSlot s p).source.transient.cells p.request.address = s.source.transient.cells p.request.address from storeSame,residualSame] at encoded
  exact encoded

theorem packedStateWriteback_persistent_reencode {D L T ps ts} (s out : ResidualCompanion D L T complementCarrierOwnership)
    (q : PackedSlotRequest) (p : @PackedSlotPlan D L T ps ts) (prepared : preparePackedSlot ps ts q = some p)
    (step : packedStateWriteback ps ts s q = some out) (tr : p.request.transient = false) (sep : finiteSeparated (ps p.request.address)) :
    reencodePersistentSlot ps out p.request.address p.request.slot = some p.request.raw := by
  unfold packedStateWriteback at step
  rw [prepared] at step
  change some (if packedRequestUnchanged s p then s else applyPackedSlot s p) = some out at step
  cases unchanged : packedRequestUnchanged s p
  · rw [unchanged] at step
    cases step
    exact packedPersistent_reencode s p tr sep
  · rw [unchanged] at step
    cases step
    exact packedUnchanged_persistent_reencode s p tr sep unchanged

theorem packedStateWriteback_transient_reencode {D L T ps ts} (s out : ResidualCompanion D L T complementCarrierOwnership)
    (q : PackedSlotRequest) (p : @PackedSlotPlan D L T ps ts) (prepared : preparePackedSlot ps ts q = some p)
    (step : packedStateWriteback ps ts s q = some out) (tr : p.request.transient = true) (sep : finiteSeparated (ts p.request.address)) :
    reencodeTransientSlot ts out p.request.address p.request.slot = some p.request.raw := by
  unfold packedStateWriteback at step
  rw [prepared] at step
  change some (if packedRequestUnchanged s p then s else applyPackedSlot s p) = some out at step
  cases unchanged : packedRequestUnchanged s p
  · rw [unchanged] at step
    cases step
    exact packedTransient_reencode s p tr sep
  · rw [unchanged] at step
    cases step
    exact packedUnchanged_transient_reencode s p tr sep unchanged

end Solidity.Yul.Views

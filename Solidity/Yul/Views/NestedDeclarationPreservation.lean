import Solidity.Yul.Views.NestedDeclarationReads

namespace Solidity.Yul.Views

/-- Algebraic bank preservation for the actual prepared operation; avoids
expanding every decoded source cell of a multi-slot canonical write. -/
theorem packedTransient_world {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = true) :
    (applyPackedSlot s p).source.world = s.source.world := by
  have prepared := p.prepared
  unfold packedRequestOp? finiteTransientWrite? at prepared
  rw [tr] at prepared
  obtain ⟨update,_,same⟩ := Option.map_eq_some_iff.mp prepared
  change (s.source.apply p.sourceOp).world = s.source.world
  rw [← same]
  rfl

theorem packedTransient_persistent_reencode {D L T ps ts} (s : ResidualCompanion D L T complementCarrierOwnership)
    (p : @PackedSlotPlan D L T ps ts) (tr : p.request.transient = true) (a : Roadmap.Address) (q : Roadmap.Word) :
    reencodePersistentSlot ps (applyPackedSlot s p) a q = reencodePersistentSlot ps s a q := by
  have different : complementKey false a q ≠ p.residualUpdate.1 := by
    intro same
    have bits := congrArg ResidualKey.transient same
    change false = p.request.transient at bits
    rw [tr] at bits
    cases bits
  unfold reencodePersistentSlot
  rw [packedTransient_world s p tr,packed_other_complement s p _ different]

end Solidity.Yul.Views

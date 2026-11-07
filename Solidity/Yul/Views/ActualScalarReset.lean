import Solidity.Yul.Views.ActualScalarFrame
import Solidity.Yul.Views.TransientSlots

/-! Actual typed transient writes preserve the fixed registry with its existing
complement. Physical transaction reset uses BOTH actual Source.endTx and the
existing residualEndTx; unlike field-only snapshot reconstruction it clears all
transient complement bytes too. Zero-default facts are codec computations. -/
namespace Solidity.Yul.Views

theorem actualScalarWrite_transient_registry_reencode {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (c : ScalarPath E.layout (E.lay F.this))
    (member : c∈cs) (separated : finiteSeparated cs) (raw : SlotView)
    (view : finiteView cs (s.2.ex.transient.cells F.this) raw)
    (value : Source.Val E.layout (E.cellTy c.path)) (transient : E.transientRoot c.path=true)
    (allowed : F.static=false) (r : ResidualJournal complementCarrierOwnership)
    (slice : (fun q=>r.cells (complementKey true F.this q))=packedMask cs raw) :
    finiteEncode cs ((actualScalarWrite F c.path c.codec c.slot value raw s).1.2.2.ex.transient.cells F.this)
      (fun q=>r.cells (complementKey true F.this q))=
      some (actualScalarWrite F c.path c.codec c.slot value raw s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_transient_storage F c.path c.codec c.slot value raw s transient allowed,slice]
  rw [actualScalarWrite_transient_run F c.path c.codec c.slot value raw s transient allowed]
  exact PackedCellUpdate.reencode_original_complement cs c member separated _ raw view value

/-- Real paired reset after the actual typed computation, for every account and
slot. Default availability/zero encoding remain explicit codec obligations. -/
theorem actualScalarWrite_endTx_load {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (raw : SlotView) (r : ResidualJournal complementCarrierOwnership)
    (ts : (a : Roadmap.Address)→List (ScalarPath E.layout (E.lay a)))
    (defaults : ∀ a d, d∈ts a → ∃ v, Source.Val.default E.layout (E.lay a d.path)=some v ∧ (d.codec.encode v).val=0)
    (a : Roadmap.Address) (slot : Roadmap.Word) :
    transientSlotLoad ts
      (companionEndTx ⟨(actualScalarWrite F c.path c.codec c.slot value raw s).1.2.2.ex,r⟩) a slot=some 0 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact transientSlot_endTx ts _ defaults a slot

theorem actualScalarWrite_endTx_journals {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (raw : SlotView) (r : ResidualJournal complementCarrierOwnership) :
    let reset := companionEndTx (⟨(actualScalarWrite F c.path c.codec c.slot value raw s).1.2.2.ex,r⟩ :
      ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
    reset.source.world=(actualScalarWrite F c.path c.codec c.slot value raw s).1.2.2.ex.world ∧
      reset.source.journal=[] ∧ reset.residual.journal=[] := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact transientSlot_endTx_journals _
end Solidity.Yul.Views

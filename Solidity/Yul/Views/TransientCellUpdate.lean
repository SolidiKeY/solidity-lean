import Solidity.Yul.Views.PackedCellUpdate
import Solidity.Yul.Views.PackedResidualPlan

/-! Canonical finite-field agreement for actual Source transient cell writes.
The complementary raw map stays unchanged; ordinary source journaling, static
refusal, paired rollback and transaction reset retain their actual contracts.
This does not admit transient aggregates or dirty-owned representations. -/
namespace Solidity.Yul.Views.TransientCellUpdate

theorem source {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (bank : E.transientRoot c.path=true) (allowed : F.static=false) :
    (Source.setCell F c.path (some value)).run s=
      (.ok (),(s.1,{s.2 with ex:=s.2.ex.apply (.transient F.this (fun store => store.write c.path value))})) := by
  first | (simp only;done) | skip
  simp only [Source.setCell,bank,if_true,Source.applyOp,allowed,Bool.false_eq_true,if_false]
  rfl

theorem view {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (c : ScalarPath E.layout (E.lay F.this))
    (member : c ∈ cs) (separated : finiteSeparated cs) (m : SlotView)
    (before : finiteView cs (s.2.ex.transient.cells F.this) m)
    (value : Source.Val E.layout (E.cellTy c.path))
    (bank : E.transientRoot c.path=true) (allowed : F.static=false) :
    finiteView cs (((Source.setCell F c.path (some value)).run s).2.2.ex.transient.cells F.this)
      (PackedCellUpdate.raw c value m) := by
  rw [source F s c value bank allowed]
  change finiteView cs ((s.2.ex.transient.set F.this _).cells F.this) _
  simp only [Source.Transient.set,dif_pos]
  exact PackedCellUpdate.view cs c member separated _ m before value

theorem reencode {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (c : ScalarPath E.layout (E.lay F.this))
    (member : c ∈ cs) (separated : finiteSeparated cs) (m : SlotView)
    (before : finiteView cs (s.2.ex.transient.cells F.this) m)
    (value : Source.Val E.layout (E.cellTy c.path))
    (bank : E.transientRoot c.path=true) (allowed : F.static=false) :
    finiteEncode cs (((Source.setCell F c.path (some value)).run s).2.2.ex.transient.cells F.this)
      (packedMask cs m)=some (PackedCellUpdate.raw c value m) := by
  rw [←PackedCellUpdate.complement cs c member value m]
  exact finiteEncode_fromComplement cs _ _ separated (view F s cs c member separated m before value bank allowed)

theorem persistent {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (bank : E.transientRoot c.path=true) (allowed : F.static=false) :
    ((Source.setCell F c.path (some value)).run s).2.2.ex.world=s.2.ex.world := by
  rw [source F s c value bank allowed]
  rfl

theorem static {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (bank : E.transientRoot c.path=true) (blocked : F.static=true) :
    (Source.setCell F c.path (some value)).run s=(.error (.revert []),s) := by
  simp only [Source.setCell,bank,if_true,Source.applyOp,blocked]
  rfl

theorem rollback {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (residual : ResidualJournal complementCarrierOwnership)
    (bank : E.transientRoot c.path=true) (allowed : F.static=false) :
    companionRollback (companionEnter (⟨s.2.ex,residual⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
      F.this F.sender F.value F.cd F.static)
      ⟨((Source.setCell F c.path (some value)).run s).2.2.ex,residual⟩=⟨s.2.ex,residual⟩ := by
  rw [source F s c value bank allowed]
  exact companionRollback_run ⟨s.2.ex,residual⟩ [.transient F.this (fun store => store.write c.path value)] []
    F.this F.sender F.value F.cd F.static
/-- Reset preserves the persistent bank, clears transient/default cells and
closes both real journals. No zero-encoding assumption for arbitrary codecs. -/
theorem endTx {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (residual : ResidualJournal complementCarrierOwnership)
    (bank : E.transientRoot c.path=true) (allowed : F.static=false)
    (address : Roadmap.Address) (path : Source.SPath) (slot : Roadmap.Word) :
    let reached : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership :=
      ⟨((Source.setCell F c.path (some value)).run s).2.2.ex,residual⟩
    (companionEndTx reached).source.world=s.2.ex.world ∧
    ((companionEndTx reached).source.transient.cells address).read path=Source.Val.default E.layout (E.lay address path) ∧
    (companionEndTx reached).residual.cells (complementKey false address slot)=residual.cells (complementKey false address slot) ∧
    (companionEndTx reached).residual.cells (complementKey true address slot)=0 ∧
    (companionEndTx reached).source.journal=[] ∧ (companionEndTx reached).residual.journal=[] := by
  dsimp only
  exact ⟨persistent F s c value bank allowed,rfl,residualEndTx_persistent _ _ rfl,
    residualEndTx_transient _ _ rfl,rfl,rfl⟩
end Solidity.Yul.Views.TransientCellUpdate

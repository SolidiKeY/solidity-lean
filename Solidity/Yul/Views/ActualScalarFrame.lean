import Solidity.Yul.Views.ActualScalarTransient
import Solidity.Yul.Views.RepeatedCellWrites
import Solidity.Yul.Views.ResidualJournal

/-! Actual typed-cell writes share the existing Source/residual frame carrier.
For a fixed separated registry, owned-field patches leave its complement fixed;
rollback restores Source and that complement reconstructs the original raw map.
Changing ownership, arbitrary calls and whole-frame heap transport remain open. -/
namespace Solidity.Yul.Views

theorem actualScalarWrite_operation {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (raw : SlotView) (allowed : F.static=false) :
    actualScalarWrite F c.path c.codec c.slot value raw s=
      ((.ok (),(s.1,{s.2 with ex:=s.2.ex.apply (RepeatedCellWrites.operation F c value)})),
       PackedCellUpdate.raw c value raw) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold actualScalarWrite
  have typed : Source.writeAt F c.path value=Source.setCell (E:=E) (Γ:=Γ) F c.path (some value) := by
    simp only [Source.writeAt,dite_true]
  rw [typed,RepeatedCellWrites.one F s c value allowed]
  rfl

theorem actualScalarWrite_companion {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (raw : SlotView) (allowed : F.static=false) (r : ResidualJournal complementCarrierOwnership) :
    (⟨(actualScalarWrite F c.path c.codec c.slot value raw s).1.2.2.ex,r⟩ :
      ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)=
      companionRunSource ⟨s.2.ex,r⟩ [RepeatedCellWrites.operation F c value] := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_operation F s c value raw allowed]
  rfl

theorem actualScalarWrite_registry_reencode {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (c : ScalarPath E.layout (E.lay F.this))
    (member : c∈cs) (separated : finiteSeparated cs) (raw : SlotView)
    (view : finiteView cs (s.2.ex.world.accounts F.this).storage raw)
    (value : Source.Val E.layout (E.cellTy c.path)) (persistent : E.transientRoot c.path=false)
    (allowed : F.static=false) (r : ResidualJournal complementCarrierOwnership)
    (slice : (fun q=>r.cells (complementKey false F.this q))=packedMask cs raw) :
    finiteEncode cs ((actualScalarWrite F c.path c.codec c.slot value raw s).1.2.2.ex.world.accounts F.this).storage
      (fun q=>r.cells (complementKey false F.this q))=
      some (actualScalarWrite F c.path c.codec c.slot value raw s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_storage F c.path c.codec c.slot value raw s persistent allowed,slice]
  rw [actualScalarWrite_run F c.path c.codec c.slot value raw s persistent allowed]
  exact PackedCellUpdate.reencode_original_complement cs c member separated _ raw view value

theorem actualScalarWrite_frame_rollback {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c : ScalarPath E.layout (E.lay F.this)) (value : Source.Val E.layout (E.cellTy c.path))
    (raw : SlotView) (allowed : F.static=false) (r : ResidualJournal complementCarrierOwnership) :
    companionRollback (companionEnter (⟨s.2.ex,r⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
      F.this F.sender F.value F.cd F.static)
      ⟨(actualScalarWrite F c.path c.codec c.slot value raw s).1.2.2.ex,r⟩=⟨s.2.ex,r⟩ := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_companion F s c value raw allowed r]
  exact companionRollback_run ⟨s.2.ex,r⟩ [RepeatedCellWrites.operation F c value] [] _ _ _ _ _

theorem actualScalarWrite_outer_commit_rollback {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (c d : ScalarPath E.layout (E.lay F.this)) (v : Source.Val E.layout (E.cellTy c.path))
    (w : Source.Val E.layout (E.cellTy d.path)) (raw : SlotView) (allowed : F.static=false)
    (r : ResidualJournal complementCarrierOwnership) :
    let first := actualScalarWrite F c.path c.codec c.slot v raw s
    let second := actualScalarWrite F d.path d.codec d.slot w first.2 first.1.2
    companionRollback (companionEnter (⟨s.2.ex,r⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
      F.this F.sender F.value F.cd F.static)
      (companionCommit (companionEnter ⟨first.1.2.2.ex,r⟩ F.this F.sender F.value F.cd F.static)
        ⟨second.1.2.2.ex,r⟩)=⟨s.2.ex,r⟩ := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  rw [actualScalarWrite_companion F _ d w _ allowed r]
  rw [actualScalarWrite_companion F s c v raw allowed r]
  exact companionRollback_outer_commit ⟨s.2.ex,r⟩ [RepeatedCellWrites.operation F c v]
    [RepeatedCellWrites.operation F d w] [] [] _ _ _ _ _
end Solidity.Yul.Views

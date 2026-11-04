import Solidity.Yul.Views.ActualScalarWrite

/-! Transient counterpart of the actual typed-cell physical bridge. The same
Source.writeAt chooses its real bank; callers supply a bank-specific raw map.
Transaction reset reconstructs one declared scalar field, preserving raw padding.
No whole-registry or aggregate ownership reset is implied. -/
namespace Solidity.Yul.Views

theorem actualScalarWrite_transient_run {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (transient : E.transientRoot path=true) (allowed : F.static=false) :
    actualScalarWrite F path codec slot value raw s=
      ((.ok (),(s.1,{s.2 with ex:=s.2.ex.apply (.transient F.this
        (fun cells=>cells.write path value))})),patchScalarSlot raw slot f (codec.encode value)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold actualScalarWrite Source.writeAt
  simp only [dite_true]
  unfold Source.setCell
  rw [transient]
  simp only [↓reduceIte]
  rw [actualApplyOp_run,allowed]
  rfl

theorem actualScalarWrite_transient_storage {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (transient : E.transientRoot path=true) (allowed : F.static=false) :
    (actualScalarWrite F path codec slot value raw s).1.2.2.ex.transient.cells F.this=
      (s.2.ex.transient.cells F.this).write path value := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_transient_run F path codec slot value raw s transient allowed]
  simp only [Source.ExecState.apply,Source.Transient.set,dif_pos]

theorem actualScalarWrite_transient_reencode {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (transient : E.transientRoot path=true) (allowed : F.static=false) :
    encodeScalarPath path codec slot ((actualScalarWrite F path codec slot value raw s).1.2.2.ex.transient.cells F.this) raw=
      some (actualScalarWrite F path codec slot value raw s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_transient_storage F path codec slot value raw s transient allowed]
  rw [actualScalarWrite_transient_run F path codec slot value raw s transient allowed]
  simp only [encodeScalarPath,Source.Storage.write_read,Option.map_some]

theorem actualScalarWrite_transient_world {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (transient : E.transientRoot path=true) (allowed : F.static=false) :
    (actualScalarWrite F path codec slot value raw s).1.2.2.ex.world=s.2.ex.world := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_transient_run F path codec slot value raw s transient allowed]
  rfl

/-- Reset uses actual Source.endTx defaults, not erasure of unowned raw bytes. -/
theorem actualScalarTransient_reset {E : Source.Env} {f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (default : Source.Val E.layout (E.cellTy path)) (raw : SlotView)
    (source : Source.ExecState E.layout E.lay E.lay)
    (computed : Source.Val.default E.layout (E.cellTy path)=some default) :
    encodeScalarPath path codec slot (source.endTx.transient.cells F.this) raw=
      some (patchScalarSlot raw slot f (codec.encode default)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold encodeScalarPath
  rw [Source.endTx_transient,computed]
  rfl
end Solidity.Yul.Views

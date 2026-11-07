import Solidity.Yul.Views.ScalarWriteback
import Solidity.Yul.Views.ComputedSnapshotSource

/-! Actual typed persistent-cell writes coupled to canonical packed-field updates.
The raw map advances only after Source success. Administrative default writes
remain real writes; this is not unchanged preparation or aggregate adequacy. -/
namespace Solidity.Yul.Views

def actualScalarWrite {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ) :=
  let source := (Source.writeAt F path value).run s
  (source,match source.1 with
    | .error _ => raw
    | .ok _ => patchScalarSlot raw slot f (codec.encode value))

theorem actualScalarWrite_source {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ) :
    (actualScalarWrite F path codec slot value raw s).1=(Source.writeAt F path value).run s := rfl

theorem actualScalarWrite_run {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (persistent : E.transientRoot path=false) (allowed : F.static=false) :
    actualScalarWrite F path codec slot value raw s=
      ((.ok (),(s.1,{s.2 with ex:=s.2.ex.apply (.account F.this
        (fun account=>{account with storage:=account.storage.write path value}))})),
       patchScalarSlot raw slot f (codec.encode value)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold actualScalarWrite Source.writeAt
  simp only [dite_true]
  unfold Source.setCell
  rw [persistent]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [actualApplyOp_run,allowed]
  rfl

theorem actualScalarWrite_static {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (blocked : F.static=true) : actualScalarWrite F path codec slot value raw s=((.error (.revert []),s),raw) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold actualScalarWrite Source.writeAt
  simp only [dite_true]
  unfold Source.setCell
  split <;> rw [actualApplyOp_run,blocked] <;> rfl

theorem actualScalarWrite_storage {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (persistent : E.transientRoot path=false) (allowed : F.static=false) :
    ((actualScalarWrite F path codec slot value raw s).1.2.2.ex.world.accounts F.this).storage=
      (s.2.ex.world.accounts F.this).storage.write path value := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_run F path codec slot value raw s persistent allowed]
  simp only [Source.ExecState.apply,Source.World.set_get]

theorem actualScalarWrite_reencode {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (persistent : E.transientRoot path=false) (allowed : F.static=false) :
    encodeScalarPath path codec slot
      ((actualScalarWrite F path codec slot value raw s).1.2.2.ex.world.accounts F.this).storage raw=
      some (actualScalarWrite F path codec slot value raw s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_storage F path codec slot value raw s persistent allowed]
  rw [actualScalarWrite_run F path codec slot value raw s persistent allowed]
  simp only [encodeScalarPath,Source.Storage.write_read,Option.map_some]
theorem actualScalarWrite_other_cell {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (persistent : E.transientRoot path=false) (allowed : F.static=false)
    (other : Source.SPath) (different : other≠path) :
    ((actualScalarWrite F path codec slot value raw s).1.2.2.ex.world.accounts F.this).storage.cell other=
      (s.2.ex.world.accounts F.this).storage.cell other := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_storage F path codec slot value raw s persistent allowed]
  simp only [Source.Storage.write,Source.Storage.set,dif_neg different]

theorem actualScalarWrite_other_bank {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (persistent : E.transientRoot path=false) (allowed : F.static=false) :
    (actualScalarWrite F path codec slot value raw s).1.2.2.ex.transient=s.2.ex.transient := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_run F path codec slot value raw s persistent allowed]
  rfl

theorem actualScalarWrite_unowned_byte {E Γ f} (F : Source.Fr) (path : Source.SPath)
    (codec : ScalarCodec E.layout (E.cellTy path) f) (slot : Roadmap.Word)
    (value : Source.Val E.layout (E.cellTy path)) (raw : SlotView) (s : Source.EMState E Γ)
    (persistent : E.transientRoot path=false) (allowed : F.static=false)
    (a : Nat) (bound : a < (2^256)*32) (unowned : scalarByteUnowned slot f a) :
    slotBytes (actualScalarWrite F path codec slot value raw s).2 a=slotBytes raw a := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualScalarWrite_run F path codec slot value raw s persistent allowed]
  exact patchScalarSlot_unowned_byte raw slot f (codec.encode value) a bound unowned
end Solidity.Yul.Views

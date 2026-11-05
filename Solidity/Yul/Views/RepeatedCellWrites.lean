import Solidity.Yul.Views.MixedCellSequence
import Solidity.Source.WellTyped

/-! Arbitrary finite typed writes to one represented cell, in its actual bank,
with a fixed frame. The program is composed from Source.setCell, not a second
evaluator. The physical fold has no imposed trace bound or ownership change. -/
namespace Solidity.Yul.Views.RepeatedCellWrites

def program {E Γ} (F : Source.Fr) (c : ScalarPath E.layout (E.lay F.this)) :
    List (Source.Val E.layout (E.cellTy c.path)) → Source.EM E Γ Unit
  | [] => pure ()
  | v::rest => do Source.setCell F c.path (some v); program F c rest

def raw {D L} (c : ScalarPath D L) (values : List (Source.Val D (L c.path))) (m : SlotView) :=
  values.foldl (fun current value => PackedCellUpdate.raw c value current) m

def operation {E : Source.Env} (F : Source.Fr) (c : ScalarPath E.layout (E.lay F.this))
    (v : Source.Val E.layout (E.cellTy c.path)) : Source.Op E.layout E.lay E.lay :=
  if E.transientRoot c.path then MixedCellSequence.transientOp F c v else MixedCellSequence.persistentOp F c v

def cells {E Γ} (F : Source.Fr) (bank : Bool) (s : Source.EMState E Γ) :=
  if bank then s.2.ex.transient.cells F.this else (s.2.ex.world.accounts F.this).storage

theorem one {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) (c : ScalarPath E.layout (E.lay F.this))
    (v : Source.Val E.layout (E.cellTy c.path)) (allowed : F.static=false) :
    (Source.setCell F c.path (some v)).run s=(.ok (),(s.1,{s.2 with ex:=s.2.ex.apply (operation F c v)})) := by
  first | (simp only;done) | skip
  cases bank : E.transientRoot c.path
  · rw [PackedCellUpdate.source F s c v bank allowed]
    simp only [operation,bank,Bool.false_eq_true,if_false]
    rfl
  · rw [TransientCellUpdate.source F s c v bank allowed]
    simp only [operation,bank,if_true]
    rfl

theorem run {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) (c : ScalarPath E.layout (E.lay F.this))
    (values : List (Source.Val E.layout (E.cellTy c.path))) (allowed : F.static=false) :
    (program F c values).run s=
      (.ok (),(s.1,{s.2 with ex:=s.2.ex.run (values.map (operation F c))})) := by
  first | (simp only;done) | skip
  induction values generalizing s with
  | nil => rfl
  | cons value rest ih =>
    rw [program,Source.Hoare.run_bind,one F s c value allowed]
    dsimp only
    rw [ih]
    rfl

theorem complement {D L} (cs : List (ScalarPath D L)) (c : ScalarPath D L) (member : c ∈ cs)
    (values : List (Source.Val D (L c.path))) (m : SlotView) : packedMask cs (raw c values m)=packedMask cs m := by
  first | (simp only;done) | skip
  induction values generalizing m with
  | nil => rfl
  | cons value rest ih =>
    change packedMask cs (raw c rest (PackedCellUpdate.raw c value m))=_
    rw [ih,PackedCellUpdate.complement cs c member value m]

theorem view {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (c : ScalarPath E.layout (E.lay F.this))
    (member : c ∈ cs) (separated : finiteSeparated cs) (m : SlotView)
    (before : finiteView cs (cells F (E.transientRoot c.path) s) m)
    (values : List (Source.Val E.layout (E.cellTy c.path))) (allowed : F.static=false) :
    finiteView cs (cells F (E.transientRoot c.path) ((program F c values).run s).2) (raw c values m) := by
  first | (simp only;done) | skip
  induction values generalizing s m with
  | nil => exact before
  | cons value rest ih =>
    have next : finiteView cs (cells F (E.transientRoot c.path) ((Source.setCell F c.path (some value)).run s).2)
        (PackedCellUpdate.raw c value m) := by
      cases bank : E.transientRoot c.path
      · rw [bank] at before
        exact PackedCellUpdate.source_view F s cs c member separated m before value bank allowed
      · rw [bank] at before
        exact TransientCellUpdate.view F s cs c member separated m before value bank allowed
    rw [program,Source.Hoare.run_bind,one F s c value allowed]
    dsimp only
    change finiteView cs _ (raw c rest (PackedCellUpdate.raw c value m))
    apply ih
    simpa only [one F s c value allowed] using next

theorem reencode {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (cs : List (ScalarPath E.layout (E.lay F.this))) (c : ScalarPath E.layout (E.lay F.this))
    (member : c ∈ cs) (separated : finiteSeparated cs) (m : SlotView)
    (before : finiteView cs (cells F (E.transientRoot c.path) s) m)
    (values : List (Source.Val E.layout (E.cellTy c.path))) (allowed : F.static=false) :
    finiteEncode cs (cells F (E.transientRoot c.path) ((program F c values).run s).2)
      (packedMask cs m)=some (raw c values m) := by
  rw [←complement cs c member values m]
  exact finiteEncode_fromComplement cs _ _ separated (view F s cs c member separated m before values allowed)

theorem static {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) (c : ScalarPath E.layout (E.lay F.this))
    (value : Source.Val E.layout (E.cellTy c.path)) (rest : List (Source.Val E.layout (E.cellTy c.path)))
    (blocked : F.static=true) : (program F c (value::rest)).run s=(.error (.revert []),s) := by
  simp only [program,Source.Hoare.run_bind,Source.setCell]
  cases bank : E.transientRoot c.path <;>
    simp only [Bool.false_eq_true,if_false,if_true,Source.applyOp,blocked] <;> rfl

theorem rollback {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) (c : ScalarPath E.layout (E.lay F.this))
    (values : List (Source.Val E.layout (E.cellTy c.path))) (residual : ResidualJournal complementCarrierOwnership)
    (allowed : F.static=false) :
    companionRollback (companionEnter (⟨s.2.ex,residual⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
      F.this F.sender F.value F.cd F.static)
      ⟨((program F c values).run s).2.2.ex,residual⟩=⟨s.2.ex,residual⟩ := by
  rw [run F s c values allowed]
  exact companionRollback_run ⟨s.2.ex,residual⟩ (values.map (operation F c)) [] F.this F.sender F.value F.cd F.static
theorem preserves {E Γ} (F : Source.Fr) (c : ScalarPath E.layout (E.lay F.this))
    (values : List (Source.Val E.layout (E.cellTy c.path))) (H : Source.HeapTy) :
    Source.Hoare (Source.MemOK E H) (program (Γ:=Γ) F c values)
      (fun _ state => Source.MemOK E H state) (fun _ state => Source.MemOK E H state) := by
  first | (simp only;done) | skip
  induction values with
  | nil => exact Source.Hoare.pure' (fun _ safe => safe)
  | cons value rest ih => exact Source.Hoare.bind (Source.setCell_mem F c.path (some value)) (fun _ => ih)

theorem MemOK {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) (c : ScalarPath E.layout (E.lay F.this))
    (values : List (Source.Val E.layout (E.cellTy c.path))) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H ((program F c values).run s).2 := by
  first | (simp only;done) | skip
  have safe := preserves F c values H s ok
  rcases actual : (program F c values).run s with ⟨result,state⟩
  rw [actual] at safe
  cases result <;> exact safe
end Solidity.Yul.Views.RepeatedCellWrites

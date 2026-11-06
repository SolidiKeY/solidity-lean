import Solidity.Yul.Views.TransientCellUpdate

/-! One actual Source bind writes persistent and transient canonical fields.
Both complete raw reconstructions describe that SAME reached state. No
changing-inventory, arbitrary-call or dirty-owned adequacy is asserted. -/
namespace Solidity.Yul.Views.MixedCellSequence

def program {E Γ} (F : Source.Fr) (p t : ScalarPath E.layout (E.lay F.this))
    (pv : Source.Val E.layout (E.cellTy p.path)) (tv : Source.Val E.layout (E.cellTy t.path))
    (firstStatic secondStatic : Bool) : Source.EM E Γ Unit := do
  Source.setCell {F with static:=firstStatic} p.path (some pv)
  Source.setCell {F with static:=secondStatic} t.path (some tv)

def persistentOp {E : Source.Env} (F : Source.Fr) (p : ScalarPath E.layout (E.lay F.this))
    (pv : Source.Val E.layout (E.cellTy p.path)) : Source.Op E.layout E.lay E.lay :=
  .account F.this (fun account => {account with storage:=account.storage.write p.path pv})
def transientOp {E : Source.Env} (F : Source.Fr) (t : ScalarPath E.layout (E.lay F.this))
    (tv : Source.Val E.layout (E.cellTy t.path)) : Source.Op E.layout E.lay E.lay :=
  .transient F.this (fun store => store.write t.path tv)

theorem run {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) (p t : ScalarPath E.layout (E.lay F.this))
    (pv : Source.Val E.layout (E.cellTy p.path)) (tv : Source.Val E.layout (E.cellTy t.path))
    (pb : E.transientRoot p.path=false) (tb : E.transientRoot t.path=true) :
    (program F p t pv tv false false).run s=
      (.ok (),(s.1,{s.2 with ex:=(s.2.ex.apply (persistentOp F p pv)).apply (transientOp F t tv)})) := by
  first | (simp only;done) | skip
  unfold program
  rw [Source.Hoare.run_bind,PackedCellUpdate.source {F with static:=false} s p pv pb rfl]
  dsimp only
  rw [TransientCellUpdate.source {F with static:=false} _ t tv tb rfl]
  rfl

theorem late_static {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) (p t : ScalarPath E.layout (E.lay F.this))
    (pv : Source.Val E.layout (E.cellTy p.path)) (tv : Source.Val E.layout (E.cellTy t.path))
    (pb : E.transientRoot p.path=false) (tb : E.transientRoot t.path=true) :
    (program F p t pv tv false true).run s=
      (.error (.revert []),(s.1,{s.2 with ex:=s.2.ex.apply (persistentOp F p pv)})) := by
  unfold program
  rw [Source.Hoare.run_bind,PackedCellUpdate.source {F with static:=false} s p pv pb rfl]
  dsimp only
  rw [TransientCellUpdate.static {F with static:=true} _ t tv tb rfl]
  rfl

theorem first_static {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) (p t : ScalarPath E.layout (E.lay F.this))
    (pv : Source.Val E.layout (E.cellTy p.path)) (tv : Source.Val E.layout (E.cellTy t.path))
    (pb : E.transientRoot p.path=false) (secondStatic : Bool) :
    (program F p t pv tv true secondStatic).run s=(.error (.revert []),s) := by
  simp only [program,Source.Hoare.run_bind,Source.setCell,pb,Bool.false_eq_true,if_false,Source.applyOp]
  rfl

theorem agreement {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (p t : ScalarPath E.layout (E.lay F.this))
    (pv : Source.Val E.layout (E.cellTy p.path)) (tv : Source.Val E.layout (E.cellTy t.path))
    (pm : p ∈ ps) (tm : t ∈ ts) (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (mp mt : SlotView) (pview : finiteView ps (s.2.ex.world.accounts F.this).storage mp)
    (tview : finiteView ts (s.2.ex.transient.cells F.this) mt)
    (pb : E.transientRoot p.path=false) (tb : E.transientRoot t.path=true) :
    let reached := (program F p t pv tv false false).run s
    finiteEncode ps (reached.2.2.ex.world.accounts F.this).storage (packedMask ps mp)=some (PackedCellUpdate.raw p pv mp) ∧
    finiteEncode ts (reached.2.2.ex.transient.cells F.this) (packedMask ts mt)=some (PackedCellUpdate.raw t tv mt) := by
  first | (simp only;done) | skip
  dsimp only
  rw [run F s p t pv tv pb tb]
  simp only [persistentOp,transientOp,Source.ExecState.apply,Source.World.set_get,Source.Transient.set,dif_pos]
  exact ⟨PackedCellUpdate.reencode_original_complement ps p pm psep _ mp pview pv,
    PackedCellUpdate.reencode_original_complement ts t tm tsep _ mt tview tv⟩

theorem rollback {E Γ} (F : Source.Fr) (s : Source.EMState E Γ) (p t : ScalarPath E.layout (E.lay F.this))
    (pv : Source.Val E.layout (E.cellTy p.path)) (tv : Source.Val E.layout (E.cellTy t.path))
    (residual : ResidualJournal complementCarrierOwnership)
    (pb : E.transientRoot p.path=false) (tb : E.transientRoot t.path=true) :
    companionRollback (companionEnter (⟨s.2.ex,residual⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)
      F.this F.sender F.value F.cd F.static)
      ⟨((program F p t pv tv false false).run s).2.2.ex,residual⟩=⟨s.2.ex,residual⟩ := by
  rw [run F s p t pv tv pb tb]
  exact companionRollback_run ⟨s.2.ex,residual⟩ [persistentOp F p pv,transientOp F t tv] []
    F.this F.sender F.value F.cd F.static
end Solidity.Yul.Views.MixedCellSequence

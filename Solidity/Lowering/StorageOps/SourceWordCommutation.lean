import Solidity.Lowering.StorageOps.SourceWordWrite
open Solidity Solidity.Lowering.StorageOps
/-! Captured ordinary typed Source cell writes. Distinct-path updates commute
as full worlds; actual execution retains exact order-dependent journal entries.
Values and paths are fixed captures, not effectful RHS/address evaluations.
Fresh liveness, target compilation and implicit rollback are separate. -/
namespace Solidity.Lowering.StorageOps.SourceWordCommutation
theorem storage_commute : ∀ (E : Source.Env) (s : Source.Storage E.layout E.cellTy) (p q : Source.SPath)
 (v : Source.Val E.layout (E.cellTy p)) (w : Source.Val E.layout (E.cellTy q)) (_different : p≠q),
 (s.write p v).write q w=(s.write q w).write p v := by
  intro E s p q v w different
  apply congrArg (fun cells => (⟨cells⟩ : Source.Storage E.layout E.cellTy))
  funext r
  by_cases hp : r=p
  · subst r
    simp only [Source.Storage.write,Source.Storage.set,dif_neg different,dif_pos]
  · by_cases hq : r=q
    · subst r
      simp only [Source.Storage.write,Source.Storage.set,dif_neg (Ne.symm different),dif_pos]
    · simp only [Source.Storage.write,Source.Storage.set,dif_neg hp,dif_neg hq]
theorem world_commute : ∀ (E : Source.Env) (frame : Source.Fr) (p q : Source.SPath)
 (v : Source.Val E.layout (E.cellTy p)) (w : Source.Val E.layout (E.cellTy q))
 (state : Source.St E) (_different : p≠q),
 (SourceWordWrite.after frame q w (SourceWordWrite.after frame p v state)).ex.world =
 (SourceWordWrite.after frame p v (SourceWordWrite.after frame q w state)).ex.world := by
  intro E frame p q v w state different
  simp only [SourceWordWrite.after,SourceWordWrite.op,Source.ExecState.apply,Source.World.set,dif_pos]
  apply congrArg Source.World.mk
  funext a
  by_cases ha : a=frame.this
  · subst a
    simp only [dif_pos]
    exact congrArg (fun storage => {(state.ex.world.accounts frame.this) with storage:=storage})
      (storage_commute E (state.ex.world.accounts frame.this).storage p q v w different)
  · simp only [dif_neg ha]

def two {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
 (p : Source.SPath) (v : Source.Val E.layout (E.cellTy p))
 (q : Source.SPath) (w : Source.Val E.layout (E.cellTy q)) : Source.EM E Γ Unit := do
 Source.writeAt frame p v
 Source.writeAt frame q w

theorem run {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
 (p : Source.SPath) (v : Source.Val E.layout (E.cellTy p))
 (q : Source.SPath) (w : Source.Val E.layout (E.cellTy q))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (writable : frame.static=false) (ordinaryP : E.transientRoot p=false) (ordinaryQ : E.transientRoot q=false) :
 (two frame p v q w).run (locals,state)=
 (.ok (), (locals,SourceWordWrite.after frame q w (SourceWordWrite.after frame p v state))) := by
  unfold two
  rw [Source.Hoare.run_bind,SourceWordWrite.source_write frame p v locals state writable ordinaryP]
  exact SourceWordWrite.source_write frame q w locals (SourceWordWrite.after frame p v state) writable ordinaryQ

theorem journal_order {E : Source.Env} (frame : Source.Fr)
 (p : Source.SPath) (v : Source.Val E.layout (E.cellTy p))
 (q : Source.SPath) (w : Source.Val E.layout (E.cellTy q)) (state : Source.St E) :
 (SourceWordWrite.after frame q w (SourceWordWrite.after frame p v state)).ex.journal =
 .account frame.this ((SourceWordWrite.after frame p v state).ex.world.accounts frame.this) ::
 .account frame.this (state.ex.world.accounts frame.this) :: state.ex.journal := by rfl

/-- Package both actual captured-write runs, world equality and their distinct journal orders. -/
theorem complete {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
 (p : Source.SPath) (v : Source.Val E.layout (E.cellTy p))
 (q : Source.SPath) (w : Source.Val E.layout (E.cellTy q))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (writable : frame.static=false) (ordinaryP : E.transientRoot p=false) (ordinaryQ : E.transientRoot q=false)
 (different : p≠q) :
 let forward := (two frame p v q w).run (locals,state)
 let reverse := (two frame q w p v).run (locals,state)
 forward=(.ok (), (locals,SourceWordWrite.after frame q w (SourceWordWrite.after frame p v state))) ∧
 reverse=(.ok (), (locals,SourceWordWrite.after frame p v (SourceWordWrite.after frame q w state))) ∧
 forward.2.2.ex.world=reverse.2.2.ex.world ∧
 forward.2.2.ex.journal =
 .account frame.this ((SourceWordWrite.after frame p v state).ex.world.accounts frame.this) ::
 .account frame.this (state.ex.world.accounts frame.this) :: state.ex.journal ∧
 reverse.2.2.ex.journal =
 .account frame.this ((SourceWordWrite.after frame q w state).ex.world.accounts frame.this) ::
 .account frame.this (state.ex.world.accounts frame.this) :: state.ex.journal := by
  dsimp only
  rw [run frame p v q w locals state writable ordinaryP ordinaryQ,
    run frame q w p v locals state writable ordinaryQ ordinaryP]
  exact ⟨rfl, rfl, world_commute E frame p q v w state different,
    journal_order frame p v q w state, journal_order frame q w p v state⟩

end Solidity.Lowering.StorageOps.SourceWordCommutation





/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutation.storage_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutation.storage_commute

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutation.world_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutation.world_commute

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutation.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutation.run

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutation.journal_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutation.journal_order

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutation.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutation.complete

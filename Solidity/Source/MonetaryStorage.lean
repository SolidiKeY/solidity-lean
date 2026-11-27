import Solidity.Source.MonetaryExecution

namespace Solidity.Source
open Solidity.Roadmap (Address)
variable {D : Layout} {L T : Address → SPath → STy}

theorem ExecState.storage_balancesFit (state : ExecState D L T) (address : Address)
    (update : Storage D (L address) → Storage D (L address)) (fit : state.BalancesFit) :
    (state.apply (.account address (fun account =>
      { account with storage := update account.storage }))).BalancesFit := by
  refine ⟨World.set_balancesFit _ _ _ fit.1 (fit.1 address), ?_⟩
  intro entry member
  change entry ∈ .account address (state.world.accounts address) :: state.journal at member
  rcases List.mem_cons.mp member with same | previous
  · cases same
    exact fit.1 address
  · exact fit.2 entry previous

theorem ExecState.transient_balancesFit (state : ExecState D L T) (address : Address)
    (update : Storage D (T address) → Storage D (T address)) (fit : state.BalancesFit) :
    (state.apply (.transient address update)).BalancesFit := by
  refine ⟨fit.1, ?_⟩
  intro entry member
  change entry ∈ .transient address (state.transient.cells address) :: state.journal at member
  rcases List.mem_cons.mp member with same | previous
  · cases same
    exact True.intro
  · exact fit.2 entry previous

namespace MonetaryStorage
variable {E : Env} {Γ : RCtx}

theorem applyOp_run (locals : Locals E.layout Γ) (state : St E) (frame : Fr)
    (operation : Op E.layout E.lay E.lay) :
    (applyOp frame operation : EM E Γ Unit).run (locals,state) =
      if frame.static then (.error (.revert []),(locals,state))
      else (.ok (),(locals,{state with ex := state.ex.apply operation})) := by
  unfold applyOp
  cases frame.static <;> rfl

theorem setCell_preserves (locals : Locals E.layout Γ) (state : St E) (frame : Fr)
    (path : SPath) (value : Option (Val E.layout (E.cellTy path)))
    (fit : state.ex.BalancesFit) :
    ((setCell frame path value : EM E Γ Unit).run (locals,state)).2.2.ex.BalancesFit := by
  unfold setCell
  split
  · rw [applyOp_run]
    split
    · exact fit
    · exact state.ex.transient_balancesFit frame.this _ fit
  · rw [applyOp_run]
    split
    · exact fit
    · exact state.ex.storage_balancesFit frame.this (fun storage => storage.set path value) fit

theorem writeAt_preserves (locals : Locals E.layout Γ) (state : St E) (frame : Fr)
    (path : SPath) {type : STy} (value : Val E.layout type) (fit : state.ex.BalancesFit) :
    ((writeAt frame path value : EM E Γ Unit).run (locals,state)).2.2.ex.BalancesFit := by
  unfold writeAt
  split
  · exact setCell_preserves locals state frame path _ fit
  · exact fit

example (locals : Locals E.layout Γ) (state : St E) (frame : Fr)
    (path : SPath) {type : STy} (value : Val E.layout type)
    (wrong : type ≠ E.cellTy path) :
    (writeAt frame path value : EM E Γ Unit).run (locals,state) =
      (.error (.stuck "storage cell type"),(locals,state)) := by
  simp only [writeAt, dif_neg wrong] <;> rfl

end MonetaryStorage
end Solidity.Source

/-- info: 'Solidity.Source.ExecState.storage_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.ExecState.storage_balancesFit
/-- info: 'Solidity.Source.ExecState.transient_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.ExecState.transient_balancesFit
/-- info: 'Solidity.Source.MonetaryStorage.applyOp_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.applyOp_run
/-- info: 'Solidity.Source.MonetaryStorage.setCell_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.setCell_preserves
/-- info: 'Solidity.Source.MonetaryStorage.writeAt_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.writeAt_preserves

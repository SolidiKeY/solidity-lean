import Solidity.Yul.World.DelegateBody

namespace Solidity.Yul.World.DelegateEntry
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.DelegateBody

/-- Narrow selected-code port. None is unsupported code selection, not an EVM
revert. Actual enterInstance supplies execution, fresh memory and rollback.
Depth eligibility is checked by the consumer; this is not Source.callAddr. -/
def execute (failed : Bool) (G : Glob env) (owner sender target : Address)
    (value : Word) (depth horizon : Nat) (bytes : Bytes) (s : EMState env []) :
    Option (Except Halt Outcome × EMState env []) :=
  match (Source.instanceAt (glob failed G) target).run s with
  | (.ok (some "Finite"),selected) =>
      some ((Source.enterInstance (glob failed G) horizon owner sender value bytes false "Finite" depth
        (selected.2.ex.journal.length,selected.2.logs.length,selected.2.heap)).run selected)
  | _ => none

theorem selection (failed : Bool) (G : Glob env) (target : Address) (s : EMState env [])
    (code : (s.2.ex.world.accounts target).code=some 0) :
    (Source.instanceAt (glob failed G) target).run s=(.ok (some "Finite"),s) := by
  simp only [Source.instanceAt,Source.Hoare.run_bind,ReturningCall.run_st,code,ReturningCall.run_pure]
  rfl

theorem success (G : Glob env) (a sender target : Address) (v : Word) (depth : Nat)
    (s : EMState env []) (code : (s.2.ex.world.accounts target).code=some 0) :
    execute false G a sender target v depth 9 (input G) s=
      some (.ok (.success ReturningCall.output),changed s a) := by
  simp only [execute,selection false G target s code,DelegateBody.enter_success]
  rfl

theorem rollback_write (s : EMState env []) (a : Address) :
    ((Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run (changed s a)).2=s := by
  change (s.1,{s.2 with ex := (s.2.ex.apply (writeOp a)).undoN ((s.2.ex.apply (writeOp a)).journal.length - s.2.ex.journal.length), logs := s.2.logs.drop (s.2.logs.length - s.2.logs.length)}) = s
  rw [ExecState.journal_apply,show s.2.ex.journal.length+1-s.2.ex.journal.length=1 from by omega,
    ExecState.undoN,ExecState.undo_apply]
  simp only [Nat.sub_self,List.drop_zero,ExecState.undoN]

theorem revert_exact (G : Glob env) (a sender target : Address) (v : Word) (depth : Nat)
    (s : EMState env []) (code : (s.2.ex.world.accounts target).code=some 0) :
    execute true G a sender target v depth 9 (input G) s=
      some (.ok (.revert (errorData G)),s) := by
  simp only [execute,selection true G target s code,DelegateBody.enter_revert]
  change some ((Except.ok (Outcome.revert (errorData G)) : Except Halt Outcome),((Source.rollbackTo
    (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run (changed s a)).2)=_
  rw [rollback_write]

theorem timeout (failed : Bool) (G : Glob env) (a sender target : Address) (v : Word) (depth : Nat)
    (s : EMState env []) (code : (s.2.ex.world.accounts target).code=some 0) :
    execute failed G a sender target v depth 5 (input G) s=some (.error .timeout,s) := by
  simp only [execute,selection failed G target s code,DelegateBody.enter_timeout]

/-- Full caller fields are preserved, not just their value projections. -/
theorem success_frame {Γ} (s : EMState env Γ) (a : Address) :
    (changed s a).1=s.1 ∧ (changed s a).2.heap=s.2.heap ∧
    (changed s a).2.fnLocals=s.2.fnLocals ∧ (changed s a).2.events=s.2.events ∧
    (changed s a).2.logs=s.2.logs := ⟨rfl,rfl,rfl,rfl,rfl⟩
end Solidity.Yul.World.DelegateEntry

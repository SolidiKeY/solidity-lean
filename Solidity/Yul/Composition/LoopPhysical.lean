import Solidity.Yul.Composition.LocalPhysicalControls

/-! Actual scoped Yul FOR execution AFTER the actual physical source step.
This is a component loop, not old Source.RStmt loop dispatch, compiler lowering
or final coverage of the Solidity-loop combination. No raw EM resumption. -/
namespace Solidity.Yul.Composition.LoopPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open LocalPhysicalControls

def binary (op : Pure 2) (a b : Expr [] X 1 1) : Expr [] X 1 1 :=
  .builtin (.pure op) (Fin.cases a (Fin.cases b Fin.elim0))
def condition (count : Nat) : Expr [] X 1 1 := binary .lt (.local 0) (.literal (word count))
def post : Stmt [] X ⟨false,false⟩ 1 :=
  .assign (Fin.cases (.local 0) Fin.elim0) (binary .add (.local 0) (.literal (word 1)))
def increment : Stmt [] X ⟨false,true⟩ 1 :=
  .assign (Fin.cases (.external small.writeRef) Fin.elim0)
    (binary .add (.external small.readRef) (.literal (word 256)))
def body (transfer : Nat) : Stmt [] X ⟨false,true⟩ 1 :=
  .seq increment (if transfer=1 then .continue_ else if transfer=2 then .break_ else .skip)
def code (count transfer : Nat) : Stmt [] X ⟨false,false⟩ 0 :=
  .seq (dirtyCode _) (.zero 1 (.for_ .skip (condition count) post (body transfer)))
def policy (count transfer : Nat) : Policy.StmtP .A (code count transfer) := by
  apply (Policy.stmt_iff .A _).mp
  cases transfer with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n <;> rfl

def run (count transfer fuel : Nat) := runLocalBlock ctx (code count transfer) (policy count transfer) fuel
  (LocalState.ofClean firstPhysical.1.1.2)
theorem loop_completes : (run 3 0 32).isSome := by decide +kernel
def completed := (run 3 0 32).get loop_completes

theorem three_iterations : snapshot completed.state =
    [2,2^256-1,2309737967,1025,22136,2^256-1,171*2^248] := by decide +kernel

theorem loop_normal : completed.flow = .normal := rfl

theorem loop_source : completed.state.2 = firstPhysical.1.1.2.2 :=
  runLocalBlock_world ctx (code 3 0) (policy 3 0) 32 _ (Option.some_get loop_completes).symm

theorem loop_nonword : completed.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index :=
  runLocalBlock_nonword ctx (code 3 0) (policy 3 0) 32 _ (Option.some_get loop_completes).symm memoryRef memoryShape rfl

theorem loop_physical_word :
    reencodePersistentSlot (representedBanks originRegistry false firstPhysical.2)
      ⟨completed.state.2.ex,firstPhysical.1.2⟩ account 43 = some ownedOriginRequest.raw := by
  rw [loop_source]
  exact physical_checked.2.2

theorem loop_all_completed (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run 3 0 fuel = some result) : result=completed :=
  LocalBlockLogic.completed_unique (code 3 0) (policy 3 0) _ done (Option.some_get loop_completes).symm

/-- CONTINUE runs the post and next test; BREAK runs neither and is consumed. -/
theorem transfer_runs_complete : (run 3 1 32).isSome ∧ (run 3 2 32).isSome := by decide +kernel

theorem continue_iterations : snapshot ((run 3 1 32).get transfer_runs_complete.1).state =
    [2,2^256-1,2309737967,1025,22136,2^256-1,171*2^248] := by decide +kernel

theorem break_one_iteration : snapshot ((run 3 2 32).get transfer_runs_complete.2).state =
    [2,2^256-1,2309737967,513,22136,2^256-1,171*2^248] := by decide +kernel

theorem transfers_consumed : ((run 3 1 32).get transfer_runs_complete.1).flow = .normal ∧
    ((run 3 2 32).get transfer_runs_complete.2).flow = .normal := ⟨rfl,rfl⟩

theorem wrong_count_control : (run 2 0 32).map (fun result=>snapshot result.state) =
    some [2,2^256-1,2309737967,769,22136,2^256-1,171*2^248] := by decide +kernel

example : (run 3 0 0).isNone = true := rfl
#print axioms three_iterations
#print axioms loop_source
#print axioms loop_all_completed
#print axioms continue_iterations
#print axioms break_one_iteration
end Solidity.Yul.Composition.LoopPhysical

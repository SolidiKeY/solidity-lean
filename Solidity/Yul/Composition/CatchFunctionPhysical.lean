import Solidity.Yul.Composition.RawCatchPhysical

/-! Scoped function continuation of the EXISTING raw catch result. No dirty
initializer/ofClean in the real path; existing intrinsic bodies and runner only.
This is not general raw Source function/session dispatch or compiler adequacy. -/
namespace Solidity.Yul.Composition.CatchFunctionPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

def code (withLeave wrongCallee : Bool) : Stmt [] X ⟨false,false⟩ 0 :=
  .functions FunctionPhysical.F (FunctionPhysical.definitions withLeave)
    (.assign (Fin.cases (.external small.writeRef) Fin.elim0)
      (.call (if wrongCallee then .here else .there .here)
        (Fin.cases (.external small.readRef) Fin.elim0)))
def policy (withLeave wrongCallee : Bool) : Policy.StmtP .A (code withLeave wrongCallee) := by
  apply (Policy.stmt_iff .A _).mp
  cases withLeave <;> cases wrongCallee <;> rfl

def runFrom (withLeave wrongCallee : Bool) (fuel : Nat) (state : LocalState originEnv ctx.tys) :=
  runLocalBlock ctx (code withLeave wrongCallee) (policy withLeave wrongCallee) fuel state

def run (withLeave wrongCallee : Bool) (fuel : Nat) :=
  runFrom withLeave wrongCallee fuel RawCatchPhysical.completed.state

/-- Every typed raw input and EVERY horizon; no execution oracle premise. -/
theorem all_horizon_rebase (withLeave wrongCallee : Bool) (fuel : Nat)
    (values : LocalValues originEnv ctx.tys) (first last : Source.St originEnv) :
    runFrom withLeave wrongCallee fuel (values,last) =
      (runFrom withLeave wrongCallee fuel (values,first)).map
        (fun result => ⟨(result.state.1,last),result.flow⟩) :=
  local_rebase ctx (code withLeave wrongCallee) (policy withLeave wrongCallee) fuel values first last

theorem source_preserved (state : LocalState originEnv ctx.tys) (fuel : Nat)
    (result : LocalBlockOutcome ctx ⟨false,false⟩) (done : runFrom true false fuel state = some result) :
    result.state.2 = state.2 := runLocalBlock_world ctx (code true false) (policy true false) fuel state done

theorem nonword_preserved (state : LocalState originEnv ctx.tys) (fuel : Nat)
    (result : LocalBlockOutcome ctx ⟨false,false⟩) (done : runFrom true false fuel state = some result) :
    result.state.1.get memoryRef.index = state.1.get memoryRef.index :=
  runLocalBlock_nonword ctx (code true false) (policy true false) fuel state done memoryRef memoryShape rfl

theorem completed_from_unique (state : LocalState originEnv ctx.tys) (a b : Nat)
    (first last : LocalBlockOutcome ctx ⟨false,false⟩)
    (one : runFrom true false a state = some first) (two : runFrom true false b state = some last) : first=last :=
  LocalBlockLogic.completed_unique (code true false) (policy true false) state one two

theorem raw_from (state : LocalState originEnv ctx.tys) (fuel : Nat)
    (result : LocalBlockOutcome ctx ⟨false,false⟩) (done : runFrom true false fuel state = some result) :
    LocalState.clean? result.state = none := by
  unfold runFrom runLocalBlock at done
  cases actual : WordAdapter.run (code true false) (policy true false) fuel ⟨Fin.elim0,localWordCells ctx state.1⟩ with
  | none => rw [actual] at done; cases done
  | some raw =>
      rw [actual] at done
      cases done
      change (LocalValues.clean? ctx.tys (writebackLocalWords ctx state.1 raw.state.cells)).map _ = none
      rw [RawCatchPhysical.writeback_raw]
      rfl

theorem completes : (run true false 32).isSome := by decide +kernel
def completed : LocalBlockOutcome ctx ⟨false,false⟩ := (run true false 32).get completes

theorem exact_words : snapshot completed.state =
    [2,2^256-1,2309737967,1793,22136,2^256-1,171*2^248] := by decide +kernel

theorem normal_return : completed.flow = .normal := FunctionPhysical.normal_flow _

theorem caller_source_retained : completed.state.2 = LocalPhysicalControls.initial.2 := by
  have kept : completed.state.2 = RawCatchPhysical.completed.state.2 :=
    source_preserved _ 32 completed (Option.some_get completes).symm
  exact kept.trans RawCatchPhysical.caller_source_retained

theorem nonword_retained : completed.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index := by
  have kept : completed.state.1.get memoryRef.index = RawCatchPhysical.completed.state.1.get memoryRef.index :=
    nonword_preserved _ 32 completed (Option.some_get completes).symm
  exact kept.trans RawCatchPhysical.nonword_retained

theorem raw_not_clean : LocalState.clean? completed.state = none :=
  raw_from _ 32 completed (Option.some_get completes).symm

theorem no_clean_resume (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action completed.state = none := LocalState.runClean_refuses action _ raw_not_clean

theorem all_completed (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run true false fuel = some result) : result=completed :=
  completed_from_unique _ fuel 32 result completed done (Option.some_get completes).symm

theorem wrong_callee : (run true true 32).map (fun result=>snapshot result.state) =
    some [2,2^256-1,2309737967,1537,22136,2^256-1,171*2^248] := by decide +kernel

theorem missing_leave : (run false false 32).map (fun result=>snapshot result.state) =
    some [2,2^256-1,2309737967,0,22136,2^256-1,171*2^248] := by decide +kernel

/-- Wrong input RESET is a separate negative control, not the real path. -/
theorem raw_reset_control : (runFrom true false 32 (LocalState.ofClean LocalPhysicalControls.initial)).map (fun result=>snapshot result.state) =
    some [1,4660,2309737967,513,22136,16909060,171*2^248] := by decide +kernel

theorem heap_alias : completed.state.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0xaa,0xbb]⟩ := by
  rw [caller_source_retained]
  rfl

theorem coupled_journals :
    revertedCore = ⟨completed.state.2.ex,ownedOriginResidual⟩ ∧ revertedEncoding = boolEncodingInitial := by
  rw [caller_source_retained]
  exact three_journals_restore

theorem restored_word : reencodePersistentSlot (representedBanks originRegistry false revertedEncoding)
    ⟨completed.state.2.ex,revertedCore.residual⟩ account 43 = some (word 0) := by
  rw [caller_source_retained]
  decide +kernel

theorem exact_failure (data : List UInt8) : RawCatchPhysical.reverted data =
    ⟨completed.state.2.ex,[⟨account,⟨0,by decide⟩,#v[],[0x55]⟩],data⟩ := by
  rw [caller_source_retained]
  exact RawCatchPhysical.exact_failure data

theorem failure_window : (RawCatchPhysical.failureCopy [0xde,0xad]).map (fun out =>
    (out.1.returndata,[out.2.memory 30,out.2.memory 31,out.2.memory 32,out.2.memory 33])) =
      some ([0xde,0xad],[0xee,0xde,0xad,0xee]) := RawCatchPhysical.failure_window

theorem wrong_argument_arity : Member FunctionPhysical.F ⟨2,1⟩ → False := FunctionPhysical.wrong_argument_arity

theorem wrong_result_arity : Member FunctionPhysical.F ⟨1,2⟩ → False := FunctionPhysical.wrong_result_arity

theorem zero_horizon : run true false 0 = none := rfl
#print axioms exact_words
#print axioms all_horizon_rebase
#print axioms completed_from_unique
#print axioms caller_source_retained
#print axioms coupled_journals
#print axioms exact_failure
end Solidity.Yul.Composition.CatchFunctionPhysical

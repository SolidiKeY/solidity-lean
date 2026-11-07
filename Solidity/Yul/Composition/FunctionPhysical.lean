import Solidity.Yul.Composition.LoopPhysical

/-! Actual scoped function calls from the actual intrinsic Yul loop after the
selected physical source action. No outer local capture, duplicate interpreter,
old Source dispatch/raw resumption, compiler theorem or full Source combination. -/
namespace Solidity.Yul.Composition.FunctionPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open LocalPhysicalControls

def signature : Sig := ⟨1,1⟩
abbrev F := [signature,signature]
def binary {F X n} (op : Pure 2) (a b : Expr F X n 1) : Expr F X n 1 :=
  .builtin (.pure op) (Fin.cases a (Fin.cases b Fin.elim0))

def returnTo (value : Expr F [] 2 1) : Stmt F [] ⟨true,false⟩ 2 :=
  .assign (Fin.cases (.local 1) Fin.elim0) value
/-- First function returns normally, without leave. -/
def incrementBody : Stmt F [] ⟨true,false⟩ 2 :=
  returnTo (binary .add (.local 0) (.literal (word 256)))
/-- Second function makes a genuine nested call. Leave must prevent poison0. -/
def nestedBody (withLeave : Bool) : Stmt F [] ⟨true,false⟩ 2 :=
  .seq (returnTo (.call .here (Fin.cases
    (binary .add (.local 0) (.literal (word 256))) Fin.elim0)))
    (.seq (if withLeave then .leave else .skip) (returnTo (.literal (word 0))))
def definitions (withLeave : Bool) : Bodies F [] F :=
  .cons incrementBody (.cons (nestedBody withLeave) .nil)

def condition : Expr F X 1 1 := binary .lt (.local 0) (.literal (word 3))
def post : Stmt F X ⟨false,false⟩ 1 :=
  .assign (Fin.cases (.local 0) Fin.elim0) (binary .add (.local 0) (.literal (word 1)))
def body (wrongCallee : Bool) : Stmt F X ⟨false,true⟩ 1 :=
  .assign (Fin.cases (.external small.writeRef) Fin.elim0)
    (.call (if wrongCallee then .here else .there .here)
      (Fin.cases (.external small.readRef) Fin.elim0))
def code (withLeave wrongCallee : Bool) : Stmt [] X ⟨false,false⟩ 0 :=
  .seq (dirtyCode _) (.functions F (definitions withLeave)
    (.zero 1 (.for_ .skip condition post (body wrongCallee))))
def policy (withLeave wrongCallee : Bool) : Policy.StmtP .A (code withLeave wrongCallee) := by
  apply (Policy.stmt_iff .A _).mp
  cases withLeave <;> cases wrongCallee <;> rfl

def run (withLeave wrongCallee : Bool) (fuel : Nat) : Option (LocalBlockOutcome ctx ⟨false,false⟩) :=
  runLocalBlock ctx (code withLeave wrongCallee) (policy withLeave wrongCallee) fuel
    (LocalState.ofClean LocalPhysicalControls.firstPhysical.1.1.2)
def joint (fuel : Nat) := representedThenLocal ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
  packedStepFrame ownedOriginPlan initial ownedOriginResidual (code true false) (policy true false) fuel

theorem run_source (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run true false fuel = some result) : result.state.2 = LocalPhysicalControls.firstPhysical.1.1.2.2 :=
  runLocalBlock_world ctx (code true false) (policy true false) fuel _ done

theorem run_nonword (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run true false fuel = some result) :
    result.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index :=
  runLocalBlock_nonword ctx (code true false) (policy true false) fuel _ done memoryRef memoryShape rfl

theorem writeback_raw (cells : WordCells X) :
    LocalValues.clean? ctx.tys (writebackLocalWords ctx (LocalValues.ofClean locals) cells) = none := rfl

theorem run_raw (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run true false fuel = some result) : LocalState.clean? result.state = none := by
  unfold run runLocalBlock at done
  dsimp only [LocalState.ofClean] at done
  cases actual : WordAdapter.run (code true false) (policy true false) fuel
      ⟨Fin.elim0,localWordCells ctx (LocalValues.ofClean LocalPhysicalControls.firstPhysical.1.1.2.1)⟩ with
  | none => rw [actual] at done; cases done
  | some raw =>
      rw [actual] at done
      cases done
      change (LocalValues.clean? ctx.tys (writebackLocalWords ctx (LocalValues.ofClean locals) raw.state.cells)).map _ = none
      rw [writeback_raw]
      rfl

theorem completes : (run true false 32).isSome := by decide +kernel
def completed : LocalBlockOutcome ctx ⟨false,false⟩ := (run true false 32).get completes

theorem nested_loop_words : snapshot completed.state =
    [2,2^256-1,2309737967,1793,22136,2^256-1,171*2^248] := by decide +kernel

theorem normal_flow (flow : Closed.Flow ⟨false,false⟩) : flow = .normal := by
  cases flow with
  | normal => rfl
  | leave_ impossible => cases impossible
  | break_ impossible => cases impossible
  | continue_ impossible => cases impossible

theorem leave_consumed : completed.flow = .normal := normal_flow _

theorem physical_result_retained (fuel : Nat) : (joint fuel).1 = LocalPhysicalControls.firstPhysical := rfl

theorem joint_completes : (joint 32).2 = .ok (some completed) :=
  congrArg Except.ok (Option.some_get completes).symm

theorem source_retained : completed.state.2 = LocalPhysicalControls.firstPhysical.1.1.2.2 :=
  run_source 32 completed (Option.some_get completes).symm

theorem nonword_retained : completed.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index :=
  run_nonword 32 completed (Option.some_get completes).symm

theorem raw_not_clean : LocalState.clean? completed.state = none :=
  run_raw 32 completed (Option.some_get completes).symm

theorem no_clean_resume (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action completed.state = none := LocalState.runClean_refuses action _ raw_not_clean

theorem physical_word : reencodePersistentSlot (representedBanks originRegistry false LocalPhysicalControls.firstPhysical.2)
    ⟨completed.state.2.ex,LocalPhysicalControls.firstPhysical.1.2⟩ account 43 = some ownedOriginRequest.raw := by
  rw [source_retained]
  exact physical_checked.2.2

theorem all_completed (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run true false fuel = some result) : result=completed := by
  rcases Nat.le_total fuel 32 with lower | upper
  · have stable := runLocalBlock_stable ctx (code true false) (policy true false) _ lower done
    exact Option.some.inj (stable.symm.trans (Option.some_get completes).symm)
  · have stable := runLocalBlock_stable ctx (code true false) (policy true false) _ upper (Option.some_get completes).symm
    exact Option.some.inj (done.symm.trans stable)

theorem wrong_callee_control : (run true true 32).map (fun result=>snapshot result.state) =
    some [2,2^256-1,2309737967,1025,22136,2^256-1,171*2^248] := by decide +kernel

theorem missing_leave_control : (run false false 32).map (fun result=>snapshot result.state) =
    some [2,2^256-1,2309737967,0,22136,2^256-1,171*2^248] := by decide +kernel

/-- No wrong input/output arity reference can inhabit this actual group. -/
theorem group_arity (sig : Sig) (ref : Member F sig) : sig.args=1 ∧ sig.rets=1 := by
  cases ref with
  | here => exact ⟨rfl,rfl⟩
  | there tail => cases tail with
    | here => exact ⟨rfl,rfl⟩
    | there impossible => cases impossible

theorem wrong_argument_arity : Member F ⟨2,1⟩ → False := by
  intro ref
  have impossible : (2:Nat)=1 := (group_arity _ ref).1
  cases impossible

theorem wrong_result_arity : Member F ⟨1,2⟩ → False := by
  intro ref
  have impossible : (2:Nat)=1 := (group_arity _ ref).2
  cases impossible

theorem heap_window_target :
    completed.state.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0xaa,0xbb]⟩ ∧
    ReservedOK memoryView placement.free ∧
    target = some {(PhysicalMemoryControls.caller) with memory := copyBytes PhysicalMemoryControls.caller.memory memoryView 31 (placement.address 0+33) 1} ∧
    ValidRange (placement.address 0+33) 1 :=
  local_heap_window_target ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan initial ownedOriginResidual (code true false) (policy true false) 32 joint_completes
    placement 0 [0xaa,0xbb] (by decide) rfl LocalPhysicalControls.reserved reserved_valid 1 1 31 [0xbb] (by decide)
    PhysicalMemoryControls.caller (by decide)

/-- Actual coupled physical rollback is retained separately. Raw locals are
rebased between real runs, never resumed as old clean Source.Locals. -/
theorem rollback_transport (fuel : Nat) :
    runLocalBlock ctx (code true false) (policy true false) fuel (LocalValues.ofClean locals,restored.2) =
      (runLocalBlock ctx (code true false) (policy true false) fuel
        (LocalValues.ofClean locals,childPhysical.1.1.2.2)).map
        (fun result => ⟨(result.state.1,initial.2),result.flow⟩) := by
  rw [full_source_restored]
  exact local_rebase ctx (code true false) (policy true false) fuel _ _ _

theorem actual_three_journals :
    revertedCore = ⟨initial.2.ex,ownedOriginResidual⟩ ∧ revertedEncoding = boolEncodingInitial := three_journals_restore

theorem static_no_call (fuel : Nat) :
    (representedThenLocal ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
      {packedStepFrame with static:=true} ownedOriginPlan initial ownedOriginResidual (code true false) (policy true false) fuel).2 =
      .error (.revert []) :=
  congrArg Prod.snd (represented_local_static ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    {packedStepFrame with static:=true} ownedOriginPlan initial ownedOriginResidual (code true false) (policy true false) fuel rfl)

theorem small_horizon_control : (run true false 4).isNone = true := by decide +kernel
#print axioms heap_window_target
#print axioms rollback_transport
#print axioms wrong_argument_arity
#print axioms static_no_call
example : (run true false 0).isNone = true := rfl
#print axioms nested_loop_words
#print axioms source_retained
#print axioms all_completed
#print axioms wrong_callee_control
#print axioms missing_leave_control
end Solidity.Yul.Composition.FunctionPhysical

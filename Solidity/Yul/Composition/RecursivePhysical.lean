import Solidity.Yul.Composition.FunctionPhysical

/-! A genuine self-call in the staged intrinsic runner, after the actual physical
source action. No raw Source resumption or compiler/world adequacy is claimed. -/
namespace Solidity.Yul.Composition.RecursivePhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls
open FunctionPhysical (binary)
def signature : Sig := ⟨2,1⟩
abbrev F := [signature]
def put (value : Expr F [] 3 1) : Stmt F [] ⟨true,false⟩ 3 :=
  .assign (Fin.cases (.local 2) Fin.elim0) value
/-- Counter0 leaves with the accumulator. The recursive branch calls THIS body. -/
def recursiveBody (decrement : Bool) : Stmt F [] ⟨true,false⟩ 3 :=
  .seq (.if_ (.builtin (.pure .iszero) (Fin.cases (.local 0) Fin.elim0))
    (.seq (put (.local 1)) .leave))
    (put (.call .here (Fin.cases
      (if decrement then binary .sub (.local 0) (.literal (word 1)) else .local 0)
      (Fin.cases (binary .add (.local 1) (.literal (word 256))) Fin.elim0))))
def definitions (decrement : Bool) : Bodies F [] F := .cons (recursiveBody decrement) .nil
def code (decrement : Bool) : Stmt [] X ⟨false,false⟩ 0 :=
  .seq (dirtyCode _) (.functions F (definitions decrement)
    (.assign (Fin.cases (.external small.writeRef) Fin.elim0)
      (.call .here (Fin.cases (.literal (word 3))
        (Fin.cases (.external small.readRef) Fin.elim0)))))
def policy (decrement : Bool) : Policy.StmtP .A (code decrement) := by
  apply (Policy.stmt_iff .A _).mp
  cases decrement <;> rfl
def run (decrement : Bool) (fuel : Nat) : Option (LocalBlockOutcome ctx ⟨false,false⟩) :=
  runLocalBlock ctx (code decrement) (policy decrement) fuel
    (LocalState.ofClean LocalPhysicalControls.firstPhysical.1.1.2)
def joint (fuel : Nat) := representedThenLocal ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
  packedStepFrame ownedOriginPlan initial ownedOriginResidual (code true) (policy true) fuel

theorem source_preserved (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run true fuel = some result) : result.state.2 = LocalPhysicalControls.firstPhysical.1.1.2.2 :=
  runLocalBlock_world ctx (code true) (policy true) fuel _ done
theorem nonword_preserved (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run true fuel = some result) :
    result.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index :=
  runLocalBlock_nonword ctx (code true) (policy true) fuel _ done memoryRef memoryShape rfl

theorem raw_preserved (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run true fuel = some result) : LocalState.clean? result.state = none := by
  unfold run runLocalBlock at done
  dsimp only [LocalState.ofClean] at done
  cases actual : WordAdapter.run (code true) (policy true) fuel
      ⟨Fin.elim0,localWordCells ctx (LocalValues.ofClean LocalPhysicalControls.firstPhysical.1.1.2.1)⟩ with
  | none => rw [actual] at done; cases done
  | some raw =>
      rw [actual] at done
      cases done
      change (LocalValues.clean? ctx.tys (writebackLocalWords ctx (LocalValues.ofClean locals) raw.state.cells)).map _ = none
      rw [FunctionPhysical.writeback_raw]
      rfl

theorem completes : (run true 32).isSome := by decide +kernel
def completed : LocalBlockOutcome ctx ⟨false,false⟩ := (run true 32).get completes
theorem recursive_words : snapshot completed.state =
    [2,2^256-1,2309737967,1025,22136,2^256-1,171*2^248] := by decide +kernel
theorem normal_return : completed.flow = .normal := FunctionPhysical.normal_flow _
theorem completed_unique (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : run true fuel = some result) : result=completed :=
  runLocalBlock_unique ctx (code true) (policy true) _ done (Option.some_get completes).symm
theorem physical_retained (fuel : Nat) : (joint fuel).1 = LocalPhysicalControls.firstPhysical := rfl
theorem joint_completes : (joint 32).2 = .ok (some completed) :=
  congrArg Except.ok (Option.some_get completes).symm
theorem source_retained : completed.state.2 = LocalPhysicalControls.firstPhysical.1.1.2.2 :=
  source_preserved 32 completed (Option.some_get completes).symm
theorem physical_word : reencodePersistentSlot (representedBanks originRegistry false LocalPhysicalControls.firstPhysical.2)
    ⟨completed.state.2.ex,LocalPhysicalControls.firstPhysical.1.2⟩ account 43 = some ownedOriginRequest.raw := by
  rw [source_retained]
  exact physical_checked.2.2
theorem heap_window_target :
    completed.state.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0xaa,0xbb]⟩ ∧
    ReservedOK memoryView placement.free ∧
    target = some {(PhysicalMemoryControls.caller) with memory := copyBytes PhysicalMemoryControls.caller.memory memoryView 31 (placement.address 0+33) 1} ∧
    ValidRange (placement.address 0+33) 1 :=
  local_heap_window_target ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan initial ownedOriginResidual (code true) (policy true) 32 joint_completes
    placement 0 [0xaa,0xbb] (by decide) rfl LocalPhysicalControls.reserved reserved_valid 1 1 31 [0xbb] (by decide)
    PhysicalMemoryControls.caller (by decide)
/-- All actual physical journals remain coupled; this is not raw-local rollback. -/
theorem actual_three_journals :
    revertedCore = ⟨initial.2.ex,ownedOriginResidual⟩ ∧ revertedEncoding = boolEncodingInitial := three_journals_restore
theorem rollback_transport (fuel : Nat) :
    runLocalBlock ctx (code true) (policy true) fuel (LocalValues.ofClean locals,restored.2) =
      (runLocalBlock ctx (code true) (policy true) fuel
        (LocalValues.ofClean locals,childPhysical.1.1.2.2)).map
        (fun result => ⟨(result.state.1,initial.2),result.flow⟩) := by
  rw [full_source_restored]
  exact local_rebase ctx (code true) (policy true) fuel _ _ _
theorem missing_decrement_control : (run false 32).isNone = true := by decide +kernel
theorem prefix_control : (run true 4).isNone = true := by decide +kernel
theorem zero_control : run true 0 = none := rfl
theorem wrong_argument_arity : Member F ⟨1,1⟩ → False := by
  intro ref
  cases ref with
  | there impossible => cases impossible
#print axioms recursive_words
#print axioms completed_unique
#print axioms physical_word
#print axioms heap_window_target
#print axioms actual_three_journals
#print axioms rollback_transport
#print axioms missing_decrement_control
end Solidity.Yul.Composition.RecursivePhysical

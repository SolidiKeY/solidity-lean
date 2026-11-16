import Solidity.Yul.Compilation.ScopedForCompilation
import Solidity.Yul.Compilation.ScopedLoopExecutionControls
/-! Actual initialized FOR with conditional/scoped body and nontrivial post.
Initializer+3 executes even on zero exit; post+7 only follows an executed body.
All full raw words, caller tails and model nonstack fields are retained. -/
namespace Solidity.Yul.Compilation.ScopedForCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)
open ScopedLoopExecution.Controls (work body)

def startup : Solidity.Yul.Stmt [] [] root 2 :=
 .assign (fun _ : Fin 1 => .local 1)
  (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .literal 3)))
def startupReference : ProducerStatements.Compiled 7 startup :=
 ProducerStatements.assign 1 (binary addBridge (localExpr 4 1) (literal 4 3))
def step : Solidity.Yul.Stmt [] [] root 2 :=
 .assign (fun _ : Fin 1 => .local 1)
  (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .literal 7)))
def stepReference : ProducerStatements.Compiled 6 step :=
 ProducerStatements.assign 1 (binary addBridge (localExpr 3 1) (literal 3 7))
def source : Solidity.Yul.Stmt [] [] root 2 := .for_ startup (.local 0) step work
def artifact := (lower 6 source).get (by rfl)
def finish (b c : Scalar.Word) := if b = 0 then c+3 else (c+3)+7

theorem startup_source (b c : Scalar.Word) :
 evalStmt 7 .nil True.intro startup startupReference.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[b,c+3],.normal⟩ := by
 have same : startupReference.update #v[b,c] = #v[b,c+3] := by rfl
 have ran := startupReference.source #v[b,c]
 rw [same] at ran
 exact ran

theorem step_source (c : Scalar.Word) :
 evalStmt 6 .nil True.intro step stepReference.profile (sourceLocals #v[0,c]) =
 some ⟨sourceLocals #v[0,c+7],.normal⟩ := by
 have same : stepReference.update #v[0,c] = #v[0,c+7] := by rfl
 have ran := stepReference.source #v[0,c]
 rw [same] at ran
 exact ran

theorem loop_source (b c : Scalar.Word) (nonzero : b ≠ 0) :
 evalLoop (c := root) 7 .nil True.intro (.local 0) True.intro step stepReference.profile
   work body.compiled.profile (sourceLocals #v[b,c]) = some ⟨sourceLocals #v[0,c+7],.normal⟩ := by
 have nz : b.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 change (if b.toNat = 0 then some (⟨sourceLocals #v[b,c],.normal⟩ : Outcome root 2) else _) = _
 rw [if_neg nz]
 change Option.bind (evalStmt 6 .nil True.intro work body.compiled.profile (sourceLocals #v[b,c])) _ = _
 rw [ScopedLoopExecution.Controls.body_source b c nonzero]
 change Option.bind (evalStmt 6 .nil True.intro step stepReference.profile (sourceLocals #v[0,c])) _ = _
 rw [step_source c]
 change evalLoop (c := root) 6 .nil True.intro (.local 0) True.intro step stepReference.profile
   work body.compiled.profile (sourceLocals #v[0,c+7]) = _
 rfl

theorem source_done (b c : Scalar.Word) :
 evalStmt 8 .nil True.intro source artifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[0,finish b c],.normal⟩ := by
 have phase : evalLoop (c := root) 7 .nil True.intro (.local 0) True.intro step stepReference.profile
   work body.compiled.profile (sourceLocals #v[b,c+3]) = some ⟨sourceLocals #v[0,finish b c],.normal⟩ := by
  by_cases zero : b = 0
  · subst b
    rw [finish,if_pos rfl]
    exact CompletionControls.completed_horizon
      (fun fuel => evalLoop (c := root) fuel .nil True.intro (.local 0) True.intro
        step stepReference.profile work body.compiled.profile (sourceLocals #v[0,c+3]))
      (fun fuel extra => evalLoop_refines_add (c := root) fuel extra .nil True.intro (.local 0) True.intro
        step stepReference.profile work body.compiled.profile (sourceLocals #v[0,c+3]))
      (show 2 ≤ 7 by omega) (by rfl)
  · rw [finish,if_neg zero]
    exact loop_source b (c+3) zero
 exact source_for (c := root) (pre := startup) (test := .local 0) (post := step) (body := work) startupReference.profile True.intro stepReference.profile body.compiled.profile
   7 #v[b,c] #v[b,c+3] #v[0,finish b c] (startup_source b c) phase

theorem target_done (b c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::coreWord c::caller} =
 .ok {m with stack := coreWord 0::coreWord (finish b c)::caller} 0 :=
 artifact.normal_to_model 8 #v[b,c] #v[0,finish b c] (source_done b c) m caller

theorem zero_target (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord 0::coreWord c::caller} =
 .ok {m with stack := coreWord 0::coreWord (c+3)::caller} 0 := by
 simpa only [finish,ite_true] using target_done 0 c m caller

theorem nonzero_target (b c : Scalar.Word) (nonzero : b ≠ 0) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::coreWord c::caller} =
 .ok {m with stack := coreWord 0::coreWord ((c+3)+7)::caller} 0 := by
 simpa only [finish,if_neg nonzero] using target_done b c m caller

#guard (ForCompilation.lower 6 source 0).isNone
#guard (lower 0 source).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty,dirty])).isNone
#guard finish dirty dirty = BitVec.ofNat 256 (2^200+267)
#guard finish 0 dirty = BitVec.ofNat 256 (2^200+260)
#guard finish 0 dirty ≠ finish dirty dirty
-- Isolated resource/operand controls are not whole-artifact native validity.
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false
#guard Scalar.run [Backend.Instr.op (.DUP 0)] [] = none

/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.Controls.startup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms startup_source
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.Controls.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms step_source
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.Controls.loop_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loop_source
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.Controls.zero_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_target
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.Controls.nonzero_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nonzero_target
end Solidity.Yul.Compilation.ScopedForCompilation.Controls

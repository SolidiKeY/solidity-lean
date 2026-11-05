import Solidity.Yul.Compilation.SequenceCompletion
/-! Original zero scopes around actual recursive sequence/switch bodies.
Existing top-first prefix entry, source context extension and prefix retirement
are reused, without a new layout or source representation. Whole normal-success
proofs do not discharge actual scalar trace capacity or native/Source/G24. -/
namespace Solidity.Yul.Compilation.ZeroSequenceCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

structure Artifact {c n} (fresh fuel : Nat) (body : Stmt [] [] c (fresh+n)) where
 compiledBody : SequenceCompilation.Artifact fuel body
 beginCode : List Evm.Instr
 finishCode : List Evm.Instr
 entrySelected : WordMachine.selectCode (ZeroLoopScope.entry fresh) = some beginCode
 exitSelected : WordMachine.selectCode (popPrefix fresh) = some finishCode

def Artifact.profile {c n fresh fuel} {body : Stmt [] [] c (fresh+n)}
 (artifact : Artifact fresh fuel body) : StmtWordP (.zero fresh body) := artifact.compiledBody.compiled.profile

def Artifact.block {c n fresh fuel} {body : Stmt [] [] c (fresh+n)}
 (artifact : Artifact fresh fuel body) : Backend.Block :=
 .seq (.code (ZeroLoopScope.entry fresh)) (.seq artifact.compiledBody.block (.code (popPrefix fresh)))

def Artifact.code {c n fresh fuel} {body : Stmt [] [] c (fresh+n)}
 (artifact : Artifact fresh fuel body) : List Evm.Instr :=
 artifact.beginCode ++ (artifact.compiledBody.code ++ artifact.finishCode)

/-- Constructor-specific lowering of the original scope with exact extended
local count. All code comes from existing actual compilers/selectors. -/
def lower {c n} (fresh fuel : Nat) (body : Stmt [] [] c (fresh+n)) : Option (Artifact fresh fuel body) := do
 let compiled ← SequenceCompilation.lower fuel body
 match entering : WordMachine.selectCode (ZeroLoopScope.entry fresh) with
 | none => none
 | some beginCode =>
   match exiting : WordMachine.selectCode (popPrefix fresh) with
   | none => none
   | some finishCode => some ⟨compiled,beginCode,finishCode,entering,exiting⟩

theorem Artifact.selected {c n fresh fuel} {body : Stmt [] [] c (fresh+n)}
 (artifact : Artifact fresh fuel body) : WordControl.blockCode artifact.block = some artifact.code := by
 change (WordMachine.selectCode (ZeroLoopScope.entry fresh)).bind (fun p =>
   ((WordControl.blockCode artifact.compiledBody.block).bind (fun b =>
     (WordMachine.selectCode (popPrefix fresh)).map (fun q => b++q))).map (fun rest => p++rest)) = _
 rw [artifact.entrySelected,artifact.compiledBody.selected,artifact.exitSelected]
 rfl

theorem Artifact.source_to_model {c n fresh fuel} {body : Stmt [] [] c (fresh+n)}
 (artifact : Artifact fresh fuel body) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro (.zero fresh body) artifact.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 cases horizon with
 | zero => cases ran
 | succ horizon =>
   change Option.bind (evalStmt horizon .nil True.intro body artifact.compiledBody.compiled.profile
     (extendValues (fun _ : Fin fresh => word 0) (sourceLocals locals))) _ = some result at ran
   rw [←ZeroLoopScope.initial_values] at ran
   obtain ⟨middle,source,remaining⟩ := Option.bind_eq_some_iff.mp ran
   obtain ⟨out,same,bodyRun⟩ := SequenceCompilation.source_to_model artifact.compiledBody.compiled
     artifact.compiledBody.block artifact.compiledBody.code artifact.compiledBody.emitted artifact.compiledBody.selected
     horizon (Vector.replicate fresh (0 : Scalar.Word) ++ locals) middle source m caller
   subst middle
   have projected : result = ⟨sourceLocals (outerLocals out),.normal⟩ := by
     have same := (Option.some.inj remaining).symm
     rw [←ScopedStatements.locals_outer] at same
     exact same
   have entering := WordExecution.run (ZeroLoopScope.entry fresh) artifact.beginCode artifact.entrySelected locals.toList
     ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList) (pushPrefix_run _ _) m caller
   have bodyRun' : Evm.run artifact.compiledBody.code
     {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller} =
     .ok {m with stack := out.toList.map coreWord++caller} 0 := by
     simpa only [Vector.toList_append] using bodyRun
   have exiting := WordExecution.run (popPrefix fresh) artifact.finishCode artifact.exitSelected out.toList
     (outerLocals out).toList (by simpa only [List.append_nil] using popFresh_run out []) m caller
   refine ⟨outerLocals out,projected,?_⟩
   rw [Artifact.code,Evm.run_append_ok entering,Evm.run_append_ok bodyRun']
   exact exiting

/-- Body success, pending zero and its actual extended vector are derived
from whole execution; scope source completion then retires the fresh prefix. -/
theorem Artifact.model_to_source {c n fresh fuel} {body : Stmt [] [] c (fresh+n)}
 (artifact : Artifact fresh fuel body) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro (.zero fresh body) artifact.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 have entering := WordExecution.run (ZeroLoopScope.entry fresh) artifact.beginCode artifact.entrySelected locals.toList
   ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList) (pushPrefix_run _ _) m caller
 rw [Artifact.code,Evm.run_append_ok entering] at ran
 have whole : (Evm.run artifact.compiledBody.code
   {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller}).bind
   (fun middle pending => Evm.exec artifact.finishCode pending middle) = .ok final skip := by
   simpa only [Evm.run,Evm.exec_append] using ran
 cases actual : Evm.run artifact.compiledBody.code
   {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller} with
 | revert => rw [actual] at whole; cases whole
 | fault => rw [actual] at whole; cases whole
 | ok middle pending =>
   have bodyRun : Evm.run artifact.compiledBody.code
     {m with stack := (Vector.replicate fresh (0 : Scalar.Word) ++ locals).toList.map coreWord++caller} = .ok middle pending := by
     simpa only [Vector.toList_append] using actual
   obtain ⟨horizon,out,source,done,frame⟩ := SequenceCompletion.artifact_reflected artifact.compiledBody
     (Vector.replicate fresh (0 : Scalar.Word) ++ locals) m middle caller pending bodyRun
   have scopeSource := ScopedControlCompletion.source_zero artifact.compiledBody.compiled.profile horizon locals out source
   rw [actual,done,frame] at whole
   change Evm.run artifact.finishCode {m with stack := out.toList.map coreWord++caller} = .ok final skip at whole
   have exiting := WordExecution.run (popPrefix fresh) artifact.finishCode artifact.exitSelected out.toList
     (outerLocals out).toList (by simpa only [List.append_nil] using popFresh_run out []) m caller
   rw [exiting] at whole
   have parts := Evm.Out.ok.inj whole
   exact ⟨horizon+1,outerLocals out,scopeSource,parts.2.symm,parts.1.symm⟩

theorem Artifact.normal_to_model {c n fresh fuel} {body : Stmt [] [] c (fresh+n)}
 (artifact : Artifact fresh fuel body) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro (.zero fresh body) artifact.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨actual,same,target⟩ := artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller
 have equal : out = actual := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

theorem Artifact.completion_iff {c n fresh fuel} {body : Stmt [] [] c (fresh+n)}
 (artifact : Artifact fresh fuel body) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro (.zero fresh body) artifact.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 constructor
 · rintro ⟨horizon,source⟩; exact artifact.normal_to_model horizon locals out source m caller
 · intro ran
   obtain ⟨horizon,actual,source,_,frame⟩ := artifact.model_to_source locals m
     {m with stack := out.toList.map coreWord++caller} caller 0 ran
   have stacks := congrArg Evm.Machine.stack frame
   have mapped : out.toList.map coreWord = actual.toList.map coreWord := List.append_cancel_right stacks
   have lists : out.toList = actual.toList := (List.map_inj_right (fun _ _ h => coreWord_injective h)).mp mapped
   have equal : out = actual := Vector.toList_inj.mp lists
   cases equal
   exact ⟨horizon,source⟩

/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Artifact.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.selected
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Artifact.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.model_to_source
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Artifact.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.completion_iff
end Solidity.Yul.Compilation.ZeroSequenceCompilation

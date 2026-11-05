import Solidity.Yul.Compilation.SequenceCompletion
/-! Original single-result let lowering with actual recursive sequence/switch
body compilation. Original initializer values extend the top-first local frame;
actual POP retires the updated fresh word. No new source/state/layout or runtime
convention is introduced. Capacity, native and logical Source/G24 stay separate. -/
namespace Solidity.Yul.Compilation.InitializedSequenceCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

structure Artifact {c n} (f g : Nat) (rhs : Expr [] [] n 1) (body : Stmt [] [] c (1+n)) where
 initializer : ProducerExpressions.Compiled f rhs
 compiledBody : SequenceCompilation.Artifact g body
 program : Backend.Program
 beginCode : List Evm.Instr
 finishCode : List Evm.Instr
 emitted : initializer.lowered.code 0 = some program
 entrySelected : WordMachine.selectCode program = some beginCode
 exitSelected : WordMachine.selectCode (popPrefix 1) = some finishCode

def Artifact.profile {c n f g} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (artifact : Artifact f g rhs body) : StmtWordP (.let_ 1 rhs body) :=
 ⟨artifact.initializer.profile,artifact.compiledBody.compiled.profile⟩

def Artifact.block {c n f g} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (artifact : Artifact f g rhs body) : Backend.Block :=
 .seq (.code artifact.program) (.seq artifact.compiledBody.block (.code (popPrefix 1)))

def Artifact.code {c n f g} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (artifact : Artifact f g rhs body) : List Evm.Instr :=
 artifact.beginCode ++ (artifact.compiledBody.code ++ artifact.finishCode)

/-- Constructor-specific original single-result let lowering. Separate fuels
are compiler search bounds, not source horizons or native gas/capacity. -/
def lower {c n} (f g : Nat) (rhs : Expr [] [] n 1) (body : Stmt [] [] c (1+n)) : Option (Artifact f g rhs body) := do
 let initializer ← PureExpressions.compile f rhs
 let compiled ← SequenceCompilation.lower g body
 match emitted : initializer.lowered.code 0 with
 | none => none
 | some program =>
   match entering : WordMachine.selectCode program with
   | none => none
   | some beginCode =>
     match exiting : WordMachine.selectCode (popPrefix 1) with
     | none => none
     | some finishCode => some ⟨initializer,compiled,program,beginCode,finishCode,emitted,entering,exiting⟩

theorem Artifact.selected {c n f g} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (artifact : Artifact f g rhs body) : WordControl.blockCode artifact.block = some artifact.code := by
 change (WordMachine.selectCode artifact.program).bind (fun p =>
   ((WordControl.blockCode artifact.compiledBody.block).bind (fun b =>
     (WordMachine.selectCode (popPrefix 1)).map (fun q => b++q))).map (fun rest => p++rest)) = _
 rw [artifact.entrySelected,artifact.compiledBody.selected,artifact.exitSelected]
 rfl

theorem Artifact.entry_run {c n f g} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (artifact : Artifact f g rhs body) (locals : Vector Scalar.Word n) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.beginCode {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := coreWord (artifact.initializer.value locals)::(locals.toList.map coreWord++caller)} 0 := by
 simpa only [Vector.toList_empty,List.nil_append] using
   WordExecution.loweredExpr_machine artifact.initializer.lowered 0 artifact.program artifact.beginCode
     artifact.emitted artifact.entrySelected locals #v[] m caller

theorem Artifact.source_to_model {c n f g} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (artifact : Artifact f g rhs body) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro (.let_ 1 rhs body) artifact.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 cases horizon with
 | zero => cases ran
 | succ horizon =>
   change (do
     let values ← evalExpr horizon .nil True.intro rhs artifact.initializer.profile (sourceLocals locals)
     let middle ← evalStmt horizon .nil True.intro body artifact.compiledBody.compiled.profile (extendValues values (sourceLocals locals))
     pure (⟨dropValues 1 middle.vars,middle.flow⟩ : Outcome c n)) = some result at ran
   obtain ⟨values,tested,rest⟩ := Option.bind_eq_some_iff.mp ran
   have same := evalExpr_completed_unique .nil True.intro rhs artifact.initializer.profile (sourceLocals locals)
     tested (artifact.initializer.source locals)
   subst values
   rw [LetScopeCompilation.initial_values] at rest
   obtain ⟨middle,source,remaining⟩ := Option.bind_eq_some_iff.mp rest
   obtain ⟨out,same,bodyRun⟩ := SequenceCompilation.source_to_model artifact.compiledBody.compiled
     artifact.compiledBody.block artifact.compiledBody.code artifact.compiledBody.emitted artifact.compiledBody.selected
     horizon (#v[artifact.initializer.value locals] ++ locals) middle source m caller
   subst middle
   have projected : result = ⟨sourceLocals (outerLocals out),.normal⟩ := by
     have same := (Option.some.inj remaining).symm
     rw [←ScopedStatements.locals_outer] at same
     exact same
   have bodyRun' : Evm.run artifact.compiledBody.code
     {m with stack := coreWord (artifact.initializer.value locals)::(locals.toList.map coreWord++caller)} =
     .ok {m with stack := out.toList.map coreWord++caller} 0 := by
     simpa only [Vector.toList_append,Vector.toList_singleton,List.singleton_append,List.map_cons,List.append_assoc] using bodyRun
   have exiting := WordExecution.run (popPrefix 1) artifact.finishCode artifact.exitSelected out.toList
     (outerLocals out).toList (by simpa only [List.append_nil] using popFresh_run out []) m caller
   refine ⟨outerLocals out,projected,?_⟩
   rw [Artifact.code,Evm.run_append_ok (artifact.entry_run locals m caller),Evm.run_append_ok bodyRun']
   exact exiting

theorem Artifact.model_to_source {c n f g} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (artifact : Artifact f g rhs body) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro (.let_ 1 rhs body) artifact.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 rw [Artifact.code,Evm.run_append_ok (artifact.entry_run locals m caller)] at ran
 have whole : (Evm.run artifact.compiledBody.code
   {m with stack := coreWord (artifact.initializer.value locals)::(locals.toList.map coreWord++caller)}).bind
   (fun middle pending => Evm.exec artifact.finishCode pending middle) = .ok final skip := by
   simpa only [Evm.run,Evm.exec_append] using ran
 cases actual : Evm.run artifact.compiledBody.code
   {m with stack := coreWord (artifact.initializer.value locals)::(locals.toList.map coreWord++caller)} with
 | revert => rw [actual] at whole; cases whole
 | fault => rw [actual] at whole; cases whole
 | ok middle pending =>
   have bodyRun : Evm.run artifact.compiledBody.code
     {m with stack := (#v[artifact.initializer.value locals] ++ locals).toList.map coreWord++caller} = .ok middle pending := by
     simpa only [Vector.toList_append,Vector.toList_singleton,List.singleton_append,List.map_cons,List.append_assoc] using actual
   obtain ⟨horizon,out,source,done,frame⟩ := SequenceCompletion.artifact_reflected artifact.compiledBody
     (#v[artifact.initializer.value locals] ++ locals) m middle caller pending bodyRun
   have scopeSource := ScopedControlCompletion.source_let artifact.initializer artifact.compiledBody.compiled.profile horizon locals out source
   rw [actual,done,frame] at whole
   change Evm.run artifact.finishCode {m with stack := out.toList.map coreWord++caller} = .ok final skip at whole
   have exiting := WordExecution.run (popPrefix 1) artifact.finishCode artifact.exitSelected out.toList
     (outerLocals out).toList (by simpa only [List.append_nil] using popFresh_run out []) m caller
   rw [exiting] at whole
   have parts := Evm.Out.ok.inj whole
   exact ⟨max f horizon+1,outerLocals out,scopeSource,parts.2.symm,parts.1.symm⟩

theorem Artifact.normal_to_model {c n f g} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (artifact : Artifact f g rhs body) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro (.let_ 1 rhs body) artifact.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨actual,same,target⟩ := artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller
 have equal : out = actual := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

theorem Artifact.completion_iff {c n f g} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (artifact : Artifact f g rhs body) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro (.let_ 1 rhs body) artifact.profile (sourceLocals locals) =
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

/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Artifact.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.selected
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Artifact.entry_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.entry_run
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Artifact.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.model_to_source
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Artifact.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.completion_iff
end Solidity.Yul.Compilation.InitializedSequenceCompilation

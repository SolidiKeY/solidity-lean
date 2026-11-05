import Solidity.Yul.Compilation.SequenceCompletion
/-! Original if lowering with actual recursive sequence/switch body artifacts.
The existing pure guard compiler, original word profile and relative-skip Block
selector are reused. Only the selected arm must complete. This adds no source
AST/state or native calling convention; Source/G24 and capacity stay separate. -/
namespace Solidity.Yul.Compilation.ConditionalCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

structure Artifact {c n} (f g : Nat) (test : Expr [] [] n 1) (body : Stmt [] [] c n) where
 condition : ProducerExpressions.Compiled f test
 arm : SequenceCompilation.Artifact g body
 program : Backend.Program
 guardCode : List Evm.Instr
 emitted : condition.lowered.code 0 = some program
 guardSelected : WordMachine.selectCode program = some guardCode

def Artifact.profile {c n f g} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (artifact : Artifact f g test body) : StmtWordP (.if_ test body) :=
 ⟨artifact.condition.profile,artifact.arm.compiled.profile⟩

def Artifact.block {c n f g} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (artifact : Artifact f g test body) : Backend.Block := .ite artifact.program artifact.arm.block (.code [])

def Artifact.code {c n f g} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (artifact : Artifact f g test body) : List Evm.Instr := MachineControl.branchCode artifact.guardCode artifact.arm.code []

/-- Actual lowering of an original if node; neither child carries a run field. -/
def lower {c n} (f g : Nat) (test : Expr [] [] n 1) (body : Stmt [] [] c n) :
 Option (Artifact f g test body) := do
 let condition ← PureExpressions.compile f test
 let arm ← SequenceCompilation.lower g body
 match emitted : condition.lowered.code 0 with
 | none => none
 | some program =>
   match selected : WordMachine.selectCode program with
   | none => none
   | some code => some ⟨condition,arm,program,code,emitted,selected⟩

theorem Artifact.selected {c n f g} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (artifact : Artifact f g test body) : WordControl.blockCode artifact.block = some artifact.code := by
 change (WordMachine.selectCode artifact.program).bind (fun guard =>
   (WordControl.blockCode artifact.arm.block).bind (fun arm =>
     (WordControl.blockCode (.code [])).map (fun empty => MachineControl.branchCode guard arm empty))) = _
 rw [artifact.guardSelected,artifact.arm.selected]
 rfl

theorem Artifact.test_run {c n f g} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (artifact : Artifact f g test body) (locals : Vector Scalar.Word n) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.guardCode {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := coreWord (artifact.condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
 simpa only [Vector.toList_empty,List.nil_append] using
   WordExecution.loweredExpr_machine artifact.condition.lowered 0 artifact.program artifact.guardCode
     artifact.emitted artifact.guardSelected locals #v[] m caller

theorem Artifact.source_to_model {c n f g} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (artifact : Artifact f g test body) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro (.if_ test body) artifact.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 cases horizon with
 | zero => cases ran
 | succ horizon =>
   change Option.bind (evalExpr horizon .nil True.intro test artifact.condition.profile (sourceLocals locals)) _ = some result at ran
   obtain ⟨values,tested,remaining⟩ := Option.bind_eq_some_iff.mp ran
   have same := evalExpr_completed_unique .nil True.intro test artifact.condition.profile (sourceLocals locals)
     tested (artifact.condition.source locals)
   subst values
   change (if (artifact.condition.value locals).toNat = 0 then
     some (⟨sourceLocals locals,.normal⟩ : Outcome c n)
     else evalStmt horizon .nil True.intro body artifact.arm.compiled.profile (sourceLocals locals)) = some result at remaining
   by_cases zero : artifact.condition.value locals = 0
   · have zn : (artifact.condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
     rw [if_pos zn] at remaining
     refine ⟨locals,(Option.some.inj remaining).symm,?_⟩
     rw [Artifact.code,MachineControl.branchCode,Evm.run_append_ok (artifact.test_run locals m caller),zero]
     change Evm.exec artifact.arm.code artifact.arm.code.length {m with stack := locals.toList.map coreWord++caller} = _
     exact Evm.exec_length artifact.arm.code _
   · have nz : (artifact.condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
     rw [if_neg nz] at remaining
     obtain ⟨out,same,armRun⟩ := SequenceCompilation.source_to_model artifact.arm.compiled artifact.arm.block
       artifact.arm.code artifact.arm.emitted artifact.arm.selected horizon locals result remaining m caller
     refine ⟨out,same,?_⟩
     rw [Artifact.code,MachineControl.branchCode,Evm.run_append_ok (artifact.test_run locals m caller)]
     rw [FramedBranch.nonzero_tail (artifact.condition.value locals) artifact.arm.code []
       {m with stack := locals.toList.map coreWord++caller} zero]
     exact armRun

theorem Artifact.model_to_source {c n f g} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (artifact : Artifact f g test body) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro (.if_ test body) artifact.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 rw [Artifact.code,MachineControl.branchCode,Evm.run_append_ok (artifact.test_run locals m caller)] at ran
 by_cases zero : artifact.condition.value locals = 0
 · rw [zero] at ran
   change Evm.exec artifact.arm.code artifact.arm.code.length {m with stack := locals.toList.map coreWord++caller} = .ok final skip at ran
   rw [Evm.exec_length] at ran
   have parts := Evm.Out.ok.inj ran
   exact ⟨_,locals,LetControlCompletion.source_false artifact.condition artifact.arm.compiled.profile locals zero,
     parts.2.symm,parts.1.symm⟩
 · rw [FramedBranch.nonzero_tail (artifact.condition.value locals) artifact.arm.code []
     {m with stack := locals.toList.map coreWord++caller} zero] at ran
   obtain ⟨horizon,out,source,done,frame⟩ := SequenceCompletion.artifact_reflected artifact.arm locals m final caller skip ran
   exact ⟨_,out,LetControlCompletion.source_true artifact.condition artifact.arm.compiled.profile horizon locals out zero source,done,frame⟩

theorem Artifact.normal_to_model {c n f g} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (artifact : Artifact f g test body) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro (.if_ test body) artifact.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨actual,same,target⟩ := artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller
 have equal : out = actual := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

theorem Artifact.completion_iff {c n f g} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (artifact : Artifact f g test body) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro (.if_ test body) artifact.profile (sourceLocals locals) =
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

/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Artifact.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.selected
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Artifact.test_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.test_run
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Artifact.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.model_to_source
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Artifact.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.completion_iff
end Solidity.Yul.Compilation.ConditionalCompilation

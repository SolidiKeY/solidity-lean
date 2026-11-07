import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.LetControlCompilation
import Solidity.Yul.Compilation.LetScopeCompletion
/-! Reflection of recursive original seq/if control around actual let scope
artifacts. Source branch-construction helpers use the original typed body and
word profile; no alternative syntax, state or producer interface is added. -/
namespace Solidity.Yul.Compilation.LetControlCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

/-- A completed zero guard constructs the original source completion without
an arm execution premise, regardless of the arm's runtime horizon. -/
theorem source_false {c : Control} {n fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (condition : ProducerExpressions.Compiled fuel test) (profile : StmtWordP body)
 (locals : Vector Scalar.Word n) (zero : condition.value locals = 0) :
 evalStmt (fuel+1) .nil True.intro (.if_ test body) ⟨condition.profile,profile⟩ (sourceLocals locals) =
 some ⟨sourceLocals locals,.normal⟩ := by
 change (do
   let values ← evalExpr fuel .nil True.intro test condition.profile (sourceLocals locals)
   if (values 0).val = 0 then pure (⟨sourceLocals locals,.normal⟩ : Outcome c n)
   else evalStmt fuel .nil True.intro body profile (sourceLocals locals)) = _
 rw [condition.source locals]
 change (if (condition.value locals).toNat = 0 then some (⟨sourceLocals locals,.normal⟩ : Outcome c n)
   else evalStmt fuel .nil True.intro body profile (sourceLocals locals)) = _
 have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
 rw [if_pos zn]

/-- Reconcile actual guard/body completion horizons and construct the original
nonzero source branch, preserving its precise updated locals. -/
theorem source_true {c : Control} {n fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (condition : ProducerExpressions.Compiled fuel test) (profile : StmtWordP body)
 (horizon : Nat) (locals out : Vector Scalar.Word n) (nonzero : condition.value locals ≠ 0)
 (ran : evalStmt horizon .nil True.intro body profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) :
 evalStmt (max fuel horizon+1) .nil True.intro (.if_ test body) ⟨condition.profile,profile⟩ (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ := by
 have tested := evalExpr_stable (Nat.le_max_left fuel horizon) .nil True.intro test condition.profile
   (sourceLocals locals) (condition.source locals)
 have completed := evalStmt_stable (Nat.le_max_right fuel horizon) .nil True.intro body profile
   (sourceLocals locals) ran
 change (do
   let values ← evalExpr (max fuel horizon) .nil True.intro test condition.profile (sourceLocals locals)
   if (values 0).val = 0 then pure (⟨sourceLocals locals,.normal⟩ : Outcome c n)
   else evalStmt (max fuel horizon) .nil True.intro body profile (sourceLocals locals)) = _
 rw [tested]
 change (if (condition.value locals).toNat = 0 then some (⟨sourceLocals locals,.normal⟩ : Outcome c n)
   else evalStmt (max fuel horizon) .nil True.intro body profile (sourceLocals locals)) = _
 have nz : (condition.value locals).toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 rw [if_neg nz]
 exact completed

/-- Actual whole success determines both source completions and their shared
intermediate locals, normal flow and exact caller/nonstack frame. -/
theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : LetControlCompilation.Compiled fuel stmt) (code : List Evm.Instr)
 (lowered : compiled.code = some code) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 induction compiled generalizing code locals m final skip with
 | scope artifact =>
   change some artifact.code = some code at lowered
   cases Option.some.inj lowered
   exact LetScopeCompletion.model_to_source artifact locals m final caller skip ran
 | seq left right ihLeft ihRight =>
   change (left.code).bind (fun a => (right.code).bind (fun b => some (a++b))) = some code at lowered
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have whole : (Evm.run a {m with stack := locals.toList.map coreWord++caller}).bind
     (fun middle pending => Evm.exec b pending middle) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run a {m with stack := locals.toList.map coreWord++caller} with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok middle pending =>
     obtain ⟨lo,mid,sourceLeft,done,frame⟩ := ihLeft a ha locals m middle pending actual
     rw [actual,done,frame] at whole
     change Evm.run b {m with stack := mid.toList.map coreWord++caller} = .ok final skip at whole
     obtain ⟨hi,out,sourceRight,done,frame⟩ := ihRight b hb mid m final skip whole
     have first := evalStmt_stable (Nat.le_max_left lo hi) .nil True.intro _ left.profile
       (sourceLocals locals) sourceLeft
     have last := evalStmt_stable (Nat.le_max_right lo hi) .nil True.intro _ right.profile
       (sourceLocals mid) sourceRight
     have source := LoopControlCompilation.sequence_source _ _ left.profile right.profile (max lo hi)
       (sourceLocals locals) (sourceLocals mid) (sourceLocals out) first last
     exact ⟨max lo hi+1,out,source,done,frame⟩

 | branch condition arm ih =>
   change (condition.lowered.code 0).bind (fun p => (WordMachine.selectCode p).bind (fun q =>
     (arm.code).bind (fun body => some (MachineControl.branchCode q body [])))) = some code at lowered
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨q,sq,rest⟩ := Option.bind_eq_some_iff.mp rest
   obtain ⟨body,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have testedTarget : Evm.run q {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p q hp sq locals #v[] m caller
   rw [MachineControl.branchCode,Evm.run_append_ok testedTarget] at ran
   by_cases zero : condition.value locals = 0
   · rw [zero] at ran
     change Evm.exec body body.length {m with stack := locals.toList.map coreWord++caller} = .ok final skip at ran
     rw [Evm.exec_length] at ran
     have parts := Evm.Out.ok.inj ran
     exact ⟨_,locals,source_false condition arm.profile locals zero,parts.2.symm,parts.1.symm⟩
   · rw [FramedBranch.nonzero_tail (condition.value locals) body []
       {m with stack := locals.toList.map coreWord++caller} zero] at ran
     obtain ⟨horizon,out,source,done,frame⟩ := ih body hb locals m final skip ran
     exact ⟨_,out,source_true condition arm.profile horizon locals out zero source,done,frame⟩

/-- Actual compiler artifact projection; no simulation law is stored. -/
theorem artifact_reflected {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : LetControlCompilation.Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact.compiled artifact.code artifact.lowered locals m final caller skip ran

/-- Normal-success equivalence at an existential original source horizon.
No capacity/native/G24/admission or failure/divergence equivalence follows. -/
theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : LetControlCompilation.Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (artifact_reflected artifact) locals out m caller

/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.source_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_false
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.source_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_true
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.artifact_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms artifact_reflected
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.LetControlCompletion

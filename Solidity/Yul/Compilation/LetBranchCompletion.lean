import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.LetBranchCompilation
import Solidity.Yul.Compilation.LetSequenceCompletion
/-! Actual conditional success reflection. The false path needs no body
completion; the true path reflects only the actual selected arm. Original
source syntax/profiles, raw words and target branch semantics are unchanged. -/
namespace Solidity.Yul.Compilation.LetBranchCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

/-- A completed zero guard constructs the original source completion without
an arm execution premise, regardless of the arm's runtime horizon. -/
theorem source_false {c : Control} {n fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (condition : ProducerExpressions.Compiled fuel test) (arm : LetSequenceCompilation.Artifact fuel body)
 (locals : Vector Scalar.Word n) (zero : condition.value locals = 0) :
 evalStmt (fuel+1) .nil True.intro (.if_ test body) ⟨condition.profile,arm.compiled.profile⟩ (sourceLocals locals) =
 some ⟨sourceLocals locals,.normal⟩ := by
 change (do
   let values ← evalExpr fuel .nil True.intro test condition.profile (sourceLocals locals)
   if (values 0).val = 0 then pure (⟨sourceLocals locals,.normal⟩ : Outcome c n)
   else evalStmt fuel .nil True.intro body arm.compiled.profile (sourceLocals locals)) = _
 rw [condition.source locals]
 change (if (condition.value locals).toNat = 0 then some (⟨sourceLocals locals,.normal⟩ : Outcome c n)
   else evalStmt fuel .nil True.intro body arm.compiled.profile (sourceLocals locals)) = _
 have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
 rw [if_pos zn]

/-- Reconcile actual guard/body completion horizons and construct the original
nonzero source branch, preserving its precise updated locals. -/
theorem source_true {c : Control} {n fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (condition : ProducerExpressions.Compiled fuel test) (arm : LetSequenceCompilation.Artifact fuel body)
 (horizon : Nat) (locals out : Vector Scalar.Word n) (nonzero : condition.value locals ≠ 0)
 (ran : evalStmt horizon .nil True.intro body arm.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) :
 evalStmt (max fuel horizon+1) .nil True.intro (.if_ test body) ⟨condition.profile,arm.compiled.profile⟩ (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ := by
 have tested := evalExpr_stable (Nat.le_max_left fuel horizon) .nil True.intro test condition.profile
   (sourceLocals locals) (condition.source locals)
 have completed := evalStmt_stable (Nat.le_max_right fuel horizon) .nil True.intro body arm.compiled.profile
   (sourceLocals locals) ran
 change (do
   let values ← evalExpr (max fuel horizon) .nil True.intro test condition.profile (sourceLocals locals)
   if (values 0).val = 0 then pure (⟨sourceLocals locals,.normal⟩ : Outcome c n)
   else evalStmt (max fuel horizon) .nil True.intro body arm.compiled.profile (sourceLocals locals)) = _
 rw [tested]
 change (if (condition.value locals).toNat = 0 then some (⟨sourceLocals locals,.normal⟩ : Outcome c n)
   else evalStmt (max fuel horizon) .nil True.intro body arm.compiled.profile (sourceLocals locals)) = _
 have nz : (condition.value locals).toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 rw [if_neg nz]
 exact completed

/-- Whole actual model success fixes the source branch and exact frame.
No inactive arm execution, desired source result or source horizon is assumed. -/
theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : LetBranchCompilation.Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | branch condition arm =>
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨q,sq,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have testedTarget : Evm.run q {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p q hp sq locals #v[] m caller
   change Evm.run (MachineControl.branchCode q arm.code [])
     {m with stack := locals.toList.map coreWord++caller} = .ok final skip at ran
   rw [MachineControl.branchCode,Evm.run_append_ok testedTarget] at ran
   by_cases zero : condition.value locals = 0
   · rw [zero] at ran
     change Evm.exec arm.code arm.code.length {m with stack := locals.toList.map coreWord++caller} = .ok final skip at ran
     rw [Evm.exec_length] at ran
     have parts := Evm.Out.ok.inj ran
     exact ⟨fuel+1,locals,source_false condition arm locals zero,parts.2.symm,parts.1.symm⟩
   · rw [FramedBranch.nonzero_tail (condition.value locals) arm.code []
       {m with stack := locals.toList.map coreWord++caller} zero] at ran
     obtain ⟨horizon,out,source,done,frame⟩ := LetSequenceCompletion.artifact_reflected arm locals m final caller skip ran
     exact ⟨max fuel horizon+1,out,source_true condition arm horizon locals out zero source,done,frame⟩

/-- Exact normal-success equivalence at some original source horizon.
This states neither failure/divergence equivalence nor native/G24 adequacy. -/
theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : LetBranchCompilation.Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (model_to_source artifact) locals out m caller

/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.source_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_false
/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.source_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_true
/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.completion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.LetBranchCompletion

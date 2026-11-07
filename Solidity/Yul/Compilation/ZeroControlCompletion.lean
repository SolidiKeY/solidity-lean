import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.ZeroControlCompilation
import Solidity.Yul.Compilation.LetControlCompletion
/-! Reverse normal-success correspondence for actual zero/control artifacts.
The initialized body's source completion is derived before exact retirement
uses the concrete forward theorem; fresh words may have changed arbitrarily. -/
namespace Solidity.Yul.Compilation.ZeroControlCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

/-- Whole selected success derives real original body/scope completion and
exact outer/caller/nonstack framing, with no desired source or body run. -/
theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : ZeroControlCompilation.Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 have forward := artifact.source_to_model
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | @scope fresh bodyStmt body =>
   obtain ⟨begin,beginSelected,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨finish,finishSelected,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have entering := WordExecution.run (ZeroLoopScope.entry fresh) begin beginSelected locals.toList
     ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList) (pushPrefix_run _ _) m caller
   change Evm.run (begin ++ body.code ++ finish) {m with stack := locals.toList.map coreWord++caller} = .ok final skip at ran
   have original := ran
   rw [List.append_assoc,Evm.run_append_ok entering] at ran
   have whole : (Evm.run body.code
     {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller}).bind
     (fun mid pending => Evm.exec finish pending mid) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run body.code
     {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller} with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok middle pending =>
     have bodyRun : Evm.run body.code
       {m with stack := (Vector.replicate fresh (0 : Scalar.Word) ++ locals).toList.map coreWord++caller} =
       .ok middle pending := by
       simpa only [Vector.toList_append] using actual
     obtain ⟨horizon,out,source,_,_⟩ := LetControlCompletion.artifact_reflected body
       (Vector.replicate fresh (0 : Scalar.Word) ++ locals) m middle caller pending bodyRun
     have scopeSource := ZeroControlCompilation.source_scope body horizon locals out source
     obtain ⟨outer,same,computed⟩ := forward (horizon+1) locals
       ⟨sourceLocals (outerLocals out),.normal⟩ scopeSource m caller
     have equal : outerLocals out = outer :=
       SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
     subst outer
     have parts := Evm.Out.ok.inj (computed.symm.trans original)
     exact ⟨horizon+1,outerLocals out,scopeSource,parts.2.symm,parts.1.symm⟩

/-- Exact normal-success equivalence with existential source horizon. This
is not native/capacity/G24 or failure/divergence/admission equivalence. -/
theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : ZeroControlCompilation.Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (model_to_source artifact) locals out m caller

/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.ZeroControlCompletion

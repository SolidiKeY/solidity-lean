import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.ZeroLoopScope
import Solidity.Yul.Compilation.LoopControlCompletion
/-! Reverse normal-success correspondence for actual lexical zero scopes.
Body success is derived from whole execution; concrete source scope/forward
laws then derive retirement and exact framing. No native/G24 adequacy claim. -/
namespace Solidity.Yul.Compilation.ZeroScopeCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
/-- Actual scope success derives a body completion at a real source horizon.
The source scope is constructed BEFORE the existing concrete forward theorem
is reused for exact exit framing; no source or desired body run is assumed. -/
theorem model_to_source {c : Control} {n fresh fuel : Nat} {body : Stmt [] [] c (fresh+n)}
 (artifact : LoopControlCompilation.Artifact fuel body 0) (code : List Evm.Instr)
 (lowered : ZeroLoopScope.lower fresh artifact = some code)
 (locals : Vector Scalar.Word n) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro (.zero fresh body) artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := out.toList.map coreWord++caller} := by
 obtain ⟨begin,beginSelected,rest⟩ := Option.bind_eq_some_iff.mp lowered
 obtain ⟨finish,finishSelected,same⟩ := Option.bind_eq_some_iff.mp rest
 cases Option.some.inj same
 have original := ran
 have entering := WordExecution.run (ZeroLoopScope.entry fresh) begin beginSelected locals.toList
   ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList)
   (pushPrefix_run _ _) m caller
 rw [List.append_assoc,Evm.run_append_ok entering] at ran
 have whole : (Evm.run artifact.code
   {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller}).bind
   (fun mid pending => Evm.exec finish pending mid) = .ok final skip := by
   simpa only [Evm.run,Evm.exec_append] using ran
 cases actual : Evm.run artifact.code
   {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller} with
 | revert => rw [actual] at whole; cases whole
 | fault => rw [actual] at whole; cases whole
 | ok middle pending =>
   have bodyRun : Evm.run artifact.code
     {m with stack := (Vector.replicate fresh (0 : Scalar.Word) ++ locals).toList.map coreWord++caller} =
     .ok middle pending := by
     simpa only [Vector.toList_append] using actual
   obtain ⟨horizon,out,source,_,_⟩ := LoopControlCompletion.artifact_reflected artifact
     (Vector.replicate fresh (0 : Scalar.Word) ++ locals) #v[] m middle caller pending bodyRun
   have scopeSource := ZeroLoopScope.source_scope artifact horizon locals out source
   obtain ⟨outer,same,computed⟩ := ZeroLoopScope.source_to_model artifact _ lowered (horizon+1) locals
     ⟨sourceLocals (outerLocals out),.normal⟩ scopeSource m caller
   have equal : outerLocals out = outer :=
     SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
   subst outer
   have parts := Evm.Out.ok.inj (computed.symm.trans original)
   exact ⟨horizon+1,outerLocals out,scopeSource,parts.2.symm,parts.1.symm⟩

/-- Exact scope normal-success equivalence with existential source horizon.
Fresh contents may change arbitrarily under the actual body proof and are
retired. Scalar/model success still does not establish native stack capacity. -/
theorem completion_iff {c : Control} {n fresh fuel : Nat} {body : Stmt [] [] c (fresh+n)}
 (artifact : LoopControlCompilation.Artifact fuel body 0) (code : List Evm.Instr)
 (lowered : ZeroLoopScope.lower fresh artifact = some code)
 (locals out : Vector Scalar.Word n) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro (.zero fresh body) artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 apply CompletionControls.completion_iff_zero (.zero fresh body) artifact.compiled.profile code
   ?_ (model_to_source artifact code lowered) locals out m caller
 intro horizon locals out source m caller
 obtain ⟨actual,same,target⟩ := ZeroLoopScope.source_to_model artifact code lowered horizon locals
   ⟨sourceLocals out,.normal⟩ source m caller
 have equal : out = actual := CompletionControls.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompletion.completion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.ZeroScopeCompletion

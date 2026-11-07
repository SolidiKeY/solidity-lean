import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.MultiSwitchCompilation
import Solidity.Yul.Compilation.CaseCompletion
/-! Exact normal-success equivalence for actual finite-case switch artifacts.
Reverse transport derives original case/default runs first, then reconciles
those horizons with the selector horizon using existing source stability. -/
namespace Solidity.Yul.Compilation.MultiSwitchCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open MultiSwitchCompilation

theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 rcases artifact with ⟨compiled,block,code,emitted,selected⟩
 cases compiled with
 | @many test arms fallbackStmt condition cases default =>
   change (condition.lowered.code 0).bind (fun p => (cases.emit default.block).bind
     (fun next => some (Backend.Block.seq (.code p) next))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨next,hn,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordMachine.selectCode p).bind (fun ps => (WordControl.blockCode next).map (fun ns => ps++ns)) = some code at selected
   obtain ⟨ps,sp,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨ns,sn,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   have selectorTarget : Evm.run ps {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p ps hp sp locals #v[] m caller

   rw [Evm.run_append_ok selectorTarget] at ran
   obtain ⟨hc,hf,out,chosen,caseSource,continued,done,frame⟩ := CaseCompletion.model_to_source cases default next ns hn sn
     (condition.value locals) locals m final caller skip ran
   let H := max fuel (max hc hf)
   have casesH : evalCases H .nil True.intro arms cases.profile (condition.value locals).toFin (sourceLocals locals) = some chosen := by
     obtain ⟨extra,eq⟩ := Nat.exists_eq_add_of_le (show hc ≤ H by dsimp only [H]; omega)
     rw [eq]
     exact evalCases_refines_add hc extra .nil True.intro arms cases.profile
       (condition.value locals).toFin (sourceLocals locals) _ caseSource
   have continuedH : (match chosen with
     | some result => some result
     | none => evalStmt H .nil True.intro fallbackStmt default.compiled.profile (sourceLocals locals)) =
       some (⟨sourceLocals out,.normal⟩ : Outcome c n) := by
     cases chosen with
     | some actual => exact continued
     | none =>
       exact evalStmt_stable (show hf ≤ H by dsimp only [H]; omega) .nil True.intro fallbackStmt default.compiled.profile
         (sourceLocals locals) continued
   have source : evalStmt (H+1) .nil True.intro (.switch (c := c) test arms fallbackStmt)
     ⟨condition.profile,cases.profile,default.compiled.profile⟩ (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩ := by
     cases chosen with
     | none =>
       exact source_chosen (c := c) (arms := arms) (fallback := fallbackStmt) condition cases.profile default.compiled.profile
         H locals none ⟨sourceLocals out,.normal⟩ (by dsimp only [H]; omega) casesH continuedH
     | some actual =>
       exact source_chosen (c := c) (arms := arms) (fallback := fallbackStmt) condition cases.profile default.compiled.profile
         H locals (some actual) ⟨sourceLocals out,.normal⟩ (by dsimp only [H]; omega) casesH continuedH
   exact ⟨H+1,out,source,done,frame⟩

theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (model_to_source artifact) locals out m caller

/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.MultiSwitchCompletion

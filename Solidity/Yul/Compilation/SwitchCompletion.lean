import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.SwitchCompilation
import Solidity.Yul.Compilation.ScopedControlCompletion
/-! Reverse normal-success transport for actual one-case/default switch
artifacts. Target success derives the chosen original source run and exact
selector retirement; native/G24/admission/failure closure remain separate. -/
namespace Solidity.Yul.Compilation.SwitchCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SwitchCompilation

theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 rcases artifact with ⟨compiled,block,code,emitted,selected⟩
 cases compiled with
 | @one test label arm fallback condition yes no =>
   change (condition.lowered.code 0).bind (fun p => ((comparison label).code 0).map (fun r =>
     Backend.Block.seq (.code p) (.ite r (.seq (.code (popPrefix 1)) yes.block)
       (.seq (.code (popPrefix 1)) no.block)))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨r,hr,same⟩ := Option.map_eq_some_iff.mp rest
   subst block
   have yesSelected : WordControl.blockCode (.seq (.code (popPrefix 1)) yes.block) = some (.pop::yes.code) := by
     change (WordMachine.selectCode (popPrefix 1)).bind (fun a => (WordControl.blockCode yes.block).map (fun b => a++b)) = _
     rw [yes.selected]
     rfl
   have noSelected : WordControl.blockCode (.seq (.code (popPrefix 1)) no.block) = some (.pop::no.code) := by
     change (WordMachine.selectCode (popPrefix 1)).bind (fun a => (WordControl.blockCode no.block).map (fun b => a++b)) = _
     rw [no.selected]
     rfl
   change (WordMachine.selectCode p).bind (fun ps =>
     ((WordMachine.selectCode r).bind (fun rs =>
       ((WordControl.blockCode (.seq (.code (popPrefix 1)) yes.block)).bind (fun ys =>
         (WordControl.blockCode (.seq (.code (popPrefix 1)) no.block)).map
           (fun ns => MachineControl.branchCode rs ys ns))))).map (fun tail => ps++tail)) = some code at selected
   rw [yesSelected,noSelected] at selected
   simp only [Option.bind_some,Option.map_some] at selected
   obtain ⟨ps,sp,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨tail,tailSelected,same⟩ := Option.map_eq_some_iff.mp rest
   obtain ⟨rs,sr,tailSame⟩ := Option.bind_eq_some_iff.mp tailSelected
   cases Option.some.inj tailSame
   subst code
   have selectorTarget : Evm.run ps {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p ps hp sp locals #v[] m caller
   have comparedTarget : Evm.run rs
     {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} =
     .ok {m with stack := (coreWord (WordExpressions.selectEq.value (condition.value locals) (BitVec.ofFin label))::
       coreWord (condition.value locals)::(locals.toList.map coreWord++caller))} 0 := by
     simpa only [Vector.toList_empty,Vector.toList_singleton,List.nil_append,List.map_cons,List.map_nil,List.singleton_append] using
       WordExecution.loweredExpr_machine (comparison label) 0 r rs hr sr #v[condition.value locals] #v[] m
         (locals.toList.map coreWord++caller)
   have popped : Evm.run [.pop] {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} =
     .ok {m with stack := locals.toList.map coreWord++caller} 0 := by rfl

   rw [Evm.run_append_ok selectorTarget,MachineControl.branchCode,Evm.run_append_ok comparedTarget,comparison_value] at ran
   by_cases equal : (condition.value locals).toFin = label
   · rw [if_pos equal] at ran
     rw [FramedBranch.nonzero_tail 1 (.pop::yes.code) (.pop::no.code)
       {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} (by decide)] at ran
     change Evm.run ([.pop]++yes.code)
       {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} = .ok final skip at ran
     rw [Evm.run_append_ok popped] at ran
     obtain ⟨horizon,out,source,done,frame⟩ := ScopedControlCompletion.artifact_reflected yes locals m final caller skip ran
     have completed := evalStmt_stable (show horizon ≤ max fuel horizon by omega) .nil True.intro arm yes.compiled.profile
       (sourceLocals locals) source
     have switchSource := source_match (c := c) (arm := arm) (fallback := fallback) condition label
       yes.compiled.profile no.compiled.profile (max fuel horizon) locals out (by omega) equal completed
     exact ⟨max fuel horizon+2,out,switchSource,done,frame⟩
   · rw [if_neg equal] at ran
     change Evm.run ((.pop::no.code)++(.jump ((.pop::yes.code).length)::(.pop::yes.code)))
       {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} = .ok final skip at ran
     have whole : (Evm.run (.pop::no.code)
       {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)}).bind
       (fun mid pending => Evm.exec (.jump ((.pop::yes.code).length)::(.pop::yes.code)) pending mid) = .ok final skip := by
       simpa only [Evm.run,Evm.exec_append] using ran
     have poppedPrefix : Evm.run (.pop::no.code)
       {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} =
       Evm.run no.code {m with stack := locals.toList.map coreWord++caller} := by
       change Evm.run ([.pop]++no.code) _ = _
       rw [Evm.run_append_ok popped]
     rw [poppedPrefix] at whole
     cases actual : Evm.run no.code {m with stack := locals.toList.map coreWord++caller} with
     | revert => rw [actual] at whole; cases whole
     | fault => rw [actual] at whole; cases whole
     | ok middle pending =>
       obtain ⟨horizon,out,source,done,frame⟩ := ScopedControlCompletion.artifact_reflected no locals m middle caller pending actual
       rw [actual,done] at whole
       have tail : Evm.exec (.jump ((.pop::yes.code).length)::(.pop::yes.code)) 0 middle = .ok middle 0 :=
         Evm.exec_length (.pop::yes.code) middle
       change Evm.exec (.jump ((.pop::yes.code).length)::(.pop::yes.code)) 0 middle = .ok final skip at whole
       rw [tail] at whole
       have parts := Evm.Out.ok.inj whole
       have completed := evalStmt_stable (show horizon ≤ max fuel horizon+2 by omega) .nil True.intro fallback no.compiled.profile
         (sourceLocals locals) source
       have switchSource := source_default (c := c) (arm := arm) (fallback := fallback) condition label
         yes.compiled.profile no.compiled.profile (max fuel horizon) locals out (by omega) equal completed
       exact ⟨max fuel horizon+3,out,switchSource,parts.2.symm,parts.1.symm.trans frame⟩

theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (model_to_source artifact) locals out m caller




/-- info: 'Solidity.Yul.Compilation.SwitchCompletion.model_to_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.SwitchCompletion.completion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.SwitchCompletion

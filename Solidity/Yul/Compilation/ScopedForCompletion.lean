import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.ScopedForCompilation
import Solidity.Yul.Compilation.ScopedLoopCompletion
/-! Reverse normal-success correspondence for actual scoped FOR artifacts.
Successful target initialization/iterations derive genuine original source
completions; no source/count/termination or desired intermediate run is assumed. -/
namespace Solidity.Yul.Compilation.ScopedForCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open ScopedForCompilation

theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 rcases artifact with ⟨compiled,block,code,emitted,selected⟩
 cases compiled with
 | @loop pre test post body initializer condition step work =>
   change (condition.lowered.code 0).map (fun p =>
     Backend.Block.seq initializer.block (.loop p (.seq work.block step.block))) = some block at emitted
   obtain ⟨p,hp,same⟩ := Option.map_eq_some_iff.mp emitted
   subst block
   change (WordControl.blockCode initializer.block).bind (fun a =>
     ((WordMachine.selectCode p).bind (fun q =>
       ((WordControl.blockCode work.block).bind (fun b =>
         (WordControl.blockCode step.block).map (fun s => b++s))).map
           (fun b => [Evm.Instr.loop q b]))).map (fun b => a++b)) = some code at selected
   rw [initializer.selected,work.selected,step.selected] at selected
   simp only [Option.bind_some,Option.map_some] at selected
   obtain ⟨loopCode,loopSelected,same⟩ := Option.map_eq_some_iff.mp selected
   obtain ⟨q,sq,loopSame⟩ := Option.bind_eq_some_iff.mp loopSelected
   cases Option.some.inj loopSame
   subst code

   have whole : (Evm.run initializer.code {m with stack := locals.toList.map coreWord++caller}).bind
     (fun mid pending => Evm.exec [Evm.Instr.loop q (work.code++step.code)] pending mid) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run initializer.code {m with stack := locals.toList.map coreWord++caller} with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok middle pending =>
     obtain ⟨hi,mid,initialSource,done,frame⟩ := ScopedControlCompletion.artifact_reflected initializer locals m middle caller pending actual
     rw [actual,done,frame] at whole
     change Evm.run [Evm.Instr.loop q (work.code++step.code)] {m with stack := mid.toList.map coreWord++caller} = .ok final skip at whole
     obtain ⟨hl,out,loopSource,done,frame⟩ := ScopedLoopCompletion.model_to_source condition step work p q hp sq mid m final caller skip whole
     have started := evalStmt_stable (Nat.le_max_left hi hl) .nil True.intro pre initializer.compiled.profile (sourceLocals locals) initialSource
     have completed : evalLoop (max hi hl) .nil True.intro test condition.profile post step.compiled.profile
       body work.compiled.profile (sourceLocals mid) = some (⟨sourceLocals out,.normal⟩ : Outcome c n) := by
       exact CompletionControls.completed_horizon
         (fun fuel => evalLoop fuel .nil True.intro test condition.profile post step.compiled.profile
           body work.compiled.profile (sourceLocals mid))
         (fun fuel extra => evalLoop_refines_add fuel extra .nil True.intro test condition.profile
           post step.compiled.profile body work.compiled.profile (sourceLocals mid))
         (Nat.le_max_right hi hl) loopSource
     have source := ScopedForCompilation.source_for (c := c) (pre := pre) (test := test) (post := post) (body := body)
       initializer.compiled.profile condition.profile step.compiled.profile work.compiled.profile
       (max hi hl) locals mid out started completed
     exact ⟨max hi hl+1,out,source,done,frame⟩

theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (model_to_source artifact) locals out m caller

/-- info: 'Solidity.Yul.Compilation.ScopedForCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.ScopedForCompletion.completion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.ScopedForCompletion

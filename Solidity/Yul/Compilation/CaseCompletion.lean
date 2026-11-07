import Solidity.Yul.Compilation.CaseCompilation
import Solidity.Yul.Compilation.ScopedControlCompletion
/-! Reverse actual finite-case dispatch. Reflection recovers separate case and
default source horizons and the original optional case result, preserving the
unchanged default continuation across misses. No source run is assumed. -/
namespace Solidity.Yul.Compilation.CaseCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open CaseCompilation

theorem model_to_source {c : Control} {n fuel ff : Nat} {arms : Cases [] [] c n} {fallbackStmt : Stmt [] [] c n}
 (compiled : Compiled fuel arms) (fallback : ScopedControlCompilation.Artifact ff fallbackStmt)
 (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit fallback.block = some block) (selected : WordControl.blockCode block = some code)
 (selector : Scalar.Word) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} = .ok final skip) :
 ∃ (caseHorizon fallbackHorizon : Nat) (out : Vector Scalar.Word n) (chosen : Option (Outcome c n)),
 evalCases caseHorizon .nil True.intro arms compiled.profile selector.toFin (sourceLocals locals) = some chosen ∧
 (match chosen with
  | some result => some result
  | none => evalStmt fallbackHorizon .nil True.intro fallbackStmt fallback.compiled.profile (sourceLocals locals)) =
    some ⟨sourceLocals out,.normal⟩ ∧
 skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 induction compiled generalizing block code final skip with
 | nil fuel =>
   change some (Backend.Block.seq (.code (popPrefix 1)) fallback.block) = some block at emitted
   cases Option.some.inj emitted
   change (WordMachine.selectCode (popPrefix 1)).bind (fun p => (WordControl.blockCode fallback.block).map (fun q => p++q)) = some code at selected
   rw [fallback.selected] at selected
   change some (.pop::fallback.code) = some code at selected
   cases Option.some.inj selected
   have popped : Evm.run [.pop] {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} =
     .ok {m with stack := locals.toList.map coreWord++caller} 0 := by rfl
   change Evm.run ([.pop]++fallback.code)
     {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} = .ok final skip at ran
   rw [Evm.run_append_ok popped] at ran
   obtain ⟨hf,out,source,done,frame⟩ := ScopedControlCompletion.artifact_reflected fallback locals m final caller skip ran
   exact ⟨1,hf,out,none,by rfl,source,done,frame⟩
 | @cons fuel label body restStmt arm tail ih =>
   change ((SwitchCompilation.comparison label).code 0).bind (fun p => (tail.emit fallback.block).bind
     (fun next => some (Backend.Block.ite p (.seq (.code (popPrefix 1)) arm.block) next))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨next,ht,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have armSelected : WordControl.blockCode (.seq (.code (popPrefix 1)) arm.block) = some (.pop::arm.code) := by
     change (WordMachine.selectCode (popPrefix 1)).bind (fun p => (WordControl.blockCode arm.block).map (fun q => p++q)) = _
     rw [arm.selected]
     rfl
   change (WordMachine.selectCode p).bind (fun ps =>
     (WordControl.blockCode (.seq (.code (popPrefix 1)) arm.block)).bind (fun yes =>
       (WordControl.blockCode next).map (fun no => MachineControl.branchCode ps yes no))) = some code at selected
   rw [armSelected] at selected
   simp only [Option.bind_some] at selected
   obtain ⟨ps,sp,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨ns,sn,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   have compared : Evm.run ps {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} =
     .ok {m with stack := (coreWord (WordExpressions.selectEq.value selector (BitVec.ofFin label))::
       coreWord selector::(locals.toList.map coreWord++caller))} 0 := by
     simpa only [Vector.toList_empty,Vector.toList_singleton,List.nil_append,List.map_cons,List.map_nil,List.singleton_append] using
       WordExecution.loweredExpr_machine (SwitchCompilation.comparison label) 0 p ps hp sp #v[selector] #v[] m
         (locals.toList.map coreWord++caller)

   rw [MachineControl.branchCode,Evm.run_append_ok compared,SwitchCompilation.comparison_value] at ran
   by_cases equal : selector.toFin = label
   · rw [if_pos equal] at ran
     rw [FramedBranch.nonzero_tail 1 (.pop::arm.code) ns
       {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} (by decide)] at ran
     have popped : Evm.run [.pop] {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} =
       .ok {m with stack := locals.toList.map coreWord++caller} 0 := by rfl
     change Evm.run ([.pop]++arm.code)
       {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} = .ok final skip at ran
     rw [Evm.run_append_ok popped] at ran
     obtain ⟨horizon,out,source,done,frame⟩ := ScopedControlCompletion.artifact_reflected arm locals m final caller skip ran
     have hit := CaseCompilation.source_hit (body := body) (rest := restStmt) label selector.toFin
       arm.compiled.profile tail.profile horizon locals out equal source
     exact ⟨horizon+1,0,out,some ⟨sourceLocals out,.normal⟩,hit,rfl,done,frame⟩
   · rw [if_neg equal] at ran
     change Evm.run (ns++(.jump ((.pop::arm.code).length)::(.pop::arm.code)))
       {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} = .ok final skip at ran
     have whole : (Evm.run ns {m with stack := coreWord selector::(locals.toList.map coreWord++caller)}).bind
       (fun mid pending => Evm.exec (.jump ((.pop::arm.code).length)::(.pop::arm.code)) pending mid) = .ok final skip := by
       simpa only [Evm.run,Evm.exec_append] using ran
     cases actual : Evm.run ns {m with stack := coreWord selector::(locals.toList.map coreWord++caller)} with
     | revert => rw [actual] at whole; cases whole
     | fault => rw [actual] at whole; cases whole
     | ok middle pending =>
       obtain ⟨hc,hf,out,chosen,caseSource,continued,done,frame⟩ := ih next ns ht sn middle pending actual
       rw [actual,done] at whole
       have skipped : Evm.exec (.jump ((.pop::arm.code).length)::(.pop::arm.code)) 0 middle = .ok middle 0 :=
         Evm.exec_length (.pop::arm.code) middle
       change Evm.exec (.jump ((.pop::arm.code).length)::(.pop::arm.code)) 0 middle = .ok final skip at whole
       rw [skipped] at whole
       have parts := Evm.Out.ok.inj whole
       have missed := CaseCompilation.source_miss (body := body) (rest := restStmt) label selector.toFin
         arm.compiled.profile tail.profile hc locals chosen equal caseSource
       exact ⟨hc+1,hf,out,chosen,missed,continued,parts.2.symm,parts.1.symm.trans frame⟩

/-- info: 'Solidity.Yul.Compilation.CaseCompletion.model_to_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
end Solidity.Yul.Compilation.CaseCompletion

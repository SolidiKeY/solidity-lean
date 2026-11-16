import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.StructuredSequenceCompilation
import Solidity.Yul.Compilation.SequenceCompletion
/-! Reverse normal-success transport through recursively composed original
sequence/if/zero/single-let nodes. Actual leaf reflection and executor equations
derive source completions, local frames and pending zero. Existing source scope
constructors are reused; native capacity, Source/G24 and failure stay separate. -/
namespace Solidity.Yul.Compilation.StructuredSequenceCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open StructuredSequenceCompilation

theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : Compiled c fuel stmt) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit = some block) (selected : WordControl.blockCode block = some code)
 (locals : Vector Scalar.Word n) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 induction compiled generalizing block code m final skip with
 | base artifact =>
   change some artifact.block = some block at emitted
   cases Option.some.inj emitted
   have equal : code = artifact.code := Option.some.inj (selected.symm.trans artifact.selected)
   subst code
   exact SequenceCompletion.artifact_reflected artifact locals m final caller skip ran
 | seq left right ihLeft ihRight =>
   change (left.emit).bind (fun a => (right.emit).bind (fun b => some (Backend.Block.seq a b))) = some block at emitted
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordControl.blockCode a).bind (fun qa => (WordControl.blockCode b).map (fun qb => qa++qb)) = some code at selected
   obtain ⟨qa,sa,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code

   have whole : (Evm.run qa {m with stack := locals.toList.map coreWord++caller}).bind
     (fun mid pending => Evm.exec qb pending mid) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run qa {m with stack := locals.toList.map coreWord++caller} with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok mid pending =>
     obtain ⟨lo,intermediate,leftSource,done,frame⟩ := ihLeft a qa ha sa locals m mid pending actual
     rw [actual,done,frame] at whole
     change Evm.run qb {m with stack := intermediate.toList.map coreWord++caller} = .ok final skip at whole
     obtain ⟨hi,out,rightSource,done,frame⟩ := ihRight b qb hb sb intermediate m final skip whole
     have first : evalStmt (max lo hi) .nil True.intro _ left.profile (sourceLocals locals) =
       some ⟨sourceLocals intermediate,.normal⟩ := CompletionControls.completed_horizon
       (fun fuel => evalStmt fuel .nil True.intro _ left.profile (sourceLocals locals))
       (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ left.profile (sourceLocals locals))
       (Nat.le_max_left lo hi) leftSource
     have last : evalStmt (max lo hi) .nil True.intro _ right.profile (sourceLocals intermediate) =
       some ⟨sourceLocals out,.normal⟩ := CompletionControls.completed_horizon
       (fun fuel => evalStmt fuel .nil True.intro _ right.profile (sourceLocals intermediate))
       (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ right.profile (sourceLocals intermediate))
       (Nat.le_max_right lo hi) rightSource
     have source := LoopControlCompilation.sequence_source _ _ left.profile right.profile (max lo hi)
       (sourceLocals locals) (sourceLocals intermediate) (sourceLocals out) first last
     exact ⟨max lo hi+1,out,source,done,frame⟩
 | branch condition arm ih =>
   change (condition.lowered.code 0).bind (fun p => (arm.emit).bind (fun b =>
     some (Backend.Block.ite p b (.code [])))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordMachine.selectCode p).bind (fun q => (WordControl.blockCode b).bind (fun qb =>
     some (MachineControl.branchCode q qb []))) = some code at selected
   obtain ⟨q,sq,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have testedTarget : Evm.run q {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p q hp sq locals #v[] m caller

   rw [MachineControl.branchCode,Evm.run_append_ok testedTarget] at ran
   by_cases zero : condition.value locals = 0
   · rw [zero] at ran
     change Evm.exec qb qb.length {m with stack := locals.toList.map coreWord++caller} = .ok final skip at ran
     rw [Evm.exec_length] at ran
     have parts := Evm.Out.ok.inj ran
     exact ⟨_,locals,LetControlCompletion.source_false condition arm.profile locals zero,parts.2.symm,parts.1.symm⟩
   · rw [FramedBranch.nonzero_tail (condition.value locals) qb []
       {m with stack := locals.toList.map coreWord++caller} zero] at ran
     obtain ⟨horizon,out,source,done,frame⟩ := ih b qb hb sb locals m final skip ran
     exact ⟨_,out,LetControlCompletion.source_true condition arm.profile horizon locals out zero source,done,frame⟩
 | @zero n fuel fresh bodyStmt scope ih =>
   change (scope.emit).bind (fun b => some (Backend.Block.seq (.code (ZeroLoopScope.entry fresh))
     (.seq b (.code (popPrefix fresh))))) = some block at emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp emitted
   cases Option.some.inj same
   obtain ⟨begin,middle,finish,hs,hm,hf,same⟩ := ScopedControlCompilation.scope_selected _ _ _ _ selected
   subst code

   have entering := WordExecution.run (ZeroLoopScope.entry fresh) begin hs locals.toList
     ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList) (pushPrefix_run _ _) m caller
   have entering' : Evm.run begin {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := (Vector.replicate fresh (0 : Scalar.Word) ++ locals).toList.map coreWord++caller} 0 := by
     simpa only [Vector.toList_append] using entering
   rw [Evm.run_append_ok entering'] at ran
   have whole : (Evm.run middle
     {m with stack := (Vector.replicate fresh (0 : Scalar.Word) ++ locals).toList.map coreWord++caller}).bind
     (fun mid pending => Evm.exec finish pending mid) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run middle
     {m with stack := (Vector.replicate fresh (0 : Scalar.Word) ++ locals).toList.map coreWord++caller} with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok mid pending =>
     obtain ⟨horizon,out,source,done,frame⟩ := ih b middle hb hm
       (Vector.replicate fresh (0 : Scalar.Word) ++ locals) m mid pending actual
     rw [actual,done,frame] at whole
     change Evm.run finish {m with stack := out.toList.map coreWord++caller} = .ok final skip at whole
     have exitScalar : Scalar.run (popPrefix fresh) out.toList = some (outerLocals out).toList := by
       simpa only [List.append_nil] using popFresh_run out []
     have exiting := WordExecution.run (popPrefix fresh) finish hf out.toList (outerLocals out).toList exitScalar m caller
     have parts := Evm.Out.ok.inj (exiting.symm.trans whole)
     exact ⟨horizon+1,outerLocals out,ScopedControlCompletion.source_zero scope.profile horizon locals out source,parts.2.symm,parts.1.symm⟩
 | @letOne n fuel rhs bodyStmt initializer scope ih =>
   change (initializer.lowered.code 0).bind (fun p => (scope.emit).bind (fun b =>
     some (Backend.Block.seq (.code p) (.seq b (.code (popPrefix 1)))))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   obtain ⟨begin,middle,finish,hs,hm,hf,same⟩ := ScopedControlCompilation.scope_selected _ _ _ _ selected
   subst code

   have initScalar : Scalar.run p locals.toList = some (initializer.value locals::locals.toList) := by
     simpa only [Vector.toList_empty,List.nil_append,List.append_nil] using
       initializer.lowered.correct 0 p hp locals #v[] []
   have entering := WordExecution.run p begin hs locals.toList (initializer.value locals::locals.toList) initScalar m caller
   have entering' : Evm.run begin {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := (#v[initializer.value locals] ++ locals).toList.map coreWord++caller} 0 := by
     simpa only [Vector.toList_append,Vector.toList_singleton,List.singleton_append] using entering
   rw [Evm.run_append_ok entering'] at ran
   have whole : (Evm.run middle
     {m with stack := (#v[initializer.value locals] ++ locals).toList.map coreWord++caller}).bind
     (fun mid pending => Evm.exec finish pending mid) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run middle
     {m with stack := (#v[initializer.value locals] ++ locals).toList.map coreWord++caller} with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok mid pending =>
     obtain ⟨horizon,out,source,done,frame⟩ := ih b middle hb hm
       (#v[initializer.value locals] ++ locals) m mid pending actual
     rw [actual,done,frame] at whole
     change Evm.run finish {m with stack := out.toList.map coreWord++caller} = .ok final skip at whole
     have exitScalar : Scalar.run (popPrefix 1) out.toList = some (outerLocals out).toList := by
       simpa only [List.append_nil] using popFresh_run out []
     have exiting := WordExecution.run (popPrefix 1) finish hf out.toList (outerLocals out).toList exitScalar m caller
     have parts := Evm.Out.ok.inj (exiting.symm.trans whole)
     exact ⟨max fuel horizon+1,outerLocals out,ScopedControlCompletion.source_let initializer scope.profile horizon locals out source,
       parts.2.symm,parts.1.symm⟩

theorem artifact_reflected {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact.compiled artifact.block artifact.code artifact.emitted artifact.selected locals m final caller skip ran

theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (artifact_reflected artifact) locals out m caller


/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.artifact_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms artifact_reflected
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.StructuredSequenceCompletion

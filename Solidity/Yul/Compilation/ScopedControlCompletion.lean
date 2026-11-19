import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.ScopedControlCompilation
import Solidity.Yul.Compilation.LetControlCompletion
/-! Reverse normal-success transport through recursively varying local contexts.
Actual emitted compiler blocks and selected runs derive original source runs;
capacity, native execution and logical Source/G24 remain separate obligations. -/
namespace Solidity.Yul.Compilation.ScopedControlCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open ScopedControlCompilation

theorem source_zero {c : Control} {n fresh : Nat} {body : Stmt [] [] c (fresh+n)}
 (profile : StmtWordP body) (horizon : Nat)
 (locals : Vector Scalar.Word n) (out : Vector Scalar.Word (fresh+n))
 (ran : evalStmt horizon .nil True.intro body profile
   (sourceLocals (Vector.replicate fresh (0 : Scalar.Word) ++ locals)) = some ⟨sourceLocals out,.normal⟩) :
 evalStmt (horizon+1) .nil True.intro (.zero fresh body) profile (sourceLocals locals) =
 some ⟨sourceLocals (outerLocals out),.normal⟩ := by
 change Option.bind (evalStmt horizon .nil True.intro body profile
   (extendValues (fun _ : Fin fresh => word 0) (sourceLocals locals))) _ = _
 rw [←ZeroLoopScope.initial_values,ran]
 change some (⟨dropValues fresh (sourceLocals out),.normal⟩ : Outcome c n) = _
 rw [←ScopedStatements.locals_outer]

theorem source_let {c : Control} {n fuel : Nat} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
 (initializer : ProducerExpressions.Compiled fuel rhs)
 (profile : StmtWordP body) (horizon : Nat)
 (locals : Vector Scalar.Word n) (out : Vector Scalar.Word (1+n))
 (ran : evalStmt horizon .nil True.intro body profile
   (sourceLocals (#v[initializer.value locals] ++ locals)) = some ⟨sourceLocals out,.normal⟩) :
 evalStmt (max fuel horizon+1) .nil True.intro (.let_ 1 rhs body)
   (⟨initializer.profile,profile⟩ : StmtWordP (.let_ 1 rhs body)) (sourceLocals locals) =
 some ⟨sourceLocals (outerLocals out),.normal⟩ := by
 have expr := evalExpr_stable (Nat.le_max_left fuel horizon) .nil True.intro rhs initializer.profile
   (sourceLocals locals) (initializer.source locals)
 have bodyRun := evalStmt_stable (Nat.le_max_right fuel horizon) .nil True.intro body profile
   (sourceLocals (#v[initializer.value locals] ++ locals)) ran
 change (do
   let values ← evalExpr (max fuel horizon) .nil True.intro rhs initializer.profile (sourceLocals locals)
   let middle ← evalStmt (max fuel horizon) .nil True.intro body profile
     (extendValues values (sourceLocals locals))
   pure (⟨dropValues 1 middle.vars,middle.flow⟩ : Outcome c n)) = _
 rw [expr]
 change (do
   let middle ← evalStmt (max fuel horizon) .nil True.intro body profile
     (extendValues (fun _ : Fin 1 => (initializer.value locals).toFin) (sourceLocals locals))
   pure (⟨dropValues 1 middle.vars,middle.flow⟩ : Outcome c n)) = _
 rw [LetScopeCompilation.initial_values,bodyRun]
 change some (⟨dropValues 1 (sourceLocals out),.normal⟩ : Outcome c n) = _
 rw [←ScopedStatements.locals_outer]


/-- Reflection supplied by an actual component theorem, including arbitrary
machine, caller frame and pending skip in the successful executor result. -/
abbrev ModelSource {c : Control} {n : Nat} (stmt : Stmt [] [] c n)
 (profile : StmtWordP stmt) (code : List Evm.Instr) (caller : List Evm.Word) :=
 ∀ (locals : Vector Scalar.Word n) (m final : Evm.Machine) (skip : Nat),
 Evm.run code {m with stack := locals.toList.map coreWord++caller} = .ok final skip →
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩ ∧
 skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller}

theorem seq_reflect {c : Control} {n : Nat} {a b : Stmt [] [] c n}
 (leftProfile : StmtWordP a) (rightProfile : StmtWordP b) (qa qb : List Evm.Instr)
 (caller : List Evm.Word)
 (leftLaw : ModelSource a leftProfile qa caller) (rightLaw : ModelSource b rightProfile qb caller) :
 ModelSource (.seq a b) ⟨leftProfile,rightProfile⟩ (qa++qb) caller := by
 intro locals m final skip ran
 have whole : (Evm.run qa {m with stack := locals.toList.map coreWord++caller}).bind
   (fun mid pending => Evm.exec qb pending mid) = .ok final skip := by
   simpa only [Evm.run,Evm.exec_append] using ran
 cases actual : Evm.run qa {m with stack := locals.toList.map coreWord++caller} with
 | revert => rw [actual] at whole; cases whole
 | fault => rw [actual] at whole; cases whole
 | ok mid pending =>
   obtain ⟨lo,intermediate,leftSource,done,frame⟩ := leftLaw locals m mid pending actual
   rw [actual,done,frame] at whole
   change Evm.run qb {m with stack := intermediate.toList.map coreWord++caller} = .ok final skip at whole
   obtain ⟨hi,out,rightSource,done,frame⟩ := rightLaw intermediate m final skip whole
   have first : evalStmt (max lo hi) .nil True.intro _ leftProfile (sourceLocals locals) =
     some ⟨sourceLocals intermediate,.normal⟩ := CompletionControls.completed_horizon
     (fun fuel => evalStmt fuel .nil True.intro _ leftProfile (sourceLocals locals))
     (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ leftProfile (sourceLocals locals))
     (Nat.le_max_left lo hi) leftSource
   have last : evalStmt (max lo hi) .nil True.intro _ rightProfile (sourceLocals intermediate) =
     some ⟨sourceLocals out,.normal⟩ := CompletionControls.completed_horizon
     (fun fuel => evalStmt fuel .nil True.intro _ rightProfile (sourceLocals intermediate))
     (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ rightProfile (sourceLocals intermediate))
     (Nat.le_max_right lo hi) rightSource
   have source := LoopControlCompilation.sequence_source _ _ leftProfile rightProfile (max lo hi)
     (sourceLocals locals) (sourceLocals intermediate) (sourceLocals out) first last
   exact ⟨max lo hi+1,out,source,done,frame⟩

theorem branch_reflect {c : Control} {n fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (condition : ProducerExpressions.Compiled fuel test) (armProfile : StmtWordP body)
 (p : Backend.Program) (q qb : List Evm.Instr)
 (hp : condition.lowered.code 0 = some p) (sq : WordMachine.selectCode p = some q)
 (caller : List Evm.Word) (armLaw : ModelSource body armProfile qb caller) :
 ModelSource (.if_ test body) ⟨condition.profile,armProfile⟩ (MachineControl.branchCode q qb []) caller := by
 intro locals m final skip ran
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
   exact ⟨_,locals,LetControlCompletion.source_false condition armProfile locals zero,parts.2.symm,parts.1.symm⟩
 · rw [FramedBranch.nonzero_tail (condition.value locals) qb []
     {m with stack := locals.toList.map coreWord++caller} zero] at ran
   obtain ⟨horizon,out,source,done,frame⟩ := armLaw locals m final skip ran
   exact ⟨_,out,LetControlCompletion.source_true condition armProfile horizon locals out zero source,done,frame⟩

theorem zero_reflect {c : Control} {n fresh : Nat} {bodyStmt : Stmt [] [] c (fresh+n)}
 (bodyProfile : StmtWordP bodyStmt) (begin middle finish : List Evm.Instr)
 (hs : WordMachine.selectCode (ZeroLoopScope.entry fresh) = some begin)
 (hf : WordMachine.selectCode (popPrefix fresh) = some finish)
 (caller : List Evm.Word) (bodyLaw : ModelSource bodyStmt bodyProfile middle caller) :
 ModelSource (.zero fresh bodyStmt) bodyProfile (begin++(middle++finish)) caller := by
 intro locals m final skip ran
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
   obtain ⟨horizon,out,source,done,frame⟩ := bodyLaw
     (Vector.replicate fresh (0 : Scalar.Word) ++ locals) m mid pending actual
   rw [actual,done,frame] at whole
   change Evm.run finish {m with stack := out.toList.map coreWord++caller} = .ok final skip at whole
   have exitScalar : Scalar.run (popPrefix fresh) out.toList = some (outerLocals out).toList := by
     simpa only [List.append_nil] using popFresh_run out []
   have exiting := WordExecution.run (popPrefix fresh) finish hf out.toList (outerLocals out).toList exitScalar m caller
   have parts := Evm.Out.ok.inj (exiting.symm.trans whole)
   exact ⟨horizon+1,outerLocals out,source_zero bodyProfile horizon locals out source,parts.2.symm,parts.1.symm⟩

theorem let_reflect {c : Control} {n fuel : Nat} {rhs : Expr [] [] n 1} {bodyStmt : Stmt [] [] c (1+n)}
 (initializer : ProducerExpressions.Compiled fuel rhs) (bodyProfile : StmtWordP bodyStmt)
 (p : Backend.Program) (begin middle finish : List Evm.Instr)
 (hp : initializer.lowered.code 0 = some p) (hs : WordMachine.selectCode p = some begin)
 (hf : WordMachine.selectCode (popPrefix 1) = some finish)
 (caller : List Evm.Word) (bodyLaw : ModelSource bodyStmt bodyProfile middle caller) :
 ModelSource (.let_ 1 rhs bodyStmt) ⟨initializer.profile,bodyProfile⟩ (begin++(middle++finish)) caller := by
 intro locals m final skip ran
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
   obtain ⟨horizon,out,source,done,frame⟩ := bodyLaw
     (#v[initializer.value locals] ++ locals) m mid pending actual
   rw [actual,done,frame] at whole
   change Evm.run finish {m with stack := out.toList.map coreWord++caller} = .ok final skip at whole
   have exitScalar : Scalar.run (popPrefix 1) out.toList = some (outerLocals out).toList := by
     simpa only [List.append_nil] using popFresh_run out []
   have exiting := WordExecution.run (popPrefix 1) finish hf out.toList (outerLocals out).toList exitScalar m caller
   have parts := Evm.Out.ok.inj (exiting.symm.trans whole)
   exact ⟨max fuel horizon+1,outerLocals out,source_let initializer bodyProfile horizon locals out source,
     parts.2.symm,parts.1.symm⟩

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
   simpa only [Vector.toList_empty,List.nil_append] using
     LoopControlCompletion.artifact_reflected artifact locals #v[] m final caller skip ran
 | seq left right ihLeft ihRight =>
   change (left.emit).bind (fun a => (right.emit).bind (fun b => some (Backend.Block.seq a b))) = some block at emitted
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordControl.blockCode a).bind (fun qa => (WordControl.blockCode b).map (fun qb => qa++qb)) = some code at selected
   obtain ⟨qa,sa,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code

   exact seq_reflect left.profile right.profile qa qb caller (ihLeft a qa ha sa) (ihRight b qb hb sb) locals m final skip ran
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
   exact branch_reflect condition arm.profile p q qb hp sq caller (ih b qb hb sb) locals m final skip ran
 | @zero n fuel fresh bodyStmt scope ih =>
   change (scope.emit).bind (fun b => some (Backend.Block.seq (.code (ZeroLoopScope.entry fresh))
     (.seq b (.code (popPrefix fresh))))) = some block at emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp emitted
   cases Option.some.inj same
   obtain ⟨begin,middle,finish,hs,hm,hf,same⟩ := scope_selected _ _ _ _ selected
   subst code

   exact zero_reflect scope.profile begin middle finish hs hf caller (ih b middle hb hm) locals m final skip ran
 | @letOne n fuel rhs bodyStmt initializer scope ih =>
   change (initializer.lowered.code 0).bind (fun p => (scope.emit).bind (fun b =>
     some (Backend.Block.seq (.code p) (.seq b (.code (popPrefix 1)))))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   obtain ⟨begin,middle,finish,hs,hm,hf,same⟩ := scope_selected _ _ _ _ selected
   subst code

   exact let_reflect initializer scope.profile p begin middle finish hp hs hf caller (ih b middle hb hm) locals m final skip ran

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

/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.source_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_zero
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.source_let' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_let
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.artifact_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms artifact_reflected
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.ScopedControlCompletion

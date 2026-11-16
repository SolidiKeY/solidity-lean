import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.LoopControlCompilation
/-! Reverse normal-success transport through the existing recursive compiler.
Actual target successes derive source horizons/intermediate locals; no source
or favourable component run is assumed. Native/Source-G24 remain separate. -/
namespace Solidity.Yul.Compilation.LoopControlCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions LoopControlCompilation
/-- False source guard completes without a body-run premise. -/
theorem source_zero {c : Control} {n fc : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (condition : ProducerExpressions.Compiled fc test) (hb : StmtWordP body)
 (locals : Vector Scalar.Word n) (zero : condition.value locals = 0) :
 evalStmt (fc+1) .nil True.intro (.if_ test body) ⟨condition.profile,hb⟩ (sourceLocals locals) =
 some ⟨sourceLocals locals,.normal⟩ := by
 change Option.bind (evalExpr fc .nil True.intro test condition.profile (sourceLocals locals)) _ = _
 rw [condition.source]
 have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
 change (if (condition.value locals).toNat = 0 then _ else _) = _
 rw [if_pos zn]
 rfl

/-- Real taken-body completion constructs a sufficient source if horizon.
The maximum preserves both real component horizons; no budget is changed. -/
theorem source_nonzero {c : Control} {n fc : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (condition : ProducerExpressions.Compiled fc test) (hb : StmtWordP body)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (nonzero : condition.value locals ≠ 0)
 (ran : evalStmt horizon .nil True.intro body hb (sourceLocals locals) = some result) :
 evalStmt (max fc horizon+1) .nil True.intro (.if_ test body) ⟨condition.profile,hb⟩ (sourceLocals locals) = some result := by
 have tested : evalExpr (max fc horizon) .nil True.intro test condition.profile (sourceLocals locals) =
   some (fun _ => (condition.value locals).toFin) := CompletionControls.completed_horizon
   (fun fuel => evalExpr fuel .nil True.intro test condition.profile (sourceLocals locals))
   (fun fuel extra => evalExpr_refines_add fuel extra .nil True.intro test condition.profile (sourceLocals locals))
   (Nat.le_max_left fc horizon) (condition.source locals)
 have completed : evalStmt (max fc horizon) .nil True.intro body hb (sourceLocals locals) = some result :=
   CompletionControls.completed_horizon
     (fun fuel => evalStmt fuel .nil True.intro body hb (sourceLocals locals))
     (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro body hb (sourceLocals locals))
     (Nat.le_max_right fc horizon) ran
 change Option.bind (evalExpr (max fc horizon) .nil True.intro test condition.profile (sourceLocals locals)) _ = _
 rw [tested]
 have nz : (condition.value locals).toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 change (if (condition.value locals).toNat = 0 then _ else _) = _
 rw [if_neg nz]
 exact completed

/-- Actual whole model success derives all intermediate vectors, chosen runs,
normal source completions and zero pending control. No desired source horizon,
source execution, component success, count or guard sequence is a premise. -/
theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : LoopControlCompilation.Compiled fuel stmt) (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit depth = some block) (selected : WordControl.blockCode block = some code)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := (newer.toList++out.toList).map coreWord++caller} := by
 induction compiled generalizing block code locals final skip with
 | normal leaf =>
   have actual := NormalWordTransport.machine leaf depth block code emitted selected locals newer m caller
   have parts := Evm.Out.ok.inj (actual.symm.trans ran)
   exact ⟨_,leaf.update locals,leaf.source locals,parts.2.symm,parts.1.symm⟩
 | loop leaf =>
   cases leaf with
   | loop initializer condition step work =>
     exact InitializedLoopCompletion.model_to_source initializer condition step work depth block code
       emitted selected locals newer m final caller skip ran
 | seq left right ihLeft ihRight =>
   change (left.emit depth).bind (fun a => (right.emit depth).bind (fun b =>
     some (Backend.Block.seq a b))) = some block at emitted
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   obtain ⟨qa,sa,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   have whole : (Evm.run qa {m with stack := (newer.toList++locals.toList).map coreWord++caller}).bind
     (fun mid pending => Evm.exec qb pending mid) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases first : Evm.run qa {m with stack := (newer.toList++locals.toList).map coreWord++caller} with
   | revert => rw [first] at whole; cases whole
   | fault => rw [first] at whole; cases whole
   | ok middle pending =>
     obtain ⟨f1,mid,source1,zero,frame⟩ := ihLeft a qa ha sa locals middle pending first
     rw [first,zero] at whole
     change Evm.run qb middle = .ok final skip at whole
     rw [frame] at whole
     obtain ⟨f2,out,source2,done,finalFrame⟩ := ihRight b qb hb sb mid final skip whole
     have firstSource : evalStmt (max f1 f2) .nil True.intro _ left.profile (sourceLocals locals) =
       some ⟨sourceLocals mid,.normal⟩ := CompletionControls.completed_horizon
       (fun fuel => evalStmt fuel .nil True.intro _ left.profile (sourceLocals locals))
       (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ left.profile (sourceLocals locals))
       (Nat.le_max_left f1 f2) source1
     have lastSource : evalStmt (max f1 f2) .nil True.intro _ right.profile (sourceLocals mid) =
       some ⟨sourceLocals out,.normal⟩ := CompletionControls.completed_horizon
       (fun fuel => evalStmt fuel .nil True.intro _ right.profile (sourceLocals mid))
       (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ right.profile (sourceLocals mid))
       (Nat.le_max_right f1 f2) source2
     exact ⟨max f1 f2+1,out,LoopControlCompilation.sequence_source _ _ left.profile right.profile
       (max f1 f2) (sourceLocals locals) (sourceLocals mid) (sourceLocals out) firstSource lastSource,done,finalFrame⟩
 | branch condition arm ih =>
   change (condition.lowered.code depth).bind (fun p => (arm.emit depth).bind (fun b =>
     some (Backend.Block.ite p b (.code [])))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordMachine.selectCode p).bind (fun q => (WordControl.blockCode b).bind (fun qb =>
     some (MachineControl.branchCode q qb []))) = some code at selected
   obtain ⟨q,sq,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have testedTarget := WordExecution.loweredExpr_machine condition.lowered depth p q hp sq locals newer m caller
   rw [MachineControl.branchCode,Evm.run_append_ok testedTarget] at ran
   by_cases zero : condition.value locals = 0
   · rw [zero] at ran
     change Evm.exec qb qb.length {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .ok final skip at ran
     rw [Evm.exec_length] at ran
     have parts := Evm.Out.ok.inj ran
     exact ⟨_,locals,source_zero condition arm.profile locals zero,parts.2.symm,parts.1.symm⟩
   · rw [FramedBranch.nonzero_tail (condition.value locals) qb []
       {m with stack := (newer.toList++locals.toList).map coreWord++caller} zero] at ran
     obtain ⟨horizon,out,source,done,frame⟩ := ih b qb hb sb locals final skip ran
     exact ⟨_,out,source_nonzero condition arm.profile horizon locals _ zero source,done,frame⟩

/-- Exact normal-success equivalence for the existing recursive compiler.
Source horizon is existential and all real emission/selection premises remain;
this states neither fixed-fuel failure nor native/resource equivalence. -/
theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : LoopControlCompilation.Compiled fuel stmt) (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit depth = some block) (selected : WordControl.blockCode block = some code)
 (locals out : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_of_transport stmt compiled.profile code
   (LoopControlCompilation.source_to_model compiled depth block code emitted selected)
   (model_to_source compiled depth block code emitted selected) locals out newer m caller

/-- Selected artifact consumer with all actual emission/selection equations
stored by the original visitor. No new assumed simulation interface. -/
theorem artifact_iff {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}
 (artifact : LoopControlCompilation.Artifact fuel stmt depth)
 (locals out : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 :=
 completion_iff artifact.compiled depth artifact.block artifact.code artifact.emitted artifact.selected locals out newer m caller

/-- Unknown actual successful artifact result yields original source
completion and the exact whole frame, with pending skip derived as zero. -/
theorem artifact_reflected {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}
 (artifact : LoopControlCompilation.Artifact fuel stmt depth)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := (newer.toList++out.toList).map coreWord++caller} :=
 model_to_source artifact.compiled depth artifact.block artifact.code artifact.emitted artifact.selected locals newer m final caller skip ran

/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.source_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_zero
/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.source_nonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_nonzero
/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.artifact_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms artifact_iff
/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.artifact_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms artifact_reflected
end Solidity.Yul.Compilation.LoopControlCompletion

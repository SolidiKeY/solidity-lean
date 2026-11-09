import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.SequenceCompilation
import Solidity.Yul.Compilation.ScopedControlCompletion
import Solidity.Yul.Compilation.MultiSwitchCompletion
/-! Recursive normal-success reflection for the original sequence compiler.
Actual leaf reflections and actual append execution derive source completions,
intermediate raw locals, zero pending skips and exact arbitrary caller frames.
Native capacity, static admission and Source/G24 remain separate obligations. -/
namespace Solidity.Yul.Compilation.SequenceCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SequenceCompilation

theorem model_to_source {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled c fuel stmt) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit = some block) (selected : WordControl.blockCode block = some code)
 (locals : Vector Scalar.Word n) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 induction compiled generalizing block code locals m final caller skip with
 | scopeLeaf artifact =>
   cases Option.some.inj emitted
   have same : code = artifact.code := Option.some.inj (selected.symm.trans artifact.selected)
   subst code
   exact ScopedControlCompletion.artifact_reflected artifact locals m final caller skip ran
 | switch_ artifact =>
   cases Option.some.inj emitted
   have same : code = artifact.code := Option.some.inj (selected.symm.trans artifact.selected)
   subst code
   exact MultiSwitchCompletion.model_to_source artifact locals m final caller skip ran
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
     (fun middle pending => Evm.exec qb pending middle) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run qa {m with stack := locals.toList.map coreWord++caller} with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok middle pending =>
     obtain ⟨lo,mid,first,retired,frame⟩ := ihLeft a qa ha sa locals m middle caller pending actual
     rw [actual,retired,frame] at whole
     change Evm.run qb {m with stack := mid.toList.map coreWord++caller} = .ok final skip at whole
     obtain ⟨hi,out,last,done,finalFrame⟩ := ihRight b qb hb sb mid m final caller skip whole
     have firstH : evalStmt (max lo hi) .nil True.intro _ left.profile (sourceLocals locals) =
       some ⟨sourceLocals mid,.normal⟩ := CompletionControls.completed_horizon
       (fun fuel => evalStmt fuel .nil True.intro _ left.profile (sourceLocals locals))
       (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ left.profile (sourceLocals locals))
       (Nat.le_max_left lo hi) first
     have lastH : evalStmt (max lo hi) .nil True.intro _ right.profile (sourceLocals mid) =
       some ⟨sourceLocals out,.normal⟩ := CompletionControls.completed_horizon
       (fun fuel => evalStmt fuel .nil True.intro _ right.profile (sourceLocals mid))
       (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ right.profile (sourceLocals mid))
       (Nat.le_max_right lo hi) last
     have source := LoopControlCompilation.sequence_source _ _ left.profile right.profile (max lo hi)
       (sourceLocals locals) (sourceLocals mid) (sourceLocals out) firstH lastH
     exact ⟨max lo hi+1,out,source,done,finalFrame⟩

theorem artifact_reflected {c n fuel} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact.compiled artifact.block artifact.code artifact.emitted artifact.selected locals m final caller skip ran

theorem completion_iff {c n fuel} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (artifact_reflected artifact) locals out m caller

/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.model_to_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.artifact_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms artifact_reflected
/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.completion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.SequenceCompletion

import Solidity.Yul.Compilation.SourceLoopCompletion
import Solidity.Yul.Compilation.FramedLoop
/-! Success equivalence for actual emitted normal-component source for loops.
Source horizons and model iteration witnesses are recovered from completions;
no finite guards or chosen counts are premises. This does not equate horizon
exhaustion/model noncompletion faults or establish native/G24 adequacy. -/
namespace Solidity.Yul.Compilation.SourceLoopModelCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions SourceLoop
open SourceLoopCompletion

variable {c : Solidity.Yul.Control} {n fc fp fb : Nat}
 {test : Solidity.Yul.Expr [] [] n 1}
 {step : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {work : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}

/-- Real compiled turns preserve the represented local frame. A successful
actual bounded iteration therefore recovers its real finite source updates. -/
theorem iteration_completed (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (cc bb : Backend.Program) (qc qb : List Evm.Instr)
 (hc : condition.lowered.code depth = some cc)
 (hb : (lowerSeq body.lowered post.lowered).code depth = some bb)
 (sc : WordMachine.selectCode cc = some qc) (sb : WordMachine.selectCode bb = some qb)
 (horizon : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.loopIterN (Evm.run qc) (Evm.run qb) horizon
   {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .inr (.ok final skip)) :
 ∃ count, (∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0) ∧
 condition.value (Nat.repeat (next body post) count locals) = 0 ∧ skip = 0 ∧
 final = {m with stack := (newer.toList++(Nat.repeat (next body post) count locals).toList).map coreWord++caller} := by
 induction horizon generalizing locals with
 | zero => cases ran
 | succ horizon ih =>
   rewrite [Evm.loopIterN,WhileWordExecution.turn condition.lowered (lowerSeq body.lowered post.lowered)
    cc bb qc qb hc hb sc sb locals newer m caller] at ran
   by_cases zero : condition.value locals = 0
   · rewrite [if_pos zero] at ran
     have parts := Evm.Out.ok.inj (Sum.inr.inj ran)
     refine ⟨0,?_,zero,parts.2.symm,parts.1.symm⟩
     intro j bound
     omega
   · rewrite [if_neg zero] at ran
     change Evm.loopIterN (Evm.run qc) (Evm.run qb) horizon
      {m with stack := (newer.toList++(next body post locals).toList).map coreWord++caller} = .inr (.ok final skip) at ran
     obtain ⟨count,running,stopped,done,frame⟩ := ih (next body post locals) ran
     refine ⟨count+1,?_,?_,done,?_⟩
     · intro j bound
       cases j with
       | zero => exact zero
       | succ j => simpa only [repeat_shift] using running j (by omega)
     · simpa only [repeat_shift] using stopped
     · simpa only [repeat_shift] using frame

/-- A successful actual emitted artifact supplies a finite source completion,
including the exact full target frame and pending zero. No guards/count/source
horizon or favourable intermediate execution are assumed. -/
theorem model_to_source (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : SourceLoop.emit condition post body depth = some block)
 (selected : WordControl.blockCode block = some code)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .ok final skip) :
 ∃ (fuel : Nat) (out : Vector Scalar.Word n),
 evalStmt fuel .nil True.intro (Solidity.Yul.Stmt.for_ (c := c) .skip test step work)
  ⟨True.intro,condition.profile,post.profile,body.profile⟩ (sourceLocals locals) =
    some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := (newer.toList++out.toList).map coreWord++caller} := by
 change (condition.lowered.code depth).bind (fun cc =>
  (lowerSeq body.lowered post.lowered).code depth |>.map (fun bb => Backend.Block.loop cc (.code bb))) = some block at emitted
 obtain ⟨cc,hc,rest⟩ := Option.bind_eq_some_iff.mp emitted
 obtain ⟨bb,hb,same⟩ := Option.map_eq_some_iff.mp rest
 subst block
 obtain ⟨qc,sc,rest⟩ := Option.bind_eq_some_iff.mp selected
 obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
 subst code
 rewrite [FramedLoop.singleton_run] at ran
 have finite : ∃ horizon, Evm.loopIterN (Evm.run qc) (Evm.run qb) horizon
    {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .inr (.ok final skip) := by
  by_cases ends : ∃ result horizon, Evm.loopIterN (Evm.run qc) (Evm.run qb) horizon
    {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .inr result
  · obtain ⟨result,horizon,actual⟩ := ends
    have same : result = .ok final skip := (Evm.loopRun_of_iterN actual).symm.trans ran
    exact ⟨horizon,actual.trans (congrArg Sum.inr same)⟩
  · simp only [Evm.loopRun,ends,↓reduceDIte] at ran
    cases ran
 obtain ⟨horizon,actual⟩ := finite
 obtain ⟨count,running,stopped,done,frame⟩ := iteration_completed condition post body depth
   cc bb qc qb hc hb sc sb horizon locals newer m final caller skip actual
 exact ⟨max fc (max fp fb)+count+2,Nat.repeat (next body post) count locals,
  SourceLoop.for_finite condition post body count locals running stopped,done,frame⟩

/-- Exact normal-success equivalence for this ACTUAL original source form and
selected artifact. Source horizon is existential, never a fixed budget, and the
numeric locals and arbitrary caller tail determine the entire target frame. -/
theorem completion_iff (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : SourceLoop.emit condition post body depth = some block)
 (selected : WordControl.blockCode block = some code)
 (locals out : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ fuel, evalStmt fuel .nil True.intro (Solidity.Yul.Stmt.for_ (c := c) .skip test step work)
   ⟨True.intro,condition.profile,post.profile,body.profile⟩ (sourceLocals locals) =
     some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 constructor
 · rintro ⟨fuel,ran⟩
   obtain ⟨actual,same,target⟩ := source_to_model condition post body depth block code emitted selected
     fuel locals ⟨sourceLocals out,.normal⟩ ran newer m caller
   have values : sourceLocals out = sourceLocals actual := congrArg Outcome.vars same
   have equal : out = actual := sourceLocals_injective values
   cases equal
   exact target
 · intro ran
   obtain ⟨fuel,actual,source,_,frame⟩ := model_to_source condition post body depth block code emitted selected
     locals newer m {m with stack := (newer.toList++out.toList).map coreWord++caller} caller 0 ran
   have stacks := congrArg Evm.Machine.stack frame
   have mapped : (newer.toList++out.toList).map coreWord =
     (newer.toList++actual.toList).map coreWord := List.append_cancel_right stacks
   have lists : newer.toList++out.toList = newer.toList++actual.toList :=
     (List.map_inj_right (fun _ _ h => coreWord_injective h)).mp mapped
   have equal : out = actual := Vector.toList_inj.mp (List.append_cancel_left lists)
   cases equal
   exact ⟨fuel,source⟩

/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.iteration_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iteration_completed
/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.SourceLoopModelCompletion

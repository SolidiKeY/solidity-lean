import Solidity.Yul.Compilation.StructuredSequenceCompilation
/-! Actual finite original loop-phase completion through recursively structured
sequence/switch/conditional/scope body and post compiler artifacts. Existing source and model loop executors are
unchanged; no native/divergence/capacity/G24 adequacy is inferred. -/
namespace Solidity.Yul.Compilation.StructuredLoopExecution
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fc fp fb : Nat} {test : Expr [] [] n 1}
 {step : Stmt [] [] ⟨c.function,false⟩ n} {work : Stmt [] [] ⟨c.function,true⟩ n}

theorem finite (condition : ProducerExpressions.Compiled fc test)
 (post : StructuredSequenceCompilation.Artifact fp step) (body : StructuredSequenceCompilation.Artifact fb work)
 (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code 0 = some p) (selected : WordMachine.selectCode p = some q)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalLoop horizon .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.loopIterN (Evm.run q) (Evm.run (body.code++post.code)) horizon
   {m with stack := locals.toList.map coreWord++caller} =
 .inr (.ok {m with stack := out.toList.map coreWord++caller} 0) := by
 exact SourceLoop.finite_components condition post.compiled.profile body.compiled.profile
   post.code body.code p q emitted selected m caller
   (fun horizon locals result ran => post.source_to_model horizon locals result ran m caller)
   (fun horizon locals result ran => body.source_to_model horizon locals result ran m caller)
   horizon locals result ran

theorem model (condition : ProducerExpressions.Compiled fc test)
 (post : StructuredSequenceCompilation.Artifact fp step) (body : StructuredSequenceCompilation.Artifact fb work)
 (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code 0 = some p) (selected : WordMachine.selectCode p = some q)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalLoop horizon .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run [.loop q (body.code++post.code)] {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨out,same,completed⟩ := finite condition post body p q emitted selected horizon locals result ran m caller
 refine ⟨out,same,?_⟩
 have ended := Evm.loopRun_of_iterN completed
 change (Evm.loopRun (Evm.run q) (Evm.run (body.code++post.code)) _).bind
   (fun next pending => Evm.exec [] pending next) = _
 rw [ended]
 rfl

/-- Existing compiler blocks are emitted directly; body and post retain their
actual scoped compiler artifacts and exact original control indices. -/
def emit (condition : ProducerExpressions.Compiled fc test)
 (post : StructuredSequenceCompilation.Artifact fp step) (body : StructuredSequenceCompilation.Artifact fb work) :
 Option Backend.Block :=
 (condition.lowered.code 0).map (fun p => .loop p (.seq body.block post.block))

theorem selection (condition : ProducerExpressions.Compiled fc test)
 (post : StructuredSequenceCompilation.Artifact fp step) (body : StructuredSequenceCompilation.Artifact fb work)
 (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code 0 = some p) (selected : WordMachine.selectCode p = some q) :
 emit condition post body = some (.loop p (.seq body.block post.block)) ∧
 WordControl.blockCode (.loop p (.seq body.block post.block)) = some [.loop q (body.code++post.code)] := by
 constructor
 · rw [emit,emitted]; rfl
 · change (WordMachine.selectCode p).bind (fun q =>
     ((WordControl.blockCode body.block).bind (fun b => (WordControl.blockCode post.block).map (fun p => b++p))).map
       (fun b => [Evm.Instr.loop q b])) = _
   rw [selected,body.selected,post.selected]
   rfl

/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selection
end Solidity.Yul.Compilation.StructuredLoopExecution

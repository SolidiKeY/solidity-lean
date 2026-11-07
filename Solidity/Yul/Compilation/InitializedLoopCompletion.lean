import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.SourceLoopInitializer
/-! Reverse and exact normal-success transport for actual initialized Yul for
compilation. No source failure/divergence/native/Source-G24 adequacy follows. -/
namespace Solidity.Yul.Compilation.InitializedLoopCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions SourceLoop
variable {c : Solidity.Yul.Control} {n fi fc fp fb : Nat}
 {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {test : Solidity.Yul.Expr [] [] n 1}
 {step : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {work : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
/-- Whole emitted target success determines a genuine original-source horizon.
The initializer run and intermediate locals are derived from its concrete
compiler; no intermediate execution or favorable source completion is assumed. -/
theorem model_to_source (initial : ProducerStatements.Compiled fi pre) (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : SourceLoopInitializer.emit initial condition post body depth = some block)
 (selected : WordControl.blockCode block = some code)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .ok final skip) :
 ∃ (fuel : Nat) (out : Vector Scalar.Word n),
 evalStmt fuel .nil True.intro (Solidity.Yul.Stmt.for_ pre test step work)
   ⟨initial.profile,condition.profile,post.profile,body.profile⟩ (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := (newer.toList++out.toList).map coreWord++caller} := by
 change (initial.lowered.code depth).bind (fun initCode =>
   (SourceLoop.emit (c := c) condition post body depth).bind (fun loop =>
     some (Backend.Block.seq (.code initCode) loop))) = some block at emitted
 obtain ⟨initCode,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
 obtain ⟨loop,hl,eq⟩ := Option.bind_eq_some_iff.mp rest
 cases Option.some.inj eq
 obtain ⟨qp,sp,rest⟩ := Option.bind_eq_some_iff.mp selected
 obtain ⟨ql,sl,eq⟩ := Option.map_eq_some_iff.mp rest
 subst code
 have prefixRun := WordExecution.loweredStmt_machine initial.lowered depth initCode qp hp sp locals newer m caller
 rw [Evm.run_append_ok prefixRun] at ran
 obtain ⟨fuel,out,source,zero,frame⟩ := SourceLoopModelCompletion.model_to_source condition post body
   depth loop ql hl sl (initial.update locals) newer m final caller skip ran
 obtain ⟨count,running,stopped,same⟩ := SourceLoopCompletion.for_completed condition post body
   fuel (initial.update locals) ⟨sourceLocals out,.normal⟩ source
 have values := congrArg Outcome.vars same
 have equal : out = Nat.repeat (next body post) count (initial.update locals) :=
   SourceLoopCompletion.sourceLocals_injective values
 subst out
 exact ⟨max fi (max fc (max fp fb)+count+1)+1,_,
   SourceLoopInitializer.finite initial condition post body count locals running stopped,zero,frame⟩

/-- Exact normal-success equivalence with an existential original-source
horizon. It retains all actual component compiler/emission/selection premises
and an arbitrary newer prefix and caller tail; fixed-fuel failure is distinct. -/
theorem completion_iff (initial : ProducerStatements.Compiled fi pre) (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : SourceLoopInitializer.emit initial condition post body depth = some block)
 (selected : WordControl.blockCode block = some code)
 (locals out : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ fuel, evalStmt fuel .nil True.intro (Solidity.Yul.Stmt.for_ pre test step work)
   ⟨initial.profile,condition.profile,post.profile,body.profile⟩ (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
   .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_of_transport (Solidity.Yul.Stmt.for_ pre test step work)
   ⟨initial.profile, condition.profile, post.profile, body.profile⟩ code
   (SourceLoopInitializer.source_to_model initial condition post body depth block code emitted selected)
   (model_to_source initial condition post body depth block code emitted selected) locals out newer m caller

/-- info: 'Solidity.Yul.Compilation.InitializedLoopCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.InitializedLoopCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.InitializedLoopCompletion

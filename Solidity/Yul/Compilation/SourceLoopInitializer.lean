import Solidity.Yul.Compilation.SourceLoopModelCompletion
/-! Original normal initializer followed by the existing concrete loop emitter.
Success transport only: no Source/G24, early-control, native or resource claim. -/
namespace Solidity.Yul.Compilation.SourceLoopInitializer
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions SourceLoop
variable {c : Solidity.Yul.Control} {n fi fc fp fb : Nat}
 {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {test : Solidity.Yul.Expr [] [] n 1}
 {step : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {work : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}

/-- Recover the actual loop-phase run after the original initializer. Its
operand/result exists by the real source run, and uniqueness identifies it
with the existing normal initializer certificate at any completed horizon. -/
theorem phase_of_completed (initial : ProducerStatements.Compiled fi pre) (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (fuel : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt fuel .nil True.intro (Solidity.Yul.Stmt.for_ pre test step work)
   ⟨initial.profile,condition.profile,post.profile,body.profile⟩ (sourceLocals locals) = some result) :
 ∃ phase, evalLoop phase .nil True.intro test condition.profile step post.profile work body.profile
   (sourceLocals (initial.update locals)) = some result := by
 cases fuel with
 | zero => cases ran
 | succ fuel =>
   change Option.bind (evalStmt fuel .nil True.intro pre initial.profile (sourceLocals locals)) _ = some result at ran
   obtain ⟨after,started,remaining⟩ := Option.bind_eq_some_iff.mp ran
   have same : after = ⟨sourceLocals (initial.update locals),.normal⟩ :=
     evalStmt_completed_unique .nil True.intro pre initial.profile (sourceLocals locals)
       started (initial.source locals)
   subst after
   exact ⟨fuel,remaining⟩

/-- Construct a completing original-source horizon for the actual initializer
and finite reached loop. The maximum preserves both component budgets. -/
theorem finite (initial : ProducerStatements.Compiled fi pre) (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (count : Nat) (locals : Vector Scalar.Word n)
 (running : ∀ j, j < count → condition.value (Nat.repeat (next body post) j (initial.update locals)) ≠ 0)
 (stopped : condition.value (Nat.repeat (next body post) count (initial.update locals)) = 0) :
 evalStmt (max fi (max fc (max fp fb)+count+1)+1) .nil True.intro
   (Solidity.Yul.Stmt.for_ pre test step work)
   ⟨initial.profile,condition.profile,post.profile,body.profile⟩ (sourceLocals locals) =
 some ⟨sourceLocals (Nat.repeat (next body post) count (initial.update locals)),.normal⟩ := by
 have started := evalStmt_stable (Nat.le_max_left fi (max fc (max fp fb)+count+1))
   .nil True.intro pre initial.profile (sourceLocals locals) (initial.source locals)
 have completed := SourceLoop.finite condition post body count (initial.update locals) running stopped
 obtain ⟨extra,eq⟩ := Nat.exists_eq_add_of_le (Nat.le_max_right fi (max fc (max fp fb)+count+1))
 have loopDone : evalLoop (c := c) (max fi (max fc (max fp fb)+count+1)) .nil True.intro
   test condition.profile step post.profile work body.profile (sourceLocals (initial.update locals)) =
   some ⟨sourceLocals (Nat.repeat (next body post) count (initial.update locals)),.normal⟩ := by
   rw [eq]
   exact evalLoop_refines_add _ extra .nil True.intro test condition.profile step post.profile
     work body.profile (sourceLocals (initial.update locals)) _ completed
 change Option.bind (evalStmt (max fi (max fc (max fp fb)+count+1)) .nil True.intro
   pre initial.profile (sourceLocals locals)) _ = _
 rw [started]
 exact loopDone

/-- Concrete initCode emission uses the actual producer initializer code and
existing loop block; this is not a new source syntax or calling convention. -/
def emit (initial : ProducerStatements.Compiled fi pre) (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) : Option Backend.Block := do
 let initCode ← initial.lowered.code depth
 let loop ← SourceLoop.emit (c := c) condition post body depth
 pure (.seq (.code initCode) loop)

/-- Actual original for completion, whole emission and whole selection derive
the initializer execution and the finite loop run. No desired intermediate
run, iteration count or reached guards are caller premises. -/
theorem source_to_model
 (initial : ProducerStatements.Compiled fi pre) (condition : Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : emit initial condition post body depth = some block)
 (selected : WordControl.blockCode block = some code)
 (fuel : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt fuel .nil True.intro (Solidity.Yul.Stmt.for_ pre test step work)
   ⟨initial.profile,condition.profile,post.profile,body.profile⟩ (sourceLocals locals) = some result)
 (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
   .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 obtain ⟨phase,completed⟩ := phase_of_completed initial condition post body fuel locals result ran
 obtain ⟨count,running,stopped,same⟩ := SourceLoopCompletion.completed condition post body
   phase (initial.update locals) result completed
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
 have loopRun := (SourceLoop.compiled_finite condition post body depth loop ql hl sl
   count (initial.update locals) newer m caller running stopped).2
 refine ⟨Nat.repeat (next body post) count (initial.update locals),same,?_⟩
 rw [Evm.run_append_ok prefixRun]
 exact loopRun

/-- info: 'Solidity.Yul.Compilation.SourceLoopInitializer.phase_of_completed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms phase_of_completed
/-- info: 'Solidity.Yul.Compilation.SourceLoopInitializer.emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emit
/-- info: 'Solidity.Yul.Compilation.SourceLoopInitializer.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
/-- info: 'Solidity.Yul.Compilation.SourceLoopInitializer.finite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finite
end Solidity.Yul.Compilation.SourceLoopInitializer

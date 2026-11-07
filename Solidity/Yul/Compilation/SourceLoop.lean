import Solidity.Yul.Compilation.WhileWordExecution
import Solidity.Yul.Compilation.ProducerStatements
import Solidity.Yul.ClosedHorizon
/-! Finite original Yul loop-phase completion and matching compiled model loop.
Actual intrinsic condition/body/post compiler certificates supply all component
laws. Reached guards and a stopping guard are real explicit premises, not a
termination oracle or a substitute for full source/G24/native adequacy. -/
namespace Solidity.Yul.Compilation.SourceLoop
open Backend Scalar MachineAdapter Solidity.Yul.Closed
open ProducerExpressions

variable {c : Solidity.Yul.Control} {n fc fp fb : Nat}
 {test : Solidity.Yul.Expr [] [] n 1}
 {step : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {work : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}

/-- Existing component updates composed in the actual Yul body-then-post order. -/
abbrev next (body : ProducerStatements.Compiled fb work) (post : ProducerStatements.Compiled fp step) :
 Vector Scalar.Word n → Vector Scalar.Word n := fun locals => post.update (body.update locals)

private theorem repeat_shift {α : Type} (f : α → α) (count : Nat) (a : α) :
 Nat.repeat f count (f a) = Nat.repeat f (count+1) a := by
 induction count with
 | zero => rfl
 | succ count ih => exact congrArg f ih

/-- The SOURCE horizon is constructed from the component horizons and actual
finite turn count. It is not a proof/fuel-budget increase or an assertion that
the loop terminates on other inputs. All source control indices stay original. -/
theorem finite (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (count : Nat) (locals : Vector Scalar.Word n)
 (running : ∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0)
 (stopped : condition.value (Nat.repeat (next body post) count locals) = 0) :
 evalLoop (c := c) (max fc (max fp fb)+count+1) .nil True.intro
  test condition.profile step post.profile work body.profile (sourceLocals locals) =
 some ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩ := by
 have hc : fc ≤ max fc (max fp fb) := Nat.le_max_left _ _
 have hp : fp ≤ max fc (max fp fb) := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
 have hb : fb ≤ max fc (max fp fb) := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
 induction count generalizing locals with
 | zero =>
   change condition.value locals = 0 at stopped
   have tested := evalExpr_stable hc .nil True.intro test condition.profile (sourceLocals locals) (condition.source locals)
   rewrite [evalLoop,tested]
   change (if (condition.value locals).toNat = 0 then _ else _) = _
   have zero : (condition.value locals).toNat = 0 := congrArg BitVec.toNat stopped
   rewrite [if_pos zero]
   rfl
 | succ count ih =>
   have nonzero : condition.value locals ≠ 0 := running 0 (by omega)
   have runningNext : ∀ j, j < count → condition.value (Nat.repeat (next body post) j (next body post locals)) ≠ 0 := by
     intro j bound
     rewrite [repeat_shift]
     exact running (j+1) (by omega)
   have stoppedNext : condition.value (Nat.repeat (next body post) count (next body post locals)) = 0 := by
     rewrite [repeat_shift]
     exact stopped
   have completed := ih (next body post locals) runningNext stoppedNext
   have tested := evalExpr_stable (show fc ≤ max fc (max fp fb)+count+1 by omega)
     .nil True.intro test condition.profile (sourceLocals locals) (condition.source locals)
   have worked := evalStmt_stable (show fb ≤ max fc (max fp fb)+count+1 by omega)
     .nil True.intro work body.profile (sourceLocals locals) (body.source locals)
   have stepped := evalStmt_stable (show fp ≤ max fc (max fp fb)+count+1 by omega)
     .nil True.intro step post.profile (sourceLocals (body.update locals)) (post.source (body.update locals))
   change evalLoop (c := c) (max fc (max fp fb)+count+1+1) .nil True.intro
    test condition.profile step post.profile work body.profile (sourceLocals locals) = _
   rewrite [evalLoop,tested]
   change (if (condition.value locals).toNat = 0 then _ else _) = _
   have nz : (condition.value locals).toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
   change applyStmtRun (evalStmtNode (max fc (max fp fb)+count+1) work) .nil True.intro
    body.profile (sourceLocals locals) = some ⟨sourceLocals (body.update locals),.normal⟩ at worked
   change applyStmtRun (evalStmtNode (max fc (max fp fb)+count+1) step) .nil True.intro
    post.profile (sourceLocals (body.update locals)) =
      some ⟨sourceLocals (post.update (body.update locals)),.normal⟩ at stepped
   rewrite [if_neg nz,worked]
   change Option.bind (applyStmtRun (evalStmtNode (max fc (max fp fb)+count+1) step)
    .nil True.intro post.profile (sourceLocals (body.update locals))) _ = _
   rewrite [stepped]
   simpa only [Option.bind_some,repeat_shift] using completed

/-- A genuine original for with skip initialization reduces to its existing
loop phase. This changes no source evaluator or control-flow observation. -/
theorem for_skip (fuel : Nat) (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (vars : Values n) :
 evalStmt (fuel+2) .nil True.intro (Solidity.Yul.Stmt.for_ (c := c) .skip test step work)
  ⟨True.intro,condition.profile,post.profile,body.profile⟩ vars =
 evalLoop (c := c) (fuel+1) .nil True.intro test condition.profile step post.profile work body.profile vars := rfl

/-- Exact finite original for completion; no full-language admission follows. -/
theorem for_finite (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (count : Nat) (locals : Vector Scalar.Word n)
 (running : ∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0)
 (stopped : condition.value (Nat.repeat (next body post) count locals) = 0) :
 evalStmt (max fc (max fp fb)+count+2) .nil True.intro
  (Solidity.Yul.Stmt.for_ (c := c) .skip test step work) ⟨True.intro,condition.profile,post.profile,body.profile⟩
  (sourceLocals locals) = some ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩ := by
 rewrite [for_skip _ condition post body]
 exact finite condition post body count locals running stopped

/-- Source and target agree at the same actual finite turn sequence. Actual
emission/selection equations and reached guards remain explicit, while BOTH
source completion and model execution are proved from concrete components. -/
theorem source_model (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (cc bb : Backend.Program) (qc qb : List Evm.Instr)
 (hc : condition.lowered.code depth = some cc)
 (hb : (lowerSeq body.lowered post.lowered).code depth = some bb)
 (sc : WordMachine.selectCode cc = some qc) (sb : WordMachine.selectCode bb = some qb)
 (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word)
 (running : ∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0)
 (stopped : condition.value (Nat.repeat (next body post) count locals) = 0) :
 (evalStmt (max fc (max fp fb)+count+2) .nil True.intro
  (Solidity.Yul.Stmt.for_ (c := c) .skip test step work) ⟨True.intro,condition.profile,post.profile,body.profile⟩
  (sourceLocals locals) = some ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩) ∧
 Evm.run [.loop qc qb] {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++(Nat.repeat (next body post) count locals).toList).map coreWord++caller} 0 := by
 constructor
 · exact for_finite condition post body count locals running stopped
 · have completed := WhileWordExecution.finite condition.lowered (lowerSeq body.lowered post.lowered)
    cc bb qc qb hc hb sc sb count locals newer m caller running stopped
   change (Evm.loopRun (Evm.run qc) (Evm.run qb)
    {m with stack := (newer.toList++locals.toList).map coreWord++caller}).bind
    (fun next pending => Evm.exec [] pending next) = _
   rewrite [Evm.loopRun_of_iterN completed]
   rfl

/-- info: 'Solidity.Yul.Compilation.SourceLoop.finite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finite
/-- info: 'Solidity.Yul.Compilation.SourceLoop.for_skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms for_skip
/-- info: 'Solidity.Yul.Compilation.SourceLoop.for_finite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms for_finite
/-- info: 'Solidity.Yul.Compilation.SourceLoop.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_model

/-- Concrete lowering of this original normal for form reuses the existing
while emitter; source body and post compile in their actual intrinsic controls. -/
def emit (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) : Option Backend.Block :=
 lowerWhile condition.lowered (lowerSeq body.lowered post.lowered) depth

/-- Whole emitted/selected artifacts derive the component code equations.
Callers provide actual compiler results and reached guards, not desired source
or target execution. This is finite normal-for correspondence, not admission. -/
theorem compiled_finite (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : emit condition post body depth = some block)
 (selected : WordControl.blockCode block = some code)
 (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word)
 (running : ∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0)
 (stopped : condition.value (Nat.repeat (next body post) count locals) = 0) :
 (evalStmt (max fc (max fp fb)+count+2) .nil True.intro
  (Solidity.Yul.Stmt.for_ (c := c) .skip test step work) ⟨True.intro,condition.profile,post.profile,body.profile⟩
  (sourceLocals locals) = some ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩) ∧
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++(Nat.repeat (next body post) count locals).toList).map coreWord++caller} 0 := by
 change (condition.lowered.code depth).bind (fun cc =>
  (lowerSeq body.lowered post.lowered).code depth |>.map (fun bb => Backend.Block.loop cc (.code bb))) = some block at emitted
 obtain ⟨cc,hc,rest⟩ := Option.bind_eq_some_iff.mp emitted
 obtain ⟨bb,hb,same⟩ := Option.map_eq_some_iff.mp rest
 subst block
 obtain ⟨qc,sc,rest⟩ := Option.bind_eq_some_iff.mp selected
 obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
 subst code
 exact source_model condition post body depth cc bb qc qb hc hb sc sb count locals newer m caller running stopped

/-- info: 'Solidity.Yul.Compilation.SourceLoop.emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emit
/-- info: 'Solidity.Yul.Compilation.SourceLoop.compiled_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compiled_finite
end Solidity.Yul.Compilation.SourceLoop

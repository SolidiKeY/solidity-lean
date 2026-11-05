import Solidity.Yul.Compilation.ForCompilation
import Solidity.Yul.Compilation.FramedBranch
/-! Actual source conditional around a concrete loop artifact. The untaken loop
needs no successful execution premise. Source/G24/native adequacy stays open. -/
namespace Solidity.Yul.Compilation.GuardedFor
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fc componentFuel depth : Nat}
 {test : Expr [] [] n 1} {body : Stmt [] [] c n}
/-- Exact conditional driver, even if the selected loop fails. This reuses
existing relative-skip transport and derives the actual condition execution. -/
theorem machine (condition : Compiled fc test) (loop : ForCompilation.Artifact componentFuel body depth)
 (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code depth = some p)
 (selected : WordMachine.selectCode p = some q)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run (MachineControl.branchCode q loop.code [])
   {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 if condition.value locals = 0 then
   .ok {m with stack := (newer.toList++locals.toList).map coreWord++caller} 0
 else Evm.run loop.code {m with stack := (newer.toList++locals.toList).map coreWord++caller} := by
 rw [MachineControl.branchCode,Evm.run_append_ok
   (WordExecution.loweredExpr_machine condition.lowered depth p q emitted selected locals newer m caller)]
 by_cases zero : condition.value locals = 0
 · rw [if_pos zero,zero]
   change Evm.exec loop.code loop.code.length
     {m with stack := (newer.toList++locals.toList).map coreWord++caller} = _
   exact Evm.exec_length loop.code _
 · rw [if_neg zero]
   exact FramedBranch.nonzero_tail (condition.value locals) loop.code []
     {m with stack := (newer.toList++locals.toList).map coreWord++caller} zero

/-- Real guard code generation and selection around the artifact's actual
selected body. No new source/target AST or control convention. -/
def lower (condition : Compiled fc test) (loop : ForCompilation.Artifact componentFuel body depth) :
 Option (List Evm.Instr) := do
 let p ← condition.lowered.code depth
 let q ← WordMachine.selectCode p
 pure (MachineControl.branchCode q loop.code [])

/-- The existing artifact's actual source completion forces a normal output
and real model run. This is a concrete compiler-proof projection, not a new
assumed source/target producer law. -/
theorem body_completed (loop : ForCompilation.Artifact componentFuel body depth)
 (fuel : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt fuel .nil True.intro body loop.compiled.profile (sourceLocals locals) = some result)
 (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run loop.code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 rcases loop with ⟨compiled,block,code,emitted,selected⟩
 cases compiled with
 | loop initializer condition step work =>
   exact SourceLoopInitializer.source_to_model initializer condition step work depth block code
     emitted selected fuel locals result ran newer m caller

/-- A taken source guard composes existing guard and body certificates.
The source horizon bound and actual selected-body run are real premises;
this lemma avoids evaluating a concrete loop during kernel conversion. -/
theorem source_nonzero (condition : Compiled fc test) (loop : ForCompilation.Artifact componentFuel body depth)
 (fuel : Nat) (bound : fc ≤ fuel) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (nonzero : condition.value locals ≠ 0)
 (bodyRun : evalStmt fuel .nil True.intro body loop.compiled.profile (sourceLocals locals) = some result) :
 evalStmt (fuel+1) .nil True.intro (.if_ test body) ⟨condition.profile,loop.compiled.profile⟩
   (sourceLocals locals) = some result := by
 have tested := evalExpr_stable bound .nil True.intro test condition.profile
   (sourceLocals locals) (condition.source locals)
 change Option.bind (evalExpr fuel .nil True.intro test condition.profile (sourceLocals locals)) _ = _
 rw [tested]
 have nz : (condition.value locals).toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 change (if (condition.value locals).toNat = 0 then _ else _) = _
 rw [if_neg nz]
 exact bodyRun

/-- Completed ACTUAL source if transports through ACTUAL guard lowering and
loop artifact. Guard values and taken-body execution are derived, not assumed;
the inactive body needs no successful run or source completion. -/
theorem source_to_model (condition : Compiled fc test)
 (loop : ForCompilation.Artifact componentFuel body depth) (code : List Evm.Instr)
 (lowered : lower condition loop = some code)
 (fuel : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt fuel .nil True.intro (.if_ test body) ⟨condition.profile,loop.compiled.profile⟩
   (sourceLocals locals) = some result)
 (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp lowered
 obtain ⟨q,hq,same⟩ := Option.bind_eq_some_iff.mp rest
 cases Option.some.inj same
 have target := machine condition loop p q hp hq locals newer m caller
 cases fuel with
 | zero => cases ran
 | succ fuel =>
   change Option.bind (evalExpr fuel .nil True.intro test condition.profile (sourceLocals locals)) _ = some result at ran
   obtain ⟨values,tested,remaining⟩ := Option.bind_eq_some_iff.mp ran
   have same := evalExpr_completed_unique .nil True.intro test condition.profile (sourceLocals locals)
     tested (condition.source locals)
   subst values
   change (if (condition.value locals).toNat = 0 then
     some (⟨sourceLocals locals,.normal⟩ : Outcome c n)
     else evalStmt fuel .nil True.intro body loop.compiled.profile (sourceLocals locals)) = some result at remaining
   by_cases zero : condition.value locals = 0
   · have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
     rw [if_pos zn] at remaining
     exact ⟨locals,(Option.some.inj remaining).symm,by simpa only [if_pos zero] using target⟩
   · have nz : (condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
     rw [if_neg nz] at remaining
     obtain ⟨out,same,bodyRun⟩ := body_completed loop fuel locals result remaining newer m caller
     refine ⟨out,same,?_⟩
     rw [if_neg zero,bodyRun] at target
     exact target

/-- info: 'Solidity.Yul.Compilation.GuardedFor.machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine
/-- info: 'Solidity.Yul.Compilation.GuardedFor.lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lower
/-- info: 'Solidity.Yul.Compilation.GuardedFor.body_completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms body_completed
/-- info: 'Solidity.Yul.Compilation.GuardedFor.source_nonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_nonzero
/-- info: 'Solidity.Yul.Compilation.GuardedFor.source_to_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
end Solidity.Yul.Compilation.GuardedFor

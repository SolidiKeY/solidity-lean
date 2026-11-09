import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.GuardedFor
/-! Reverse normal-success transport for the actual source conditional around
an existing loop artifact; no inactive-body completion premise. -/
namespace Solidity.Yul.Compilation.GuardedForCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fc componentFuel depth : Nat}
 {test : Expr [] [] n 1} {body : Stmt [] [] c n}
/-- Actual whole target success yields a real original source horizon, exact
normal words and full frame. False guards never require body completion. -/
theorem model_to_source (condition : Compiled fc test) (loop : ForCompilation.Artifact componentFuel body depth)
 (code : List Evm.Instr) (lowered : GuardedFor.lower condition loop = some code)
 (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .ok final skip) :
 ∃ (fuel : Nat) (out : Vector Scalar.Word n),
 evalStmt fuel .nil True.intro (.if_ test body) ⟨condition.profile,loop.compiled.profile⟩
   (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := (newer.toList++out.toList).map coreWord++caller} := by
 obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp lowered
 obtain ⟨q,hq,same⟩ := Option.bind_eq_some_iff.mp rest
 cases Option.some.inj same
 have target := GuardedFor.machine condition loop p q hp hq locals newer m caller
 by_cases zero : condition.value locals = 0
 · rw [if_pos zero] at target
   have parts := Evm.Out.ok.inj (target.symm.trans ran)
   refine ⟨fc+1,locals,?_,parts.2.symm,parts.1.symm⟩
   change Option.bind (evalExpr fc .nil True.intro test condition.profile (sourceLocals locals)) _ = _
   rw [condition.source]
   have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
   change (if (condition.value locals).toNat = 0 then _ else _) = _
   rw [if_pos zn]
   rfl
 · rw [if_neg zero] at target
   have bodyRun := target.symm.trans ran
   obtain ⟨fuel,out,source,done,frame⟩ := loop.reflected locals newer m final caller skip bodyRun
   have stable : evalStmt (max fc fuel) .nil True.intro body loop.compiled.profile (sourceLocals locals) =
     some ⟨sourceLocals out,.normal⟩ := CompletionControls.completed_horizon
     (fun horizon => evalStmt horizon .nil True.intro body loop.compiled.profile (sourceLocals locals))
     (fun horizon extra => evalStmt_refines_add horizon extra .nil True.intro body loop.compiled.profile (sourceLocals locals))
     (Nat.le_max_right fc fuel) source
   exact ⟨max fc fuel+1,out,GuardedFor.source_nonzero condition loop (max fc fuel)
     (Nat.le_max_left fc fuel) locals _ zero stable,done,frame⟩

/-- Exact normal-success equivalence for the original if and actually lowered
conditional. Source horizon is existential; source exhaustion is not a target
fault or a native divergence theorem. All concrete compiler premises remain. -/
theorem completion_iff (condition : Compiled fc test) (loop : ForCompilation.Artifact componentFuel body depth)
 (code : List Evm.Instr) (lowered : GuardedFor.lower condition loop = some code)
 (locals out : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ fuel, evalStmt fuel .nil True.intro (.if_ test body) ⟨condition.profile,loop.compiled.profile⟩
   (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
   .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_of_transport (.if_ test body)
   ⟨condition.profile, loop.compiled.profile⟩ code
   (GuardedFor.source_to_model condition loop code lowered)
   (model_to_source condition loop code lowered) locals out newer m caller

/-- info: 'Solidity.Yul.Compilation.GuardedForCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.GuardedForCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.GuardedForCompletion

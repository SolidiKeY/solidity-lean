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
   have stable := evalStmt_stable (Nat.le_max_right fc fuel) .nil True.intro body
     loop.compiled.profile (sourceLocals locals) source
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
 constructor
 · rintro ⟨fuel,source⟩
   obtain ⟨actual,same,target⟩ := GuardedFor.source_to_model condition loop code lowered
     fuel locals ⟨sourceLocals out,.normal⟩ source newer m caller
   have equal : out = actual := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
   cases equal
   exact target
 · intro ran
   obtain ⟨fuel,actual,source,_,frame⟩ := model_to_source condition loop code lowered
     locals newer m {m with stack := (newer.toList++out.toList).map coreWord++caller} caller 0 ran
   have stacks := congrArg Evm.Machine.stack frame
   have mapped : (newer.toList++out.toList).map coreWord =
     (newer.toList++actual.toList).map coreWord := List.append_cancel_right stacks
   have lists : newer.toList++out.toList = newer.toList++actual.toList :=
     (List.map_inj_right (fun _ _ h => coreWord_injective h)).mp mapped
   have equal : out = actual := Vector.toList_inj.mp (List.append_cancel_left lists)
   cases equal
   exact ⟨fuel,source⟩

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

import SolidityBridge.Yul.ForCompletionSource
import SolidityBridge.Yul.StructuredFor
import SolidityBridge.Yul.StructuredSource

/-! Recover finite loop counts from actual original source completion, then
transport through the existing compiler. No native/G24/capacity adequacy. -/
namespace SolidityBridge.Yul.ForCompletion
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
section
variable {c : Solidity.Yul.Control} {n cf pf bf : Nat}
  {condition : Solidity.Yul.Expr [] [] n 1}
  {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
  (test : ProducerExpressions.Compiled cf condition)
  (after : NormalControl.Derivation pf post)
  (inside : NormalControl.Derivation bf body)


theorem loop_complete (fuel : Nat) (locals : Vector Scalar.Word n) (out : Outcome c n)
    (completed : evalLoop fuel .nil True.intro condition test.profile post after.profile
      body inside.profile (sourceLocals locals) = some out) :
    ∃ count, count < fuel ∧
      (∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l)) j locals) ≠ 0) ∧
      test.value (Nat.repeat (fun l => after.update (inside.update l)) count locals) = 0 ∧
      out = ⟨sourceLocals (Nat.repeat (fun l => after.update (inside.update l)) count locals),.normal⟩ :=
  ForCompletionSource.loop_complete test after.profile after.update after.source
    inside.profile inside.update inside.source fuel locals out completed

variable {af : Nat} {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  (before : NormalControl.Derivation af pre)

/-- The iteration witness is extracted from the actual successful source run;
no count or guard sequence is supplied by the caller. -/
theorem source_complete (fuel : Nat) (locals : Vector Scalar.Word n) (out : Outcome c n)
    (completed : evalStmt fuel .nil True.intro (.for_ (c := c) pre condition post body)
      (StructuredFor.profile test after inside before) (sourceLocals locals) = some out) :
    ∃ count, count+1 < fuel ∧
      (∀ j, j < count → test.value (Nat.repeat (fun l => after.update (inside.update l))
        j (before.update locals)) ≠ 0) ∧
      test.value (Nat.repeat (fun l => after.update (inside.update l)) count (before.update locals)) = 0 ∧
      out = ⟨sourceLocals (Nat.repeat (fun l => after.update (inside.update l))
        count (before.update locals)),.normal⟩ := by
  cases fuel with
  | zero => cases completed
  | succ fuel =>
    change (evalStmt fuel .nil True.intro pre before.profile (sourceLocals locals)).bind _ = some out at completed
    cases preRun : evalStmt fuel .nil True.intro pre before.profile (sourceLocals locals) with
    | none => simp only [preRun] at completed; cases completed
    | some result =>
      rw [preRun] at completed
      have same := evalStmt_completed_unique .nil True.intro pre before.profile
        (sourceLocals locals) preRun (before.source locals)
      subst result
      change evalLoop fuel .nil True.intro condition test.profile post after.profile
        body inside.profile (sourceLocals (before.update locals)) = some out at completed
      obtain ⟨count,bound,running,stopped,result⟩ :=
        loop_complete test after inside fuel (before.update locals) out completed
      exact ⟨count,by omega,running,stopped,result⟩

/-- Concrete forward transport from source completion through the actual
emissions and selected model. No stopping count or desired target run premise. -/
theorem transport (fuel : Nat) (locals : Vector Scalar.Word n) (out : Outcome c n)
    (completed : evalStmt fuel .nil True.intro (.for_ (c := c) pre condition post body)
      (StructuredFor.profile test after inside before) (sourceLocals locals) = some out)
    (depth : Nat) (block : Backend.Block)
    (emitted : StructuredFor.emit test after inside before depth = some block)
    (selected : OccurrenceControl.Selected block)
    (newer : Vector Scalar.Word depth) (tail : Stack)
    (m : Evm.Machine) (represented : m.stack = irStack (newer.toList ++ (locals.toList ++ tail))) :
    ∃ count, count+1 < fuel ∧
      out = ⟨sourceLocals (Nat.repeat (fun l => after.update (inside.update l))
        count (before.update locals)),.normal⟩ ∧
      StructuredExec block (newer.toList ++ (locals.toList ++ tail))
        (newer.toList ++ ((Nat.repeat (fun l => after.update (inside.update l))
          count (before.update locals)).toList ++ tail)) ∧
      Evm.run selected.realization.ir m =
        .ok {m with stack := irStack (newer.toList ++
          ((Nat.repeat (fun l => after.update (inside.update l))
            count (before.update locals)).toList ++ tail))} 0 := by
  obtain ⟨count,bound,running,stopped,result⟩ := source_complete test after inside before fuel locals out completed
  exact ⟨count,bound,result,
    StructuredFor.structured test after inside before depth block emitted count locals newer tail running stopped,
    StructuredFor.model test after inside before depth block emitted selected count locals newer tail
      running stopped m represented⟩

/-- Match the caller's actual successful source output exactly, including all
raw high bits; no target result is assumed. -/
theorem transport_output (fuel : Nat) (locals final : Vector Scalar.Word n)
    (completed : evalStmt fuel .nil True.intro (.for_ (c := c) pre condition post body)
      (StructuredFor.profile test after inside before) (sourceLocals locals) =
      some ⟨sourceLocals final,.normal⟩)
    (depth : Nat) (block : Backend.Block)
    (emitted : StructuredFor.emit test after inside before depth = some block)
    (selected : OccurrenceControl.Selected block)
    (newer : Vector Scalar.Word depth) (tail : Stack)
    (m : Evm.Machine) (represented : m.stack = irStack (newer.toList ++ (locals.toList ++ tail))) :
    StructuredExec block (newer.toList ++ (locals.toList ++ tail))
      (newer.toList ++ (final.toList ++ tail)) ∧
    Evm.run selected.realization.ir m =
      .ok {m with stack := irStack (newer.toList ++ (final.toList ++ tail))} 0 := by
  obtain ⟨count,_bound,result,structured,ran⟩ := transport test after inside before fuel locals
    ⟨sourceLocals final,.normal⟩ completed depth block emitted selected newer tail m represented
  have same : final = Nat.repeat (fun l => after.update (inside.update l)) count (before.update locals) := by
    apply Vector.ext
    intro i bound
    exact BitVec.eq_of_toFin_eq (congrFun (congrArg Outcome.vars result) ⟨i,bound⟩)
  rw [←same] at structured ran
  exact ⟨structured,ran⟩

end
/-- info: 'SolidityBridge.Yul.ForCompletion.loop_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms loop_complete
/-- info: 'SolidityBridge.Yul.ForCompletion.source_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_complete
/-- info: 'SolidityBridge.Yul.ForCompletion.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transport
/-- info: 'SolidityBridge.Yul.ForCompletion.transport_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transport_output
end SolidityBridge.Yul.ForCompletion

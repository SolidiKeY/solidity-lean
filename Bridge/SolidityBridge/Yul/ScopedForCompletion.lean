import SolidityBridge.Yul.ForCompletionSource
import SolidityBridge.Yul.ScopedFor

/-! Source-success-driven concrete scope/switch FOR transport. Every shared
normal-source premise is discharged by the actual component compiler. No
stopping count/guard oracle, native/G24/capacity or frontend adequacy. -/
namespace SolidityBridge.Yul.ScopedForCompletion
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions
section
variable {c : Solidity.Yul.Control} {n compilerFuel : Nat}
  {pre : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {condition : Solidity.Yul.Expr [] [] n 1}
  {post : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
  {body : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}
  (compiled : ScopedFor.Prepared compilerFuel (c := c) pre condition post body)

theorem loop_complete (horizon : Nat) (locals : Vector Scalar.Word n) (out : Outcome c n)
    (completed : evalLoop horizon .nil True.intro condition compiled.test.profile post compiled.after.profile
      body compiled.inside.profile (sourceLocals locals) = some out) :
    ∃ count, count < horizon ∧
      (∀ j, j < count → compiled.test.value (Nat.repeat (ScopedFor.update compiled) j locals) ≠ 0) ∧
      compiled.test.value (Nat.repeat (ScopedFor.update compiled) count locals) = 0 ∧
      out = ⟨sourceLocals (Nat.repeat (ScopedFor.update compiled) count locals),.normal⟩ :=
  ForCompletionSource.loop_complete compiled.test compiled.after.profile compiled.after.update compiled.after.source
    compiled.inside.profile compiled.inside.update compiled.inside.source horizon locals out completed

theorem source_complete (horizon : Nat) (locals : Vector Scalar.Word n) (out : Outcome c n)
    (completed : evalStmt horizon .nil True.intro (.for_ (c := c) pre condition post body)
      (ScopedFor.profile compiled) (sourceLocals locals) = some out) :
    ∃ count, count+1 < horizon ∧
      (∀ j, j < count → compiled.test.value
        (Nat.repeat (ScopedFor.update compiled) j (compiled.before.update locals)) ≠ 0) ∧
      compiled.test.value (Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)) = 0 ∧
      out = ⟨sourceLocals (Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)),.normal⟩ := by
  cases horizon with
  | zero => cases completed
  | succ horizon =>
    change (evalStmt horizon .nil True.intro pre compiled.before.profile (sourceLocals locals)).bind _ = some out at completed
    cases preRun : evalStmt horizon .nil True.intro pre compiled.before.profile (sourceLocals locals) with
    | none => simp only [preRun] at completed; cases completed
    | some result =>
      rw [preRun] at completed
      have same := evalStmt_completed_unique .nil True.intro pre compiled.before.profile
        (sourceLocals locals) preRun (compiled.before.source locals)
      subst result
      change evalLoop horizon .nil True.intro condition compiled.test.profile post compiled.after.profile
        body compiled.inside.profile (sourceLocals (compiled.before.update locals)) = some out at completed
      obtain ⟨count,bound,running,stopped,result⟩ := loop_complete compiled horizon
        (compiled.before.update locals) out completed
      exact ⟨count,by omega,running,stopped,result⟩

/-- Actual source success supplies count and guards internally; the selected
packet supplies concrete emission and opcode correspondence, not an assumed run. -/
theorem transport (packet : ScopedFor.Packet compiled) (horizon : Nat)
    (locals : Vector Scalar.Word n) (out : Outcome c n)
    (completed : evalStmt horizon .nil True.intro (.for_ (c := c) pre condition post body)
      (ScopedFor.profile compiled) (sourceLocals locals) = some out)
    (caller : Stack) (m : Evm.Machine) (represented : m.stack = irStack (locals.toList ++ caller)) :
    ∃ count, count+1 < horizon ∧
      out = ⟨sourceLocals (Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)),.normal⟩ ∧
      StructuredExec packet.block (locals.toList ++ caller)
        ((Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals)).toList ++ caller) ∧
      Evm.run packet.selected.realization.ir m =
        .ok {m with stack := irStack ((Nat.repeat (ScopedFor.update compiled) count
          (compiled.before.update locals)).toList ++ caller)} 0 := by
  obtain ⟨count,bound,running,stopped,result⟩ := source_complete compiled horizon locals out completed
  exact ⟨count,bound,result,
    ScopedFor.structured compiled packet.block packet.emitted count locals caller running stopped,
    ScopedFor.Packet.model compiled packet count locals caller running stopped m represented⟩

/-- Exact successful source output, preserving all raw bits and caller/frame.
No lower bound on source horizon and no caller-supplied iteration count. -/
theorem transport_output (packet : ScopedFor.Packet compiled) (horizon : Nat)
    (locals final : Vector Scalar.Word n)
    (completed : evalStmt horizon .nil True.intro (.for_ (c := c) pre condition post body)
      (ScopedFor.profile compiled) (sourceLocals locals) = some ⟨sourceLocals final,.normal⟩)
    (caller : Stack) (m : Evm.Machine) (represented : m.stack = irStack (locals.toList ++ caller)) :
    StructuredExec packet.block (locals.toList ++ caller) (final.toList ++ caller) ∧
    Evm.run packet.selected.realization.ir m =
      .ok {m with stack := irStack (final.toList ++ caller)} 0 := by
  obtain ⟨count,_bound,result,structured,ran⟩ := transport compiled packet horizon locals
    ⟨sourceLocals final,.normal⟩ completed caller m represented
  have same : final = Nat.repeat (ScopedFor.update compiled) count (compiled.before.update locals) := by
    apply Vector.ext
    intro i bound
    exact BitVec.eq_of_toFin_eq (congrFun (congrArg Outcome.vars result) ⟨i,bound⟩)
  rw [←same] at structured ran
  exact ⟨structured,ran⟩
end
/-- info: 'SolidityBridge.Yul.ScopedForCompletion.loop_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms loop_complete
/-- info: 'SolidityBridge.Yul.ScopedForCompletion.source_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_complete
/-- info: 'SolidityBridge.Yul.ScopedForCompletion.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transport
/-- info: 'SolidityBridge.Yul.ScopedForCompletion.transport_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transport_output
end SolidityBridge.Yul.ScopedForCompletion

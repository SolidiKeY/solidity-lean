import SolidityBridge.Yul.ScopedForCompletion
import SolidityBridge.Yul.ScopedForControls

/-! Actual combined compiler witnesses drive source-success transport with no
caller stopping count/guards. Source horizon and compiler fuel stay distinct.
These are kernel/model controls, not native/G24/admission adequacy. -/
namespace SolidityBridge.Yul.ScopedForCompletion.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions
open ScopedFor.Controls

/-- Uniform at every source horizon and every claimed complete source output;
no new source horizon budget or inferred success is supplied. -/
theorem from_any_source (horizon : Nat) (initial : Scalar.Word) (final : Vector Scalar.Word 2)
    (completed : evalStmt horizon .nil True.intro statement (ScopedFor.profile prepared)
      (sourceLocals #v[initial,dirty]) = some ⟨sourceLocals final,.normal⟩)
    (caller : Stack) (m : Evm.Machine) (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    StructuredExec packet.block ([initial,dirty] ++ caller) (final.toList ++ caller) ∧
    Evm.run packet.selected.realization.ir m = .ok {m with stack := irStack (final.toList ++ caller)} 0 :=
  transport_output prepared packet horizon #v[initial,dirty] final completed caller m represented

/-- Genuine inhabited source witness at unchanged horizon10. The iteration
count is not an argument of this compiler correctness application. -/
theorem from_ten (initial : Scalar.Word) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    StructuredExec packet.block ([initial,dirty] ++ caller) ([0,dirty+11] ++ caller) ∧
    Evm.run packet.selected.realization.ir m = .ok {m with stack := irStack ([0,dirty+11] ++ caller)} 0 :=
  from_any_source 10 initial #v[0,dirty+11] (source_ten initial) caller m represented

/-- No successful early-flow outcome can be smuggled by changing source fuel. -/
theorem every_completed_normal (horizon : Nat) (initial : Scalar.Word)
    (out : Outcome ⟨false,false⟩ 2)
    (completed : evalStmt horizon .nil True.intro statement (ScopedFor.profile prepared)
      (sourceLocals #v[initial,dirty]) = some out) : out.flow.isNormal = true := by
  obtain ⟨count,bound,running,stopped,same⟩ := source_complete prepared horizon #v[initial,dirty] out completed
  rw [same]
  rfl

theorem short_refused (horizon : Nat) (small : horizon ≤ 1) (initial : Scalar.Word)
    (out : Outcome ⟨false,false⟩ 2) :
    evalStmt horizon .nil True.intro statement (ScopedFor.profile prepared)
      (sourceLocals #v[initial,dirty]) ≠ some out := by
  intro completed
  obtain ⟨count,bound,_⟩ := source_complete prepared horizon #v[initial,dirty] out completed
  omega

/-- The wrong body/post order cannot be rescued by a different source horizon.
Use actual completed-run uniqueness with the genuine source10 witness. -/
theorem wrong_order_refused (horizon : Nat) (initial : Scalar.Word) :
    evalStmt horizon .nil True.intro statement (ScopedFor.profile prepared)
      (sourceLocals #v[initial,dirty]) ≠ some ⟨sourceLocals #v[0,dirty+2],.normal⟩ := by
  intro completed
  have same := evalStmt_completed_unique .nil True.intro statement (ScopedFor.profile prepared)
    (sourceLocals #v[initial,dirty]) completed (source_ten initial)
  have value := congrArg (fun out : Outcome ⟨false,false⟩ 2 => out.vars (1 : Fin 2)) same
  change (dirty+2).toFin = (dirty+11).toFin at value
  exact (by decide : (dirty+2).toFin ≠ (dirty+11).toFin) value

#check from_ten 99 [88,dirty]
#check from_ten 0 []
#check short_refused 1 (by decide)
#check wrong_order_refused 0
#guard observe (Evm.run packet.selected.realization.ir (machine [99,dirty,88])) ==
  some ([some 0,some (dirty+11).toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
/-- info: 'SolidityBridge.Yul.ScopedForCompletion.Controls.from_any_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms from_any_source
/-- info: 'SolidityBridge.Yul.ScopedForCompletion.Controls.from_ten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms from_ten
/-- info: 'SolidityBridge.Yul.ScopedForCompletion.Controls.every_completed_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms every_completed_normal
/-- info: 'SolidityBridge.Yul.ScopedForCompletion.Controls.short_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms short_refused
/-- info: 'SolidityBridge.Yul.ScopedForCompletion.Controls.wrong_order_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_order_refused
end SolidityBridge.Yul.ScopedForCompletion.Controls

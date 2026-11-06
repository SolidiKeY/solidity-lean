import SolidityBridge.Yul.ScopedForAdequacy
import SolidityBridge.Yul.ScopedForCompletionControls

/-! Inhabited exact-output and genuinely unending scoped FOR controls.
The unending model is never evaluated by a runtime command. -/
namespace SolidityBridge.Yul.ScopedForAdequacy.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions
open ScopedFor.Controls

theorem exact_output (initial : Scalar.Word) (final : Vector Scalar.Word 2)
    (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    (∃ horizon, evalStmt horizon .nil True.intro statement (ScopedFor.profile prepared)
      (sourceLocals #v[initial,dirty]) = some ⟨sourceLocals final,.normal⟩) ↔
    Evm.run packet.selected.realization.ir m = .ok {m with stack := irStack (final.toList ++ caller)} 0 :=
  output_iff prepared packet 6 (by decide) #v[initial,dirty] final caller m represented

/-- The literal condition is the real original AST and compiler leaf; body,
post and prelude retain their real lexical-temporary/switch compilers. -/
def foreverCondition : Solidity.Yul.Expr [] [] 2 1 := .literal (Solidity.Yul.word 1)
def foreverStatement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .for_ pre foreverCondition post body
def foreverPrepared : ScopedFor.Prepared 6 (c := ⟨false,false⟩) pre foreverCondition post body :=
  ⟨prepared.before,ProducerExpressions.literal 5 (Solidity.Yul.word 1),prepared.after,prepared.inside⟩
def foreverTarget := (ScopedFor.emit foreverPrepared).get (by rfl)
def foreverSelected := (LoopSelection.selectBlock foreverTarget).get (by rfl)
def foreverPacket : ScopedFor.Packet foreverPrepared :=
  ⟨foreverTarget,(Option.some_get (by rfl)).symm,foreverSelected⟩

theorem actual_preparation : ScopedFor.prepare 6 (c := ⟨false,false⟩) pre foreverCondition post body =
    some foreverPrepared := by rfl

/-- A successful source outcome would require the literal one to equal zero.
This proves absence at every horizon, not just an exhausted small horizon. -/
theorem source_never (initial : Scalar.Word) (horizon : Nat) :
    evalStmt horizon .nil True.intro foreverStatement (ScopedFor.profile foreverPrepared)
      (sourceLocals #v[initial,dirty]) = none := by
  cases completed : evalStmt horizon .nil True.intro foreverStatement (ScopedFor.profile foreverPrepared)
      (sourceLocals #v[initial,dirty]) with
  | none => rfl
  | some out =>
    obtain ⟨count,bound,running,stopped,result⟩ := ScopedForCompletion.source_complete foreverPrepared horizon
      #v[initial,dirty] out completed
    change (1 : Scalar.Word) = 0 at stopped
    exact False.elim ((by decide : (1 : Scalar.Word) ≠ 0) stopped)

/-- Selected numeric model fault here is its denotation of no finite outcome.
No source Panic/revert or native exceptional-halt claim follows. -/
theorem model_no_finite_outcome (initial : Scalar.Word) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    Evm.run foreverPacket.selected.realization.ir m = .fault :=
  (no_source_iff_fault foreverPrepared foreverPacket 6 (by decide) #v[initial,dirty] caller m represented).mp
    (source_never initial)

theorem successful_output_refused (initial : Scalar.Word) (caller : Stack) (m actual : Evm.Machine)
    (pending : Nat) (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    Evm.run foreverPacket.selected.realization.ir m ≠ .ok actual pending := by
  rw [model_no_finite_outcome initial caller m represented]
  intro impossible
  cases impossible

/-- Source10 is a genuine success witness for the terminating original loop,
contrasting with the new all-horizon noncompletion control. -/
theorem terminating_not_fault (initial : Scalar.Word) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    Evm.run packet.selected.realization.ir m ≠ .fault := by
  rw [(ScopedForCompletion.Controls.from_ten initial caller m represented).2]
  intro impossible
  cases impossible

#check model_no_finite_outcome 99 [88,dirty]
#check successful_output_refused 0 []
#check source_never 99 0
#check source_never 99 10
#guard observe (Evm.run packet.selected.realization.ir (machine [99,dirty,88])) ==
  some ([some 0,some (dirty+11).toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
/-- info: 'SolidityBridge.Yul.ScopedForAdequacy.Controls.exact_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exact_output
/-- info: 'SolidityBridge.Yul.ScopedForAdequacy.Controls.actual_preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_preparation
/-- info: 'SolidityBridge.Yul.ScopedForAdequacy.Controls.source_never' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_never
/-- info: 'SolidityBridge.Yul.ScopedForAdequacy.Controls.model_no_finite_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_no_finite_outcome
/-- info: 'SolidityBridge.Yul.ScopedForAdequacy.Controls.successful_output_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms successful_output_refused
/-- info: 'SolidityBridge.Yul.ScopedForAdequacy.Controls.terminating_not_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms terminating_not_fault
end SolidityBridge.Yul.ScopedForAdequacy.Controls

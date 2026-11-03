import Solidity.Lowering.V08.SourceTransactionControls
import Solidity.Source.Hoare

/-! Actual bounded Source transaction-prefix consumers. No replacement evaluator,
SourceSpec instance, intrinsic/bytecode simulation or resource admission. -/
namespace Solidity.Roadmap.V16.SourceTransactionConsumer
open Solidity Source
open Source.SemanticsExamples
open Solidity.Lowering.V08.SourceTransactionControls

def revertThenSuccess (bytes : Roadmap.Bytes) : Source.St EB :=
  {success bytes with events := (reverted bytes).events ++
    [.tx user thisC (word 0) (word 12345) (selOf "g()") (.success (wordBytes (toWord 12)))]}

def successThenRevert (bytes : Roadmap.Bytes) : Source.St EB :=
  {success bytes with events := (success bytes).events ++
    [.tx user thisC (word 0) (word 12345) (selOf "poke()") (.revert [])]}


/-- The second actual call runs after a completed reverted transaction.
The existing undo certificate restores the first entry world before it. -/
theorem after_revert_success : ∀ (p : Solidity.Roadmap.Pipeline) (bytes : Solidity.Roadmap.Bytes),
 (Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20
   (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "g()"))).run
   (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Lowering.V08.SourceTransactionControls.reverted bytes) =
 (.ok (.success (Solidity.Source.wordBytes (Solidity.Source.toWord 12))),
   (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Roadmap.V16.SourceTransactionConsumer.revertThenSuccess bytes)) := by
  intro p bytes
  have undo : Solidity.Source.ExecState.undoN 3 ((Solidity.Lowering.V08.SourceTransactionControls.initial bytes).ex.run [Solidity.Lowering.V08.SourceTransactionControls.creditOp,Solidity.Lowering.V08.SourceTransactionControls.xOp Solidity.Lowering.V08.SourceTransactionControls.v1,Solidity.Lowering.V08.SourceTransactionControls.tOp Solidity.Lowering.V08.SourceTransactionControls.v2]) = (Solidity.Lowering.V08.SourceTransactionControls.initial bytes).ex := Solidity.Source.ExecState.undoN_run (Solidity.Lowering.V08.SourceTransactionControls.initial bytes).ex [Solidity.Lowering.V08.SourceTransactionControls.creditOp,Solidity.Lowering.V08.SourceTransactionControls.xOp Solidity.Lowering.V08.SourceTransactionControls.v1,Solidity.Lowering.V08.SourceTransactionControls.tOp Solidity.Lowering.V08.SourceTransactionControls.v2]
  simp only [Solidity.Lowering.V08.SourceTransactionControls.reverted, Solidity.Roadmap.V16.SourceTransactionConsumer.revertThenSuccess, Solidity.Lowering.V08.SourceTransactionControls.success, undo]
  cases p <;> rfl


/-- A later reverting call rolls back to the committed first transaction,
not the original world or a dirty intermediate checkpoint. -/
theorem after_success_revert : ∀ (p : Solidity.Roadmap.Pipeline) (bytes : Solidity.Roadmap.Bytes),
 (Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20
   (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "poke()"))).run
   (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Lowering.V08.SourceTransactionControls.success bytes) =
 (.ok (.revert []),
   (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes)) := by
  intro p bytes
  have undo : Solidity.Source.ExecState.undoN 3 ((Solidity.Lowering.V08.SourceTransactionControls.success bytes).ex.run [Solidity.Lowering.V08.SourceTransactionControls.creditOp,Solidity.Lowering.V08.SourceTransactionControls.xOp Solidity.Lowering.V08.SourceTransactionControls.v1,Solidity.Lowering.V08.SourceTransactionControls.tOp Solidity.Lowering.V08.SourceTransactionControls.v2]) = (Solidity.Lowering.V08.SourceTransactionControls.success bytes).ex := Solidity.Source.ExecState.undoN_run (Solidity.Lowering.V08.SourceTransactionControls.success bytes).ex [Solidity.Lowering.V08.SourceTransactionControls.creditOp,Solidity.Lowering.V08.SourceTransactionControls.xOp Solidity.Lowering.V08.SourceTransactionControls.v1,Solidity.Lowering.V08.SourceTransactionControls.tOp Solidity.Lowering.V08.SourceTransactionControls.v2]
  cases p
  all_goals
    change (Except.ok (ε := Solidity.Source.Halt) (Solidity.Roadmap.Outcome.revert []), (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB, { Solidity.Lowering.V08.SourceTransactionControls.success bytes with ex := (Solidity.Source.ExecState.undoN 3 ((Solidity.Lowering.V08.SourceTransactionControls.success bytes).ex.run [Solidity.Lowering.V08.SourceTransactionControls.creditOp,Solidity.Lowering.V08.SourceTransactionControls.xOp Solidity.Lowering.V08.SourceTransactionControls.v1,Solidity.Lowering.V08.SourceTransactionControls.tOp Solidity.Lowering.V08.SourceTransactionControls.v2])).endTx, heap := Solidity.Source.Heap.empty, events := (Solidity.Lowering.V08.SourceTransactionControls.success bytes).events ++ [Solidity.Roadmap.Event.tx Solidity.Source.SemanticsExamples.user Solidity.Source.SemanticsExamples.thisC (Solidity.Source.SemanticsExamples.word 0) (Solidity.Source.SemanticsExamples.word 12345) (Solidity.Source.SemanticsExamples.selOf "poke()") (.revert [])] })) = _
    rw [undo]
    rfl


theorem revert_success_prefix : ∀ (p : Solidity.Roadmap.Pipeline) (bytes : Solidity.Roadmap.Bytes),
 ((do
    let first ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "poke()"))
    let second ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "g()"))
    pure (first,second)) : Solidity.Source.EM Solidity.Source.SemanticsExamples.EB [] (Solidity.Roadmap.Outcome × Solidity.Roadmap.Outcome)).run
    (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Lowering.V08.SourceTransactionControls.initial bytes) = (.ok (.revert [],.success (Solidity.Source.wordBytes (Solidity.Source.toWord 12))),(Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Roadmap.V16.SourceTransactionConsumer.revertThenSuccess bytes)) := by
  intro p bytes
  simp only [Solidity.Source.Hoare.run_bind, Solidity.Lowering.V08.SourceTransactionControls.revert_actual p 0 bytes, Solidity.Roadmap.V16.SourceTransactionConsumer.after_revert_success p bytes] <;> rfl

theorem success_revert_prefix : ∀ (p : Solidity.Roadmap.Pipeline) (bytes : Solidity.Roadmap.Bytes),
 ((do
    let first ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "g()"))
    let second ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "poke()"))
    pure (first,second)) : Solidity.Source.EM Solidity.Source.SemanticsExamples.EB [] (Solidity.Roadmap.Outcome × Solidity.Roadmap.Outcome)).run
    (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Lowering.V08.SourceTransactionControls.initial bytes) = (.ok (.success (Solidity.Source.wordBytes (Solidity.Source.toWord 12)),.revert []),(Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes)) := by
  intro p bytes
  simp only [Solidity.Source.Hoare.run_bind, Solidity.Lowering.V08.SourceTransactionControls.success_actual p 0 bytes, Solidity.Roadmap.V16.SourceTransactionConsumer.after_success_revert p bytes] <;> rfl

theorem timeout_prefix : ∀ (p : Solidity.Roadmap.Pipeline) (bytes : Solidity.Roadmap.Bytes),
 ((do
    let first ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 0 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "g()"))
    let second ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "poke()"))
    pure (first,second)) : Solidity.Source.EM Solidity.Source.SemanticsExamples.EB [] (Solidity.Roadmap.Outcome × Solidity.Roadmap.Outcome)).run
    (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Lowering.V08.SourceTransactionControls.initial bytes) = (.error .timeout,(Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Lowering.V08.SourceTransactionControls.timed bytes)) := by
  intro p bytes
  simp only [Solidity.Source.Hoare.run_bind, Solidity.Lowering.V08.SourceTransactionControls.timeout_actual p bytes] <;> rfl


theorem success_revert_spec : ∀ (p : Solidity.Roadmap.Pipeline) (bytes : Solidity.Roadmap.Bytes),
 Solidity.Source.Hoare (fun x => x = (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Lowering.V08.SourceTransactionControls.initial bytes))
 ((do
    let first ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "g()"))
    let second ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "poke()"))
    pure (first,second)) : Solidity.Source.EM Solidity.Source.SemanticsExamples.EB [] (Solidity.Roadmap.Outcome × Solidity.Roadmap.Outcome))
 (fun value after => value = (.success (Solidity.Source.wordBytes (Solidity.Source.toWord 12)),.revert []) ∧ after = (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes))
 (fun _ _ => False) := by
  intro p bytes x hx
  subst x
  rw [Solidity.Roadmap.V16.SourceTransactionConsumer.success_revert_prefix p bytes]
  exact ⟨rfl,rfl⟩

theorem wrong_original_rollback : ∀ (p : Solidity.Roadmap.Pipeline) (bytes : Solidity.Roadmap.Bytes),
 ((do
    let first ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "g()"))
    let second ← Solidity.Source.runTx (Solidity.Lowering.V08.SourceTransactionControls.global p) 20 (Solidity.Lowering.V08.SourceTransactionControls.request (Solidity.Source.SemanticsExamples.selOf "poke()"))
    pure (first,second)) : Solidity.Source.EM Solidity.Source.SemanticsExamples.EB [] (Solidity.Roadmap.Outcome × Solidity.Roadmap.Outcome)).run
    (Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Lowering.V08.SourceTransactionControls.initial bytes) ≠ (.ok (.success (Solidity.Source.wordBytes (Solidity.Source.toWord 12)),.revert []),(Solidity.Source.L0 Solidity.Source.SemanticsExamples.EB,Solidity.Lowering.V08.SourceTransactionControls.initial bytes)) := by
  intro p bytes
  rw [Solidity.Roadmap.V16.SourceTransactionConsumer.success_revert_prefix p bytes]
  intro same
  have cell := congrArg (fun result : Except Solidity.Source.Halt (Solidity.Roadmap.Outcome × Solidity.Roadmap.Outcome) × (Solidity.Source.Locals Solidity.Source.SemanticsExamples.EB.layout [] × Solidity.Source.St Solidity.Source.SemanticsExamples.EB) => Solidity.Source.SemanticsExamples.readX result.2.2) same
  change (some (5 : Int)) = some 3 at cell
  cases cell

theorem wrong_event_order : ∀ (bytes : Solidity.Roadmap.Bytes), (Solidity.Roadmap.V16.SourceTransactionConsumer.revertThenSuccess bytes).events ≠ (Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes).events := by
  intro bytes same
  have status := congrArg (fun events : List Solidity.Roadmap.Event => events[1]?.map (fun ev => match ev with | .tx _ _ _ _ _ (.revert _) => true | _ => false)) same
  change some true = some false at status
  cases status

theorem complete_vector : ∀ (bytes : Solidity.Roadmap.Bytes),
 Solidity.Source.SemanticsExamples.readX (Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes) = some 5 ∧
 Solidity.Source.SemanticsExamples.readT (Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes) = some 0 ∧
 (Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes).ex.journal = [] ∧
 (Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes).heap.next = 0 ∧
 (Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes).logs = (Solidity.Lowering.V08.SourceTransactionControls.initial bytes).logs ∧
 (Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes).fnLocals = (Solidity.Lowering.V08.SourceTransactionControls.initial bytes).fnLocals ∧
 (Solidity.Roadmap.V16.SourceTransactionConsumer.successThenRevert bytes).events = (Solidity.Lowering.V08.SourceTransactionControls.initial bytes).events ++
 [.tx Solidity.Source.SemanticsExamples.user Solidity.Source.SemanticsExamples.thisC (Solidity.Source.SemanticsExamples.word 0) (Solidity.Source.SemanticsExamples.word 12345) (Solidity.Source.SemanticsExamples.selOf "g()") (.success (Solidity.Source.wordBytes (Solidity.Source.toWord 12))),
  .tx Solidity.Source.SemanticsExamples.user Solidity.Source.SemanticsExamples.thisC (Solidity.Source.SemanticsExamples.word 0) (Solidity.Source.SemanticsExamples.word 12345) (Solidity.Source.SemanticsExamples.selOf "poke()") (.revert [])] := by
  intro bytes
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


/-- info: 'Solidity.Roadmap.V16.SourceTransactionConsumer.after_revert_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms after_revert_success

/-- info: 'Solidity.Roadmap.V16.SourceTransactionConsumer.after_success_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms after_success_revert

/-- info: 'Solidity.Roadmap.V16.SourceTransactionConsumer.revert_success_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms revert_success_prefix

/-- info: 'Solidity.Roadmap.V16.SourceTransactionConsumer.success_revert_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms success_revert_prefix

/-- info: 'Solidity.Roadmap.V16.SourceTransactionConsumer.timeout_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms timeout_prefix

/-- info: 'Solidity.Roadmap.V16.SourceTransactionConsumer.success_revert_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms success_revert_spec

/-- info: 'Solidity.Roadmap.V16.SourceTransactionConsumer.wrong_original_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_original_rollback

/-- info: 'Solidity.Roadmap.V16.SourceTransactionConsumer.wrong_event_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_event_order

/-- info: 'Solidity.Roadmap.V16.SourceTransactionConsumer.complete_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_vector

end Solidity.Roadmap.V16.SourceTransactionConsumer

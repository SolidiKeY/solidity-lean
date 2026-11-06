import Solidity.Lowering.V08.SourceTransientEmitControls
import Solidity.Lowering.V08.SourceStandardRethrowControls

/-! Actual arithmetic argument failure after the reached transient/caller and
hash prefix. The existing panic decoder is only a byte observation, not Source
catch selection or compiler/frame/ABI adequacy. -/
namespace Solidity.Lowering.V08.SourceTransientEmitPanicControls
open Solidity Source
open SourceEmitControls
open SourceTransientEmitControls (opening written afterArgs)

theorem arguments_reached (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalConvArgs (global pipeline) {frame with static:=static} 10 failingArguments).run
      (locals,written) =
      (.error (.revert (Source.panicData .divZero)),(locals,afterArgs)) := by
  cases pipeline <;> rfl

theorem direct_panic (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 11 1 none
      (.emit eventDeclaration rfl failingArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,written) =
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,afterArgs)) :=
  SourceEmit.exec_argument_failure (global pipeline) {frame with static:=static} 10
    eventDeclaration rfl failingArguments locals locals written afterArgs
    (.revert (Source.panicData .divZero)) (arguments_reached pipeline static)

def execution (pipeline : Roadmap.Pipeline) (static : Bool) (horizon : Nat := 13) :=
  Source.execItems (global pipeline) {frame with static:=static} horizon 1 none
    (SourceTransientEmitControls.items failingArguments) locals

theorem items_panic (pipeline : Roadmap.Pipeline) :
    (execution pipeline false).run (Source.L0 E,opening) =
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,afterArgs)) := by
  have prefixRun := SourceTransientEmitControls.assignment_statement pipeline 0
  have event :
      (Source.execS (global pipeline) frame 11 1 none
        (.emit eventDeclaration rfl failingArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
        (Source.L0 E,written) =
        (.error (.revert (Source.panicData .divZero)),(Source.L0 E,afterArgs)) := direct_panic pipeline false
  change (Source.execItems (global pipeline) frame 13 1 none
    (.stmt (.expr SourceTransientEmitControls.setScratch)
      (.stmt (.emit eventDeclaration rfl failingArguments) .nil) :
      RItems E [] false .body [.bool] [.bool]) locals).run (Source.L0 E,opening) = _
  simp only [ExceptT.run] at prefixRun event
  simp only [Source.execItems,bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,prefixRun,event]

/-- Complete error bytes, without assuming a compiler-selected target statement. -/
theorem intrinsic_payload (pipeline : Roadmap.Pipeline) :
    (execution pipeline false).run (Source.L0 E,opening) =
      (.error (.revert (Semantics.encodePanic 0x12)),(Source.L0 E,afterArgs)) := by
  rw [items_panic,panicData_transport]
  rfl

/-- The published intrinsic decoder observes the actually produced bytes. It
is lossy and supplies no Source catch/frame/admission relation. -/
theorem decoder_observation (pipeline : Roadmap.Pipeline) :
    ((SourceStandardRethrowControls.revertBytes
      ((execution pipeline false).run (Source.L0 E,opening))).bind
      (fun bytes => (Semantics.decodePanic bytes).map (fun word => word.1))) = some (0x12 : Int) := by
  rw [items_panic]
  change (Semantics.decodePanic (Source.panicData .divZero)).map (fun word => word.1) = some (0x12 : Int)
  decide +kernel

theorem prefix_static_refusal (pipeline : Roadmap.Pipeline) :
    (execution pipeline true).run (Source.L0 E,opening) =
      (.error (.revert []),(Source.L0 E,opening)) := rfl

theorem zero_timeout (pipeline : Roadmap.Pipeline) (static : Bool) :
    (execution pipeline static 0).run (Source.L0 E,opening) =
      (.error .timeout,(Source.L0 E,opening)) := rfl

theorem complete_vector :
    (afterArgs.ex.world.accounts sender).balance.val = 93 ∧
    (afterArgs.ex.world.accounts self).balance.val = 7 ∧
    (afterArgs.ex.world.accounts self).code = some 0 ∧
    (afterArgs.ex.world.accounts self).nonce = 1 ∧
    (afterArgs.ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (opening.ex.transient.cells self).read scratch = some (.bool false) ∧
    (afterArgs.ex.transient.cells self).read scratch = some (.bool true) ∧
    (afterArgs.ex.transient.cells sender).read scratch = some (.bool true) ∧
    opening.ex.journal.length = 1 ∧ afterArgs.ex.journal.length = 2 ∧
    afterArgs.heap.next = 2 ∧
    afterArgs.heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    afterArgs.heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    afterArgs.events = populated.events ∧ afterArgs.logs = populated.logs ∧
    afterArgs.fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_empty_payload (pipeline : Roadmap.Pipeline) :
    (execution pipeline false).run (Source.L0 E,opening) ≠
      (.error (.revert []),(Source.L0 E,afterArgs)) := by
  rw [items_panic]
  intro same
  exact SourceEmitControls.nonempty_panic
    (Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same)))

theorem wrong_assert_payload (pipeline : Roadmap.Pipeline) :
    (execution pipeline false).run (Source.L0 E,opening) ≠
      (.error (.revert (Source.panicData .assert)),(Source.L0 E,afterArgs)) := by
  rw [items_panic]
  intro same
  have bytesEq : Source.panicData .divZero = Source.panicData .assert :=
    Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  have codes : (.divZero : Source.PanicCode) = .assert :=
    Source.panic_distinct (congrArg Source.revertOutcome bytesEq)
  cases codes

theorem wrong_before_hash (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.execS (global pipeline) {frame with static:=static} 11 1 none
      (.emit eventDeclaration rfl failingArguments : RStmt E [] false .body [.bool] [.bool]) locals).run
      (Source.L0 E,written) ≠
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,written)) := by
  rw [direct_panic]
  intro same
  have heaps := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heaps
  cases heaps

/-- Raw failure first, then an explicit journal-only operation; no automatic
rollback or EVM frame/log adequacy is inferred. -/
theorem rollback_after_panic (pipeline : Roadmap.Pipeline) :
    (execution pipeline false).run (Source.L0 E,opening) =
      (.error (.revert (Source.panicData .divZero)),(Source.L0 E,afterArgs)) ∧
    {afterArgs with ex:=SourceTransientEmitControls.mark.rollback afterArgs.ex} =
      SourceKeccak.afterLiteral opening binary :=
  ⟨items_panic pipeline,SourceTransientEmitControls.rollback_static⟩

theorem end_fields :
    (SourceTransient.endExecution afterArgs).ex.world = afterArgs.ex.world ∧
    (SourceTransient.endExecution afterArgs).ex.journal = [] ∧
    (SourceTransient.endExecution afterArgs).heap = afterArgs.heap ∧
    (SourceTransient.endExecution afterArgs).events = afterArgs.events ∧
    (SourceTransient.endExecution afterArgs).logs = afterArgs.logs ∧
    (SourceTransient.endExecution afterArgs).fnLocals = afterArgs.fnLocals :=
  SourceTransient.end_execution_fields afterArgs

theorem end_reads (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution afterArgs) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution afterArgs)) ∧
    (Source.evalE (global pipeline) {frame with this:=sender} 2 (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution afterArgs) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution afterArgs)) := ⟨rfl,rfl⟩

theorem erased_failure (pipeline : Roadmap.Pipeline) :
    let result := (execution pipeline false).run (Source.L0 E,opening)
    (result.1,result.2.1,SourceEmit.eraseLogs result.2.2) =
      (.error (.revert (Source.panicData .divZero)),Source.L0 E,SourceEmit.eraseLogs afterArgs) := by
  simp only [items_panic]

#print axioms arguments_reached
#print axioms direct_panic
#print axioms items_panic
#print axioms intrinsic_payload
#print axioms decoder_observation
#print axioms prefix_static_refusal
#print axioms zero_timeout
#print axioms complete_vector
#print axioms wrong_empty_payload
#print axioms wrong_assert_payload
#print axioms wrong_before_hash
#print axioms rollback_after_panic
#print axioms end_fields
#print axioms end_reads
#print axioms erased_failure
end Solidity.Lowering.V08.SourceTransientEmitPanicControls

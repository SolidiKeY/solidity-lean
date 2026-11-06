import Solidity.Lowering.V08.SourceTransientRethrowControls

/-! Further actual effecting ABI application at the genuinely reached transient
prefix. No fixed-populated producer is applied to a changed input world. -/
namespace Solidity.Lowering.V08.SourceTransientMixedRethrowControls
open Solidity Source
open SourceCustomErrorControls SourceAbiControls
open SourceTransientRethrowControls (opening written)

def after (pipeline : Roadmap.Pipeline) (packed : Bool) : Source.St E :=
  SourceKeccak.afterLiteral (SourceKeccak.afterLiteral written binary) (data packed pipeline)

theorem arguments_reached (pipeline : Roadmap.Pipeline) :
    (Source.evalArgs (global pipeline) frame 16 arguments).run (locals,written) =
      (.ok (values pipeline),(.cons (.bool false) .nil,SourceKeccak.afterLiteral written binary)) := rfl

/-- Existing typed encoder laws are applied at the reached state, not at the
old fixed populated input. The argument effects have already run in order. -/
theorem encoding_reached (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (Source.encodeVals frame 16 packed (values pipeline) : Source.EM E [.bool] _).run
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral written binary) =
      (.ok (data packed pipeline),(.cons (.bool false) .nil,SourceKeccak.afterLiteral written binary)) := by
  have wordRead : (digest pipeline).word = some (digestWord pipeline) := by
    rw [digestWord_eq]
    exact digest_word pipeline
  have wordEncoded := SourceAbi.encode_fixed_bytes32 (E:=E) (Γ:=[.bool])
    frame 16 packed (digest pipeline) (digestWord pipeline) wordRead
  have literalEncoded (bytes : Roadmap.Bytes) :
      (Source.encodeOne frame 16 packed (.strLit bytes) : Source.EM E [.bool] _) =
        pure (true,bytes) := rfl
  have falseEncoded :
      (Source.encodeOne frame 16 packed (.val (.bool false)) : Source.EM E [.bool] _) =
        pure (false,if packed then [0] else zeroWord) := by
    cases packed <;> rfl
  unfold data
  generalize wordEquation : digestWord pipeline = word at wordEncoded ⊢
  simp only [SourceAbiControls.values,Source.encodeVals,Source.encodeParts]
  rw [literalEncoded binary,falseEncoded,literalEncoded long33,wordEncoded]
  cases packed <;> simp only [Bool.false_eq_true,↓reduceIte,bind,pure,
    ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,
    List.foldr_cons,List.foldr_nil,List.append_nil,List.append_assoc]


theorem expression_reached (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (Source.evalE (global pipeline) frame 17
      (.abiEncode (if packed then .encodePacked else .encode) arguments)).run (locals,written) =
      (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,after pipeline packed)) :=
  SourceAbi.execute (global pipeline) frame 16 packed arguments locals
    (.cons (.bool false) .nil) (.cons (.bool false) .nil) written _ _ (values pipeline) _
    (arguments_reached pipeline) (encoding_reached pipeline packed)

def sequence (packed : Bool) : RItems E [] false .body [.bool] [.bytes .memory,.bool] :=
  .stmt (.expr setScratch)
    (.stmt (.declInit (.abiEncode (if packed then .encodePacked else .encode) arguments) rfl)
      (.stmt (.rethrow .here) .nil))
def execution (pipeline : Roadmap.Pipeline) (static packed : Bool) (horizon : Nat := 20) :=
  Source.execItems (global pipeline) {frame with static:=static} horizon 1 none (sequence packed) locals

theorem declaration_reached (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (Source.execS (global pipeline) frame 18 1 none
      (.declInit (.abiEncode (if packed then .encodePacked else .encode) arguments) rfl :
        RStmt E [] false .body [.bool] [.bytes .memory,.bool]) locals).run (Source.L0 E,written) =
      (.ok (.normal (.cons (.memRef rfl 2) (.cons (.bool false) .nil))),
        (Source.L0 E,after pipeline packed)) := by
  have expression := expression_reached pipeline packed
  simp only [ExceptT.run] at expression
  simp only [Source.execS,Source.EM.sub,Source.convRV,Source.getV,Source.RVal.get,
    Source.EM.lift,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,expression,↓reduceDIte] <;> rfl

theorem sequence_complete (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (execution pipeline false packed).run (Source.L0 E,opening) =
      (.error (.revert (data packed pipeline)),(Source.L0 E,after pipeline packed)) := by
  have prefixRun := SourceTransientRethrowControls.assignment_statement pipeline 10
  have allocation := declaration_reached pipeline packed
  have rethrowRun :
      (Source.execS (global pipeline) frame 17 1 none
        (.rethrow .here : RStmt E [] false .body [.bytes .memory,.bool] [.bytes .memory,.bool])
        (.cons (.memRef rfl 2) (.cons (.bool false) .nil))).run (Source.L0 E,after pipeline packed) =
        (.error (.revert (data packed pipeline)),(Source.L0 E,after pipeline packed)) :=
    SourceCustomErrorFailures.rethrow_bytes (global pipeline) frame 16 .here
      (.cons (.memRef rfl 2) (.cons (.bool false) .nil)) (after pipeline packed) 2 _ rfl
      (SourceRethrow.allocated_object (SourceKeccak.afterLiteral written binary) _)
  have frameEq : {frame with static:=false} = frame := rfl
  simp only [ExceptT.run] at prefixRun allocation rethrowRun
  simp only [execution,sequence,frameEq,Source.execItems,bind,pure,ExceptT.bind,
    ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,prefixRun,allocation,rethrowRun]

theorem static_before_arguments (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (execution pipeline true packed).run (Source.L0 E,opening) =
      (.error (.revert []),(Source.L0 E,opening)) := rfl

theorem argument_timeout (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (Source.evalE (global pipeline) frame 6
      (.abiEncode (if packed then .encodePacked else .encode) arguments)).run (locals,written) =
      (.error .timeout,(.cons (.bool false) .nil,written)) := by cases packed <;> rfl

theorem sequence_timeout (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (execution pipeline false packed 9).run (Source.L0 E,opening) =
      (.error .timeout,(Source.L0 E,written)) := by cases packed <;> rfl

theorem complete_vector (pipeline : Roadmap.Pipeline) (packed : Bool) :
    ((after pipeline packed).ex.world.accounts sender).balance = 93 ∧
    ((after pipeline packed).ex.world.accounts self).balance = 7 ∧
    ((after pipeline packed).ex.world.accounts self).code = some 0 ∧
    ((after pipeline packed).ex.world.accounts self).nonce = 1 ∧
    ((after pipeline packed).ex.world.accounts self).storage.read saved = some (.bool true) ∧
    (opening.ex.transient.cells self).read scratch = some (.bool false) ∧
    ((after pipeline packed).ex.transient.cells self).read scratch = some (.bool true) ∧
    ((after pipeline packed).ex.transient.cells sender).read scratch = some (.bool true) ∧
    opening.ex.journal.length = 1 ∧ (after pipeline packed).ex.journal.length = 2 ∧
    (after pipeline packed).heap.next = 3 ∧
    (after pipeline packed).heap.get 0 = some ⟨.bytes .memory,.bytes [0,255]⟩ ∧
    (after pipeline packed).heap.get 1 = some ⟨.bytes .memory,.bytes binary⟩ ∧
    (after pipeline packed).heap.get 2 = some ⟨.bytes .memory,.bytes (data packed pipeline)⟩ ∧
    (after pipeline packed).events = populated.events ∧
    (after pipeline packed).logs = populated.logs ∧
    (after pipeline packed).fnLocals = populated.fnLocals :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem rollback_complete_state (pipeline : Roadmap.Pipeline) (packed : Bool) :
    {after pipeline packed with ex:=SourceTransientRethrowControls.mark.rollback (after pipeline packed).ex} =
      SourceKeccak.afterLiteral (SourceKeccak.afterLiteral opening binary) (data packed pipeline) := by
  change {after pipeline packed with ex:=SourceTransientRethrowControls.mark.rollback written.ex} = _
  rw [SourceTransientRethrowControls.rollback_execution_component]
  rfl

theorem end_fields (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (SourceTransient.endExecution (after pipeline packed)).ex.world = (after pipeline packed).ex.world ∧
    (SourceTransient.endExecution (after pipeline packed)).ex.journal = [] ∧
    (SourceTransient.endExecution (after pipeline packed)).heap = (after pipeline packed).heap ∧
    (SourceTransient.endExecution (after pipeline packed)).events = (after pipeline packed).events ∧
    (SourceTransient.endExecution (after pipeline packed)).logs = (after pipeline packed).logs ∧
    (SourceTransient.endExecution (after pipeline packed)).fnLocals = (after pipeline packed).fnLocals :=
  SourceTransient.end_execution_fields (after pipeline packed)

/-- Actual reads after the raw halt and after the separate public end operation. -/
theorem transient_reads (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run (locals,after pipeline packed) =
      (.ok (.val (.bool true)),(locals,after pipeline packed)) ∧
    (Source.evalE (global pipeline) frame 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution (after pipeline packed)) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution (after pipeline packed))) ∧
    (Source.evalE (global pipeline) {frame with this:=sender} 2
      (.state scratchDecl rfl : RExpr E [.bool] .bool)).run
      (locals,SourceTransient.endExecution (after pipeline packed)) =
      (.ok (.val (.bool false)),(locals,SourceTransient.endExecution (after pipeline packed))) :=
  ⟨rfl,rfl,rfl⟩

theorem wrong_original_base (pipeline : Roadmap.Pipeline) (packed : Bool) :
    (execution pipeline false packed).run (Source.L0 E,opening) ≠
      (.error (.revert (data packed pipeline)),(Source.L0 E,
        SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary) (data packed pipeline))) := by
  rw [sequence_complete]
  intro same
  have journals := congrArg (fun result => result.2.2.ex.journal.length) same
  change 2 = 3 at journals
  cases journals

theorem wrong_reversed_payload (pipeline : Roadmap.Pipeline) :
    (execution pipeline false false).run (Source.L0 E,opening) ≠
      (.error (.revert (reversedData pipeline)),(Source.L0 E,after pipeline false)) := by
  rw [sequence_complete]
  intro same
  have bytesEq : data false pipeline = reversedData pipeline :=
    Source.Halt.revert.inj (Except.error.inj (congrArg Prod.fst same))
  exact different_ordered_bytes pipeline bytesEq

#print axioms arguments_reached
#print axioms encoding_reached
#print axioms expression_reached
#print axioms declaration_reached
#print axioms sequence_complete
#print axioms static_before_arguments
#print axioms argument_timeout
#print axioms sequence_timeout
#print axioms complete_vector
#print axioms rollback_complete_state
#print axioms end_fields
#print axioms transient_reads
#print axioms wrong_original_base
#print axioms wrong_reversed_payload
end Solidity.Lowering.V08.SourceTransientMixedRethrowControls

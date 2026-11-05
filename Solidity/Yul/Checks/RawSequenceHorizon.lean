import Solidity.Yul.RawSequenceHorizon
import Solidity.Yul.Checks.RawStatementHorizon

namespace Solidity.Yul.Checks.RawSequenceHorizon
namespace Old
export Solidity.Yul.Checks.RawStatementHorizon
  (ctx env dirty initial flag small flipped flippedProof expression proof)
end Old
export Old (ctx env dirty initial flag small)
def tailExpression : Solidity.Source.RExpr env ctx.tys .bool :=
  .cond (.assign (.local .here) (.bool false)) (.bool false)
    (.assign (.local .here) Old.flipped)
def tailProof : RawSource.Supported ctx [] false ⟨true,false⟩ (.expr tailExpression) :=
  .expression (.cond (.assign .here (.base (.literal false))) (.base (.literal false))
    (.assign .here Old.flippedProof))
def items : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
  .stmt (.expr Old.expression) (.stmt (.expr tailExpression) .nil)
def proof : RawSequence.Supported ctx [] false ⟨true,false⟩ items :=
  .cons Old.proof (.cons tailProof .nil)
def witness : Nonempty (RawSequence.Supported ctx [] false ⟨true,false⟩ items) := ⟨proof⟩
theorem completed : (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).1 = .ok () := by
  rfl


theorem blockCompleted : (Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawSequenceHorizon.proof 10 Solidity.Yul.Checks.RawSequenceHorizon.dirty).1 = .ok () := by
  rfl


theorem stable : ∀ extra : Nat, Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof (9+extra) Solidity.Yul.Checks.RawSequenceHorizon.dirty = Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawSequenceHorizon.extension Solidity.Yul.Checks.RawSequenceHorizon.ctx [] false ⟨true,false⟩ _ Solidity.Yul.Checks.RawSequenceHorizon.proof 9 extra Solidity.Yul.Checks.RawSequenceHorizon.dirty (by rw [Solidity.Yul.Checks.RawSequenceHorizon.completed]; intro bad; cases bad)


theorem blockStable : ∀ extra : Nat, Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawSequenceHorizon.proof (10+extra) Solidity.Yul.Checks.RawSequenceHorizon.dirty = Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawSequenceHorizon.proof 10 Solidity.Yul.Checks.RawSequenceHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawSequenceHorizon.blockExtension Solidity.Yul.Checks.RawSequenceHorizon.ctx [] false ⟨true,false⟩ _ Solidity.Yul.Checks.RawSequenceHorizon.proof 10 extra Solidity.Yul.Checks.RawSequenceHorizon.dirty (by rw [Solidity.Yul.Checks.RawSequenceHorizon.blockCompleted]; intro bad; cases bad)


theorem partialStages : (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 5 Solidity.Yul.Checks.RawSequenceHorizon.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 5 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceHorizon.flag).val = 1 ∧
 (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 8 Solidity.Yul.Checks.RawSequenceHorizon.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 8 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceHorizon.flag).val = 0 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 8 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩


theorem completedValues : (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceHorizon.flag).val = 1 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceHorizon.small).val = 257 ∧
 Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawSequenceHorizon.proof 10 Solidity.Yul.Checks.RawSequenceHorizon.dirty = Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty := by
  exact ⟨rfl,rfl,rfl⟩


theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSequenceHorizon.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSequenceHorizon.env)),
 Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawSequenceHorizon.proof fuel Solidity.Yul.Checks.RawSequenceHorizon.initial) =
 some ((Solidity.Source.execS glob frame fuel nps ph (.block Solidity.Yul.Checks.RawSequenceHorizon.items) Solidity.Yul.Checks.RawSequenceHorizon.initial.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawSequenceHorizon.env,Solidity.Yul.Checks.RawSequenceHorizon.initial.world)) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.RawSequence.block_source_agrees Solidity.Yul.Checks.RawSequenceHorizon.proof glob frame fuel nps ph Solidity.Yul.Checks.RawSequenceHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)


theorem dirtyProjectionRefused : Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2 = false ∧
 Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty) = none ∧
 Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawSequenceHorizon.proof 10 Solidity.Yul.Checks.RawSequenceHorizon.dirty) = none := by
  have incoherent : Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2 = false := by
    have rawSmall : (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2 Solidity.Yul.Checks.RawSequenceHorizon.small).val = 257 := rfl
    have cleanSmall : (Solidity.Yul.localWordCells Solidity.Yul.Checks.RawSequenceHorizon.ctx
        (Solidity.Yul.LocalValues.ofClean (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2.clean) Solidity.Yul.Checks.RawSequenceHorizon.small).val = 1 := rfl
    cases same : Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2 with
    | false => rfl
    | true =>
      have views := (Solidity.Yul.RawCoherent.coherent_iff (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).2).mp same
      have numbers := congrArg (fun cells => (cells Solidity.Yul.Checks.RawSequenceHorizon.small).val) views
      dsimp only at numbers
      rw [rawSmall,cleanSmall] at numbers
      cases numbers
  refine ⟨incoherent,?_,?_⟩
  · simp only [Solidity.Yul.RawCoherent.observe,incoherent,Bool.false_eq_true,if_false]
  · change Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty) = none
    simp only [Solidity.Yul.RawCoherent.observe,incoherent,Bool.false_eq_true,if_false]


theorem cleanObservation : Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawSequenceHorizon.proof 10 Solidity.Yul.Checks.RawSequenceHorizon.initial).2 = true ∧
 (Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawSequence.block Solidity.Yul.Checks.RawSequenceHorizon.proof 10 Solidity.Yul.Checks.RawSequenceHorizon.initial)).isSome = true := by
  decide


theorem timeoutChanges : (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 8 Solidity.Yul.Checks.RawSequenceHorizon.dirty).1 ≠ (Solidity.Yul.RawSequence.run Solidity.Yul.Checks.RawSequenceHorizon.proof 9 Solidity.Yul.Checks.RawSequenceHorizon.dirty).1 := by
  intro bad; cases bad

#print axioms Solidity.Yul.RawSequenceHorizon.successor
#print axioms Solidity.Yul.RawSequenceHorizon.blockSuccessor
#print axioms Solidity.Yul.RawSequenceHorizon.extension
#print axioms Solidity.Yul.RawSequenceHorizon.blockExtension
#print axioms completed
#print axioms blockCompleted
#print axioms stable
#print axioms blockStable
#print axioms partialStages
#print axioms completedValues
#print axioms cleanSource
#print axioms dirtyProjectionRefused
#print axioms cleanObservation
#print axioms timeoutChanges
end Solidity.Yul.Checks.RawSequenceHorizon

import Solidity.Yul.RawStatementHorizon
import Solidity.Yul.Checks.RawSourceVoidReturn

namespace Solidity.Yul.Checks.RawStatementHorizon
export RawSourceVoidReturn (dirty)
export RawSourceVoidReturn.Old (ctx env locals flag small)
def flipped : Solidity.Source.RExpr env ctx.tys .bool :=
  .unary .not (.unary .not (.unary .not (.local .here)))
def flippedProof : LocalBoolControl.Supported env ctx.tys flipped :=
  .not (.not (.not (.base (.local .here))))
def expression : Solidity.Source.RExpr env ctx.tys .bool :=
  .cond (.assign (.local .here) (.bool true))
    (.assign (.local .here) flipped) (.bool false)
def proof : RawSource.Supported ctx [] false ⟨true,false⟩ (.expr expression) :=
  .expression (.cond (.assign .here (.base (.literal true)))
    (.assign .here flippedProof) (.base (.literal false)))
def initial : RawFrame.State ctx := RawFrame.ofClean locals (Solidity.Source.St.init env)
def witness : Nonempty (RawSource.Supported ctx [] false ⟨true,false⟩ (.expr expression)) := ⟨proof⟩
theorem rawComplete : (Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty).1 = .ok () := by
  rfl


theorem coherentComplete : (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty).1 = .ok () := by
  rfl


theorem rawStable : ∀ extra : Nat, Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof (7+extra) Solidity.Yul.Checks.RawStatementHorizon.dirty = Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawStatementHorizon.rawExtension Solidity.Yul.Checks.RawStatementHorizon.ctx [] false ⟨true,false⟩ _ Solidity.Yul.Checks.RawStatementHorizon.proof 7 extra Solidity.Yul.Checks.RawStatementHorizon.dirty (by rw [Solidity.Yul.Checks.RawStatementHorizon.rawComplete]; intro bad; cases bad)


theorem coherentStable : ∀ extra : Nat, Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof (7+extra) Solidity.Yul.Checks.RawStatementHorizon.dirty = Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawStatementHorizon.coherentExtension Solidity.Yul.Checks.RawStatementHorizon.ctx [] false ⟨true,false⟩ _ Solidity.Yul.Checks.RawStatementHorizon.proof 7 extra Solidity.Yul.Checks.RawStatementHorizon.dirty (by rw [Solidity.Yul.Checks.RawStatementHorizon.coherentComplete]; intro bad; cases bad)


theorem partialWrites : (Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof 4 Solidity.Yul.Checks.RawStatementHorizon.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof 4 Solidity.Yul.Checks.RawStatementHorizon.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.flag).val = 1 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof 4 Solidity.Yul.Checks.RawStatementHorizon.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.small).val = 257 ∧
 (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 4 Solidity.Yul.Checks.RawStatementHorizon.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 4 Solidity.Yul.Checks.RawStatementHorizon.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.flag).val = 1 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 4 Solidity.Yul.Checks.RawStatementHorizon.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩


theorem dirtyCompleted : (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.small).val = 257 ∧
 (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty).2 Solidity.Yul.Checks.RawStatementHorizon.small).val = 257 ∧
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty).2 = false := by
  decide


theorem projectionRefused : Solidity.Yul.RawSource.observation Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty = none ∧
 Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty) = none := by
  exact ⟨rfl,rfl⟩


theorem timeoutChanges : (Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof 4 Solidity.Yul.Checks.RawStatementHorizon.dirty).1 ≠ (Solidity.Yul.RawSource.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty).1 ∧
 (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 4 Solidity.Yul.Checks.RawStatementHorizon.dirty).1 ≠ (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.dirty).1 := by
  constructor <;> intro bad <;> cases bad


theorem cleanCompletion : Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.initial).2 = true ∧
 (Solidity.Yul.RawCoherent.observe (Solidity.Yul.RawCoherent.execS Solidity.Yul.Checks.RawStatementHorizon.proof 7 Solidity.Yul.Checks.RawStatementHorizon.initial)).isSome = true := by
  decide


theorem dirtyInput : Solidity.Yul.RawCoherent.coherent Solidity.Yul.Checks.RawStatementHorizon.dirty = false ∧
 (Solidity.Yul.RawFrame.view Solidity.Yul.Checks.RawStatementHorizon.dirty Solidity.Yul.Checks.RawStatementHorizon.flag).val = 2 ∧
 (Solidity.Yul.RawFrame.view Solidity.Yul.Checks.RawStatementHorizon.dirty Solidity.Yul.Checks.RawStatementHorizon.small).val = 257 := by
  decide

#print axioms Solidity.Yul.RawStatementHorizon.discardSuccessor
#print axioms Solidity.Yul.RawStatementHorizon.rawSuccessor
#print axioms Solidity.Yul.RawStatementHorizon.coherentSuccessor
#print axioms Solidity.Yul.RawStatementHorizon.rawExtension
#print axioms Solidity.Yul.RawStatementHorizon.coherentExtension
#print axioms rawComplete
#print axioms coherentComplete
#print axioms rawStable
#print axioms coherentStable
#print axioms partialWrites
#print axioms dirtyCompleted
#print axioms projectionRefused
#print axioms timeoutChanges
#print axioms cleanCompletion
#print axioms dirtyInput
end Solidity.Yul.Checks.RawStatementHorizon

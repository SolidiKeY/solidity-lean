import Solidity.Yul.RawControlledWhileHorizon
import Solidity.Yul.RawReadOnlyViews
import Solidity.Yul.Checks.RawLoopBodyHorizon

namespace Solidity.Yul.Checks.RawControlledWhileHorizon
namespace Old
export Solidity.Yul.Checks.RawLoopBodyHorizon
  (ctx env dirty initial flag small read breakBody continueBody)
export Solidity.Yul.Checks.RawStatementHorizon (expression proof)
end Old
export Old (ctx env dirty initial flag small read breakBody continueBody)
def singleItems : Solidity.Source.RItems env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
  .stmt (.expr Old.expression) .nil
def singleProof : RawSequence.Supported ctx [] false ⟨true,false⟩ singleItems :=
  .cons Old.proof .nil
def normalBody : RawLoopBody.Supported ctx [] false false (.block singleItems) := .plain singleProof
def writeThenTrue : LocalBoolControl.Supported env ctx.tys
    (.unary .not (.assign (.local .here) (.bool false))) :=
  .not (.assign .here (.base (.literal false)))
def mutatingContinue : RawLoopBody.Supported ctx [] false false
    (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont) :=
  .ifThen writeThenTrue .continue_
def stopped : LocalBoolControl.Supported env ctx.tys (.bool false) := .base (.literal false)
def sourceLoop : Solidity.Source.RStmt env [] false ⟨false,false⟩ ctx.tys ctx.tys :=
  .whileLoop (.local .here) (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont)
def witness : Nonempty (RawLoopBody.Supported ctx [] false false
    (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont)) := ⟨mutatingContinue⟩
theorem breakExit : (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.breakBody 3 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.breakBody 3 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.breakBody 3 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem breakStable : ∀ extra : Nat, Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.breakBody (3+extra) Solidity.Yul.Checks.RawControlledWhileHorizon.dirty = Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.breakBody 3 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawControlledWhileHorizon.extension Solidity.Yul.Checks.RawControlledWhileHorizon.ctx [] false false (.local .here) Solidity.Yul.Checks.RawControlledWhileHorizon.read _ Solidity.Yul.Checks.RawControlledWhileHorizon.breakBody 3 extra Solidity.Yul.Checks.RawControlledWhileHorizon.dirty (by rw [(Solidity.Yul.Checks.RawControlledWhileHorizon.breakExit).1]; intro bad; cases bad)


theorem continueExit : (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.mutatingContinue 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.mutatingContinue 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.mutatingContinue 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem continueStable : ∀ extra : Nat, Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.mutatingContinue (5+extra) Solidity.Yul.Checks.RawControlledWhileHorizon.dirty = Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.mutatingContinue 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawControlledWhileHorizon.extension Solidity.Yul.Checks.RawControlledWhileHorizon.ctx [] false false (.local .here) Solidity.Yul.Checks.RawControlledWhileHorizon.read _ Solidity.Yul.Checks.RawControlledWhileHorizon.mutatingContinue 5 extra Solidity.Yul.Checks.RawControlledWhileHorizon.dirty (by rw [(Solidity.Yul.Checks.RawControlledWhileHorizon.continueExit).1]; intro bad; cases bad)


theorem normalExit : (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 10 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 10 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.flag).val = 0 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 10 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem normalStable : ∀ extra : Nat, Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody (10+extra) Solidity.Yul.Checks.RawControlledWhileHorizon.dirty = Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 10 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty := by
  intro extra
  exact Solidity.Yul.RawControlledWhileHorizon.extension Solidity.Yul.Checks.RawControlledWhileHorizon.ctx [] false false (.local .here) Solidity.Yul.Checks.RawControlledWhileHorizon.read _ Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 10 extra Solidity.Yul.Checks.RawControlledWhileHorizon.dirty (by rw [(Solidity.Yul.Checks.RawControlledWhileHorizon.normalExit).1]; intro bad; cases bad)


theorem falseSkipsBody : (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.stopped Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 2 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).1 = .ok () ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.stopped Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 2 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.stopped Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 2 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem continueTimeout : (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.continueBody 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.continueBody 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.flag).val = 2 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.continueBody 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.small).val = 257 := by
  have preserved := Solidity.Yul.RawReadOnlyViews.loop Solidity.Yul.Checks.RawControlledWhileHorizon.ctx [] false false .here 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty
  refine ⟨?_,?_,?_⟩
  · rfl
  · calc
      (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.continueBody 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.flag).val =
        (Solidity.Yul.RawFrame.view Solidity.Yul.Checks.RawControlledWhileHorizon.dirty Solidity.Yul.Checks.RawControlledWhileHorizon.flag).val :=
          congrArg (fun value : Solidity.Yul.Word => value.val) (congrFun preserved Solidity.Yul.Checks.RawControlledWhileHorizon.flag)
      _ = 2 := rfl
  · calc
      (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.continueBody 5 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.small).val =
        (Solidity.Yul.RawFrame.view Solidity.Yul.Checks.RawControlledWhileHorizon.dirty Solidity.Yul.Checks.RawControlledWhileHorizon.small).val :=
          congrArg (fun value : Solidity.Yul.Word => value.val) (congrFun preserved Solidity.Yul.Checks.RawControlledWhileHorizon.small)
      _ = 257 := rfl


theorem partialNormal : (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 9 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).1 = .error .timeout ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 9 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.flag).val = 1 ∧ (Solidity.Yul.RawFrame.view (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 9 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).2 Solidity.Yul.Checks.RawControlledWhileHorizon.small).val = 257 := by
  exact ⟨rfl,rfl,rfl⟩


theorem timeoutChanges : (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 9 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).1 ≠ (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.normalBody 10 Solidity.Yul.Checks.RawControlledWhileHorizon.dirty).1 := by
  rw [(Solidity.Yul.Checks.RawControlledWhileHorizon.partialNormal).1,(Solidity.Yul.Checks.RawControlledWhileHorizon.normalExit).1]
  intro bad; cases bad


theorem cleanSource : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawControlledWhileHorizon.env) (frame : Solidity.Source.Fr)
 (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawControlledWhileHorizon.env)),
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.mutatingContinue fuel Solidity.Yul.Checks.RawControlledWhileHorizon.initial).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   Solidity.Yul.Checks.RawControlledWhileHorizon.sourceLoop Solidity.Yul.Checks.RawControlledWhileHorizon.initial.clean).run
   (Solidity.Source.L0 Solidity.Yul.Checks.RawControlledWhileHorizon.env,Solidity.Yul.Checks.RawControlledWhileHorizon.initial.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawControlledWhile.run Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.mutatingContinue fuel Solidity.Yul.Checks.RawControlledWhileHorizon.initial) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.RawControlledWhile.correct (l := false) Solidity.Yul.Checks.RawControlledWhileHorizon.read Solidity.Yul.Checks.RawControlledWhileHorizon.mutatingContinue glob frame fuel nps ph Solidity.Yul.Checks.RawControlledWhileHorizon.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

#print axioms Solidity.Yul.RawControlledWhileHorizon.successor
#print axioms Solidity.Yul.RawControlledWhileHorizon.extension
#print axioms Solidity.Yul.RawReadOnlyViews.condition
#print axioms Solidity.Yul.RawReadOnlyViews.continueBody
#print axioms Solidity.Yul.RawReadOnlyViews.loop
#print axioms breakExit
#print axioms breakStable
#print axioms continueExit
#print axioms continueStable
#print axioms normalExit
#print axioms normalStable
#print axioms falseSkipsBody
#print axioms continueTimeout
#print axioms partialNormal
#print axioms timeoutChanges
#print axioms cleanSource
end Solidity.Yul.Checks.RawControlledWhileHorizon

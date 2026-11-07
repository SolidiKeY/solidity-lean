import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingTurnViews
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarLeaves

/-! Actual allocating root and continuation-tail recognition. The guard and
zero arm are checked against their original scalar syntax. The continuation
is retained unmodified; its call/argument/return/child checks remain open. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingGuardedTurn
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

structure Head {C : Contract} (R : RefTy) (source : Prog C (Frame R) (Frame R)) : Type where
 continuation : Prog C (Frame R) (Frame R)
 shape : source=.cons (.ite guard (.cons AllocatingScalarSource.allocate continuation) (.cons zero .nil)) .nil

def assemble {C : Contract} {R : RefTy} {source : Prog C (Frame R) (Frame R)}
 (turn : AllocatingTurnViews.Turn source) (condition : turn.condition=guard)
 (alternative : AllocatingSourceViews.ClosedCons turn.alternative)
 (zeroEq : alternative.head=zero) (ending : AllocatingHeadViews.NilView alternative.tail) : Head R source := by
 refine ⟨turn.continuation,?_⟩
 simp only [turn.shape,condition,alternative.shape,zeroEq,eq_of_heq ending.shape,
   AllocatingDeclarationCheck.allocation,AllocatingScalarSource.allocate,AllocatingScalarSource.lengthExpr]

def read {C : Contract} (R : RefTy) (source : Prog C (Frame R) (Frame R)) : Option (Head R source) := do
 let turn ← AllocatingTurnViews.read source
 let condition ← AllocatingScalarLeaves.checkGuard turn.condition
 let alternative ← AllocatingSourceViews.readClosedCons turn.alternative
 let zeroEq ← AllocatingScalarLeaves.checkZero alternative.head
 let ending ← AllocatingHeadViews.readNil alternative.tail
 pure (assemble turn condition.down alternative zeroEq.down ending)

def checkTail {C : Contract} {R : RefTy} (source : Prog C (Frame R) (Frame R)) :
 Option (PLift (source=.cons increment .nil)) := do
 let parts ← AllocatingSourceViews.readClosedCons source
 let headEq ← AllocatingScalarLeaves.checkIncrement parts.head
 let ending ← AllocatingHeadViews.readNil parts.tail
 pure ⟨by simp only [parts.shape,headEq.down,eq_of_heq ending.shape]⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingGuardedTurn
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingGuardedTurn.assemble' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingGuardedTurn.assemble

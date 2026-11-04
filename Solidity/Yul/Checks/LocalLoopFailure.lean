import Solidity.Yul.LocalLoopFailure
import Solidity.Yul.Checks.LocalDefaultNoGuard

namespace Solidity.Yul.Checks.LocalLoopFailure

def witness := Solidity.Yul.Checks.LocalDefaultNoGuard.witness
def rawConcrete (fuel : Nat) (state : LocalState Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.ctx.tys) :=
 Solidity.Yul.LocalLoopFailure.noPostTimeout Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env [] false false Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultNoGuard.Out Solidity.Yul.Checks.LocalDefaultNoGuard.items Solidity.Yul.Checks.LocalDefaultNoGuard.proof fuel state

def sourceConcrete (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env))
 (locals : Solidity.Source.Locals Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env.layout Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env) :=
 Solidity.Yul.LocalLoopFailure.sourceNoPostTimeout Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env [] false false Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultNoGuard.Out Solidity.Yul.Checks.LocalDefaultNoGuard.items Solidity.Yul.Checks.LocalDefaultNoGuard.proof glob frame fuel nps ph locals world

theorem omittedTimeout : Solidity.Yul.LocalDefaultNoGuard.runNoPost Solidity.Yul.Checks.LocalDefaultNoGuard.proof 9 Solidity.Yul.Checks.LocalDefaultNoGuard.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultNoGuard.afterFalsePostBody := by
  rfl

theorem guardedCompletion : Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultPostIter.readTest Solidity.Yul.Checks.LocalDefaultNoGuard.proof 9 Solidity.Yul.Checks.LocalDefaultNoGuard.initial = .normal (Solidity.Yul.Checks.LocalDefaultNoGuard.assigned false) := by
  rfl

theorem falseGuard : Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalDefaultPostIter.stopTest Solidity.Yul.Checks.LocalDefaultNoGuard.proof 2 Solidity.Yul.Checks.LocalDefaultNoGuard.initial = .normal Solidity.Yul.Checks.LocalDefaultNoGuard.initial := by
  rfl

theorem retainedScope : Solidity.Yul.LocalDefaultItems.blockRun Solidity.Yul.Checks.LocalDefaultNoGuard.proof 7 Solidity.Yul.Checks.LocalDefaultNoGuard.initial = .halted .timeout Solidity.Yul.Checks.LocalDefaultItems.bodyState := by
  rfl

theorem notRevert : Solidity.Yul.LocalDefaultNoGuard.runNoPost Solidity.Yul.Checks.LocalDefaultNoGuard.proof 9 Solidity.Yul.Checks.LocalDefaultNoGuard.initial ≠ .halted (.revert []) Solidity.Yul.Checks.LocalDefaultNoGuard.afterFalsePostBody := by
  intro bad; cases bad

theorem breakingSourceCompletes : let items : Solidity.Source.RItems Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env [] false ⟨true,false⟩ Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.ctx.tys := .stmt .brk .nil
∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env) (frame : Solidity.Source.Fr) (nps : Nat)
 (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env)) (locals : Solidity.Source.Locals Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env.layout Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.ctx.tys)
 (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env),
 (Solidity.Source.forIter glob frame 4 nps ph .none .none (.block items) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env,world) =
 (.ok (.normal locals),(Solidity.Source.L0 Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env,world)) := by
  dsimp only []; intro glob frame nps ph locals world; rfl

theorem breakingBodyRefused : let items : Solidity.Source.RItems Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env [] false ⟨true,false⟩ Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.ctx.tys Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.ctx.tys := .stmt .brk .nil
¬ Nonempty (Solidity.Yul.LocalDefaultItems.Supported Solidity.Yul.Checks.LocalDefaultNoGuard.Fixture.env [] false ⟨true,false⟩ items) := by
  dsimp only []; rintro ⟨proof⟩; cases proof with | body child => cases child

#print axioms Solidity.Yul.LocalLoopFailure.block
#print axioms Solidity.Yul.LocalLoopFailure.whileLoop
#print axioms Solidity.Yul.LocalLoopFailure.noPostTimeout
#print axioms Solidity.Yul.LocalLoopFailure.sourceNoPostTimeout
#print axioms omittedTimeout
#print axioms guardedCompletion
#print axioms falseGuard
#print axioms retainedScope
#print axioms notRevert
#print axioms breakingSourceCompletes
#print axioms breakingBodyRefused

end Solidity.Yul.Checks.LocalLoopFailure

import Solidity.Yul.RawSourceReturnControl
import Solidity.Yul.Checks.RawSourceVoidReturn

namespace Solidity.Yul.Checks.RawSourceReturnControl
namespace Fixture
export Solidity.Yul.Checks.RawSourceVoidReturn (dirty)
export Solidity.Yul.Checks.RawSourceVoidReturn.Old (ctx env locals flag small)
end Fixture

def condition : Solidity.Source.RExpr Fixture.env Fixture.ctx.tys .bool :=
  .assign (.local .here) (.bool false)
def loop : Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys :=
  .doWhile (.ret rfl) condition
def innerTail : Solidity.Source.RItems Fixture.env [] false ⟨false,true⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) :=
  .stmt (.declVar .bool) .nil
def outerTail : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) :=
  .stmt (.expr condition) (.stmt (.declVar .bool) .nil)
def uncheckedCode : Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys) :=
  .unchecked (.stmt (.ret rfl) innerTail) outerTail
def loopWitness : Nonempty (Solidity.Source.RStmt Fixture.env [] false ⟨false,false⟩ Fixture.ctx.tys Fixture.ctx.tys) :=
  ⟨loop⟩
def uncheckedWitness : Nonempty (Solidity.Source.RItems Fixture.env [] false ⟨false,false⟩
    Fixture.ctx.tys (.bool :: Fixture.ctx.tys)) := ⟨uncheckedCode⟩

def loopConcrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawSourceReturnControl.doWhile_correct Fixture.ctx false false false
    glob frame fuel nps ph Fixture.dirty condition
def uncheckedConcrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawSourceReturnControl.unchecked_correct Fixture.ctx false false
    glob frame fuel nps ph Fixture.dirty (.bool :: Fixture.ctx.tys)
    (.bool :: Fixture.ctx.tys) innerTail outerTail

def normal {output} (result : Solidity.Source.R
    (Solidity.Source.Out Fixture.env.layout Fixture.ctx.tys output) × RawFrame.State Fixture.ctx) : Bool :=
  match result.1 with
  | .ok (.normal _) => true
  | _ => false

theorem horizons : (
Solidity.Yul.Checks.RawSourceVoidReturn.timeout (Solidity.Yul.RawSourceReturnControl.doWhile 1 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.returned (Solidity.Yul.RawSourceReturnControl.doWhile 2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.timeout (Solidity.Yul.RawSourceReturnControl.unchecked (output := .bool :: Solidity.Yul.Checks.RawSourceReturnControl.Fixture.ctx.tys) 2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.returned (Solidity.Yul.RawSourceReturnControl.unchecked (output := .bool :: Solidity.Yul.Checks.RawSourceReturnControl.Fixture.ctx.tys) 3 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.returned (Solidity.Yul.RawSourceReturnControl.whileLiteral true 2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty) = true ∧
Solidity.Yul.Checks.RawSourceVoidReturn.returned (Solidity.Yul.RawSourceReturnControl.whileLiteral false 2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty) = false ∧
Solidity.Yul.Checks.RawSourceVoidReturn.timeout (Solidity.Yul.RawSourceReturnControl.whileLiteral false 2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty) = false ∧
(Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceReturnControl.doWhile 2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty).2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.flag).val = 2 ∧
(Solidity.Yul.RawFrame.view (Solidity.Yul.RawSourceReturnControl.unchecked (output := .bool :: Solidity.Yul.Checks.RawSourceReturnControl.Fixture.ctx.tys) 3 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty).2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.small).val = 257 ∧
 Solidity.Yul.Checks.RawSourceReturnControl.normal
 (Solidity.Yul.RawSourceReturnControl.whileLiteral false 2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty) = true
) := by
  decide

theorem condition_changes : (Solidity.Source.Locals.get Solidity.Yul.Checks.RawSourceReturnControl.Fixture.locals .here).key = some 1 ∧
 (Solidity.Source.Locals.get (Solidity.Source.Locals.set Solidity.Yul.Checks.RawSourceReturnControl.Fixture.locals
 .here (.bool false)) .here).key = some 0 := by
  decide

theorem retention : (Solidity.Yul.RawSourceReturnControl.doWhile 2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty).2 =
 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty ∧
 (Solidity.Yul.RawSourceReturnControl.unchecked (output := .bool :: Solidity.Yul.Checks.RawSourceReturnControl.Fixture.ctx.tys) 3 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty).2 =
 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty ∧
 (Solidity.Yul.RawSourceReturnControl.whileLiteral false 2 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty).2 =
 Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty := by
  exact ⟨rfl,rfl,rfl⟩

theorem condition_writes : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceReturnControl.Fixture.env)
 (frame : Solidity.Source.Fr),
 (Solidity.Source.evalE glob frame 4 Solidity.Yul.Checks.RawSourceReturnControl.condition).run
  (Solidity.Yul.Checks.RawSourceReturnControl.Fixture.locals,
   Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty.world) =
 (.ok (.val (.bool false)),
  (Solidity.Source.Locals.set Solidity.Yul.Checks.RawSourceReturnControl.Fixture.locals
    .here (.bool false),Solidity.Yul.Checks.RawSourceReturnControl.Fixture.dirty.world)) := by
  intro glob frame; rfl

/-- Resolved-only negative shape; not a frontend-admitted program. -/
def refusedConcrete (glob : Solidity.Source.Glob Fixture.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Fixture.env)) :=
  Solidity.Yul.RawSourceReturnControl.initializer_refused_correct Fixture.ctx false false false
    glob frame fuel nps ph Fixture.dirty Fixture.ctx.tys (.some condition)
    (.some condition) (.expr condition)

#print axioms Solidity.Yul.RawSourceReturnControl.doWhile_correct
#print axioms Solidity.Yul.RawSourceReturnControl.unchecked_correct
#print axioms Solidity.Yul.RawSourceReturnControl.whileLiteral_correct
#print axioms Solidity.Yul.RawSourceReturnControl.initializer_refused_correct
#print axioms loopConcrete
#print axioms uncheckedConcrete
#print axioms refusedConcrete
#print axioms horizons
#print axioms condition_changes
#print axioms retention
#print axioms condition_writes

end Solidity.Yul.Checks.RawSourceReturnControl

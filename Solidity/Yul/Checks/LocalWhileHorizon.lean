import Solidity.Yul.LocalWhileHorizon
import Solidity.Yul.Checks.LocalDefaultControlRepresentation

namespace Solidity.Yul.Checks.LocalWhileHorizon
export LocalDefaultControlRepresentation (env state raw cleanFalse read stop)
abbrev Ty := Solidity.Source.STy.int Solidity.Source.IntTy.u8
abbrev Out : Solidity.Source.RCtx := [Ty,.bool]
def zero := RawDefaultDeclaration.intDefault env Solidity.Source.IntTy.u8
def flag : Solidity.Source.Idx Out .bool := .there .here
def items : Solidity.Source.RItems env [] false ⟨true,false⟩ [.bool] Out :=
  .stmt (.declVar Ty)
    (.stmt (.expr (.assign (.local flag) (.bool false)))
      (.stmt (.expr (.unary .not (.unary .not (.unary .not (.local flag))))) .nil))
def body : LocalDefaultItems.Supported env [] false ⟨true,false⟩ items :=
  .declaration zero (.body
    (.expression (.assign flag (.base (.literal false)))
      (.expression (.not (.not (.not (.base (.local flag))))) .nil)))
def witness : Nonempty (LocalDefaultItems.Supported env [] false ⟨true,false⟩ items) := ⟨body⟩
def reached (value : LocalValue env .bool) (world : Solidity.Source.St env) :
    LocalState env Out := ((.clean zero.value,(value,())),world)


theorem stoppedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.stop Solidity.Yul.Checks.LocalWhileHorizon.body (2+extra) (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) := by
  intro world extra
  have completed : Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.stop Solidity.Yul.Checks.LocalWhileHorizon.body 2 (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) := by rfl
  exact Solidity.Yul.LocalWhileHorizon.extension _ _ _ _ _ _ _ _ _ _ 2 extra _ _ completed

theorem completedObserved : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env), Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.read Solidity.Yul.Checks.LocalWhileHorizon.body 10 (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalWhileHorizon.state Solidity.Yul.Checks.LocalWhileHorizon.cleanFalse world) := by
  intro world
  rfl

theorem completedStable : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env) (extra : Nat), Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.read Solidity.Yul.Checks.LocalWhileHorizon.body (10+extra) (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) = .normal (Solidity.Yul.Checks.LocalWhileHorizon.state Solidity.Yul.Checks.LocalWhileHorizon.cleanFalse world) := by
  intro world extra
  exact Solidity.Yul.LocalWhileHorizon.extension _ _ _ _ _ _ _ _ _ _ 10 extra _ _ (completedObserved world)

theorem prefixTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env), Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.read Solidity.Yul.Checks.LocalWhileHorizon.body 5 (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalWhileHorizon.reached (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) := by
  intro world
  rfl

theorem writtenTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env), Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.read Solidity.Yul.Checks.LocalWhileHorizon.body 7 (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalWhileHorizon.reached Solidity.Yul.Checks.LocalWhileHorizon.cleanFalse world) := by
  intro world
  rfl

theorem timeoutMayChange : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env), Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.read Solidity.Yul.Checks.LocalWhileHorizon.body 7 (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) ≠ Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.read Solidity.Yul.Checks.LocalWhileHorizon.body 10 (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) := by
  intro world same
  rw [writtenTimeout,completedObserved] at same
  cases same

theorem skippedBodyTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env), Solidity.Yul.LocalDefaultItems.blockRun Solidity.Yul.Checks.LocalWhileHorizon.body 1 (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) := by
  intro world
  rfl

theorem zeroTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env), Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.read Solidity.Yul.Checks.LocalWhileHorizon.body 0 (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) := by
  intro world
  rfl

theorem dirtyProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env) (extra : Nat), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultWhile.run Solidity.Yul.Checks.LocalWhileHorizon.stop Solidity.Yul.Checks.LocalWhileHorizon.body (2+extra) (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world)) = none := by
  intro world extra
  rw [stoppedStable]
  rfl

theorem literalTrueNeverCompletes : ∀ (fuel : Nat) (world : Solidity.Source.St Solidity.Yul.Checks.LocalWhileHorizon.env) (next : Solidity.Yul.LocalState Solidity.Yul.Checks.LocalWhileHorizon.env [.bool]), Solidity.Yul.LocalDefaultWhile.run (.base (.literal true)) Solidity.Yul.Checks.LocalWhileHorizon.body fuel (Solidity.Yul.Checks.LocalWhileHorizon.state (Solidity.Yul.Checks.LocalWhileHorizon.raw 2) world) ≠ .normal next := by
  intro fuel world next
  exact Solidity.Yul.LocalDefaultWhile.no_normal _ _ _ _ _ _ _ _ fuel _ _

#print axioms Solidity.Yul.LocalWhileHorizon.successor
#print axioms Solidity.Yul.LocalWhileHorizon.extension
#print axioms stoppedStable
#print axioms completedObserved
#print axioms completedStable
#print axioms prefixTimeout
#print axioms writtenTimeout
#print axioms timeoutMayChange
#print axioms skippedBodyTimeout
#print axioms zeroTimeout
#print axioms dirtyProjection
#print axioms literalTrueNeverCompletes

end Solidity.Yul.Checks.LocalWhileHorizon

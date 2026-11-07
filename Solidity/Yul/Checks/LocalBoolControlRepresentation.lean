import Solidity.Yul.LocalBoolControlRepresentation
import Solidity.Yul.Checks.LocalBoolRepresentation

/-! Concrete raw Boolean controls for short-circuiting, conditional updates,
partial evaluation and the typed representation relation. -/
namespace Solidity.Yul.Checks.LocalBoolControlRepresentation
export Solidity.Yul.Checks.LocalBoolRepresentation (env raw cleanTrue cleanFalse)
def state (value : LocalValue env .bool) (world : Solidity.Source.St env) :
    LocalState env [.bool] := ((value,()),world)
def read : LocalBoolControl.Supported env [.bool] (.local .here) := .base (.local .here)
def setTrue : LocalBoolControl.Supported env [.bool] (.assign (.local .here) (.bool true)) :=
  .assign .here (.base (.literal true))
def andExpr : Solidity.Source.RExpr env [.bool] .bool :=
  .binary .and (.bool false) (.assign (.local .here) (.bool true))
def andProof : LocalBoolControl.Supported env [.bool] andExpr :=
  .and (.base (.literal false)) setTrue
def orExpr : Solidity.Source.RExpr env [.bool] .bool :=
  .binary .or (.local .here) (.assign (.local .here) (.bool true))
def orProof : LocalBoolControl.Supported env [.bool] orExpr := .or read setTrue
def condExpr : Solidity.Source.RExpr env [.bool] .bool :=
  .cond (.assign (.local .here) (.bool false)) (.bool true) (.local .here)
def condProof : LocalBoolControl.Supported env [.bool] condExpr :=
  .cond (.assign .here (.base (.literal false))) (.base (.literal true)) read
def faultExpr : Solidity.Source.RExpr env [.bool] .bool :=
  .binary .and (.assign (.local .here) (.bool true))
    (.unary .not (.unary .not (.unary .not (.local .here))))
def fault : LocalBoolControl.Supported env [.bool] faultExpr :=
  .and setTrue (.not (.not (.not read)))
def witness : Nonempty (LocalBoolControl.Supported env [.bool] condExpr) := ⟨condProof⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalBoolControlRepresentation.control env [.bool] condExpr condProof fuel one two related

theorem andSkip : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.andProof 2 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.ok Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanFalse, Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) := by

  intro world; rfl

theorem orRetains : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.orProof 2 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.ok (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2), Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) := by

  intro world; rfl

theorem conditionalUpdate : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.condProof 3 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.ok Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanFalse, Solidity.Yul.Checks.LocalBoolControlRepresentation.state Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanFalse world) := by

  intro world; rfl

theorem partialTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.fault 3 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.error .timeout, Solidity.Yul.Checks.LocalBoolControlRepresentation.state Solidity.Yul.Checks.LocalBoolControlRepresentation.cleanTrue world) := by

  intro world; rfl

theorem zeroTimeout : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.condProof 0 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) = (.error .timeout, Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world) := by

  intro world; rfl

theorem rawNotClean : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), (Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.orProof 2 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)).1.map Solidity.Yul.LocalValue.clean? = .ok none := by

  intro world; rfl

theorem dirtyObservationDistinct : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolControlRepresentation.env), (Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.orProof 2 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 2) world)).1.map Solidity.Yul.LocalBoolRepresentation.word ≠ (Solidity.Yul.LocalBoolControl.eval Solidity.Yul.Checks.LocalBoolControlRepresentation.orProof 2 (Solidity.Yul.Checks.LocalBoolControlRepresentation.state (Solidity.Yul.Checks.LocalBoolControlRepresentation.raw 1) world)).1.map Solidity.Yul.LocalBoolRepresentation.word := by

  intro world
  change (Except.ok (Solidity.Yul.word 2) : Solidity.Source.R Solidity.Yul.Word) ≠ .ok (Solidity.Yul.word 1)
  intro same
  exact (by decide : Solidity.Yul.word 2 ≠ Solidity.Yul.word 1) (Except.ok.inj same)

#print axioms Solidity.Yul.LocalBoolControlRepresentation.control
#print axioms andSkip
#print axioms orRetains
#print axioms conditionalUpdate
#print axioms partialTimeout
#print axioms zeroTimeout
#print axioms rawNotClean

#print axioms dirtyObservationDistinct

end Solidity.Yul.Checks.LocalBoolControlRepresentation

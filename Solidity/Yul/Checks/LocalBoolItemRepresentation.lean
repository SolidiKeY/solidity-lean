import Solidity.Yul.LocalBoolItemRepresentation
import Solidity.Yul.Checks.LocalBoolControlRepresentation

/-! Raw Boolean declaration and initialization controls with pinned axiom reports. -/
namespace Solidity.Yul.Checks.LocalBoolItemRepresentation
export Solidity.Yul.Checks.LocalBoolControlRepresentation (env state raw cleanTrue cleanFalse)
def body : Solidity.Source.RItems env [] false ⟨false,false⟩ [.bool] [.bool,.bool] :=
  .stmt (.declInit (τ := .bool) (.local .here) (by rfl))
    (.stmt (.expr (.assign (.local .here) (.unary .not (.local .here)))) .nil)
def proof : LocalBoolItems.Supported env [] false ⟨false,false⟩ body :=
  .declaration (.base (.local .here))
    (.expression (.assign .here (.not (.base (.local .here)))) .nil)
def witness : Nonempty (LocalBoolItems.Supported env [] false ⟨false,false⟩ body) := ⟨proof⟩
def extended (world : Solidity.Source.St env) : LocalState env [.bool,.bool] :=
  ((raw 2,(raw 2,())),world)
def finalState (world : Solidity.Source.St env) : LocalState env [.bool,.bool] :=
  ((cleanFalse,(raw 2,())),world)
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalBoolItemRepresentation.items env [] false ⟨false,false⟩
    [.bool] [.bool,.bool] body proof fuel one two related

theorem completed : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 6 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .normal (Solidity.Yul.Checks.LocalBoolItemRepresentation.finalState world) := by

  intro world; rfl

theorem beforeDeclaration : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 2 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) := by

  intro world; rfl

theorem afterDeclaration : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 3 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolItemRepresentation.extended world) := by

  intro world; rfl

theorem zeroFuel : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 0 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) = .halted .timeout (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world) := by

  intro world; rfl

theorem normalProjectionRefused : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 6 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world)) = none := by

  intro world; rfl

theorem haltProjection : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 3 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world)) = some (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.LocalBoolItemRepresentation.env,world)) := by

  intro world; rfl

theorem reachedContextDistinct : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalBoolItemRepresentation.env), ¬ Solidity.Yul.LocalBoolItemRepresentation.Items Solidity.Yul.Checks.LocalBoolItemRepresentation.env [.bool,.bool] (Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 2 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world)) (Solidity.Yul.LocalBoolItems.run Solidity.Yul.Checks.LocalBoolItemRepresentation.proof 3 (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world)) := by

  intro world related
  change Solidity.Yul.LocalBoolItemRepresentation.Items _ _
    (.halted .timeout (Solidity.Yul.Checks.LocalBoolItemRepresentation.state (Solidity.Yul.Checks.LocalBoolItemRepresentation.raw 2) world)) (.halted .timeout (Solidity.Yul.Checks.LocalBoolItemRepresentation.extended world)) at related
  cases related

/-- info: 'Solidity.Yul.LocalBoolItemRepresentation.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.LocalBoolItemRepresentation.finish
/-- info: 'Solidity.Yul.LocalBoolItemRepresentation.initialization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.LocalBoolItemRepresentation.initialization
/-- info: 'Solidity.Yul.LocalBoolItemRepresentation.items' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.LocalBoolItemRepresentation.items
/-- info: 'Solidity.Yul.Checks.LocalBoolItemRepresentation.completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms completed
/-- info: 'Solidity.Yul.Checks.LocalBoolItemRepresentation.beforeDeclaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms beforeDeclaration
/-- info: 'Solidity.Yul.Checks.LocalBoolItemRepresentation.afterDeclaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms afterDeclaration
/-- info: 'Solidity.Yul.Checks.LocalBoolItemRepresentation.zeroFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroFuel
/-- info: 'Solidity.Yul.Checks.LocalBoolItemRepresentation.normalProjectionRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalProjectionRefused
/-- info: 'Solidity.Yul.Checks.LocalBoolItemRepresentation.haltProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms haltProjection
/-- info: 'Solidity.Yul.Checks.LocalBoolItemRepresentation.reachedContextDistinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reachedContextDistinct

end Solidity.Yul.Checks.LocalBoolItemRepresentation

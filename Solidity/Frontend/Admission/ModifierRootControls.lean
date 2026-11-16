import Solidity.Frontend.Admission.ModifierRoots
import Solidity.Frontend.Admission.ProgramObservationControls

/-! Actual modifier selector controls, not Elaborated/execution witnesses. -/
namespace Solidity.Frontend.Admission.ModifierRootControls
open Solidity.Source ProgramControls

def bare : Decl := ⟨.modifier, "empty", some "C", false,
  .modifier "empty" .none false none
    (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil)))⟩
def bareEnv : Env := ⟨[bare]⟩

/-- Both supported parameter forms are inhabited; qualification preserves the selected identity, while wrong kinds and deeper paths remain refused. -/
theorem selector_controls :
    env.modifierAt (some "C") ⟨"guard", []⟩ = some (modifierDecl, [.int IntTy.u256]) ∧
    env.modifierAt none ⟨"C", ["guard"]⟩ = some (modifierDecl, [.int IntTy.u256]) ∧
    bareEnv.modifierAt (some "C") ⟨"empty", []⟩ = some (bare, []) ∧
    env.modifierAt (some "C") ⟨"run", []⟩ = none ∧
    env.modifierAt none ⟨"C", ["guard", "extra"]⟩ = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- info: 'Solidity.Frontend.Admission.ModifierRootControls.selector_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selector_controls
end Solidity.Frontend.Admission.ModifierRootControls

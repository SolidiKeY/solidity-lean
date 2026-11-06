import Lean

open Lean Elab Command

namespace Solidity.TrustFragmentsFixture

theorem usesPropext : True = True := propext Iff.rfl
theorem alsoUsesPropext : True = True := propext Iff.rfl

run_cmd do
  let headlines : List Name := [``Solidity.TrustFragmentsFixture.usesPropext]
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in headlines do
    let _ ← getConstInfo name
    let axioms ← collectAxioms name
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do
      throwError "trust: {name} depends on unexpected axioms {extra}"
  logInfo m!"fixture passed"

end Solidity.TrustFragmentsFixture

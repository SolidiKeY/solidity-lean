import Solidity.Tools.Preconditions
import Solidity.Calculus.Spec

/-!
# Entry conditions checked separately from postconditions

The impossible entry certificate reveals a vacuous specification; a possible
entry certificate says nothing about whether its body meets its postcondition.
Both are tied to the original typed obligation rather than a separately copied
precondition. Unknown shapes create no theorem.
-/

namespace Solidity.Examples.Preconditions

def Conditions : Contract := contract!{
  requires amount > 10 && amount < 3;
  ensures false;
  function impossible(uint amount) public pure { assert(false); }

  requires amount > 0;
  ensures \result == amount;
  function possible(uint amount) public pure returns (uint) { return amount; }

  requires amount == 2;
  ensures false;
  function badPost(uint amount) public pure { assert(false); }
}

def impossibleSpec : Fml Conditions [] := cspec[Conditions]{impossible}
def possibleSpec : Fml Conditions [] := cspec[Conditions]{possible}
def badPostSpec : Fml Conditions [] := cspec[Conditions]{badPost}

/-- info: preconditions: impossible (kernel-checked: Solidity.Examples.Preconditions.impossibleEntry) -/
#guard_msgs in #audit_preconditions impossibleSpec as impossibleEntry

/-- info: preconditions: possible (kernel-checked: Solidity.Examples.Preconditions.possibleEntry) -/
#guard_msgs in #audit_preconditions possibleSpec as possibleEntry

-- A false postcondition does not make the entry condition impossible.
/-- info: preconditions: possible (kernel-checked: Solidity.Examples.Preconditions.badPostEntry) -/
#guard_msgs in #audit_preconditions badPostSpec as badPostEntry

example : Fml.PreconditionsImpossible impossibleSpec := impossibleEntry
example : Fml.PreconditionsPossible possibleSpec := possibleEntry
example : Fml.PreconditionsPossible badPostSpec := badPostEntry

/-- The specification can hold solely because its entry condition is impossible. -/
example : Fml.Valid impossibleSpec := impossibleEntry.valid

example : ¬ Fml.PreconditionsPossible impossibleSpec := impossibleEntry.not_possible

def noEntry : Fml Conditions [] := .tt

/-- info: preconditions: unknown (no leading implication under parameter binders) -/
#guard_msgs in #audit_preconditions noEntry as unknownEntry

open Lean Elab Command in
run_cmd do
  if (← getEnv).contains ((← getCurrNamespace) ++ Name.mkSimple "unknownEntry") then
    throwError "an unknown audit must not create a theorem"

/-- info: 'Solidity.Examples.Preconditions.impossibleEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms impossibleEntry
/-- info: 'Solidity.Examples.Preconditions.possibleEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms possibleEntry
/-- info: 'Solidity.Examples.Preconditions.badPostEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms badPostEntry

end Solidity.Examples.Preconditions

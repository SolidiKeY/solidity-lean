import tests.h62.item4.«generic-source-frontend».Core

/-! Typed witnesses for acceptance, profile mismatch, missing tag and refusal.
These supplement the universal semantic proof, not original parser fixtures. -/
namespace Solidity.Frontend.GenericSourceControls.Controls
open Solidity.Source
open Solidity.Frontend.GenericSourceControls

def unitTree : Syn .unit := .unit .nil

def good : Except Unit (Syn .unit) := .ok unitTree
def refused : Except Unit (Syn .unit) := .error ()
def profile : Syn .unit → Bool := fun _ => true
def tags : Syn .unit → List Nat := fun _ => [1, 2]

example : check good true true [1, 2] profile tags = true := rfl
example : check good true false [1, 2] profile tags = false := rfl
example : check good true true [3] profile tags = false := rfl
example : check good false true [] profile tags = false := rfl
example : check refused true true [] profile tags = false := rfl
-- Negative controls require refusal, regardless of unused profile/tag fields.
example : check refused false false [99] profile tags = true := rfl

/-- A concrete inhabited semantic witness, using the universal correspondence. -/
theorem accepted_witness : Specification good true true [1, 2] profile tags :=
  (check_iff good true true [1, 2] profile tags).mp rfl

theorem refused_witness : ∃ e : Unit, refused = .error e :=
  negative_requires_refusal refused false [99] profile tags rfl

/-- Inhabited typed fixture rows independent of the migration-blocked parser. -/
def witnesses : List (Row (Except Unit (Syn .unit))
    (fun result => check result false false [99] profile tags)) :=
  [⟨refused, rfl⟩]

#print axioms accepted_witness
#print axioms refused_witness
end Solidity.Frontend.GenericSourceControls.Controls

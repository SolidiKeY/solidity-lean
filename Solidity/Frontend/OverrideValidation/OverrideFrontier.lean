import Solidity.Frontend.OverrideValidation.Graph

/-! Override legality considers private declarations too, whereas visible
implementation exposure does not. The existing visible Frontier is preserved. -/
namespace Solidity.Frontend.OverrideValidation
open Solidity.Source

def OverrideOwn (E : Env) (key owner d : Node E) : Prop :=
  Own E owner d ∧ SameSlot E key.decl d.decl

def overrideOwnB (E : Env) (key owner d : Node E) : Bool :=
  ownB E owner d && sameSlotB E key.decl d.decl

def OverrideStep (E : Env) (key a b : Node E) : Prop :=
  BaseEdge E a b ∧ ∀ d, ¬ OverrideOwn E key a d

def overrideStepB (E : Env) (key a b : Node E) : Bool :=
  baseEdgeB E a b && !((nodes E).any fun d => overrideOwnB E key a d)

/-- All first matching declarations on direct-base paths, including private
functions that a redeclaration would illegally override. -/
def OverrideFrontier (E : Env) (c key f : Node E) : Prop :=
  ∃ b owner, BaseEdge E c b ∧ OverrideOwn E key owner f ∧
    RelRoute (OverrideStep E key) (nodes E) b owner

def overrideFrontierB (E : Env) (c key f : Node E) : Bool :=
  (nodes E).any fun b => baseEdgeB E c b && (nodes E).any fun owner =>
    overrideOwnB E key owner f && routeB (overrideStepB E key) (nodes E) b owner

theorem overrideOwnB_iff {E : Env} {key owner d : Node E} :
    overrideOwnB E key owner d = true ↔ OverrideOwn E key owner d := by
  simp only [overrideOwnB, OverrideOwn, Bool.and_eq_true, ownB_iff, sameSlotB_iff]

theorem overrideStepB_iff {E : Env} {key a b : Node E} :
    overrideStepB E key a b = true ↔ OverrideStep E key a b := by
  simp only [overrideStepB, OverrideStep, Bool.and_eq_true, baseEdgeB_iff,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, any_nodes_iff, overrideOwnB_iff, not_exists]

theorem overrideFrontierB_iff {E : Env} {c key f : Node E} :
    overrideFrontierB E c key f = true ↔ OverrideFrontier E c key f := by
  simp only [overrideFrontierB, OverrideFrontier, any_nodes_iff, Bool.and_eq_true,
    baseEdgeB_iff, overrideOwnB_iff, routeB_rel_iff (fun _ _ => overrideStepB_iff)]
  constructor
  · rintro ⟨b, hb, owner, ho, hr⟩
    exact ⟨b, owner, hb, ho, hr⟩
  · rintro ⟨b, owner, hb, ho, hr⟩
    exact ⟨b, hb, owner, ho, hr⟩


end Solidity.Frontend.OverrideValidation

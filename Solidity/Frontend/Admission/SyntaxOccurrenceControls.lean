import Solidity.Frontend.Admission.SyntaxOccurrenceLaws

/-! Inhabited exact-payload/order controls. These are syntax inventories,
not execution-root, semantic reachability or profile witnesses. -/
namespace Solidity.Frontend.Admission.OccurrenceControls
open Solidity.Source

def pairTree (left right : String) : Syn (.list .expr) :=
  .cons (.ident left) (.cons (.ident right) .nil)

def pairInventory (left right : String) : List SyntaxOccurrence :=
  [⟨.list .expr, pairTree left right⟩, ⟨.expr, .ident left⟩,
   ⟨.list .expr, .cons (.ident right) .nil⟩, ⟨.expr, .ident right⟩,
   ⟨.list .expr, .nil⟩]

theorem exact_pair_inventory (left right : String) :
    syntaxOccurrences (pairTree left right) = pairInventory left right := rfl

theorem distinct_payload_order :
    syntaxOccurrences (pairTree "left" "right") = pairInventory "left" "right" :=
  exact_pair_inventory "left" "right"

theorem repeated_payloads_retained :
    syntaxOccurrences (pairTree "same" "same") = pairInventory "same" "same" :=
  exact_pair_inventory "same" "same"

/-- The child may not be silently omitted even though its parent is retained. -/
theorem omitted_child_refused :
    syntaxOccurrences (Syn.some (Syn.ident "seed")) ≠
      ([⟨_, Syn.some (Syn.ident "seed")⟩] : List SyntaxOccurrence) := by
  intro h
  have hl := congrArg List.length h
  change 2 = 1 at hl
  cases hl

#print axioms exact_pair_inventory
#print axioms distinct_payload_order
#print axioms repeated_payloads_retained
#print axioms omitted_child_refused
end Solidity.Frontend.Admission.OccurrenceControls

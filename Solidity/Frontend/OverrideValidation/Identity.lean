import Solidity.Source.Inheritance

/-!
# Declaration identity for the additive G14 candidate

A node is a position in the existing resolved environment, not a name or a
reconstructed callable. All projections read the original dependent `Decl`.
No Source or Static definition is replaced. Graph rules and their checker
will live above this module; these lemmas alone do not certify overrides.
-/

namespace Solidity.Frontend.OverrideValidation

open Solidity.Source

/-- Positions retain distinct declarations even if signatures coincide. -/
abbrev Node (E : Env) := Fin E.decls.length

/-- Read the original declaration, including its intrinsic syntax and body. -/
def Node.decl {E : Env} (n : Node E) : Decl := E.decls[n.val]

/-- A requested and a chosen declaration retain their original identities. -/
structure Selection (E : Env) where
  requested : Node E
  chosen : Node E

/-- A selection reads a member of this fixed environment. -/
theorem selected_in_env {E : Env} (s : Selection E) : s.chosen.decl ∈ E.decls :=
  List.getElem_mem s.chosen.isLt

/-- Reading a node is functional, without a well-formedness assumption. -/
theorem same_node_same_decl {E : Env} {a b : Node E} (h : a = b) : a.decl = b.decl :=
  congrArg Node.decl h

/-- Two distinct declaration bodies cannot be identified by one position. -/
theorem distinct_decl_distinct_node {E : Env} {a b : Node E}
    (h : a.decl ≠ b.decl) : a ≠ b :=
  fun he => h (same_node_same_decl he)

/-- An environment lookup and the node's read agree on the whole declaration. -/
theorem node_lookup {E : Env} (n : Node E) : E.decls[n.val]? = some n.decl :=
  List.getElem?_eq_getElem n.isLt

/-- No selected implementation can have an invented declaration body. -/
theorem selected_lookup {E : Env} (s : Selection E) :
    E.decls[s.chosen.val]? = some s.chosen.decl := node_lookup s.chosen

/-- Sharing a signature or a spelling does not collapse positions. -/
theorem position_identity {E : Env} {a b : Node E} : a = b ↔ a.val = b.val :=
  Fin.ext_iff

end Solidity.Frontend.OverrideValidation

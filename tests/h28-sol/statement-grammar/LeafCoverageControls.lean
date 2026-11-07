import Solidity.Frontend.StatementGrammarH28.LeafCoverage

/-! Inhabited control-leaf parser states with a boundary suffix and existing layout. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def leafSuffix : St :=
  ⟨[atToken (.kw .else_) 70 74], [.attrs [.vis]], 80⟩

example : stmt 1 ⟨true, false⟩ (controlInput (.kw .break_) 3 8 8 9 leafSuffix) =
    .ok (.breakStmt, leafSuffix) := break_coverage 0 false 3 8 8 9 leafSuffix

example : stmt 1 ⟨true, true⟩ (controlInput (.kw .continue_) 3 11 11 12 leafSuffix) =
    .ok (.continueStmt, leafSuffix) := continue_coverage 0 true 3 11 11 12 leafSuffix

example : stmt 2 .body (controlInput (.kw .return_) 3 9 9 10 leafSuffix) =
    .ok (.returnStmt .none, leafSuffix) := empty_return_coverage 0 .body 3 9 9 10 leafSuffix

example : stmt 1 ⟨false, true⟩ (controlInput (.kw .break_) 3 8 8 9 leafSuffix) =
    .error ⟨3, "break outside a loop"⟩ := break_outside_loop 0 true 3 8 8 9 leafSuffix

example : stmt 1 .body (controlInput (.kw .continue_) 3 11 11 12 leafSuffix) =
    .error ⟨3, "continue outside a loop"⟩ := continue_outside_loop 0 false 3 11 11 12 leafSuffix

example : stmt 0 ⟨true, true⟩ (controlInput (.kw .break_) 3 8 8 9 leafSuffix) =
    .error ⟨3, "nesting too deep"⟩ := control_zero_fuel _ _ _ _ _ _ _

example : stmt 0 ⟨true, false⟩ (controlInput (.kw .continue_) 3 11 11 12 leafSuffix) =
    .error ⟨3, "nesting too deep"⟩ := control_zero_fuel _ _ _ _ _ _ _

example : stmt 1 .body (controlInput (.kw .return_) 3 9 9 10 leafSuffix) =
    .error ⟨9, "nesting too deep"⟩ := empty_return_underfuel _ _ _ _ _ _

example : (Syn.breakStmt (u := true)).yield leafSuffix.ch =
    some ([[.kw .break_, .punct .semi]], leafSuffix.ch) := break_yield _ _

example : (Syn.continueStmt (u := false)).yield leafSuffix.ch =
    some ([[.kw .continue_, .punct .semi]], leafSuffix.ch) := continue_yield _ _

example : (Syn.returnStmt (k := .body) .none).yield leafSuffix.ch =
    some ([[.kw .return_, .punct .semi]], leafSuffix.ch) := empty_return_yield _ _

end Solidity.Frontend.StatementGrammarH28

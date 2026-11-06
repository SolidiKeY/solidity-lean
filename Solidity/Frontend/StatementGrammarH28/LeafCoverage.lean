import Solidity.Frontend.Checked.Parser

/-!
# Concrete parser coverage for control leaves

These are equations of the existing parser on all suffix states and excess
fuel. Fuel is supplied from each constructor's actual call depth; there is
no successful-parse hypothesis. This module does not cover compound statements
or expressions, and does not assert whole-statement completeness.
-/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- Token location is immaterial to successful parsing; errors use its start. -/
def atToken (t : Tok) (start stop : Nat) : Located := ⟨t, start, stop⟩

def controlInput (t : Tok) (a b c d : Nat) (s : St) : St :=
  { s with ts := atToken t a b :: atToken (.punct .semi) c d :: s.ts }

/-- One statement call suffices for break; suffix and layout are preserved. -/
theorem break_coverage (n : Nat) (u : Bool) (a b c d : Nat) (s : St) :
    stmt (n + 1) ⟨true, u⟩ (controlInput (.kw .break_) a b c d s) =
      .ok (.breakStmt, s) := by rfl

/-- One statement call suffices for continue. -/
theorem continue_coverage (n : Nat) (u : Bool) (a b c d : Nat) (s : St) :
    stmt (n + 1) ⟨true, u⟩ (controlInput (.kw .continue_) a b c d s) =
      .ok (.continueStmt, s) := by rfl

/-- Return additionally calls optExprBefore, so its structural bound is two. -/
theorem empty_return_coverage (n : Nat) (k : SCtx) (a b c d : Nat) (s : St) :
    stmt (n + 2) k (controlInput (.kw .return_) a b c d s) =
      .ok (.returnStmt .none, s) := by rfl

theorem break_outside_loop (n : Nat) (u : Bool) (a b c d : Nat) (s : St) :
    stmt (n + 1) ⟨false, u⟩ (controlInput (.kw .break_) a b c d s) =
      .error ⟨a, "break outside a loop"⟩ := by rfl

theorem continue_outside_loop (n : Nat) (u : Bool) (a b c d : Nat) (s : St) :
    stmt (n + 1) ⟨false, u⟩ (controlInput (.kw .continue_) a b c d s) =
      .error ⟨a, "continue outside a loop"⟩ := by rfl

/-- Checked underfuel control: even an empty return needs the extra call. -/
theorem empty_return_underfuel (k : SCtx) (a b c d : Nat) (s : St) :
    stmt 1 k (controlInput (.kw .return_) a b c d s) =
      .error ⟨c, "nesting too deep"⟩ := by rfl

/-- Zero fuel rejects even a syntactically complete leaf before consumption. -/
theorem control_zero_fuel (k : SCtx) (t : Tok) (a b c d : Nat) (s : St) :
    stmt 0 k (controlInput t a b c d s) =
      .error ⟨a, "nesting too deep"⟩ := by rfl

/-- The concrete parser prefixes above are the existing syntax's actual yields. -/
theorem break_yield (u : Bool) (L : List Choice) :
    (Syn.breakStmt (u := u)).yield L = some ([[.kw .break_, .punct .semi]], L) := by rfl

theorem continue_yield (u : Bool) (L : List Choice) :
    (Syn.continueStmt (u := u)).yield L = some ([[.kw .continue_, .punct .semi]], L) := by rfl

theorem empty_return_yield (k : SCtx) (L : List Choice) :
    (Syn.returnStmt (k := k) .none).yield L = some ([[.kw .return_, .punct .semi]], L) := by rfl

#print axioms break_coverage
#print axioms continue_coverage
#print axioms empty_return_coverage
#print axioms break_outside_loop
#print axioms continue_outside_loop
#print axioms empty_return_underfuel
#print axioms control_zero_fuel
#print axioms break_yield
#print axioms continue_yield
#print axioms empty_return_yield
end Solidity.Frontend.StatementGrammarH28

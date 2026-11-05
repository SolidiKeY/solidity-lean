import Solidity.Frontend.StatementGrammarH28.SyntaxNoSemi
import Solidity.Frontend.StatementGrammarH28.RootContract

/-! Actual boundary uniqueness for the six semicolon-only statement roots.
Do-while is excluded from this *first-semicolon* fragment because its body
can itself contain semicolons. No AST equality or parser completeness claim. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def semiSuffix : List Tok → Option (List Tok)
  | [] => none
  | t :: ts => if t = .punct .semi then some ts else semiSuffix ts

theorem semiFree_scan_frame {xs : List Tok} (h : SemiFree xs) (tail : List Tok) :
    semiSuffix (xs ++ tail) = semiSuffix tail := by
  induction h generalizing tail with
  | empty => rfl
  | token t ht => simp only [List.cons_append, List.nil_append, semiSuffix, ht, ↓reduceIte]
  | append hx hy ihx ihy => rw [List.append_assoc, ihx, ihy]

theorem semiFree_end_split {xs ys rest tail : List Tok}
    (hx : SemiFree xs) (hy : SemiFree ys)
    (he : xs ++ (.punct .semi :: rest) = ys ++ (.punct .semi :: tail)) :
    xs = ys ∧ rest = tail := by
  have scan := congrArg semiSuffix he
  rw [semiFree_scan_frame hx, semiFree_scan_frame hy] at scan
  have suffix : rest = tail := Option.some.inj scan
  subst tail
  exact ⟨List.append_cancel_right he, rfl⟩

def SemiRoot : Root → Bool
  | .simple | .continueLoop | .breakLoop | .returnValue | .emitEvent | .revertError => true
  | _ => false

def SemicolonParts (parts : List (List Tok)) : Prop :=
  ∃ body : List Tok, SemiFree body ∧ parts.flatten = body ++ pu .semi

theorem statement_semicolon_shape {k : SCtx} (s : Syn (.stmt k)) :
    SemiRoot (root s) = true → PrEnsures s.yield SemicolonParts := by
  cases s with
  | simpleStmt simple =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemicolonParts (simple_yield_semiFree simple)
    intro a ha
    exact ensures_pure _ _ ⟨a.flatten, semiFreeParts_flat ha, by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]⟩
  | continueStmt =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ _ ⟨tk .continue_, semiFree_kw _, by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]⟩
  | breakStmt =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ _ ⟨tk .break_, semiFree_kw _, by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]⟩
  | returnStmt e =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemicolonParts (syntax_yield_semiFree e rfl)
    intro a ha
    exact ensures_pure _ _ ⟨tk .return_ ++ a.flatten,
      .append (semiFree_kw _) (semiFreeParts_flat ha), by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]⟩
  | emit e args =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemicolonParts (expression_yield_semiFree e)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemicolonParts (syntax_yield_semiFree args rfl)
    intro b hb
    exact ensures_pure _ _ ⟨tk .emit ++ a.flatten ++ b.flatten,
      .append (.append (semiFree_kw _) (semiFreeParts_flat ha)) (semiFreeParts_flat hb), by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]⟩
  | revert e args =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemicolonParts (expression_yield_semiFree e)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemicolonParts (syntax_yield_semiFree args rfl)
    intro b hb
    exact ensures_pure _ _ ⟨idt "revert" ++ a.flatten ++ b.flatten,
      .append (.append (semiFree_id _) (semiFreeParts_flat ha)) (semiFreeParts_flat hb), by
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]⟩
  | _ => intro h; cases h

/-- Token/suffix uniqueness for arbitrary successful yields of the six roots.
The syntax trees, expressions and layouts need not be equal or parseable. -/
theorem semicolon_statement_prefix_split {k j : SCtx}
    (s : Syn (.stmt k)) (t : Syn (.stmt j))
    (hs : SemiRoot (root s) = true) (ht : SemiRoot (root t) = true)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : s.yield L = some (xs, M)) (hyT : t.yield N = some (ys, P))
    (he : xs.flatten ++ rest = ys.flatten ++ tail) :
    xs.flatten = ys.flatten ∧ rest = tail := by
  obtain ⟨a, ha, ea⟩ := statement_semicolon_shape s hs L xs M hyS
  obtain ⟨b, hb, eb⟩ := statement_semicolon_shape t ht N ys P hyT
  rw [ea, eb] at he
  have eq : a ++ (.punct .semi :: rest) = b ++ (.punct .semi :: tail) := by
    simpa only [pu, List.append_assoc, List.cons_append, List.nil_append] using he
  obtain ⟨body, suffix⟩ := semiFree_end_split ha hb eq
  exact ⟨ea.trans ((congrArg (· ++ pu .semi) body).trans eb.symm), suffix⟩

#print axioms semiFree_scan_frame
#print axioms semiFree_end_split
#print axioms statement_semicolon_shape
#print axioms semicolon_statement_prefix_split
end Solidity.Frontend.StatementGrammarH28

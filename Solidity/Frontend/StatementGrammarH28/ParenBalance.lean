import Solidity.Frontend.Checked.Print

/-! Parenthesis token balance and matching-header splitting. This is a token
predicate, not an AST or expression uniqueness assumption. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive ParenBalanced : List Tok → Prop where
  | empty : ParenBalanced []
  | token (t : Tok) (ho : t ≠ .punct .lparen) (hc : t ≠ .punct .rparen) :
      ParenBalanced [t]
  | append {xs ys : List Tok} : ParenBalanced xs → ParenBalanced ys → ParenBalanced (xs ++ ys)
  | wrap {xs : List Tok} : ParenBalanced xs → ParenBalanced (parens xs)

/-- Return the suffix after the matching closing parenthesis. Zero depth means the
next unmatched closing parenthesis ends this scan. Recursion is on the token list. -/
def parenCloseSuffix : Nat → List Tok → Option (List Tok)
  | _, [] => none
  | d, t :: ts =>
    if t = .punct .lparen then parenCloseSuffix (d + 1) ts
    else if t = .punct .rparen then
      match d with | 0 => some ts | n + 1 => parenCloseSuffix n ts
    else parenCloseSuffix d ts

/-- Balanced content does not change which subsequent closing parenthesis ends a
scan, at any enclosing parenthesis depth and for any suffix. -/
theorem parenBalanced_scan_frame {xs : List Tok} (h : ParenBalanced xs)
    (d : Nat) (tail : List Tok) :
    parenCloseSuffix d (xs ++ tail) = parenCloseSuffix d tail := by
  induction h generalizing d tail with
  | empty => rfl
  | token t ho hc =>
    simp only [List.cons_append, List.nil_append, parenCloseSuffix, ho, hc, ↓reduceIte]
  | append hx hy ihx ihy =>
    rw [List.append_assoc, ihx, ihy]
  | @wrap xs hx ih =>
    simp only [parens, pu, List.cons_append, List.nil_append, List.append_assoc]
    change parenCloseSuffix (d + 1) (xs ++ (.punct .rparen :: tail)) = parenCloseSuffix d tail
    rw [ih]
    rfl

theorem close_after_parenBalanced {xs : List Tok} (h : ParenBalanced xs) (tail : List Tok) :
    parenCloseSuffix 0 (xs ++ (.punct .rparen :: tail)) = some tail := by
  rw [parenBalanced_scan_frame h]
  rfl

/-- Arbitrary parenBalanced parenthesized prefixes have a unique content/suffix split.
This concludes token equality, not equality of syntax trees deriving it. -/
theorem parenBalanced_parenthesized_split {xs ys rest tail : List Tok}
    (hx : ParenBalanced xs) (hy : ParenBalanced ys)
    (h : parens xs ++ rest = parens ys ++ tail) : xs = ys ∧ rest = tail := by
  have inner : xs ++ (.punct .rparen :: rest) = ys ++ (.punct .rparen :: tail) := by
    have heads : (.punct .lparen : Tok) :: (xs ++ (.punct .rparen :: rest)) =
        .punct .lparen :: (ys ++ (.punct .rparen :: tail)) := by
      simpa only [parens, pu, List.cons_append, List.nil_append, List.append_assoc] using h
    exact (List.cons.inj heads).2
  have scan := close_after_parenBalanced hx rest
  rw [inner, close_after_parenBalanced hy tail] at scan
  have suffix : tail = rest := Option.some.inj scan
  subst tail
  exact ⟨List.append_cancel_right inner, rfl⟩

theorem parenBalanced_flatten {parts : List (List Tok)} :
    (∀ part ∈ parts, ParenBalanced part) → ParenBalanced parts.flatten := by
  induction parts with
  | nil => intro _; exact .empty
  | cons head rest ih =>
    intro h
    exact .append (h head (.head _)) (ih (fun part hp => h part (.tail _ hp)))

theorem ParenBalanced.brace {xs : List Tok} (h : ParenBalanced xs) :
    ParenBalanced (braces xs) :=
  .append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) h)
    (.token _ (by intro h; cases h) (by intro h; cases h))

/-- Consume one matching parenthesized header, retaining the exact suffix. -/
def parenHeaderSuffix : List Tok → Option (List Tok)
  | .punct .lparen :: rest => parenCloseSuffix 0 rest
  | _ => none

theorem paren_header_after_balanced {xs : List Tok} (h : ParenBalanced xs) (tail : List Tok) :
    parenHeaderSuffix (parens xs ++ tail) = some tail := by
  simpa only [parens, pu, List.cons_append, List.nil_append, List.append_assoc,
    parenHeaderSuffix] using close_after_parenBalanced h tail

end Solidity.Frontend.StatementGrammarH28

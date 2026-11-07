import Solidity.Frontend.ExpressionUniqueness.TypePrefix

/-!
# Concrete followers of an existing primary expression

The flag is the original primary node's isNew value. Its first postfix can be
call/options, or index/member only after the original not-new guard. Later
postfixes preserve the first token. This is a token predicate, not another AST.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def PostfixFollower (newBase : Bool) (tail : List Tok) : Prop :=
  tail = [] ∨ (∃ rest, tail = .punct .lparen :: rest) ∨
    (∃ rest, tail = .punct .lbrace :: rest) ∨
    (newBase = false ∧ ((∃ rest, tail = .punct .lbrack :: rest) ∨
      (∃ rest, tail = .punct .period :: rest)))

theorem postfixFollower_nil (flag : Bool) : PostfixFollower flag [] := Or.inl rfl

theorem postfixFollower_parens (flag : Bool) (payload : List Tok) : PostfixFollower flag (parens payload) :=
  Or.inr (Or.inl ⟨payload ++ pu .rparen, rfl⟩)

theorem postfixFollower_braces (flag : Bool) (payload : List Tok) : PostfixFollower flag (braces payload) :=
  Or.inr (Or.inr (Or.inl ⟨payload ++ pu .rbrace, rfl⟩))

theorem postfixFollower_square (flag : Bool) (payload : List Tok) (hn : flag = false) :
    PostfixFollower flag (pu .lbrack ++ payload ++ pu .rbrack) :=
  Or.inr (Or.inr (Or.inr ⟨hn, Or.inl ⟨payload ++ pu .rbrack, rfl⟩⟩))

theorem postfixFollower_period (flag : Bool) (word : List Tok) (hn : flag = false) :
    PostfixFollower flag (pu .period ++ word) :=
  Or.inr (Or.inr (Or.inr ⟨hn, Or.inr ⟨word, rfl⟩⟩))

theorem postfixFollower_append (flag : Bool) (before frame : List Tok)
    (h : PostfixFollower flag before) (fresh : before = [] → PostfixFollower flag frame) :
    PostfixFollower flag (before ++ frame) := by
  rcases h with empty | ⟨rest, shape⟩ | ⟨rest, shape⟩ | ⟨notNew, square | period⟩
  · rw [empty, List.nil_append]
    exact fresh empty
  · rw [shape]
    exact Or.inr (Or.inl ⟨rest ++ frame, rfl⟩)
  · rw [shape]
    exact Or.inr (Or.inr (Or.inl ⟨rest ++ frame, rfl⟩))
  · obtain ⟨rest, shape⟩ := square
    rw [shape]
    exact Or.inr (Or.inr (Or.inr ⟨notNew, Or.inl ⟨rest ++ frame, rfl⟩⟩))
  · obtain ⟨rest, shape⟩ := period
    rw [shape]
    exact Or.inr (Or.inr (Or.inr ⟨notNew, Or.inr ⟨rest ++ frame, rfl⟩⟩))

theorem word_append_nonempty_right (before frame : List Tok) (h : frame ≠ []) : before ++ frame ≠ [] := by
  cases before with
  | nil => exact h
  | cons t ts => intro empty; cases empty

theorem new_postfixFollower_typeBoundary (tail : List Tok) (h : PostfixFollower true tail) : TypeBoundary tail := by
  rcases h with rfl | ⟨rest, rfl⟩ | ⟨rest, rfl⟩ | ⟨bad, other⟩
  · exact ⟨tokenBoundary_nil _, tokenBoundary_nil _⟩
  · exact ⟨tokenBoundary_cons typeAtomForbidden (.punct .lparen) rest rfl,
      tokenBoundary_cons isLeftSquare (.punct .lparen) rest rfl⟩
  · exact ⟨tokenBoundary_cons typeAtomForbidden (.punct .lbrace) rest rfl,
      tokenBoundary_cons isLeftSquare (.punct .lbrace) rest rfl⟩
  · cases bad

theorem postfixFollower_tokenBoundary (p : Tok → Bool) (flag : Bool) (tail : List Tok)
    (hp : p (.punct .lparen) = false) (hb : p (.punct .lbrace) = false)
    (hs : p (.punct .lbrack) = false) (hd : p (.punct .period) = false)
    (h : PostfixFollower flag tail) : TokenBoundary p tail := by
  rcases h with rfl | ⟨rest, rfl⟩ | ⟨rest, rfl⟩ | ⟨notNew, square | period⟩
  · exact tokenBoundary_nil _
  · exact tokenBoundary_cons p _ _ hp
  · exact tokenBoundary_cons p _ _ hb
  · obtain ⟨rest, rfl⟩ := square
    exact tokenBoundary_cons p _ _ hs
  · obtain ⟨rest, rfl⟩ := period
    exact tokenBoundary_cons p _ _ hd

end Solidity.Frontend.ExpressionUniqueness

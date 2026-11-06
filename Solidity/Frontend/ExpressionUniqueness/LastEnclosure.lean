import Solidity.Frontend.ExpressionUniqueness.DelimiterReconstruction
import Solidity.Frontend.ExpressionUniqueness.ReverseSplit

/-!
# Trailing balanced enclosures reconstruct their prefix and payload

Mirror the existing token word, use the established first enclosing cut, and
mirror back. Payload balance is sufficient; the preceding word is arbitrary.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem last_enclosed_cut_unique (k : Bracket) (base payload base' payload' : List Tok)
    (hp : Balanced payload) (hp' : Balanced payload')
    (he : base ++ openTok k :: (payload ++ [closeTok k]) =
      base' ++ openTok k :: (payload' ++ [closeTok k])) :
    base = base' ∧ payload = payload' := by
  have mirrored := congrArg mirrorWord he
  simp only [mirrorWord_append, mirrorWord_cons, mirrorTok_open,
    mirrorTok_close, List.cons_append, List.nil_append, List.append_assoc] at mirrored
  obtain ⟨inner, prefixWord⟩ := enclosed_payload_unique k
    (mirrorWord payload) (mirrorWord payload') (mirrorWord base) (mirrorWord base')
    (balanced_mirror payload hp) (balanced_mirror payload' hp') mirrored
  exact ⟨mirrorWord_injective base base' prefixWord, mirrorWord_injective payload payload' inner⟩

theorem last_parens_cut_unique (base payload base' payload' : List Tok)
    (hp : Balanced payload) (hp' : Balanced payload')
    (he : base ++ parens payload = base' ++ parens payload') :
    base = base' ∧ payload = payload' := by
  apply last_enclosed_cut_unique .round base payload base' payload' hp hp'
  simpa only [parens, pu, openTok, closeTok, List.cons_append, List.nil_append,
    List.append_assoc] using he

theorem last_square_cut_unique (base payload base' payload' : List Tok)
    (hp : Balanced payload) (hp' : Balanced payload')
    (he : base ++ pu .lbrack ++ payload ++ pu .rbrack =
      base' ++ pu .lbrack ++ payload' ++ pu .rbrack) :
    base = base' ∧ payload = payload' := by
  apply last_enclosed_cut_unique .square base payload base' payload' hp hp'
  simpa only [pu, openTok, closeTok, List.append_assoc, List.singleton_append] using he

theorem last_braces_cut_unique (base payload base' payload' : List Tok)
    (hp : Balanced payload) (hp' : Balanced payload')
    (he : base ++ braces payload = base' ++ braces payload') :
    base = base' ∧ payload = payload' := by
  apply last_enclosed_cut_unique .curly base payload base' payload' hp hp'
  simpa only [braces, pu, openTok, closeTok, List.cons_append, List.nil_append,
    List.append_assoc] using he

end Solidity.Frontend.ExpressionUniqueness

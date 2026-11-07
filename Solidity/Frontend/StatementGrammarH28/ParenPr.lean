import Solidity.Frontend.StatementGrammarH28.ParenBalance
import Solidity.Frontend.StatementGrammarH28.BalancePr

/-! H31 proof-only parenthesis invariants for immutable printer combinators. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def ParenBalancedParts (parts : List (List Tok)) : Prop := ∀ p ∈ parts, ParenBalanced p

theorem parenBalancedParts_nil : ParenBalancedParts [] := fun _ h => nomatch h

theorem parenBalancedParts_cons {p : List Tok} {parts : List (List Tok)}
    (hp : ParenBalanced p) (ht : ParenBalancedParts parts) : ParenBalancedParts (p :: parts) := by
  intro x hx
  cases hx with
  | head => exact hp
  | tail _ h => exact ht x h

theorem parenBalancedParts_singleton {p : List Tok} (hp : ParenBalanced p) : ParenBalancedParts [p] :=
  parenBalancedParts_cons hp parenBalancedParts_nil

theorem parenBalancedParts_flat {parts : List (List Tok)} (h : ParenBalancedParts parts) :
    ParenBalanced parts.flatten := parenBalanced_flatten h

theorem parenBalanced_kw (k : Kw) : ParenBalanced (tk k) :=
  .token _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_id (s : String) : ParenBalanced (idt s) :=
  .token _ (by intro h; cases h) (by intro h; cases h)

theorem parenBalanced_punct (p : Punct) (ho : p ≠ .lparen) (hc : p ≠ .rparen) :
    ParenBalanced (pu p) :=
  .token _ (by intro h; cases h; exact ho rfl) (by intro h; cases h; exact hc rfl)

theorem parenBalanced_parens {ts : List Tok} (h : ParenBalanced ts) :
    ParenBalanced (parens ts) := .wrap h

theorem parenBalanced_optToks {α : Type} (f : α → List Tok) (h : ∀ a, ParenBalanced (f a))
    (a : Option α) : ParenBalanced (optToks f a) := by
  cases a with
  | none => exact .empty
  | some a => exact h a

theorem parenBalanced_intersperse (parts : List (List Tok)) (sep : List Tok)
    (hp : ParenBalancedParts parts) (hs : ParenBalanced sep) :
    ParenBalancedParts (parts.intersperse sep) := by
  induction parts with
  | nil => exact parenBalancedParts_nil
  | cons p ps ih =>
    have head := hp p (.head _)
    have tail : ParenBalancedParts ps := fun x hx => hp x (.tail _ hx)
    cases ps with
    | nil => exact parenBalancedParts_singleton head
    | cons q qs =>
      exact parenBalancedParts_cons head (parenBalancedParts_cons hs (ih tail))

theorem parenBalanced_commaSep (parts : List (List Tok)) (hp : ParenBalancedParts parts) :
    ParenBalanced (commaSep parts) :=
  parenBalancedParts_flat (parenBalanced_intersperse parts (pu .comma) hp
    (parenBalanced_punct .comma (by intro h; cases h) (by intro h; cases h)))

theorem parenBalanced_flatMap_prefix (parts : List (List Tok)) (leader : List Tok)
    (hp : ParenBalancedParts parts) (hs : ParenBalanced leader) :
    ParenBalanced (parts.flatMap (leader ++ ·)) := by
  induction parts with
  | nil => exact .empty
  | cons p ps ih =>
    exact .append (.append hs (hp p (.head _)))
      (ih (fun x hx => hp x (.tail _ hx)))

theorem parenBalanced_map_tokens {α : Type} (f : α → Tok) (xs : List α)
    (h : ∀ x, ParenBalanced [f x]) : ParenBalanced (xs.map f) := by
  induction xs with
  | nil => exact .empty
  | cons x xs ih => exact .append (h x) ih

theorem parenBalancedParts_map {α : Type} (f : α → List Tok) (xs : List α)
    (h : ∀ x, ParenBalanced (f x)) : ParenBalancedParts (xs.map f) := by
  intro p hp
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hp
  subst p
  exact h x

theorem parenBalancedParts_replicate (n : Nat) (ts : List Tok) (h : ParenBalanced ts) :
    ParenBalancedParts (List.replicate n ts) := by
  intro p hp
  have he : p = ts := (List.mem_replicate.mp hp).2
  subst p
  exact h

theorem fragsP_parenBalanced (mk : Bytes → Tok) (bs : Bytes)
    (hm : ∀ bytes, ParenBalanced [mk bytes]) : PrEnsures (fragsP mk bs) ParenBalanced := by
  unfold fragsP
  apply ensures_bind
  intro choice
  cases choice with
  | attrs _ => exact ensures_lift_none _
  | layoutFirst _ => exact ensures_lift_none _
  | frags lens =>
    cases lens with
    | nil => exact ensures_lift_none _
    | cons n ns =>
      apply ensures_bind
      intro cs
      exact ensures_pure _ _ (parenBalanced_map_tokens mk cs hm)

theorem parenBalanced_choice (b : Bool) {xs ys : List Tok}
    (hx : ParenBalanced xs) (hy : ParenBalanced ys) : ParenBalanced (if b then xs else ys) := by
  cases b with
  | false => exact hy
  | true => exact hx

theorem parenBalanced_optional (parts : List (List Tok)) (hp : ParenBalancedParts parts)
    (f : List Tok → List Tok) (hf : ∀ ts, ParenBalanced ts → ParenBalanced (f ts)) :
    ParenBalanced (optionalChunk parts f) := by
  cases parts with
  | nil => exact .empty
  | cons p ps =>
    cases ps with
    | nil => exact hf p (hp p (.head _))
    | cons q qs => exact .empty

end Solidity.Frontend.StatementGrammarH28

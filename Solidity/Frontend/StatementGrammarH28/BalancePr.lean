import Solidity.Frontend.StatementGrammarH28.Balance
import Solidity.Frontend.StatementGrammarH28.TokenRoot

/-! H31 proof-only delimiter invariants for immutable printer computations.
No expression uniqueness or producer interface changes. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def BalancedParts (parts : List (List Tok)) : Prop := ∀ p ∈ parts, BraceBalanced p

theorem balancedParts_nil : BalancedParts [] := fun _ h => nomatch h

theorem balancedParts_cons {p : List Tok} {parts : List (List Tok)}
    (hp : BraceBalanced p) (ht : BalancedParts parts) : BalancedParts (p :: parts) := by
  intro x hx
  cases hx with
  | head => exact hp
  | tail _ h => exact ht x h

theorem balancedParts_singleton {p : List Tok} (hp : BraceBalanced p) : BalancedParts [p] :=
  balancedParts_cons hp balancedParts_nil

theorem balancedParts_flat {parts : List (List Tok)} (h : BalancedParts parts) :
    BraceBalanced parts.flatten := balanced_flatten h

theorem ensures_bind_checked {α β : Type} (p : Pr α) (f : α → Pr β)
    (P : α → Prop) (Q : β → Prop) (hp : PrEnsures p P)
    (hf : ∀ a, P a → PrEnsures (f a) Q) : PrEnsures (p >>= f) Q := by
  intro L b M h
  change (p L).bind (fun (a, N) => f a N) = some (b, M) at h
  cases he : p L with
  | none => rw [he] at h; cases h
  | some pair =>
    obtain ⟨a, N⟩ := pair
    rw [he] at h
    exact hf a (hp L a N he) N b M h

theorem balanced_kw (k : Kw) : BraceBalanced (tk k) :=
  .token _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_id (s : String) : BraceBalanced (idt s) :=
  .token _ (by intro h; cases h) (by intro h; cases h)

theorem balanced_punct (p : Punct) (ho : p ≠ .lbrace) (hc : p ≠ .rbrace) :
    BraceBalanced (pu p) :=
  .token _ (by intro h; cases h; exact ho rfl) (by intro h; cases h; exact hc rfl)

theorem balanced_parens {ts : List Tok} (h : BraceBalanced ts) : BraceBalanced (parens ts) :=
  .append (.append (balanced_punct .lparen (by intro h; cases h) (by intro h; cases h)) h)
    (balanced_punct .rparen (by intro h; cases h) (by intro h; cases h))

theorem balanced_optToks {α : Type} (f : α → List Tok) (h : ∀ a, BraceBalanced (f a))
    (a : Option α) : BraceBalanced (optToks f a) := by
  cases a with
  | none => exact .empty
  | some a => exact h a

theorem balanced_intersperse (parts : List (List Tok)) (sep : List Tok)
    (hp : BalancedParts parts) (hs : BraceBalanced sep) :
    BalancedParts (parts.intersperse sep) := by
  induction parts with
  | nil => exact balancedParts_nil
  | cons p ps ih =>
    have head := hp p (.head _)
    have tail : BalancedParts ps := fun x hx => hp x (.tail _ hx)
    cases ps with
    | nil => exact balancedParts_singleton head
    | cons q qs =>
      exact balancedParts_cons head (balancedParts_cons hs (ih tail))

theorem balanced_commaSep (parts : List (List Tok)) (hp : BalancedParts parts) :
    BraceBalanced (commaSep parts) :=
  balancedParts_flat (balanced_intersperse parts (pu .comma) hp
    (balanced_punct .comma (by intro h; cases h) (by intro h; cases h)))

theorem balanced_flatMap_prefix (parts : List (List Tok)) (leader : List Tok)
    (hp : BalancedParts parts) (hs : BraceBalanced leader) :
    BraceBalanced (parts.flatMap (leader ++ ·)) := by
  induction parts with
  | nil => exact .empty
  | cons p ps ih =>
    exact .append (.append hs (hp p (.head _)))
      (ih (fun x hx => hp x (.tail _ hx)))

theorem balanced_map_tokens {α : Type} (f : α → Tok) (xs : List α)
    (h : ∀ x, BraceBalanced [f x]) : BraceBalanced (xs.map f) := by
  induction xs with
  | nil => exact .empty
  | cons x xs ih => exact .append (h x) ih

theorem balancedParts_map {α : Type} (f : α → List Tok) (xs : List α)
    (h : ∀ x, BraceBalanced (f x)) : BalancedParts (xs.map f) := by
  intro p hp
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hp
  subst p
  exact h x

theorem balancedParts_replicate (n : Nat) (ts : List Tok) (h : BraceBalanced ts) :
    BalancedParts (List.replicate n ts) := by
  intro p hp
  have he : p = ts := (List.mem_replicate.mp hp).2
  subst p
  exact h

theorem ensures_lift_none {α : Type} (P : α → Prop) :
    PrEnsures (Pr.lift (none : Option α)) P := by
  intro L a M h
  cases h

theorem fragsP_balanced (mk : Bytes → Tok) (bs : Bytes)
    (hm : ∀ bytes, BraceBalanced [mk bytes]) : PrEnsures (fragsP mk bs) BraceBalanced := by
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
      exact ensures_pure _ _ (balanced_map_tokens mk cs hm)

theorem balanced_choice (b : Bool) {xs ys : List Tok}
    (hx : BraceBalanced xs) (hy : BraceBalanced ys) : BraceBalanced (if b then xs else ys) := by
  cases b with
  | false => exact hy
  | true => exact hx

def optionalChunk (parts : List (List Tok)) (f : List Tok → List Tok) : List Tok :=
  match parts with | [ts] => f ts | _ => []

theorem balanced_optional (parts : List (List Tok)) (hp : BalancedParts parts)
    (f : List Tok → List Tok) (hf : ∀ ts, BraceBalanced ts → BraceBalanced (f ts)) :
    BraceBalanced (optionalChunk parts f) := by
  cases parts with
  | nil => exact .empty
  | cons p ps =>
    cases ps with
    | nil => exact hf p (hp p (.head _))
    | cons q qs => exact .empty

#print axioms balanced_choice
#print axioms balanced_optional
#print axioms balanced_map_tokens
#print axioms balancedParts_map
#print axioms balancedParts_replicate
#print axioms fragsP_balanced
#print axioms ensures_bind_checked
#print axioms balanced_intersperse
#print axioms balanced_commaSep
#print axioms balanced_flatMap_prefix
end Solidity.Frontend.StatementGrammarH28

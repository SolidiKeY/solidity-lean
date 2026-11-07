import Solidity.Frontend.StatementGrammarH28.BalancePr

/-! H31 token absence for existing atom yields. Token predicates only;
no new syntax tree, expression uniqueness or producer change. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive SemiFree : List Tok → Prop where
  | empty : SemiFree []
  | token (t : Tok) (h : t ≠ .punct .semi) : SemiFree [t]
  | append {xs ys : List Tok} : SemiFree xs → SemiFree ys → SemiFree (xs ++ ys)

theorem semiFree_flatten {parts : List (List Tok)}
    (h : ∀ part ∈ parts, SemiFree part) : SemiFree parts.flatten := by
  induction parts with
  | nil => exact .empty
  | cons p ps ih =>
    exact .append (h p (.head _)) (ih (fun part hp => h part (.tail _ hp)))

theorem SemiFree.wrap {xs : List Tok} (h : SemiFree xs) : SemiFree (braces xs) :=
  .append (.append (.token _ (by intro h; cases h)) h) (.token _ (by intro h; cases h))

def SemiFreeParts (parts : List (List Tok)) : Prop := ∀ p ∈ parts, SemiFree p

theorem semiFreeParts_nil : SemiFreeParts [] := fun _ h => nomatch h

theorem semiFreeParts_cons {p : List Tok} {parts : List (List Tok)}
    (hp : SemiFree p) (ht : SemiFreeParts parts) : SemiFreeParts (p :: parts) := by
  intro x hx
  cases hx with
  | head => exact hp
  | tail _ h => exact ht x h

theorem semiFreeParts_singleton {p : List Tok} (hp : SemiFree p) : SemiFreeParts [p] :=
  semiFreeParts_cons hp semiFreeParts_nil

theorem semiFreeParts_flat {parts : List (List Tok)} (h : SemiFreeParts parts) :
    SemiFree parts.flatten := semiFree_flatten h

theorem semiFree_kw (k : Kw) : SemiFree (tk k) :=
  .token _ (by intro h; cases h)

theorem semiFree_id (s : String) : SemiFree (idt s) :=
  .token _ (by intro h; cases h)

theorem semiFree_punct (p : Punct) (hs : p ≠ .semi) : SemiFree (pu p) :=
  .token _ (by intro h; cases h; exact hs rfl)

theorem semiFree_parens {ts : List Tok} (h : SemiFree ts) : SemiFree (parens ts) :=
  .append (.append (semiFree_punct .lparen (by intro h; cases h)) h)
    (semiFree_punct .rparen (by intro h; cases h))

theorem semiFree_optToks {α : Type} (f : α → List Tok) (h : ∀ a, SemiFree (f a))
    (a : Option α) : SemiFree (optToks f a) := by
  cases a with
  | none => exact .empty
  | some a => exact h a

theorem semiFree_intersperse (parts : List (List Tok)) (sep : List Tok)
    (hp : SemiFreeParts parts) (hs : SemiFree sep) :
    SemiFreeParts (parts.intersperse sep) := by
  induction parts with
  | nil => exact semiFreeParts_nil
  | cons p ps ih =>
    have head := hp p (.head _)
    have tail : SemiFreeParts ps := fun x hx => hp x (.tail _ hx)
    cases ps with
    | nil => exact semiFreeParts_singleton head
    | cons q qs =>
      exact semiFreeParts_cons head (semiFreeParts_cons hs (ih tail))

theorem semiFree_commaSep (parts : List (List Tok)) (hp : SemiFreeParts parts) :
    SemiFree (commaSep parts) :=
  semiFreeParts_flat (semiFree_intersperse parts (pu .comma) hp
    (semiFree_punct .comma (by intro h; cases h)))

theorem semiFree_flatMap_prefix (parts : List (List Tok)) (leader : List Tok)
    (hp : SemiFreeParts parts) (hs : SemiFree leader) :
    SemiFree (parts.flatMap (leader ++ ·)) := by
  induction parts with
  | nil => exact .empty
  | cons p ps ih =>
    exact .append (.append hs (hp p (.head _)))
      (ih (fun x hx => hp x (.tail _ hx)))

theorem semiFree_map_tokens {α : Type} (f : α → Tok) (xs : List α)
    (h : ∀ x, SemiFree [f x]) : SemiFree (xs.map f) := by
  induction xs with
  | nil => exact .empty
  | cons x xs ih => exact .append (h x) ih

theorem semiFreeParts_map {α : Type} (f : α → List Tok) (xs : List α)
    (h : ∀ x, SemiFree (f x)) : SemiFreeParts (xs.map f) := by
  intro p hp
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hp
  subst p
  exact h x

theorem semiFreeParts_replicate (n : Nat) (ts : List Tok) (h : SemiFree ts) :
    SemiFreeParts (List.replicate n ts) := by
  intro p hp
  have he : p = ts := (List.mem_replicate.mp hp).2
  subst p
  exact h

theorem fragsP_semiFree (mk : Bytes → Tok) (bs : Bytes)
    (hm : ∀ bytes, SemiFree [mk bytes]) : PrEnsures (fragsP mk bs) SemiFree := by
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
      exact ensures_pure _ _ (semiFree_map_tokens mk cs hm)

theorem semiFree_choice (b : Bool) {xs ys : List Tok}
    (hx : SemiFree xs) (hy : SemiFree ys) : SemiFree (if b then xs else ys) := by
  cases b with
  | false => exact hy
  | true => exact hx

theorem semiFree_optional (parts : List (List Tok)) (hp : SemiFreeParts parts)
    (f : List Tok → List Tok) (hf : ∀ ts, SemiFree ts → SemiFree (f ts)) :
    SemiFree (optionalChunk parts f) := by
  cases parts with
  | nil => exact .empty
  | cons p ps =>
    cases ps with
    | nil => exact hf p (hp p (.head _))
    | cons q qs => exact .empty

end Solidity.Frontend.StatementGrammarH28

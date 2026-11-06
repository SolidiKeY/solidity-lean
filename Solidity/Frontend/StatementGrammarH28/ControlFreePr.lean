import Solidity.Frontend.StatementGrammarH28.SyntaxNoSemi
import Solidity.Frontend.StatementGrammarH28.BoundaryHeadPr

/-! Proof-only absence of actual else/catch/unchecked tokens throughout atoms.
Uses the existing continuation predicate and atom-category footprint; no new
syntax representation, expression uniqueness or producer implementation. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive ControlFree : List Tok → Prop where
  | empty : ControlFree []
  | token (t : Tok) (h : boundaryToken t = false) : ControlFree [t]
  | append {xs ys : List Tok} : ControlFree xs → ControlFree ys → ControlFree (xs ++ ys)

theorem controlFree_flatten {parts : List (List Tok)}
    (h : ∀ part ∈ parts, ControlFree part) : ControlFree parts.flatten := by
  induction parts with
  | nil => exact .empty
  | cons p ps ih =>
    exact .append (h p (.head _)) (ih (fun part hp => h part (.tail _ hp)))

theorem ControlFree.wrap {xs : List Tok} (h : ControlFree xs) : ControlFree (braces xs) :=
  .append (.append (.token _ rfl) h) (.token _ rfl)

def ControlFreeParts (parts : List (List Tok)) : Prop := ∀ p ∈ parts, ControlFree p

theorem controlFreeParts_nil : ControlFreeParts [] := fun _ h => nomatch h

theorem controlFreeParts_cons {p : List Tok} {parts : List (List Tok)}
    (hp : ControlFree p) (ht : ControlFreeParts parts) : ControlFreeParts (p :: parts) := by
  intro x hx
  cases hx with
  | head => exact hp
  | tail _ h => exact ht x h

theorem controlFreeParts_singleton {p : List Tok} (hp : ControlFree p) : ControlFreeParts [p] :=
  controlFreeParts_cons hp controlFreeParts_nil

theorem controlFreeParts_flat {parts : List (List Tok)} (h : ControlFreeParts parts) :
    ControlFree parts.flatten := controlFree_flatten h

theorem controlFree_kw (k : Kw) (hk : boundaryToken (.kw k) = false) : ControlFree (tk k) :=
  .token _ hk

theorem controlFree_id (s : String) : ControlFree (idt s) :=
  .token _ rfl

theorem controlFree_punct (p : Punct) : ControlFree (pu p) := .token _ rfl

theorem controlFree_parens {ts : List Tok} (h : ControlFree ts) : ControlFree (parens ts) :=
  .append (.append (controlFree_punct .lparen) h)
    (controlFree_punct .rparen)

theorem controlFree_optToks {α : Type} (f : α → List Tok) (h : ∀ a, ControlFree (f a))
    (a : Option α) : ControlFree (optToks f a) := by
  cases a with
  | none => exact .empty
  | some a => exact h a

theorem controlFree_intersperse (parts : List (List Tok)) (sep : List Tok)
    (hp : ControlFreeParts parts) (hs : ControlFree sep) :
    ControlFreeParts (parts.intersperse sep) := by
  induction parts with
  | nil => exact controlFreeParts_nil
  | cons p ps ih =>
    have head := hp p (.head _)
    have tail : ControlFreeParts ps := fun x hx => hp x (.tail _ hx)
    cases ps with
    | nil => exact controlFreeParts_singleton head
    | cons q qs =>
      exact controlFreeParts_cons head (controlFreeParts_cons hs (ih tail))

theorem controlFree_commaSep (parts : List (List Tok)) (hp : ControlFreeParts parts) :
    ControlFree (commaSep parts) :=
  controlFreeParts_flat (controlFree_intersperse parts (pu .comma) hp
    (controlFree_punct .comma))

theorem controlFree_flatMap_prefix (parts : List (List Tok)) (leader : List Tok)
    (hp : ControlFreeParts parts) (hs : ControlFree leader) :
    ControlFree (parts.flatMap (leader ++ ·)) := by
  induction parts with
  | nil => exact .empty
  | cons p ps ih =>
    exact .append (.append hs (hp p (.head _)))
      (ih (fun x hx => hp x (.tail _ hx)))

theorem controlFree_map_tokens {α : Type} (f : α → Tok) (xs : List α)
    (h : ∀ x, ControlFree [f x]) : ControlFree (xs.map f) := by
  induction xs with
  | nil => exact .empty
  | cons x xs ih => exact .append (h x) ih

theorem controlFreeParts_map {α : Type} (f : α → List Tok) (xs : List α)
    (h : ∀ x, ControlFree (f x)) : ControlFreeParts (xs.map f) := by
  intro p hp
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hp
  subst p
  exact h x

theorem controlFreeParts_replicate (n : Nat) (ts : List Tok) (h : ControlFree ts) :
    ControlFreeParts (List.replicate n ts) := by
  intro p hp
  have he : p = ts := (List.mem_replicate.mp hp).2
  subst p
  exact h

theorem fragsP_controlFree (mk : Bytes → Tok) (bs : Bytes)
    (hm : ∀ bytes, ControlFree [mk bytes]) : PrEnsures (fragsP mk bs) ControlFree := by
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
      exact ensures_pure _ _ (controlFree_map_tokens mk cs hm)

theorem controlFree_choice (b : Bool) {xs ys : List Tok}
    (hx : ControlFree xs) (hy : ControlFree ys) : ControlFree (if b then xs else ys) := by
  cases b with
  | false => exact hy
  | true => exact hx

theorem controlFree_optional (parts : List (List Tok)) (hp : ControlFreeParts parts)
    (f : List Tok → List Tok) (hf : ∀ ts, ControlFree ts → ControlFree (f ts)) :
    ControlFree (optionalChunk parts f) := by
  cases parts with
  | nil => exact .empty
  | cons p ps =>
    cases ps with
    | nil => exact hf p (hp p (.head _))
    | cons q qs => exact .empty

theorem controlFree_no_boundary {ts : List Tok} (h : ControlFree ts) (t : Tok)
    (hb : boundaryToken t = true) : t ∉ ts := by
  induction h with
  | empty => intro bad; cases bad
  | token tok ht =>
    intro hm
    have eq : t = tok := List.mem_singleton.mp hm
    subst tok
    rw [hb] at ht
    cases ht
  | append hx hy ihx ihy =>
    intro hm
    cases List.mem_append.mp hm with
    | inl hm => exact ihx hm
    | inr hm => exact ihy hm

end Solidity.Frontend.StatementGrammarH28

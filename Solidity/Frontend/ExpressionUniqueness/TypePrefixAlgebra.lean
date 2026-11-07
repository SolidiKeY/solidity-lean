import Solidity.Frontend.ExpressionUniqueness.LastEnclosure

/-!
# Maximal token runs and array-bracket spines

These are token boundary lemmas, not a second AST or a producer interface.
The type/primary certificate results must derive the concrete follower conditions
internally. No uniqueness or desired root split is an assumption here.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def AllTokens (p : Tok → Bool) (ts : List Tok) : Prop := ∀ t, t ∈ ts → p t = true

def TokenBoundary (p : Tok → Bool) (tail : List Tok) : Prop :=
  ∀ t rest, tail = t :: rest → p t = false

theorem tokenBoundary_nil (p : Tok → Bool) : TokenBoundary p [] := by
  intro t rest h
  cases h

theorem maximal_token_run_unique (p : Tok → Bool) (xs ys tail tail' : List Tok)
    (hx : AllTokens p xs) (hy : AllTokens p ys)
    (hb : TokenBoundary p tail) (hb' : TokenBoundary p tail')
    (he : xs ++ tail = ys ++ tail') : xs = ys ∧ tail = tail' := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, he⟩
    | cons t ts =>
      have hit : p t = true := hy t (List.mem_cons.mpr (Or.inl rfl))
      have miss : p t = false := hb t (ts ++ tail') he
      rw [hit] at miss
      cases miss
  | cons t ts ih =>
    cases ys with
    | nil =>
      have hit : p t = true := hx t (List.mem_cons.mpr (Or.inl rfl))
      have miss : p t = false := hb' t (ts ++ tail) he.symm
      rw [hit] at miss
      cases miss
    | cons u us =>
      obtain ⟨token, remaining⟩ := List.cons.inj he
      subst u
      obtain ⟨prefixWords, followingWords⟩ := ih us
        (fun v hv => hx v (List.mem_cons.mpr (Or.inr hv)))
        (fun v hv => hy v (List.mem_cons.mpr (Or.inr hv))) remaining
      exact ⟨congrArg (List.cons t) prefixWords, followingWords⟩

def squareWords (payloads : List (List Tok)) : List Tok :=
  payloads.flatMap fun payload => pu .lbrack ++ payload ++ pu .rbrack

def isLeftSquare : Tok → Bool
  | .punct .lbrack => true
  | _ => false

theorem squareWords_nil : squareWords [] = [] := rfl

theorem squareWords_cons (payload : List Tok) (rest : List (List Tok)) :
    squareWords (payload :: rest) = pu .lbrack ++ payload ++ pu .rbrack ++ squareWords rest := rfl

theorem squareWords_append (xs ys : List (List Tok)) :
    squareWords (xs ++ ys) = squareWords xs ++ squareWords ys := by
  simp only [squareWords, List.flatMap_append]

theorem squareWords_boundary (p : Tok → Bool) (payloads : List (List Tok)) (tail : List Tok)
    (hp : p (.punct .lbrack) = false) (hb : TokenBoundary p tail) :
    TokenBoundary p (squareWords payloads ++ tail) := by
  cases payloads with
  | nil => exact hb
  | cons first rest =>
    intro t suffix he
    have token : .punct .lbrack = t := (List.cons.inj he).1
    rw [← token]
    exact hp

theorem squareWords_cut_unique (xs ys : List (List Tok)) (tail tail' : List Tok)
    (hx : BalancedItems xs) (hy : BalancedItems ys)
    (hb : TokenBoundary isLeftSquare tail) (hb' : TokenBoundary isLeftSquare tail')
    (he : squareWords xs ++ tail = squareWords ys ++ tail') : xs = ys ∧ tail = tail' := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, he⟩
    | cons first rest =>
      have bad : isLeftSquare (.punct .lbrack) = false := hb (.punct .lbrack) _ he
      cases bad
  | cons first rest ih =>
    cases ys with
    | nil =>
      have bad : isLeftSquare (.punct .lbrack) = false := hb' (.punct .lbrack) _ he.symm
      cases bad
    | cons first' rest' =>
      have enclosed : openTok .square :: (first ++ closeTok .square :: (squareWords rest ++ tail)) =
          openTok .square :: (first' ++ closeTok .square :: (squareWords rest' ++ tail')) := by
        simpa only [squareWords_cons, pu, openTok, closeTok, List.append_assoc,
          List.singleton_append] using he
      obtain ⟨payload, remaining⟩ := enclosed_payload_unique .square first first'
        (squareWords rest ++ tail) (squareWords rest' ++ tail')
        (hx first (List.mem_cons.mpr (Or.inl rfl))) (hy first' (List.mem_cons.mpr (Or.inl rfl))) enclosed
      obtain ⟨spines, followingWords⟩ := ih rest'
        (fun word hw => hx word (List.mem_cons.mpr (Or.inr hw)))
        (fun word hw => hy word (List.mem_cons.mpr (Or.inr hw))) remaining
      exact ⟨by rw [payload, spines], followingWords⟩

def typeAttributeToken : Tok → Bool
  | .kw .internal | .kw .external | .kw .public_ | .kw .private_
  | .kw .pure | .kw .view | .kw .payable => true
  | _ => false

def typeAtomForbidden : Tok → Bool
  | .punct .period | .kw .returns => true
  | t => typeAttributeToken t

def TypeAtomBoundary (tail : List Tok) : Prop := TokenBoundary typeAtomForbidden tail

def TypeBoundary (tail : List Tok) : Prop :=
  TypeAtomBoundary tail ∧ TokenBoundary isLeftSquare tail

theorem typeAtomBoundary_squareWords (payloads : List (List Tok)) (tail : List Tok)
    (hb : TypeBoundary tail) : TypeAtomBoundary (squareWords payloads ++ tail) :=
  squareWords_boundary typeAtomForbidden payloads tail rfl hb.1

end Solidity.Frontend.ExpressionUniqueness

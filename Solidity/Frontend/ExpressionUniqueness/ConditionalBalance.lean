import Solidity.Frontend.ExpressionUniqueness.OperandMode

/-!
# Top-level conditional punctuation balance

A delimiter stack hides bracket interiors. Outside brackets a natural-number
counter pairs question marks with colons; an unmatched colon fails. The state
contains tokens' delimiter/count information only, never an expression tree.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Frontend.Checked

def QState : Type := List Bracket × Nat

def qToken (depth : Nat) : Tok → Option Nat
  | .punct .question => some (depth + 1)
  | .punct .colon => match depth with | 0 => none | n + 1 => some n
  | _ => some depth

def qStep (state : QState) (t : Tok) : Option QState :=
  (step state.1 t).bind fun next =>
    if state.1.isEmpty && next.isEmpty then (qToken state.2 t).map fun n => (next, n)
    else some (next, state.2)

def qRun (state : QState) : List Tok → Option QState
  | [] => some state
  | t :: ts => (qStep state t).bind fun next => qRun next ts

def QBalanced (ts : List Tok) : Prop :=
  ∀ depth, qRun ([], depth) ts = some ([], depth)

theorem qStep_open (k : Bracket) (stack : List Bracket) (depth : Nat) :
    qStep (stack, depth) (openTok k) = some (k :: stack, depth) := by
  cases stack <;> simp only [qStep, step_open, Option.bind_some,
    List.isEmpty_nil, List.isEmpty_cons, Bool.and_false, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

theorem qStep_close (k : Bracket) (stack : List Bracket) (depth : Nat) :
    qStep (k :: stack, depth) (closeTok k) = some (stack, depth) := by
  simp only [qStep, step_close, Option.bind_some, List.isEmpty_cons,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem qStep_atom (t : Tok) (hb : bracket t = none) (depth : Nat) :
    qStep ([], depth) t = (qToken depth t).map fun n => ([], n) := by
  simp only [qStep, step, hb, Option.bind_some, List.isEmpty_nil, Bool.true_and, ↓reduceIte]

theorem qStep_context (t : Tok) (s next tail : List Bracket) (depth : Nat)
    (hne : tail ≠ []) (hs : step s t = some next) :
    qStep (s ++ tail, depth) t = some (next ++ tail, depth) := by
  simp only [qStep, step_suffix t s next tail hs, Option.bind_some,
    append_stack_not_empty s tail hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem qRun_append (xs ys : List Tok) (state : QState) :
    qRun state (xs ++ ys) = (qRun state xs).bind (fun next => qRun next ys) := by
  induction xs generalizing state with
  | nil => rfl
  | cons t ts ih => simp only [List.cons_append, qRun, ih, Option.bind_assoc]

theorem qRun_context (ts : List Tok) (s next tail : List Bracket) (depth : Nat)
    (hne : tail ≠ []) (h : run s ts = some next) :
    qRun (s ++ tail, depth) ts = some (next ++ tail, depth) := by
  induction ts generalizing s with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases hs : step s t with
    | none => simp only [run, hs, Option.bind_none] at h; cases h
    | some middle =>
      simp only [run, hs, Option.bind_some] at h
      rw [qRun, qStep_context t s middle tail depth hne hs, Option.bind_some]
      exact ih middle h

theorem qBalanced_enclose (k : Bracket) (ts : List Tok) (h : Balanced ts) :
    QBalanced (openTok k :: (ts ++ [closeTok k])) := by
  intro depth
  have inner : qRun ([k], depth) ts = some ([k], depth) :=
    qRun_context ts [] [] [k] depth (by intro he; cases he) (h [])
  rw [qRun, qStep_open, Option.bind_some, qRun_append, inner,
    Option.bind_some, qRun, qStep_close]
  rfl

theorem qBalanced_nil : QBalanced [] := fun _ => rfl

theorem qBalanced_append {xs ys : List Tok} (hx : QBalanced xs) (hy : QBalanced ys) :
    QBalanced (xs ++ ys) := by
  intro depth
  rw [qRun_append, hx depth, Option.bind_some]
  exact hy depth

theorem qBalanced_atom (t : Tok) (hb : bracket t = none)
    (ht : ∀ depth, qToken depth t = some depth) : QBalanced [t] := by
  intro depth
  rw [qRun, qStep_atom t hb, ht depth, Option.map_some, Option.bind_some]
  rfl

theorem qBalanced_conditional {c a b : List Tok}
    (hc : QBalanced c) (ha : QBalanced a) (hb : QBalanced b) :
    QBalanced (c ++ .punct .question :: (a ++ .punct .colon :: b)) := by
  intro depth
  rw [qRun_append, hc depth, Option.bind_some, qRun,
    qStep_atom (.punct .question) rfl, qToken, Option.map_some, Option.bind_some,
    qRun_append, ha (depth + 1), Option.bind_some, qRun,
    qStep_atom (.punct .colon) rfl, qToken, Option.map_some, Option.bind_some]
  exact hb depth

def qNeutral : Tok → Bool
  | .punct .question | .punct .colon => false
  | _ => true

theorem qToken_neutral (t : Tok) (h : qNeutral t = true) (depth : Nat) :
    qToken depth t = some depth := by
  cases t <;> try rfl
  case punct p => cases p <;> first | rfl | cases h

theorem qNeutral_atom {t : Tok} (hb : bracket t = none) (ht : qNeutral t = true) :
    QBalanced [t] := qBalanced_atom t hb (qToken_neutral t ht)

theorem qStep_projection (stack next : List Bracket) (n m : Nat) (t : Tok)
    (h : qStep (stack, n) t = some (next, m)) : step stack t = some next := by
  unfold qStep at h
  cases hs : step stack t with
  | none => simp only [hs, Option.bind_none] at h; cases h
  | some middle =>
    simp only [hs, Option.bind_some] at h
    split at h
    · cases ht : qToken n t with
      | none => simp only [ht, Option.map_none] at h; cases h
      | some depth =>
        simp only [ht, Option.map_some] at h
        cases h
        rfl
    · cases h; rfl

theorem qRun_projection (ts : List Tok) (stack next : List Bracket) (n m : Nat)
    (h : qRun (stack, n) ts = some (next, m)) : run stack ts = some next := by
  induction ts generalizing stack n with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases hs : qStep (stack, n) t with
    | none => simp only [qRun, hs, Option.bind_none] at h; cases h
    | some state =>
      rcases state with ⟨middle, depth⟩
      simp only [qRun, hs, Option.bind_some] at h
      rw [run, qStep_projection stack middle n depth t hs, Option.bind_some]
      exact ih middle depth h

theorem qBalanced_balanced {ts : List Tok} (h : QBalanced ts) : Balanced ts :=
  (balanced_iff_empty ts).mpr (qRun_projection ts [] [] 0 0 (h 0))

/-- First failing transition, including malformed delimiter failures. Certified
prefixes below establish successful runs, so their selected failure is a colon. -/
def qFailure (state : QState) : List Tok → Option Nat
  | [] => none
  | t :: ts => match qStep state t with
    | none => some 0
    | some next => (qFailure next ts).map Nat.succ

theorem qFailure_after_success (xs ys : List Tok) (initial final : QState)
    (hr : qRun initial xs = some final) :
    qFailure initial (xs ++ ys) = (qFailure final ys).map (fun n => xs.length + n) := by
  induction xs generalizing initial with
  | nil =>
    cases hr
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    cases qFailure final ys <;> rfl
  | cons t ts ih =>
    cases hs : qStep initial t with
    | none => simp only [qRun, hs, Option.bind_none] at hr; cases hr
    | some next =>
      simp only [qRun, hs, Option.bind_some] at hr
      simp only [List.cons_append, qFailure, hs, ih next hr, Option.map_map,
        List.length_cons, Nat.succ_add]
      rfl

theorem qFailure_marker (xs ys : List Tok) (initial final : QState) (marker : Tok)
    (hr : qRun initial xs = some final) (hm : qStep final marker = none) :
    qFailure initial (xs ++ marker :: ys) = some xs.length := by
  rw [qFailure_after_success xs (marker :: ys) initial final hr, qFailure, hm]
  simp only [Option.map_some, Nat.add_zero]

theorem qFailure_cut_unique (xs ys xs' ys' : List Tok) (initial final final' : QState)
    (marker marker' : Tok) (hr : qRun initial xs = some final)
    (hr' : qRun initial xs' = some final')
    (hm : qStep final marker = none) (hm' : qStep final' marker' = none)
    (he : xs ++ marker :: ys = xs' ++ marker' :: ys') :
    xs = xs' ∧ marker = marker' ∧ ys = ys' := by
  have first : qFailure initial (xs ++ marker :: ys) = some xs.length :=
    qFailure_marker xs ys initial final marker hr hm
  have second : qFailure initial (xs' ++ marker' :: ys') = some xs'.length :=
    qFailure_marker xs' ys' initial final' marker' hr' hm'
  rw [he, second] at first
  obtain ⟨left, rest⟩ := List.append_inj he (Option.some.inj first).symm
  exact ⟨left, (List.cons.inj rest).1, (List.cons.inj rest).2⟩

theorem qBalanced_colon_cut_unique (xs ys xs' ys' : List Tok)
    (hx : QBalanced xs) (hx' : QBalanced xs')
    (he : xs ++ .punct .colon :: ys = xs' ++ .punct .colon :: ys') :
    xs = xs' ∧ ys = ys' := by
  obtain ⟨left, marker, right⟩ := qFailure_cut_unique xs ys xs' ys' ([], 0) ([], 0) ([], 0)
    (.punct .colon) (.punct .colon) (hx 0) (hx' 0) rfl rfl he
  exact ⟨left, right⟩

end Solidity.Frontend.ExpressionUniqueness

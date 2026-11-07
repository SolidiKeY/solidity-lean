import Solidity.Frontend.ExpressionUniqueness.OperandMode

/-!
# Operand-sensitive additive scans

A top-level subtraction is selected only after a completed operand. The skip
machine starts in an explicitly supplied state; a leading prefix minus from an
unfinished state is not selected. The last-marker scan ignores all earlier hits
when a later hit exists, supporting arbitrary left-associative root prefixes.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Frontend.Checked

def addHit (state : ModeState) (t : Tok) : Bool :=
  state.1.isEmpty && match t with
    | .punct .add => true
    | .punct .sub => state.2
    | _ => false

def addSkip (state : ModeState) : List Tok → Option ModeState
  | [] => some state
  | t :: ts => if addHit state t then none
    else (modeStep state t).bind fun next => addSkip next ts

def addScan (state : ModeState) : List Tok → Option (ModeState × Option (Nat × Tok))
  | [] => some (state, none)
  | t :: ts => (modeStep state t).bind fun next =>
    (addScan next ts).map fun result => (result.1,
      match result.2 with
      | some found => some (offset 1 found)
      | none => if addHit state t then some (0, t) else none)

def lastAdd (ts : List Tok) : Option (Nat × Tok) :=
  (addScan ([], false) ts).bind fun result => result.2

theorem addHit_inside (stack tail : List Bracket) (finished : Bool) (t : Tok)
    (hne : tail ≠ []) : addHit (stack ++ tail, finished) t = false := by
  simp only [addHit, append_stack_not_empty stack tail hne, Bool.false_and]

theorem addHit_open (k : Bracket) (finished : Bool) :
    addHit ([], finished) (openTok k) = false := by
  cases k <;> rfl

theorem addSkip_append (xs ys : List Tok) (state : ModeState) :
    addSkip state (xs ++ ys) = (addSkip state xs).bind (fun next => addSkip next ys) := by
  induction xs generalizing state with
  | nil => rfl
  | cons t ts ih =>
    cases hit : addHit state t <;>
      simp only [List.cons_append, addSkip, hit, Bool.false_eq_true,
        ↓reduceIte, Option.bind_none, ih, Option.bind_assoc]

theorem addSkip_atom (t : Tok) (finished : Bool) (hb : bracket t = none)
    (hit : addHit ([], finished) t = false) :
    addSkip ([], finished) [t] = some ([], modeToken finished t) := by
  simp only [addSkip, hit, Bool.false_eq_true, ↓reduceIte,
    modeStep_atom t hb, Option.bind_some]

theorem addSkip_context (ts : List Tok) (s next tail : List Bracket) (finished : Bool)
    (hne : tail ≠ []) (h : run s ts = some next) :
    addSkip (s ++ tail, finished) ts = some (next ++ tail, finished) := by
  induction ts generalizing s with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases hs : step s t with
    | none => simp only [run, hs, Option.bind_none] at h; cases h
    | some middle =>
      simp only [run, hs, Option.bind_some] at h
      simp only [addSkip, addHit_inside s tail finished t hne,
        Bool.false_eq_true, ↓reduceIte, modeStep_context t s middle tail finished hne hs,
        Option.bind_some]
      exact ih middle h

theorem addSkip_enclose (k : Bracket) (ts : List Tok) (finished : Bool) (h : Balanced ts) :
    addSkip ([], finished) (openTok k :: (ts ++ [closeTok k])) = some ([], true) := by
  have inner : addSkip ([k], finished) ts = some ([k], finished) :=
    addSkip_context ts [] [] [k] finished (by intro he; cases he) (h [])
  rw [addSkip, addHit_open]
  simp only [Bool.false_eq_true, ↓reduceIte, modeStep_open, Option.bind_some,
    addSkip_append, inner]
  cases k <;> rfl

theorem modeRun_of_addSkip (ts : List Tok) (state final : ModeState)
    (h : addSkip state ts = some final) : modeRun state ts = some final := by
  induction ts generalizing state with
  | nil => exact h
  | cons t ts ih =>
    cases hit : addHit state t with
    | true => simp only [addSkip, hit, ↓reduceIte] at h; cases h
    | false =>
      cases hs : modeStep state t with
      | none => simp only [addSkip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_none] at h; cases h
      | some middle =>
        simp only [addSkip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_some] at h
        simp only [modeRun, hs, Option.bind_some]
        exact ih middle h

theorem addScan_of_addSkip (ts : List Tok) (state final : ModeState)
    (h : addSkip state ts = some final) : addScan state ts = some (final, none) := by
  induction ts generalizing state with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases hit : addHit state t with
    | true => simp only [addSkip, hit, ↓reduceIte] at h; cases h
    | false =>
      cases hs : modeStep state t with
      | none => simp only [addSkip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_none] at h; cases h
      | some middle =>
        simp only [addSkip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_some] at h
        simp only [addScan, hs, Option.bind_some, ih middle h, Option.map_some,
          hit, Bool.false_eq_true, ↓reduceIte]

/-- A later hit dominates every earlier marker in an arbitrary successfully
executed prefix; no marker-freedom premise is needed for that prefix. -/
theorem addScan_suffix_found (xs ys : List Tok) (state middle final : ModeState)
    (position : Nat) (marker : Tok) (hr : modeRun state xs = some middle)
    (hs : addScan middle ys = some (final, some (position, marker))) :
    addScan state (xs ++ ys) = some (final, some (position + xs.length, marker)) := by
  induction xs generalizing state with
  | nil =>
    cases hr
    simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hs
  | cons t ts ih =>
    cases ht : modeStep state t with
    | none => simp only [modeRun, ht, Option.bind_none] at hr; cases hr
    | some next =>
      simp only [modeRun, ht, Option.bind_some] at hr
      simp only [List.cons_append, addScan, ht, Option.bind_some,
        ih next hr, Option.map_some, offset, List.length_cons, Nat.add_assoc]

theorem lastAdd_marker (xs ys : List Tok) (marker : Tok)
    (hx : ModeDone xs) (hy : addSkip ([], false) ys = some ([], true))
    (hstep : modeStep ([], true) marker = some ([], false))
    (hit : addHit ([], true) marker = true) :
    lastAdd (xs ++ marker :: ys) = some (xs.length, marker) := by
  have rest : addScan ([], false) ys = some (([], true), none) := addScan_of_addSkip ys _ _ hy
  have atMarker : addScan ([], true) (marker :: ys) = some (([], true), some (0, marker)) := by
    simp only [addScan, hstep, Option.bind_some, rest, Option.map_some, hit, ↓reduceIte]
  have whole : addScan ([], false) (xs ++ marker :: ys) =
      some (([], true), some (xs.length, marker)) := by
    simpa only [Nat.zero_add] using addScan_suffix_found xs (marker :: ys)
      ([], false) ([], true) ([], true) 0 marker (hx false) atMarker
  simp only [lastAdd, whole, Option.bind_some]

theorem lastAdd_none_of_skip (ts : List Tok) (final : ModeState)
    (h : addSkip ([], false) ts = some final) : lastAdd ts = none := by
  simp only [lastAdd, addScan_of_addSkip ts _ _ h, Option.bind_some]

theorem lastAdd_cut_unique (xs ys xs' ys' : List Tok) (marker marker' : Tok)
    (hx : ModeDone xs) (hx' : ModeDone xs')
    (hy : addSkip ([], false) ys = some ([], true))
    (hy' : addSkip ([], false) ys' = some ([], true))
    (hm : modeStep ([], true) marker = some ([], false))
    (hm' : modeStep ([], true) marker' = some ([], false))
    (hit : addHit ([], true) marker = true) (hit' : addHit ([], true) marker' = true)
    (he : xs ++ marker :: ys = xs' ++ marker' :: ys') :
    xs = xs' ∧ marker = marker' ∧ ys = ys' := by
  have left : lastAdd (xs ++ marker :: ys) = some (xs.length, marker) :=
    lastAdd_marker xs ys marker hx hy hm hit
  have right : lastAdd (xs' ++ marker' :: ys') = some (xs'.length, marker') :=
    lastAdd_marker xs' ys' marker' hx' hy' hm' hit'
  rw [he, right] at left
  have lengths : xs.length = xs'.length := (Prod.mk.inj (Option.some.inj left)).1.symm
  obtain ⟨head, tail⟩ := List.append_inj he lengths
  exact ⟨head, (List.cons.inj tail).1, (List.cons.inj tail).2⟩

end Solidity.Frontend.ExpressionUniqueness

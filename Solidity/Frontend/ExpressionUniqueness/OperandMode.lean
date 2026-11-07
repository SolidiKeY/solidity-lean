import Solidity.Frontend.ExpressionUniqueness.TokenSplit

/-!
# Delimiter-aware operand completion state

The state contains only the existing delimiter stack and one completion bit.
Interior tokens do not affect the surrounding bit; closing the outer delimiter
finishes an operand. This is a token machine, never an alternative expression AST.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Frontend.Checked

def ModeState : Type := List Bracket × Bool

def modeToken (finished : Bool) : Tok → Bool
  | .punct .inc | .punct .dec => finished
  | .punct _ => false
  | .kw .new | .kw .delete => false
  | _ => true

def modeStep (state : ModeState) (t : Tok) : Option ModeState :=
  (step state.1 t).map fun next =>
    (next, if state.1.isEmpty then
      if next.isEmpty then modeToken state.2 t else state.2
    else if next.isEmpty then true else state.2)

def modeRun (state : ModeState) : List Tok → Option ModeState
  | [] => some state
  | t :: ts => (modeStep state t).bind fun next => modeRun next ts

def ModeAny (ts : List Tok) : Prop :=
  ∀ finished, ∃ result, modeRun ([], finished) ts = some ([], result)

def ModeDone (ts : List Tok) : Prop :=
  ∀ finished, modeRun ([], finished) ts = some ([], true)

def ModeStable (ts : List Tok) : Prop := modeRun ([], true) ts = some ([], true)

theorem append_stack_not_empty (xs tail : List Bracket) (hne : tail ≠ []) :
    (xs ++ tail).isEmpty = false := by
  cases xs with
  | cons k ks => rfl
  | nil => cases tail with
    | nil => exact False.elim (hne rfl)
    | cons k ks => rfl

theorem modeStep_open (k : Bracket) (stack : List Bracket) (finished : Bool) :
    modeStep (stack, finished) (openTok k) = some (k :: stack, finished) := by
  cases stack <;> simp only [modeStep, step_open, Option.map_some,
    List.isEmpty_nil, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]

theorem modeStep_close (k : Bracket) (stack : List Bracket) (finished : Bool) :
    modeStep (k :: stack, finished) (closeTok k) =
      some (stack, if stack.isEmpty then true else finished) := by
  simp only [modeStep, step_close, Option.map_some, List.isEmpty_cons,
    Bool.false_eq_true, ↓reduceIte]

theorem modeStep_atom (t : Tok) (hb : bracket t = none) (finished : Bool) :
    modeStep ([], finished) t = some ([], modeToken finished t) := by
  simp only [modeStep, step, hb, Option.map_some, List.isEmpty_nil, ↓reduceIte]

theorem modeStep_context (t : Tok) (s next tail : List Bracket) (finished : Bool)
    (hne : tail ≠ []) (hs : step s t = some next) :
    modeStep (s ++ tail, finished) t = some (next ++ tail, finished) := by
  simp only [modeStep, step_suffix t s next tail hs, Option.map_some,
    append_stack_not_empty s tail hne, append_stack_not_empty next tail hne,
    Bool.false_eq_true, ↓reduceIte]

theorem modeRun_append (xs ys : List Tok) (state : ModeState) :
    modeRun state (xs ++ ys) = (modeRun state xs).bind (fun next => modeRun next ys) := by
  induction xs generalizing state with
  | nil => rfl
  | cons t ts ih => simp only [List.cons_append, modeRun, ih, Option.bind_assoc]

theorem modeRun_context (ts : List Tok) (s next tail : List Bracket) (finished : Bool)
    (hne : tail ≠ []) (h : run s ts = some next) :
    modeRun (s ++ tail, finished) ts = some (next ++ tail, finished) := by
  induction ts generalizing s with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases hs : step s t with
    | none => simp only [run, hs, Option.bind_none] at h; cases h
    | some middle =>
      simp only [run, hs, Option.bind_some] at h
      rw [modeRun, modeStep_context t s middle tail finished hne hs, Option.bind_some]
      exact ih middle h

theorem modeRun_of_run (ts : List Tok) (s next : List Bracket) (finished : Bool)
    (h : run s ts = some next) : ∃ result, modeRun (s, finished) ts = some (next, result) := by
  induction ts generalizing s finished with
  | nil => cases h; exact ⟨finished, rfl⟩
  | cons t ts ih =>
    cases hs : step s t with
    | none => simp only [run, hs, Option.bind_none] at h; cases h
    | some middle =>
      simp only [run, hs, Option.bind_some] at h
      let newFinished : Bool := if s.isEmpty then
        if middle.isEmpty then modeToken finished t else finished
        else if middle.isEmpty then true else finished
      have hm : modeStep (s, finished) t = some (middle, newFinished) := by
        simp only [modeStep, hs, Option.map_some, newFinished]
      obtain ⟨result, rest⟩ := ih middle newFinished h
      exact ⟨result, by rw [modeRun, hm, Option.bind_some]; exact rest⟩

theorem balanced_modeAny (ts : List Tok) (h : Balanced ts) : ModeAny ts :=
  fun finished => modeRun_of_run ts [] [] finished (h [])

theorem modeDone_enclose (k : Bracket) (ts : List Tok) (h : Balanced ts) :
    ModeDone (openTok k :: (ts ++ [closeTok k])) := by
  intro finished
  have inner : modeRun ([k], finished) ts = some ([k], finished) :=
    modeRun_context ts [] [] [k] finished (by intro he; cases he) (h [])
  rw [modeRun, modeStep_open, Option.bind_some, modeRun_append, inner,
    Option.bind_some, modeRun, modeStep_close]
  rfl

theorem modeDone_append {xs ys : List Tok} (hx : ModeAny xs) (hy : ModeDone ys) :
    ModeDone (xs ++ ys) := by
  intro finished
  obtain ⟨result, hr⟩ := hx finished
  rw [modeRun_append, hr, Option.bind_some]
  exact hy result

theorem modeDone_stable (ts : List Tok) (h : ModeDone ts) : ModeStable ts := h true

theorem modeStable_nil : ModeStable [] := rfl

theorem modeStable_append {xs ys : List Tok} (hx : ModeStable xs) (hy : ModeStable ys) :
    ModeStable (xs ++ ys) := by
  rw [ModeStable, modeRun_append, hx, Option.bind_some]
  exact hy

theorem modeDone_stable_append {xs ys : List Tok} (hx : ModeDone xs) (hy : ModeStable ys) :
    ModeDone (xs ++ ys) := by
  intro finished
  rw [modeRun_append, hx finished, Option.bind_some]
  exact hy

theorem modeDone_atom (t : Tok) (hb : bracket t = none)
    (ht : ∀ finished, modeToken finished t = true) : ModeDone [t] := by
  intro finished
  rw [modeRun, modeStep_atom t hb, ht, Option.bind_some]
  rfl

theorem modeStable_atom (t : Tok) (hb : bracket t = none)
    (ht : modeToken true t = true) : ModeStable [t] := by
  rw [ModeStable, modeRun, modeStep_atom t hb, ht, Option.bind_some]
  rfl

end Solidity.Frontend.ExpressionUniqueness

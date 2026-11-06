import Solidity.Frontend.Checked.Token

/-!
# Delimiter execution and token splitting for expression uniqueness

The machine reads the existing checked tokens. Its stack carries only delimiter
kinds, never an alternative AST. All statements quantify arbitrary token lists.
These helpers do not yet establish root decomposition for certified expressions.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Frontend.Checked

inductive Bracket where
  | round | square | curly
  deriving DecidableEq, Repr

def openTok : Bracket → Tok
  | .round => .punct .lparen
  | .square => .punct .lbrack
  | .curly => .punct .lbrace

def closeTok : Bracket → Tok
  | .round => .punct .rparen
  | .square => .punct .rbrack
  | .curly => .punct .rbrace

/-- `true` opens a delimiter, `false` closes one. -/
def bracket : Tok → Option (Bool × Bracket)
  | .punct .lparen => some (true, .round)
  | .punct .lbrack => some (true, .square)
  | .punct .lbrace => some (true, .curly)
  | .punct .rparen => some (false, .round)
  | .punct .rbrack => some (false, .square)
  | .punct .rbrace => some (false, .curly)
  | _ => none

def pop (k : Bracket) : List Bracket → Option (List Bracket)
  | [] => none
  | h :: s => if h = k then some s else none

def step (s : List Bracket) (t : Tok) : Option (List Bracket) :=
  match bracket t with
  | none => some s
  | some (true, k) => some (k :: s)
  | some (false, k) => pop k s

def run (s : List Bracket) : List Tok → Option (List Bracket)
  | [] => some s
  | t :: ts => (step s t).bind fun next => run next ts

/-- Balanced in every surrounding delimiter context. -/
def Balanced (ts : List Tok) : Prop := ∀ s, run s ts = some s

theorem open_close_disjoint (a b : Bracket) : openTok a ≠ closeTok b := by
  cases a <;> cases b <;> decide

theorem step_suffix (t : Tok) (s next tail : List Bracket)
    (h : step s t = some next) : step (s ++ tail) t = some (next ++ tail) := by
  unfold step at h ⊢
  cases hb : bracket t with
  | none =>
    simp only [hb, Option.some.injEq] at h
    subst next
    rfl
  | some tag =>
    rcases tag with ⟨opening, k⟩
    cases opening with
    | true =>
      simp only [hb, Option.some.injEq] at h
      subst next
      rfl
    | false =>
      simp only [hb] at h ⊢
      cases s with
      | nil => cases h
      | cons j rest =>
        by_cases he : j = k
        · simp only [pop, he, ↓reduceIte, Option.some.injEq] at h
          subst next
          simp only [List.cons_append, pop, he, ↓reduceIte]
        · simp only [pop, he, ↓reduceIte] at h
          cases h

/-- Successful delimiter execution is independent of an untouched stack suffix. -/
theorem run_suffix (ts : List Tok) (s next tail : List Bracket)
    (h : run s ts = some next) : run (s ++ tail) ts = some (next ++ tail) := by
  induction ts generalizing s with
  | nil =>
    cases h
    rfl
  | cons t ts ih =>
    cases hs : step s t with
    | none =>
      simp only [run, hs, Option.bind_none] at h
      cases h
    | some middle =>
      simp only [run, hs, Option.bind_some] at h
      rw [run, step_suffix t s middle tail hs, Option.bind_some]
      exact ih middle h

theorem balanced_iff_empty (ts : List Tok) : Balanced ts ↔ run [] ts = some [] := by
  constructor
  · exact fun h => h []
  · intro h s
    exact run_suffix ts [] [] s h

theorem run_append (xs ys : List Tok) (s : List Bracket) :
    run s (xs ++ ys) = (run s xs).bind (fun next => run next ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.cons_append, run, ih, Option.bind_assoc]

theorem balanced_nil : Balanced [] := fun _ => rfl

theorem balanced_append {xs ys : List Tok} (hx : Balanced xs) (hy : Balanced ys) :
    Balanced (xs ++ ys) := by
  intro s
  rw [run_append, hx]
  exact hy s

theorem balanced_atom {t : Tok} (h : bracket t = none) : Balanced [t] := by
  intro s
  simp only [run, step, h, Option.bind_some]

theorem step_open (k : Bracket) (s : List Bracket) :
    step s (openTok k) = some (k :: s) := by
  cases k <;> rfl

theorem step_close (k : Bracket) (s : List Bracket) :
    step (k :: s) (closeTok k) = some s := by
  cases k <;> rfl

theorem balanced_enclose (k : Bracket) {ts : List Tok} (h : Balanced ts) :
    Balanced (openTok k :: (ts ++ [closeTok k])) := by
  intro s
  rw [run, step_open, Option.bind_some, run_append, h (k :: s), Option.bind_some,
    run, step_close]
  rfl

theorem balanced_not_close (k : Bracket) (ts : List Tok) :
    ¬ Balanced (closeTok k :: ts) := by
  intro h
  have bad := h []
  cases k <;> simp only [closeTok, run, step, bracket, pop, Option.bind_none] at bad <;>
    cases bad

/-- Skip a prefix only if it has no selected token at depth zero. -/
def skip (p : Tok → Bool) (s : List Bracket) : List Tok → Option (List Bracket)
  | [] => some s
  | t :: ts =>
    if s.isEmpty && p t then none
    else (step s t).bind fun next => skip p next ts

def offset (n : Nat) (r : Nat × Tok) : Nat × Tok := (r.1 + n, r.2)

/-- The first selected token outside delimiters, with its zero-based index. -/
def firstTop (p : Tok → Bool) (s : List Bracket) : List Tok → Option (Nat × Tok)
  | [] => none
  | t :: ts =>
    if s.isEmpty && p t then some (0, t)
    else (step s t).bind fun next =>
      (firstTop p next ts).map (offset 1)

theorem skip_append (p : Tok → Bool) (xs ys : List Tok) (s : List Bracket) :
    skip p s (xs ++ ys) = (skip p s xs).bind (fun next => skip p next ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons t ts ih =>
    cases hit : s.isEmpty && p t <;>
      simp only [List.cons_append, skip, hit, Bool.false_eq_true,
        ↓reduceIte, Option.bind_none, ih, Option.bind_assoc]

/-- Inside a nonempty outer stack no token is a top-level marker. -/
theorem skip_inside (p : Tok → Bool) (ts : List Tok) (s next tail : List Bracket)
    (hne : tail ≠ []) (h : run s ts = some next) :
    skip p (s ++ tail) ts = some (next ++ tail) := by
  induction ts generalizing s with
  | nil =>
    cases h
    rfl
  | cons t ts ih =>
    have hit : (s ++ tail).isEmpty = false := by
      cases s with
      | nil => cases tail with
        | nil => exact False.elim (hne rfl)
        | cons k rest => rfl
      | cons k rest => rfl
    cases hs : step s t with
    | none =>
      simp only [run, hs, Option.bind_none] at h
      cases h
    | some middle =>
      simp only [run, hs, Option.bind_some] at h
      simp only [skip, hit, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        step_suffix t s middle tail hs, Option.bind_some]
      exact ih middle h

theorem skip_enclose (p : Tok → Bool) (k : Bracket) {ts : List Tok}
    (h : Balanced ts) (hop : p (openTok k) = false) :
    skip p [] (openTok k :: (ts ++ [closeTok k])) = some [] := by
  have inner : skip p [k] ts = some [k] :=
    skip_inside p ts [] [] [k] (by intro he; cases he) (h [])
  simp only [skip, List.isEmpty_nil, Bool.true_and, hop, Bool.false_eq_true,
    ↓reduceIte, step_open, Option.bind_some, skip_append, inner,
    List.isEmpty_cons, Bool.false_and, step_close]

/-- An arbitrary mixed-delimiter nesting family. -/
def nest : List Bracket → List Tok → List Tok
  | [], ts => ts
  | k :: ks, ts => openTok k :: (nest ks ts ++ [closeTok k])

theorem balanced_nest (ks : List Bracket) {ts : List Tok} (h : Balanced ts) :
    Balanced (nest ks ts) := by
  induction ks with
  | nil => exact h
  | cons k ks ih => exact balanced_enclose k ih

theorem firstTop_append_of_skip (p : Tok → Bool) (xs ys : List Tok)
    (s next : List Bracket) (h : skip p s xs = some next) :
    firstTop p s (xs ++ ys) = (firstTop p next ys).map (offset xs.length) := by
  induction xs generalizing s next with
  | nil =>
    cases h
    simp only [List.nil_append, List.length_nil]
    cases firstTop p s ys <;> rfl
  | cons t ts ih =>
    cases hit : s.isEmpty && p t with
    | true =>
      simp only [skip, hit, ↓reduceIte] at h
      cases h
    | false =>
      cases hs : step s t with
      | none =>
        simp only [skip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_none] at h
        cases h
      | some middle =>
        simp only [skip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_some] at h
        simp only [List.cons_append, firstTop, hit, Bool.false_eq_true, ↓reduceIte,
          hs, Option.bind_some, ih middle next h, Option.map_map, List.length_cons]
        congr 1

theorem firstTop_marker (p : Tok → Bool) (xs ys : List Tok) (t : Tok)
    (h : skip p [] xs = some []) (hp : p t = true) :
    firstTop p [] (xs ++ t :: ys) = some (xs.length, t) := by
  rw [firstTop_append_of_skip p xs (t :: ys) [] [] h]
  simp only [firstTop, List.isEmpty_nil, Bool.true_and, hp, ↓reduceIte,
    Option.map_some, offset, Nat.zero_add]

/-- Both the marker and the entire cut are reconstructed, for arbitrary sizes.
The skip hypotheses concern this token machine, not an assumed expression split.
Deriving them from expression certificates is a separate open obligation. -/
theorem firstTop_cut_unique (p : Tok → Bool) (xs ys xs' ys' : List Tok) (t t' : Tok)
    (hx : skip p [] xs = some []) (hx' : skip p [] xs' = some [])
    (ht : p t = true) (ht' : p t' = true)
    (heq : xs ++ t :: ys = xs' ++ t' :: ys') :
    xs = xs' ∧ t = t' ∧ ys = ys' := by
  have h1 := firstTop_marker p xs ys t hx ht
  have h2 := firstTop_marker p xs' ys' t' hx' ht'
  rw [heq, h2] at h1
  have hl : xs.length = xs'.length := (Prod.mk.inj (Option.some.inj h1)).1.symm
  obtain ⟨he, hr⟩ := List.append_inj heq hl
  exact ⟨he, (List.cons.inj hr).1, (List.cons.inj hr).2⟩

end Solidity.Frontend.ExpressionUniqueness

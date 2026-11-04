import Solidity.Frontend.ExpressionUniqueness.TokenSplit

/-!
# Reverse delimiter scanning and last-marker reconstruction

Mirroring swaps delimiter directions and reverses token words, preserving the
existing token alphabet. No expression tree representation is introduced.
The last-marker helper still requires token-selector invariants; deriving them
from certified precedence conditions remains a separate obligation.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Frontend.Checked

def mirrorTok (t : Tok) : Tok :=
  match bracket t with
  | none => t
  | some (true, k) => closeTok k
  | some (false, k) => openTok k

def mirrorWord (ts : List Tok) : List Tok := ts.reverse.map mirrorTok

theorem bracket_open (k : Bracket) : bracket (openTok k) = some (true, k) := by
  cases k <;> rfl

theorem bracket_close (k : Bracket) : bracket (closeTok k) = some (false, k) := by
  cases k <;> rfl

theorem mirrorTok_open (k : Bracket) : mirrorTok (openTok k) = closeTok k := by
  simp only [mirrorTok, bracket_open]

theorem mirrorTok_close (k : Bracket) : mirrorTok (closeTok k) = openTok k := by
  simp only [mirrorTok, bracket_close]

theorem mirrorTok_involutive (t : Tok) : mirrorTok (mirrorTok t) = t := by
  cases t with
  | punct p => cases p <;> rfl
  | _ => rfl

theorem mirrorWord_nil : mirrorWord [] = [] := rfl

theorem mirrorWord_append (xs ys : List Tok) :
    mirrorWord (xs ++ ys) = mirrorWord ys ++ mirrorWord xs := by
  simp only [mirrorWord, List.reverse_append, List.map_append]

theorem mirrorWord_singleton (t : Tok) : mirrorWord [t] = [mirrorTok t] := rfl

theorem mirrorWord_cons (t : Tok) (ts : List Tok) :
    mirrorWord (t :: ts) = mirrorWord ts ++ [mirrorTok t] := by
  simp only [mirrorWord, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]

theorem mirrorWord_involutive (ts : List Tok) : mirrorWord (mirrorWord ts) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [mirrorWord_cons, mirrorWord_append, mirrorWord_singleton,
      mirrorTok_involutive, ih]
    rfl

theorem step_reverse (t : Tok) (s next : List Bracket)
    (h : step s t = some next) : step next (mirrorTok t) = some s := by
  cases hb : bracket t with
  | none =>
    simp only [step, hb, Option.some.injEq] at h
    subst next
    simp only [mirrorTok, step, hb]
  | some tag =>
    rcases tag with ⟨opening, k⟩
    cases opening with
    | true =>
      simp only [step, hb, Option.some.injEq] at h
      subst next
      simp only [mirrorTok, hb]
      exact step_close k s
    | false =>
      simp only [step, hb] at h
      cases s with
      | nil => cases h
      | cons j rest =>
        by_cases he : j = k
        · subst j
          simp only [pop, ↓reduceIte, Option.some.injEq] at h
          subst next
          simp only [mirrorTok, hb]
          exact step_open k rest
        · simp only [pop, he, ↓reduceIte] at h
          cases h

theorem run_reverse (ts : List Tok) (s next : List Bracket)
    (h : run s ts = some next) : run next (mirrorWord ts) = some s := by
  induction ts generalizing s with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases hs : step s t with
    | none => simp only [run, hs, Option.bind_none] at h; cases h
    | some middle =>
      simp only [run, hs, Option.bind_some] at h
      rw [mirrorWord_cons, run_append, ih middle h, Option.bind_some,
        run, step_reverse t s middle hs]
      rfl

theorem balanced_mirror (ts : List Tok) (h : Balanced ts) :
    Balanced (mirrorWord ts) := fun s => run_reverse ts s s (h s)

/-- Operator selectors never select delimiters themselves. -/
def AtomicSelector (p : Tok → Bool) : Prop :=
  ∀ k, p (openTok k) = false ∧ p (closeTok k) = false

theorem atomicSelector_mirror (p : Tok → Bool) (hp : AtomicSelector p) (t : Tok) :
    p (mirrorTok t) = p t := by
  cases t with
  | punct q =>
    cases q <;> try rfl
    all_goals first
      | exact (hp .round).1.trans (hp .round).2.symm
      | exact (hp .round).2.trans (hp .round).1.symm
      | exact (hp .square).1.trans (hp .square).2.symm
      | exact (hp .square).2.trans (hp .square).1.symm
      | exact (hp .curly).1.trans (hp .curly).2.symm
      | exact (hp .curly).2.trans (hp .curly).1.symm
  | _ => rfl

theorem reverse_step_not_hit (p : Tok → Bool) (hp : AtomicSelector p)
    (t : Tok) (s next : List Bracket) (hs : step s t = some next)
    (hit : (s.isEmpty && p t) = false) : (next.isEmpty && p (mirrorTok t)) = false := by
  cases hb : bracket t with
  | none =>
    simp only [step, hb, Option.some.injEq] at hs
    subst next
    simpa only [mirrorTok, hb] using hit
  | some tag =>
    rcases tag with ⟨opening, k⟩
    cases opening <;> simp only [mirrorTok, hb, (hp k).1, (hp k).2, Bool.and_false]

theorem skip_reverse (p : Tok → Bool) (hp : AtomicSelector p)
    (ts : List Tok) (s next : List Bracket) (h : skip p s ts = some next) :
    skip p next (mirrorWord ts) = some s := by
  induction ts generalizing s with
  | nil => cases h; rfl
  | cons t ts ih =>
    cases hit : s.isEmpty && p t with
    | true => simp only [skip, hit, ↓reduceIte] at h; cases h
    | false =>
      cases hs : step s t with
      | none =>
        simp only [skip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_none] at h
        cases h
      | some middle =>
        simp only [skip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_some] at h
        rw [mirrorWord_cons, skip_append, ih middle h, Option.bind_some]
        simp only [skip, reverse_step_not_hit p hp t s middle hs hit,
          Bool.false_eq_true, ↓reduceIte, step_reverse t s middle hs, Option.bind_some]

theorem mirrorWord_injective (xs ys : List Tok) (h : mirrorWord xs = mirrorWord ys) :
    xs = ys := by
  have hm := congrArg mirrorWord h
  simpa only [mirrorWord_involutive] using hm

/-- Last selected marker and both spans are unique for arbitrary token lengths.
This is a token-machine helper, not expression root uniqueness. -/
theorem lastTop_cut_unique (p : Tok → Bool) (hp : AtomicSelector p)
    (xs ys xs' ys' : List Tok) (t t' : Tok)
    (hy : skip p [] ys = some []) (hy' : skip p [] ys' = some [])
    (ht : p t = true) (ht' : p t' = true)
    (heq : xs ++ t :: ys = xs' ++ t' :: ys') :
    xs = xs' ∧ t = t' ∧ ys = ys' := by
  have hm := congrArg mirrorWord heq
  simp only [mirrorWord_append, mirrorWord_cons, List.append_assoc,
    List.singleton_append] at hm
  obtain ⟨right, marker, left⟩ := firstTop_cut_unique p
    (mirrorWord ys) (mirrorWord xs) (mirrorWord ys') (mirrorWord xs')
    (mirrorTok t) (mirrorTok t') (skip_reverse p hp ys [] [] hy)
    (skip_reverse p hp ys' [] [] hy')
    ((atomicSelector_mirror p hp t).trans ht)
    ((atomicSelector_mirror p hp t').trans ht') hm
  have token := congrArg mirrorTok marker
  simp only [mirrorTok_involutive] at token
  exact ⟨mirrorWord_injective xs xs' left, token, mirrorWord_injective ys ys' right⟩

/-- Reverse scanning reports positions in the original word. On malformed words
this is a suffix-based scan, not a forward depth-zero claim. Applying it to
expression roots still requires the certified balance/selector invariants. -/
def lastTop (p : Tok → Bool) (ts : List Tok) : Option (Nat × Tok) :=
  (firstTop p [] (mirrorWord ts)).map fun found =>
    (ts.length - 1 - found.1, mirrorTok found.2)

theorem lastTop_marker (p : Tok → Bool) (hp : AtomicSelector p)
    (xs ys : List Tok) (t : Tok) (hy : skip p [] ys = some []) (ht : p t = true) :
    lastTop p (xs ++ t :: ys) = some (xs.length, t) := by
  have scan := firstTop_marker p (mirrorWord ys) (mirrorWord xs) (mirrorTok t)
    (skip_reverse p hp ys [] [] hy) ((atomicSelector_mirror p hp t).trans ht)
  have hlen : (xs ++ t :: ys).length - 1 - (mirrorWord ys).length = xs.length := by
    simp only [List.length_append, List.length_cons, mirrorWord,
      List.length_map, List.length_reverse]
    omega
  unfold lastTop
  rw [mirrorWord_append, mirrorWord_cons, List.append_assoc]
  change (firstTop p [] (mirrorWord ys ++ mirrorTok t :: mirrorWord xs)).map _ = _
  rw [scan]
  simp only [Option.map_some, mirrorTok_involutive, hlen]

/-- A nonempty arbitrary mixed-delimiter family hides all internal markers. -/
theorem skip_nested (p : Tok → Bool) (hp : AtomicSelector p)
    (ks : List Bracket) (hne : ks ≠ []) (ts : List Tok) (h : Balanced ts) :
    skip p [] (nest ks ts) = some [] := by
  cases ks with
  | nil => exact False.elim (hne rfl)
  | cons k ks => exact skip_enclose p k (balanced_nest ks h) (hp k).1

theorem nested_last_marker_control (p : Tok → Bool) (hp : AtomicSelector p)
    (ks : List Bracket) (hne : ks ≠ []) (inside before : List Tok)
    (hinside : Balanced inside) (t : Tok) (ht : p t = true) :
    lastTop p (before ++ t :: nest ks inside) = some (before.length, t) :=
  lastTop_marker p hp before (nest ks inside) t (skip_nested p hp ks hne inside hinside) ht

def isAddMarker (t : Tok) : Bool := decide (t = .punct .add)

theorem addMarker_atomic : AtomicSelector isAddMarker := by
  intro k
  cases k <;> exact ⟨rfl, rfl⟩

theorem repeated_add_balanced (n : Nat) : Balanced (List.replicate n (.punct .add)) := by
  induction n with
  | zero => exact balanced_nil
  | succ n ih => exact balanced_append (balanced_atom rfl) ih

/-- Inhabited operator-selector control: any number of hidden add markers in
any nonempty mixed nesting leaves the final outer add cut unchanged. -/
theorem nested_add_markers_control (ks : List Bracket) (hne : ks ≠ [])
    (before : List Tok) (n : Nat) :
    lastTop isAddMarker (before ++ .punct .add :: nest ks (List.replicate n (.punct .add))) =
      some (before.length, .punct .add) :=
  nested_last_marker_control isAddMarker addMarker_atomic ks hne _ before
    (repeated_add_balanced n) (.punct .add) rfl

/-- A negative control for the intentionally suffix-based malformed-word
semantics; this word cannot be an expression yield because it is unbalanced. -/
theorem malformed_reverse_scan_control :
    lastTop isAddMarker [.punct .lparen, .punct .add] = some (1, .punct .add) ∧
    firstTop isAddMarker [] [.punct .lparen, .punct .add] = none := by
  decide +kernel

end Solidity.Frontend.ExpressionUniqueness

import Solidity.Calculus.LinearCountermodel

/-!
# Quantified linear arithmetic over naturals, decided (M7, step 4)

`AFml.decide_iff` decides validity of a quantifier-free formula by its
binary derivatives (`Calculus/LinearDecision.lean`).  This module adds
quantifiers: `QFml` is a Boolean combination of `AFml` atoms and
existential projections `∃ xᵢ`, its variables named by position (a
binder at `i` shadows the variable `i`, as `AEnv.set` does), and
`QFml.decide_iff` decides its validity by the same derivatives.

* An atom reads its variables through a map (`atom φ m`: the variable `j`
  of `φ` is the global variable `m[j]`), so a compiled arithmetic leaf is
  placed in the global numbering without renaming its forms.
* The derivative of `∃ xᵢ. ⋁ S` at the low bits `B` of the free variables
  is `∃ xᵢ. ⋁ S'`, `S'` the derivatives of `S` at both low bits of `xᵢ`,
  without repeats: the projection of the bit automaton.  Its states are
  finite lists over the derivative universe of the body, so the universe
  of reachable formulas is one of lists, still finite (`QFml.univ`),
  never computed: it only bounds the search (`reach`).
* The zero test of `∃ xᵢ. ⋁ S` asks for a value of `xᵢ` with every other
  variable `0`, a reachability question in `S`'s automaton read with the
  other bits `0` (`QFml.atZero`).

Validity is that every reachable state holds at zero (`QFml.search_iff`);
a reachable state false at zero gives a counterassignment directly
(`QFml.verify`).  A bounded variable is an atom `xᵢ < bound p` (`2^256` at a word)
under the binder: its derivatives halve the constant, and no value is enumerated.
-/

namespace Solidity.Linear

/-! ## Assignments, bits -/

/-- The assignment `x` with the variable `i` set to `n`. -/
def updAt (x : Nat → Nat) (i n : Nat) : Nat → Nat := fun j => if j = i then n else x j

/-- The low bit of every variable. -/
def bitsAt (x : Nat → Nat) : Nat → Bool := fun j => x j % 2 == 1

/-- The bits `B` with the bit `i` set to `b`. -/
def setBit (B : Nat → Bool) (i : Nat) (b : Bool) : Nat → Bool := fun j => if j = i then b else B j

/-- The bits of an atom's variables, read through its map. -/
def localBits (B : Nat → Bool) (m : List Nat) (w : Nat) : List Bool :=
  (List.range w).map fun j => B (m.getD j 0)

theorem bitsAt_updAt (x : Nat → Nat) (i n : Nat) :
    bitsAt (updAt x i n) = setBit (bitsAt x) i (n % 2 == 1) := by
  funext j; simp only [bitsAt, updAt, setBit]; split <;> rfl

theorem halve_updAt (x : Nat → Nat) (i n : Nat) : halve (updAt x i n) = updAt (halve x) i (n / 2) := by
  funext j; simp only [halve, updAt]; split <;> rfl

/-- The low bits are the bits of each variable. -/
theorem lowBits_eq_map : ∀ (n : Nat) (y : Nat → Nat),
    lowBits n y = (List.range n).map fun j => y j % 2 == 1
  | 0, _ => rfl
  | n + 1, y => by
    rw [lowBits, lowBits_eq_map n (shift y), List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl

/-! ## Lists without repeats -/

/-- The list without repeats, the last copy kept. -/
def uniq {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as => if a ∈ uniq as then uniq as else a :: uniq as

theorem mem_uniq {α : Type} [DecidableEq α] (x : α) : ∀ l : List α, x ∈ uniq l ↔ x ∈ l
  | [] => Iff.rfl
  | a :: as => by
    unfold uniq
    split
    · next h =>
      rw [mem_uniq x as, List.mem_cons]
      exact ⟨Or.inr, fun h' => h'.elim (fun e => e ▸ (mem_uniq a as).1 h) id⟩
    · rw [List.mem_cons, mem_uniq x as, List.mem_cons]

theorem nodup_uniq {α : Type} [DecidableEq α] : ∀ l : List α, (uniq l).Nodup
  | [] => List.nodup_nil
  | a :: as => by
    unfold uniq
    split
    · exact nodup_uniq as
    · next h => exact List.nodup_cons.2 ⟨h, nodup_uniq as⟩

/-! ## Formulas -/

/-- **Quantified linear arithmetic.**  `atom φ m` reads `φ`'s variable `j`
at the variable `m[j]` (`0` past `m`), `ex i S` is `∃ xᵢ` of the
disjunction of `S`. -/
inductive QFml where
  | atom (φ : AFml) (m : List Nat)
  | not (s : QFml)
  | and (s t : QFml)
  | ex (i : Nat) (ss : List QFml)
  deriving Repr, Inhabited

mutual
/-- Equality of quantified formulas, decided. -/
def QFml.decEq : (a b : QFml) → Decidable (a = b)
  | .atom φ m, .atom ψ n =>
    if h : φ = ψ ∧ m = n then isTrue (by rw [h.1, h.2]) else isFalse (fun e => by cases e; exact h ⟨rfl, rfl⟩)
  | .not s, .not t =>
    match QFml.decEq s t with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .and s t, .and s' t' =>
    match QFml.decEq s s', QFml.decEq t t' with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .ex i ss, .ex j ts =>
    if h : i = j then
      match QFml.decEqL ss ts with
      | isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h' => isFalse (fun e => by cases e; exact h' rfl)
    else isFalse (fun e => by cases e; exact h rfl)
  | .atom .., .not _ | .atom .., .and .. | .atom .., .ex .. | .not _, .atom ..
  | .not _, .and .. | .not _, .ex .. | .and .., .atom .. | .and .., .not _ | .and .., .ex ..
  | .ex .., .atom .. | .ex .., .not _ | .ex .., .and .. => isFalse (fun e => by cases e)
/-- Equality of lists of quantified formulas, decided. -/
def QFml.decEqL : (a b : List QFml) → Decidable (a = b)
  | [], [] => isTrue rfl
  | s :: ss, t :: ts =>
    match QFml.decEq s t, QFml.decEqL ss ts with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (fun e => by cases e)
end

instance : DecidableEq QFml := QFml.decEq

namespace QFml

mutual
/-- A formula holds at an assignment. -/
def holds : QFml → (Nat → Nat) → Prop
  | .atom φ m, x => φ.holds fun j => x (m.getD j 0)
  | .not s, x => ¬ s.holds x
  | .and s t, x => s.holds x ∧ t.holds x
  | .ex i ss, x => ∃ n, holdsL ss (updAt x i n)
/-- Some formula of the list holds. -/
def holdsL : List QFml → (Nat → Nat) → Prop
  | [], _ => False
  | s :: ss, x => s.holds x ∨ holdsL ss x
end

/-- True at every assignment. -/
def Valid (s : QFml) : Prop := ∀ x, s.holds x

theorem holdsL_iff (x : Nat → Nat) : ∀ ss : List QFml, holdsL ss x ↔ ∃ s ∈ ss, s.holds x
  | [] => by simp only [holdsL, List.not_mem_nil, false_and, exists_false]
  | s :: ss => by
    simp only [holdsL, holdsL_iff x ss, List.mem_cons, exists_eq_or_imp]

theorem holdsL_uniq (x : Nat → Nat) (ss : List QFml) : holdsL (uniq ss) x ↔ holdsL ss x := by
  simp only [holdsL_iff, mem_uniq]

theorem holdsL_append (x : Nat → Nat) (ss ts : List QFml) :
    holdsL (ss ++ ts) x ↔ holdsL ss x ∨ holdsL ts x := by
  simp only [holdsL_iff, List.mem_append]
  constructor
  · rintro ⟨s, hs | hs, h⟩
    · exact .inl ⟨s, hs, h⟩
    · exact .inr ⟨s, hs, h⟩
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
    · exact ⟨s, .inl hs, h⟩
    · exact ⟨s, .inr hs, h⟩

/-! ### Derived connectives -/

/-- `φ → ψ`. -/
def imp (s t : QFml) : QFml := .not (.and s (.not t))
/-- `φ ∨ ψ`. -/
def or (s t : QFml) : QFml := .not (.and (.not s) (.not t))
/-- `∀ xᵢ. φ`. -/
def all (i : Nat) (s : QFml) : QFml := .not (.ex i [.not s])

theorem holds_imp (s t : QFml) (x : Nat → Nat) : (imp s t).holds x ↔ (s.holds x → t.holds x) := by
  simp only [imp, holds]
  exact ⟨fun h hs => Classical.byContradiction fun ht => h ⟨hs, ht⟩, fun h ⟨hs, ht⟩ => ht (h hs)⟩

theorem holds_or (s t : QFml) (x : Nat → Nat) : (or s t).holds x ↔ (s.holds x ∨ t.holds x) := by
  simp only [or, holds]
  exact ⟨fun h => Classical.byContradiction fun h' => h ⟨fun hs => h' (.inl hs), fun ht => h' (.inr ht)⟩,
    fun h ⟨hs, ht⟩ => h.elim hs ht⟩

theorem holds_ex (i : Nat) (ss : List QFml) (x : Nat → Nat) :
    (QFml.ex i ss).holds x ↔ ∃ n, ∃ s ∈ ss, s.holds (updAt x i n) := by
  simp only [holds, holdsL_iff]

theorem holds_all (i : Nat) (s : QFml) (x : Nat → Nat) :
    (all i s).holds x ↔ ∀ n, s.holds (updAt x i n) := by
  simp only [all, holds, holdsL]
  exact ⟨fun h n => Classical.byContradiction fun hn => h ⟨n, .inl hn⟩,
    fun h ⟨n, hn⟩ => hn.elim (fun hn => hn (h n)) id⟩

/-! ### Free variables -/

mutual
/-- The variables a formula reads (with repeats). -/
def free : QFml → List Nat
  | .atom φ m => (List.range φ.width).map (m.getD · 0)
  | .not s => s.free
  | .and s t => s.free ++ t.free
  | .ex i ss => (freeL ss).filter (· ≠ i)
/-- The variables a list reads. -/
def freeL : List QFml → List Nat
  | [] => []
  | s :: ss => s.free ++ freeL ss
end

theorem mem_freeL {j : Nat} : ∀ {ss : List QFml}, j ∈ freeL ss ↔ ∃ s ∈ ss, j ∈ s.free
  | [] => by simp only [freeL, List.not_mem_nil, false_and, exists_false]
  | s :: ss => by
    simp only [freeL, List.mem_append, mem_freeL, List.mem_cons, exists_eq_or_imp]

mutual
/-- **A formula reads only its free variables.** -/
theorem holds_congr : ∀ (s : QFml) (x y : Nat → Nat), (∀ j ∈ s.free, x j = y j) →
    (s.holds x ↔ s.holds y)
  | .atom φ m, x, y, h => by
    simp only [holds]
    apply AFml.holds_agree
    intro j hj
    exact h _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  | .not s, x, y, h => by
    simp only [holds]; exact not_congr (holds_congr s x y h)
  | .and s t, x, y, h => by
    simp only [holds]
    exact and_congr (holds_congr s x y fun j hj => h j (List.mem_append_left _ hj))
      (holds_congr t x y fun j hj => h j (List.mem_append_right _ hj))
  | .ex i ss, x, y, h => by
    simp only [holds]
    refine exists_congr fun n => holdsL_congr ss _ _ fun j hj => ?_
    simp only [updAt]
    split
    · rfl
    · next hji => exact h j (List.mem_filter.2 ⟨hj, by simp only [ne_eq, hji, not_false_eq_true, decide_true]⟩)
theorem holdsL_congr : ∀ (ss : List QFml) (x y : Nat → Nat), (∀ j ∈ freeL ss, x j = y j) →
    (holdsL ss x ↔ holdsL ss y)
  | [], _, _, _ => Iff.rfl
  | s :: ss, x, y, h => by
    simp only [holdsL]
    exact or_congr (holds_congr s x y fun j hj => h j (List.mem_append_left _ hj))
      (holdsL_congr ss x y fun j hj => h j (List.mem_append_right _ hj))
end

/-! ### Derivatives -/

/-- `true`. -/
abbrev tru : QFml := .atom .tt []
/-- `false`. -/
abbrev fls : QFml := .atom .ff []

/-- An atom, `true` or `false` when its formula is. -/
def mkAtom (φ : AFml) (m : List Nat) : QFml :=
  match φ with
  | .tt => tru
  | .ff => fls
  | φ => .atom φ m

/-- `¬φ`, worked out on `true` and `false`. -/
def mkNot : QFml → QFml
  | .atom .tt _ => fls
  | .atom .ff _ => tru
  | s => .not s

/-- `φ ∧ ψ`, worked out when either is `false` or both are `true`. -/
def mkAnd (s t : QFml) : QFml :=
  match s, t with
  | .atom .ff _, _ => fls
  | _, .atom .ff _ => fls
  | .atom .tt _, .atom .tt _ => tru
  | s, t => .and s t

/-- `∃ xᵢ. ⋁ S`, `false` members dropped, worked out when one is `true` or
none is left. -/
def mkEx (i : Nat) (l : List QFml) : QFml :=
  if tru ∈ l then tru
  else if (l.filter (· != fls)).isEmpty then fls
  else .ex i (l.filter (· != fls))

theorem holds_mkAtom (φ : AFml) (m : List Nat) (x : Nat → Nat) :
    (mkAtom φ m).holds x ↔ (QFml.atom φ m).holds x := by
  unfold mkAtom; split <;> simp only [holds, AFml.holds]

theorem holds_mkNot (s : QFml) (x : Nat → Nat) : (mkNot s).holds x ↔ ¬ s.holds x := by
  unfold mkNot; split <;> simp only [holds, AFml.holds, not_true_eq_false, not_false_eq_true]

theorem holds_mkAnd (s t : QFml) (x : Nat → Nat) : (mkAnd s t).holds x ↔ s.holds x ∧ t.holds x := by
  unfold mkAnd; split <;> simp_all only [holds, AFml.holds, false_and, and_false, and_self]

theorem holds_mkEx (i : Nat) (l : List QFml) (x : Nat → Nat) :
    (mkEx i l).holds x ↔ (QFml.ex i l).holds x := by
  have hf : ∀ y, holdsL (l.filter (· != fls)) y ↔ holdsL l y := by
    intro y
    simp only [holdsL_iff, List.mem_filter, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨s, ⟨hs, -⟩, h⟩; exact ⟨s, hs, h⟩
    · rintro ⟨s, hs, h⟩
      refine ⟨s, ⟨hs, fun e => ?_⟩, h⟩
      subst e; exact h
  unfold mkEx
  split
  · next ht =>
    simp only [holds, AFml.holds, true_iff]
    exact ⟨0, (holdsL_iff _ l).2 ⟨tru, ht, trivial⟩⟩
  · split
    · next he =>
      simp only [holds, AFml.holds, false_iff, not_exists]
      intro n hn
      rw [← hf] at hn
      rw [List.isEmpty_iff.1 he] at hn
      exact hn
    · simp only [holds, hf]

theorem mkAtom_cases (φ : AFml) (m : List Nat) :
    mkAtom φ m = tru ∨ mkAtom φ m = fls ∨ mkAtom φ m = .atom φ m := by
  unfold mkAtom; split <;> simp only [true_or, or_true]

theorem mkNot_cases (s : QFml) : mkNot s = tru ∨ mkNot s = fls ∨ mkNot s = .not s := by
  unfold mkNot; split <;> simp only [true_or, or_true]

theorem mkAnd_cases (s t : QFml) : mkAnd s t = tru ∨ mkAnd s t = fls ∨ mkAnd s t = .and s t := by
  unfold mkAnd; split <;> simp only [true_or, or_true]

theorem mkEx_cases (i : Nat) (l : List QFml) :
    mkEx i l = tru ∨ mkEx i l = fls ∨ mkEx i l = .ex i (l.filter (· != fls)) := by
  unfold mkEx; split
  · exact .inl rfl
  · split
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

mutual
/-- **What is left of a formula once the low bits `B` are read**: each atom
its `AFml.deriv` at its variables' bits; under `∃ xᵢ` both bits of `xᵢ`. -/
def deriv (B : Nat → Bool) : QFml → QFml
  | .atom φ m => mkAtom (φ.deriv (localBits B m φ.width)) m
  | .not s => mkNot (s.deriv B)
  | .and s t => mkAnd (s.deriv B) (t.deriv B)
  | .ex i ss => mkEx i (uniq (derivL (setBit B i false) ss ++ derivL (setBit B i true) ss))
/-- The derivatives of a list. -/
def derivL (B : Nat → Bool) : List QFml → List QFml
  | [] => []
  | s :: ss => s.deriv B :: derivL B ss
end

theorem derivL_eq_map (B : Nat → Bool) : ∀ ss : List QFml, derivL B ss = ss.map (deriv B)
  | [] => rfl
  | s :: ss => by rw [derivL, derivL_eq_map B ss, List.map_cons]

mutual
/-- **Reading the low bits keeps the meaning.** -/
theorem holds_deriv : ∀ (s : QFml) (x : Nat → Nat), s.holds x ↔ (s.deriv (bitsAt x)).holds (halve x)
  | .atom φ m, x => by
    simp only [deriv, holds_mkAtom, holds]
    rw [AFml.holds_deriv φ.width (fun j => x (m.getD j 0)) φ (Nat.le_refl _), lowBits_eq_map]
    rfl
  | .not s, x => by simp only [holds, deriv, holds_mkNot]; exact not_congr (holds_deriv s x)
  | .and s t, x => by
    simp only [holds, deriv, holds_mkAnd]; exact and_congr (holds_deriv s x) (holds_deriv t x)
  | .ex i ss, x => by
    simp only [deriv, holds_mkEx]
    simp only [holds, holdsL_uniq, holdsL_append]
    constructor
    · rintro ⟨n, hn⟩
      rw [holdsL_deriv ss, bitsAt_updAt, halve_updAt] at hn
      refine ⟨n / 2, ?_⟩
      cases hb : n % 2 == 1
      · rw [hb] at hn; exact .inl hn
      · rw [hb] at hn; exact .inr hn
    · rintro ⟨n, hn | hn⟩
      · refine ⟨2 * n, ?_⟩
        rw [holdsL_deriv ss, bitsAt_updAt, halve_updAt]
        have h1 : (2 * n % 2 == 1) = false := by rw [show 2 * n % 2 = 0 by omega]; rfl
        have h2 : 2 * n / 2 = n := by omega
        rw [h1, h2]; exact hn
      · refine ⟨2 * n + 1, ?_⟩
        rw [holdsL_deriv ss, bitsAt_updAt, halve_updAt]
        have h1 : ((2 * n + 1) % 2 == 1) = true := by rw [show (2 * n + 1) % 2 = 1 by omega]; rfl
        have h2 : (2 * n + 1) / 2 = n := by omega
        rw [h1, h2]; exact hn
theorem holdsL_deriv : ∀ (ss : List QFml) (x : Nat → Nat),
    holdsL ss x ↔ holdsL (derivL (bitsAt x) ss) (halve x)
  | [], _ => Iff.rfl
  | s :: ss, x => by simp only [holdsL, derivL]; exact or_congr (holds_deriv s x) (holdsL_deriv ss x)
end

mutual
/-- **The derivative reads only the free variables' bits.** -/
theorem deriv_congr : ∀ (s : QFml) (B B' : Nat → Bool), (∀ j ∈ s.free, B j = B' j) →
    s.deriv B = s.deriv B'
  | .atom φ m, B, B', h => by
    simp only [deriv, localBits]
    congr 2
    apply List.map_congr_left
    intro j hj
    exact h _ (List.mem_map.2 ⟨j, hj, rfl⟩)
  | .not s, B, B', h => by simp only [deriv, deriv_congr s B B' h]
  | .and s t, B, B', h => by
    simp only [deriv, deriv_congr s B B' fun j hj => h j (List.mem_append_left _ hj),
      deriv_congr t B B' fun j hj => h j (List.mem_append_right _ hj)]
  | .ex i ss, B, B', h => by
    have hb : ∀ b, derivL (setBit B i b) ss = derivL (setBit B' i b) ss := fun b =>
      derivL_congr ss _ _ fun j hj => by
        simp only [setBit]
        split
        · rfl
        · next hji => exact h j (List.mem_filter.2 ⟨hj, by simp only [ne_eq, hji, not_false_eq_true, decide_true]⟩)
    simp only [deriv, hb]
theorem derivL_congr : ∀ (ss : List QFml) (B B' : Nat → Bool), (∀ j ∈ freeL ss, B j = B' j) →
    derivL B ss = derivL B' ss
  | [], _, _, _ => rfl
  | s :: ss, B, B', h => by
    simp only [derivL, deriv_congr s B B' fun j hj => h j (List.mem_append_left _ hj),
      derivL_congr ss B B' fun j hj => h j (List.mem_append_right _ hj)]
end

/-! ### Finitely many derivatives -/

/-- Every list of length at most `k` over `L`. -/
def lists {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | k + 1, L => [] :: L.flatMap fun a => (lists k L).map (a :: ·)

theorem mem_lists {α : Type} {L : List α} : ∀ (k : Nat) (l : List α), (∀ a ∈ l, a ∈ L) →
    l.length ≤ k → l ∈ lists k L
  | 0, [], _, _ => List.mem_singleton.2 rfl
  | 0, _ :: _, _, h => by simp only [List.length_cons] at h; omega
  | _ + 1, [], _, _ => List.mem_cons_self
  | k + 1, a :: l, hl, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨a, hl a List.mem_cons_self,
      List.mem_map.2 ⟨l, mem_lists k l (fun b hb => hl b (List.mem_cons_of_mem _ hb)) h, rfl⟩⟩)

theorem of_mem_lists {α : Type} {L : List α} : ∀ {k : Nat} {l : List α}, l ∈ lists k L → ∀ a ∈ l, a ∈ L
  | 0, l, h, a, ha => by
    simp only [lists, List.mem_singleton] at h; subst h; cases ha
  | k + 1, l, h, a, ha => by
    simp only [lists, List.mem_cons, List.mem_flatMap, List.mem_map] at h
    rcases h with rfl | ⟨b, hb, l', hl', rfl⟩
    · cases ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hb
      · exact of_mem_lists hl' a ha

mutual
/-- **Every formula reading bits can lead to**: `true`, `false`, and one of
the same shape: an atom's `AFml.universe`; for `∃ xᵢ`, every list over the
universe of its body. -/
def univ : QFml → List QFml
  | .atom φ m => tru :: fls :: φ.universe.map (.atom · m)
  | .not s => tru :: fls :: s.univ.map .not
  | .and s t => tru :: fls :: s.univ.flatMap fun a => t.univ.map (.and a)
  | .ex i ss => tru :: fls :: (lists (univL ss).length (univL ss)).map (.ex i)
/-- The universes of a list, joined. -/
def univL : List QFml → List QFml
  | [] => []
  | s :: ss => s.univ ++ univL ss
end

theorem mem_univL {G : QFml} : ∀ {ss : List QFml}, G ∈ univL ss ↔ ∃ s ∈ ss, G ∈ s.univ
  | [] => by simp only [univL, List.not_mem_nil, false_and, exists_false]
  | s :: ss => by
    simp only [univL, List.mem_append, mem_univL, List.mem_cons, exists_eq_or_imp]

theorem mem_consts {G : QFml} {l : List QFml} (h : G = tru ∨ G = fls ∨ G ∈ l) : G ∈ tru :: fls :: l := by
  rcases h with rfl | rfl | h
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem tru_mem_univ (F : QFml) : tru ∈ F.univ := by cases F <;> exact mem_consts (.inl rfl)
theorem fls_mem_univ (F : QFml) : fls ∈ F.univ := by cases F <;> exact mem_consts (.inr (.inl rfl))

/-- A member of a universe: `true`, `false`, or of the formula's shape. -/
theorem mem_univ_cases {G : QFml} {l : List QFml} (h : G ∈ tru :: fls :: l) : G = tru ∨ G = fls ∨ G ∈ l := by
  rcases List.mem_cons.1 h with h | h
  · exact .inl h
  · rcases List.mem_cons.1 h with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)

mutual
/-- A formula is among the formulas it leads to. -/
theorem self_mem_univ : ∀ F : QFml, F ∈ F.univ
  | .atom φ m => mem_consts (.inr (.inr (List.mem_map.2 ⟨φ, AFml.self_mem_universe φ, rfl⟩)))
  | .not s => mem_consts (.inr (.inr (List.mem_map.2 ⟨s, self_mem_univ s, rfl⟩)))
  | .and s t => mem_consts (.inr (.inr
      (List.mem_flatMap.2 ⟨s, self_mem_univ s, List.mem_map.2 ⟨t, self_mem_univ t, rfl⟩⟩)))
  | .ex i ss => mem_consts (.inr (.inr
      (List.mem_map.2 ⟨ss, mem_lists _ _ (self_mem_univL ss) (length_le_univL ss), rfl⟩)))
theorem self_mem_univL : ∀ (ss : List QFml), ∀ s ∈ ss, s ∈ univL ss
  | [], _, h => nomatch h
  | s :: ss, t, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_append_left _ (self_mem_univ t)
    · exact List.mem_append_right _ (self_mem_univL ss t h)
theorem length_le_univL : ∀ (ss : List QFml), ss.length ≤ (univL ss).length
  | [] => Nat.le_refl _
  | s :: ss => by
    have h1 := length_le_univL ss
    have h2 : 0 < s.univ.length := List.length_pos_of_mem (self_mem_univ s)
    simp only [univL, List.length_cons, List.length_append]
    omega
end

theorem deriv_tru (B : Nat → Bool) : tru.deriv B = tru := rfl
theorem deriv_fls (B : Nat → Bool) : fls.deriv B = fls := rfl

mutual
/-- **Reading bits stays among the formulas.** -/
theorem deriv_mem_univ (B : Nat → Bool) : ∀ (F G : QFml), G ∈ F.univ → G.deriv B ∈ F.univ
  | .atom φ m, G, h => by
    rcases mem_univ_cases h with rfl | rfl | h
    · exact tru_mem_univ _
    · exact fls_mem_univ _
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 h
    rcases mkAtom_cases (ψ.deriv (localBits B m ψ.width)) m with e | e | e <;>
      simp only [deriv, e]
    · exact tru_mem_univ _
    · exact fls_mem_univ _
    · exact mem_consts (.inr (.inr (List.mem_map.2 ⟨_, AFml.deriv_mem_universe _ φ ψ hψ, rfl⟩)))
  | .not s, G, h => by
    rcases mem_univ_cases h with rfl | rfl | h
    · exact tru_mem_univ _
    · exact fls_mem_univ _
    obtain ⟨G', hG', rfl⟩ := List.mem_map.1 h
    rcases mkNot_cases (G'.deriv B) with e | e | e <;> simp only [deriv, e]
    · exact tru_mem_univ _
    · exact fls_mem_univ _
    · exact mem_consts (.inr (.inr (List.mem_map.2 ⟨_, deriv_mem_univ B s G' hG', rfl⟩)))
  | .and s t, G, h => by
    rcases mem_univ_cases h with rfl | rfl | h
    · exact tru_mem_univ _
    · exact fls_mem_univ _
    obtain ⟨a, ha, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h'
    rcases mkAnd_cases (a.deriv B) (b.deriv B) with e | e | e <;> simp only [deriv, e]
    · exact tru_mem_univ _
    · exact fls_mem_univ _
    · exact mem_consts (.inr (.inr (List.mem_flatMap.2 ⟨_, deriv_mem_univ B s a ha,
        List.mem_map.2 ⟨_, deriv_mem_univ B t b hb, rfl⟩⟩)))
  | .ex i ss, G, h => by
    rcases mem_univ_cases h with rfl | rfl | h
    · exact tru_mem_univ _
    · exact fls_mem_univ _
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
    have hsub := of_mem_lists hl
    have hin : ∀ a ∈ uniq (derivL (setBit B i false) l ++ derivL (setBit B i true) l), a ∈ univL ss := by
      intro a ha
      have ha := (mem_uniq a _).1 ha
      rw [derivL_eq_map, derivL_eq_map] at ha
      rcases List.mem_append.1 ha with ha | ha <;>
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
        exact deriv_mem_univL _ ss g (hsub g hg)
    rcases mkEx_cases i (uniq (derivL (setBit B i false) l ++ derivL (setBit B i true) l)) with e | e | e <;>
      simp only [deriv, e]
    · exact tru_mem_univ _
    · exact fls_mem_univ _
    · refine mem_consts (.inr (.inr (List.mem_map.2 ⟨_, mem_lists _ _ ?_ ?_, rfl⟩)))
      · exact fun a ha => hin a (List.mem_filter.1 ha).1
      · exact length_le_of_nodup _ ((nodup_uniq _).filter _) fun a ha => hin a (List.mem_filter.1 ha).1
theorem deriv_mem_univL (B : Nat → Bool) : ∀ (ss : List QFml) (G : QFml), G ∈ univL ss →
    G.deriv B ∈ univL ss
  | [], _, h => nomatch h
  | s :: ss, G, h => by
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append_left _ (deriv_mem_univ B s G h)
    · exact List.mem_append_right _ (deriv_mem_univL B ss G h)
end

theorem free_tru : tru.free = [] := rfl
theorem free_fls : fls.free = [] := rfl

mutual
/-- The formulas a formula leads to read no other variables. -/
theorem free_of_mem_univ : ∀ (F G : QFml), G ∈ F.univ → ∀ j ∈ G.free, j ∈ F.free
  | .atom φ m, G, h, j, hj => by
    rcases mem_univ_cases h with rfl | rfl | h
    · nomatch hj
    · nomatch hj
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 h
    have hw := AFml.width_of_mem_universe φ ψ hψ
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hj
    exact List.mem_map.2 ⟨k, List.mem_range.2 (Nat.lt_of_lt_of_le (List.mem_range.1 hk) hw), rfl⟩
  | .not s, G, h, j, hj => by
    rcases mem_univ_cases h with rfl | rfl | h
    · nomatch hj
    · nomatch hj
    obtain ⟨G', hG', rfl⟩ := List.mem_map.1 h
    exact free_of_mem_univ s G' hG' j hj
  | .and s t, G, h, j, hj => by
    rcases mem_univ_cases h with rfl | rfl | h
    · nomatch hj
    · nomatch hj
    obtain ⟨a, ha, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h'
    rcases List.mem_append.1 hj with hj | hj
    · exact List.mem_append_left _ (free_of_mem_univ s a ha j hj)
    · exact List.mem_append_right _ (free_of_mem_univ t b hb j hj)
  | .ex i ss, G, h, j, hj => by
    rcases mem_univ_cases h with rfl | rfl | h
    · nomatch hj
    · nomatch hj
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
    obtain ⟨hj, hji⟩ := List.mem_filter.1 hj
    obtain ⟨g, hg, hjg⟩ := mem_freeL.1 hj
    exact List.mem_filter.2 ⟨free_of_mem_univL ss g (of_mem_lists hl g hg) j hjg, hji⟩
theorem free_of_mem_univL : ∀ (ss : List QFml) (G : QFml), G ∈ univL ss →
    ∀ j ∈ G.free, j ∈ freeL ss
  | [], _, h, _, _ => nomatch h
  | s :: ss, G, h, j, hj => by
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append_left _ (free_of_mem_univ s G h j hj)
    · exact List.mem_append_right _ (free_of_mem_univL ss G h j hj)
end

/-! ### Nesting depth -/

mutual
/-- How deeply `∃` nests. -/
def depth : QFml → Nat
  | .atom .. => 0
  | .not s => s.depth
  | .and s t => max s.depth t.depth
  | .ex _ ss => depthL ss + 1
/-- The deepest of a list. -/
def depthL : List QFml → Nat
  | [] => 0
  | s :: ss => max s.depth (depthL ss)
end

theorem depthL_le : ∀ {ss : List QFml} {d : Nat}, (∀ s ∈ ss, s.depth ≤ d) → depthL ss ≤ d
  | [], _, _ => Nat.zero_le _
  | s :: _, _, h => Nat.max_le.2 ⟨h s List.mem_cons_self, depthL_le fun t ht => h t (List.mem_cons_of_mem _ ht)⟩

mutual
/-- The formulas a formula leads to nest no deeper. -/
theorem depth_of_mem_univ : ∀ (F G : QFml), G ∈ F.univ → G.depth ≤ F.depth
  | .atom φ m, G, h => by
    rcases mem_univ_cases h with rfl | rfl | h
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    obtain ⟨ψ, -, rfl⟩ := List.mem_map.1 h; exact Nat.le_refl _
  | .not s, G, h => by
    rcases mem_univ_cases h with rfl | rfl | h
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    obtain ⟨G', hG', rfl⟩ := List.mem_map.1 h
    exact depth_of_mem_univ s G' hG'
  | .and s t, G, h => by
    rcases mem_univ_cases h with rfl | rfl | h
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    obtain ⟨a, ha, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h'
    have := depth_of_mem_univ s a ha
    have := depth_of_mem_univ t b hb
    simp only [depth]; omega
  | .ex i ss, G, h => by
    rcases mem_univ_cases h with rfl | rfl | h
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
    simp only [depth, Nat.add_le_add_iff_right]
    exact depthL_le fun g hg => depth_of_mem_univL ss g (of_mem_lists hl g hg)
theorem depth_of_mem_univL : ∀ (ss : List QFml) (G : QFml), G ∈ univL ss → G.depth ≤ depthL ss
  | [], _, h => nomatch h
  | s :: ss, G, h => by
    rcases List.mem_append.1 h with h | h
    · exact Nat.le_trans (depth_of_mem_univ s G h) (Nat.le_max_left _ _)
    · exact Nat.le_trans (depth_of_mem_univL ss G h) (Nat.le_max_right _ _)
end

end QFml

/-! ## Reachability within a finite set

`reach` collects every state reachable from `seen` by `step`, identified by
`key`.  It terminates because the keys stay in a finite set `U` that is
never computed: it exists (`hfin`), and only bounds the recursion. -/

section Reach

variable {α β : Type} [DecidableEq β] (key : α → β) (step : α → List α)

/-- `acc` extended by the states of `as` whose key is neither in `seen`
nor already added. -/
def addKeys (seen : List β) : List α → List α → List α
  | acc, [] => acc
  | acc, a :: as =>
    if key a ∈ seen ∨ key a ∈ acc.map key then addKeys seen acc as else addKeys seen (a :: acc) as

theorem addKeys_sub (seen : List β) : ∀ (acc as : List α), ∀ a ∈ addKeys key seen acc as,
    a ∈ acc ∨ (a ∈ as ∧ key a ∉ seen)
  | acc, [], a, h => .inl h
  | acc, b :: as, a, h => by
    simp only [addKeys] at h
    split at h
    · rcases addKeys_sub seen acc as a h with h | ⟨h, h'⟩
      · exact .inl h
      · exact .inr ⟨List.mem_cons_of_mem _ h, h'⟩
    · next hb =>
      rcases addKeys_sub seen (b :: acc) as a h with h | ⟨h, h'⟩
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inr ⟨List.mem_cons_self, fun e => hb (.inl e)⟩
        · exact .inl h
      · exact .inr ⟨List.mem_cons_of_mem _ h, h'⟩

theorem addKeys_acc (seen : List β) : ∀ (acc as : List α), ∀ a ∈ acc, a ∈ addKeys key seen acc as
  | acc, [], a, h => h
  | acc, b :: as, a, h => by
    simp only [addKeys]
    split
    · exact addKeys_acc seen acc as a h
    · exact addKeys_acc seen (b :: acc) as a (List.mem_cons_of_mem _ h)

theorem addKeys_cover (seen : List β) : ∀ (acc as : List α), ∀ a ∈ as,
    key a ∈ seen ∨ key a ∈ (addKeys key seen acc as).map key
  | acc, [], a, h => nomatch h
  | acc, b :: as, a, h => by
    simp only [addKeys]
    rcases List.mem_cons.1 h with rfl | h
    · split
      · next hb =>
        rcases hb with hb | hb
        · exact .inl hb
        · obtain ⟨c, hc, he⟩ := List.mem_map.1 hb
          exact .inr (List.mem_map.2 ⟨c, addKeys_acc key seen acc as c hc, he⟩)
      · exact .inr (List.mem_map.2 ⟨a, addKeys_acc key seen (a :: acc) as a List.mem_cons_self, rfl⟩)
    · split
      · exact addKeys_cover seen acc as a h
      · exact addKeys_cover seen (b :: acc) as a h

theorem addKeys_nodup (seen : List β) : ∀ (acc as : List α), (acc.map key).Nodup →
    (∀ a ∈ acc, key a ∉ seen) →
    ((addKeys key seen acc as).map key).Nodup ∧ ∀ a ∈ addKeys key seen acc as, key a ∉ seen
  | acc, [], hn, hs => ⟨hn, hs⟩
  | acc, b :: as, hn, hs => by
    simp only [addKeys]
    split
    · exact addKeys_nodup seen acc as hn hs
    · next hb =>
      refine addKeys_nodup seen (b :: acc) as ?_ ?_
      · rw [List.map_cons]
        exact List.nodup_cons.2 ⟨fun h => hb (.inr h), hn⟩
      · intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact fun h => hb (.inl h)
        · exact hs a ha

/-- The states `step` adds to `seen` from `frontier`. -/
def reachNew (seen frontier : List α) : List α :=
  addKeys key (seen.map key) [] (frontier.flatMap step)

theorem reachNew_spec (seen frontier : List α) (hn : (seen.map key).Nodup) :
    ((reachNew key step seen frontier ++ seen).map key).Nodup ∧
      (∀ a ∈ reachNew key step seen frontier, ∃ b ∈ frontier, a ∈ step b) ∧
      ∀ b ∈ frontier, ∀ a ∈ step b, key a ∈ (reachNew key step seen frontier ++ seen).map key := by
  obtain ⟨hn', hs'⟩ := addKeys_nodup key (seen.map key) [] (frontier.flatMap step) List.nodup_nil
    (fun _ h => nomatch h)
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_append]
    refine List.nodup_append.2 ⟨hn', hn, ?_⟩
    intro x hx y hy e
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hs' a ha (e ▸ hy)
  · intro a ha
    rcases addKeys_sub key (seen.map key) [] _ a ha with h | ⟨h, -⟩
    · cases h
    · obtain ⟨b, hb, hab⟩ := List.mem_flatMap.1 h
      exact ⟨b, hb, hab⟩
  · intro b hb a ha
    rcases addKeys_cover key (seen.map key) [] _ a (List.mem_flatMap.2 ⟨b, hb, ha⟩) with h | h
    · rw [List.map_append]; exact List.mem_append_right _ h
    · rw [List.map_append]; exact List.mem_append_left _ h

theorem reach_len {P : β → Prop} (hfin : ∃ U : List β, ∀ b, P b → b ∈ U) (l : List α)
    (hs : ∀ a ∈ l, P (key a)) (hn : (l.map key).Nodup) : l.length ≤ (Classical.choose hfin).length := by
  have := length_le_of_nodup (Classical.choose hfin) hn (fun b hb => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact Classical.choose_spec hfin _ (hs a ha))
  rwa [List.length_map] at this

/-- **Every state reachable from `seen`**, `frontier` the states whose
successors are not looked at yet. -/
def reach (P : β → Prop) (hP : ∀ a, P (key a) → ∀ b ∈ step a, P (key b))
    (hfin : ∃ U : List β, ∀ b, P b → b ∈ U) (seen frontier : List α)
    (hs : ∀ a ∈ seen, P (key a)) (hn : (seen.map key).Nodup) (hf : ∀ a ∈ frontier, a ∈ seen) :
    List α :=
  if h : (reachNew key step seen frontier).isEmpty then seen
  else
    reach P hP hfin (reachNew key step seen frontier ++ seen) (reachNew key step seen frontier)
      (by
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · obtain ⟨b, hb, hab⟩ := (reachNew_spec key step seen frontier hn).2.1 a ha
          exact hP b (hs b (hf b hb)) a hab
        · exact hs a ha)
      (reachNew_spec key step seen frontier hn).1
      (fun a ha => List.mem_append_left _ ha)
termination_by (Classical.choose hfin).length + 1 - seen.length
decreasing_by
  have hl := reach_len key hfin (reachNew key step seen frontier ++ seen)
    (by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨b, hb, hab⟩ := (reachNew_spec key step seen frontier hn).2.1 a ha
        exact hP b (hs b (hf b hb)) a hab
      · exact hs a ha)
    (reachNew_spec key step seen frontier hn).1
  have hpos : 0 < (reachNew key step seen frontier).length :=
    List.length_pos_iff.2 (fun e => h (by rw [e]; rfl))
  rw [List.length_append] at hl
  rw [List.length_append]
  omega

/-- **What `reach` returns**: it keeps `seen`, keeps every invariant of the
steps, and is closed under `step` up to keys. -/
theorem reach_spec (P : β → Prop) (hP : ∀ a, P (key a) → ∀ b ∈ step a, P (key b))
    (hfin : ∃ U : List β, ∀ b, P b → b ∈ U) (Inv : α → Prop) (hInv : ∀ a, Inv a → ∀ b ∈ step a, Inv b)
    (seen frontier : List α)
    (hs : ∀ a ∈ seen, P (key a)) (hn : (seen.map key).Nodup) (hf : ∀ a ∈ frontier, a ∈ seen)
    (hI : ∀ a ∈ seen, Inv a)
    (hC : ∀ a ∈ seen, a ∈ frontier ∨ ∀ b ∈ step a, key b ∈ seen.map key) :
    (∀ a ∈ seen, a ∈ reach key step P hP hfin seen frontier hs hn hf) ∧
      (∀ a ∈ reach key step P hP hfin seen frontier hs hn hf, Inv a) ∧
      ∀ a ∈ reach key step P hP hfin seen frontier hs hn hf, ∀ b ∈ step a,
        key b ∈ (reach key step P hP hfin seen frontier hs hn hf).map key := by
  by_cases h : (reachNew key step seen frontier).isEmpty
  · rw [reach, dif_pos h]
    refine ⟨fun a ha => ha, hI, fun a ha b hb => ?_⟩
    rcases hC a ha with hfr | hc
    · have := (reachNew_spec key step seen frontier hn).2.2 a hfr b hb
      rwa [List.isEmpty_iff.1 h, List.nil_append] at this
    · exact hc b hb
  · rw [reach, dif_neg h]
    have hsp := reachNew_spec key step seen frontier hn
    have ih := reach_spec P hP hfin Inv hInv (reachNew key step seen frontier ++ seen)
      (reachNew key step seen frontier)
      (by
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · obtain ⟨b, hb, hab⟩ := hsp.2.1 a ha
          exact hP b (hs b (hf b hb)) a hab
        · exact hs a ha)
      hsp.1 (fun a ha => List.mem_append_left _ ha)
      (by
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · obtain ⟨b, hb, hab⟩ := hsp.2.1 a ha
          exact hInv b (hI b (hf b hb)) a hab
        · exact hI a ha)
      (by
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · exact .inl ha
        · refine .inr fun b hb => ?_
          rcases hC a ha with hfr | hc
          · exact hsp.2.2 a hfr b hb
          · rw [List.map_append]; exact List.mem_append_right _ (hc b hb))
    exact ⟨fun a ha => ih.1 a (List.mem_append_right _ ha), ih.2⟩
termination_by (Classical.choose hfin).length + 1 - seen.length
decreasing_by
  have hl := reach_len key hfin (reachNew key step seen frontier ++ seen)
    (by
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨b, hb, hab⟩ := (reachNew_spec key step seen frontier hn).2.1 a ha
        exact hP b (hs b (hf b hb)) a hab
      · exact hs a ha)
    (reachNew_spec key step seen frontier hn).1
  have hpos : 0 < (reachNew key step seen frontier).length :=
    List.length_pos_iff.2 (fun e => h (by rw [e]; rfl))
  rw [List.length_append] at hl
  rw [List.length_append]
  omega

end Reach

namespace QFml

/-! ## The zero test -/

/-- The low bits of `updAt 0 i n`, `b` the low bit of `n`. -/
def zeroBits (i : Nat) (b : Bool) : Nat → Bool := setBit (fun _ => false) i b

/-- Both bits of `xᵢ` read, every other bit `0`. -/
def zeroStep (i : Nat) (s : QFml) : List QFml := [s.deriv (zeroBits i false), s.deriv (zeroBits i true)]

theorem zeroStep_mem (ss : List QFml) (i : Nat) :
    ∀ a, id a ∈ univL ss → ∀ b ∈ zeroStep i a, id b ∈ univL ss := by
  intro a ha b hb
  simp only [zeroStep, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;> exact deriv_mem_univL _ ss a ha

theorem nodup_map_id_uniq (ss : List QFml) : ((uniq ss).map id).Nodup := by
  rw [List.map_id]; exact nodup_uniq ss

/-- **The formulas `∃ xᵢ. ⋁ S` reaches with the other variables `0`.** -/
def zeroReach (i : Nat) (ss : List QFml) : List QFml :=
  reach id (zeroStep i) (· ∈ univL ss) (zeroStep_mem ss i) ⟨univL ss, fun _ h => h⟩
    (uniq ss) (uniq ss) (fun a ha => self_mem_univL ss a ((mem_uniq a ss).1 ha))
    (nodup_map_id_uniq ss) (fun _ h => h)

theorem zeroReach_spec (i : Nat) (ss : List QFml) (Inv : QFml → Prop)
    (hInv : ∀ a, Inv a → ∀ b ∈ zeroStep i a, Inv b) (hI : ∀ a ∈ ss, Inv a) :
    (∀ a ∈ ss, a ∈ zeroReach i ss) ∧ (∀ a ∈ zeroReach i ss, Inv a ∧ a ∈ univL ss) ∧
      ∀ a ∈ zeroReach i ss, ∀ b ∈ zeroStep i a, b ∈ zeroReach i ss := by
  have h := reach_spec id (zeroStep i) (· ∈ univL ss) (zeroStep_mem ss i) ⟨univL ss, fun _ h => h⟩
    (fun a => Inv a ∧ a ∈ univL ss)
    (fun a ha b hb => ⟨hInv a ha.1 b hb, zeroStep_mem ss i a ha.2 b hb⟩)
    (uniq ss) (uniq ss) (fun a ha => self_mem_univL ss a ((mem_uniq a ss).1 ha))
    (nodup_map_id_uniq ss) (fun _ h => h)
    (fun a ha => ⟨hI a ((mem_uniq a ss).1 ha), self_mem_univL ss a ((mem_uniq a ss).1 ha)⟩)
    (fun a ha => .inl ha)
  refine ⟨fun a ha => h.1 a ((mem_uniq a ss).2 ha), h.2.1, fun a ha b hb => ?_⟩
  have := h.2.2 a ha b hb
  rwa [List.map_id] at this

theorem depth_le_depthL {s : QFml} : ∀ {ss : List QFml}, s ∈ ss → s.depth ≤ depthL ss
  | _ :: _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (depth_le_depthL h) (Nat.le_max_right _ _)

theorem lex_lt {a a' b b' : Nat} (h1 : a ≤ a') (h2 : b < b') :
    Prod.Lex (· < ·) (· < ·) (a, b) (a', b') := by
  rcases Nat.lt_or_eq_of_le h1 with h | rfl
  · exact .left _ _ h
  · exact .right _ h2

/-- **The formula at zero**: `∃ xᵢ. ⋁ S` holds with every other variable
`0` when some formula `S` reaches so holds at zero. -/
def atZero : QFml → Bool
  | .atom φ _ => φ.atZero
  | .not s => !s.atZero
  | .and s t => s.atZero && t.atZero
  | .ex i ss => (ss.attach.any fun t => t.1.atZero) || (zeroReach i ss).attach.any fun t => t.1.atZero
termination_by s => (s.depth, sizeOf s)
decreasing_by
  · exact lex_lt (Nat.le_refl _) (by simp only [not.sizeOf_spec]; omega)
  · exact lex_lt (Nat.le_max_left _ _) (by simp only [and.sizeOf_spec]; omega)
  · exact lex_lt (Nat.le_max_right _ _) (by simp only [and.sizeOf_spec]; omega)
  · rename_i i ss
    exact .left _ _ (Nat.lt_succ_of_le (depth_le_depthL t.2))
  · rename_i i ss
    exact .left _ _ (Nat.lt_succ_of_le (depth_of_mem_univL ss t.1 ((zeroReach_spec i ss (fun _ => True)
      (fun _ _ _ _ => trivial) (fun _ _ => trivial)).2.1 t.1 t.2).2))

/-- `updAt 0 i n`'s bits are `zeroBits`. -/
theorem bitsAt_zero_updAt (i n : Nat) :
    bitsAt (updAt (fun _ => 0) i n) = zeroBits i (n % 2 == 1) := by
  rw [bitsAt_updAt]; rfl

theorem halve_zero_updAt (i n : Nat) : halve (updAt (fun _ => 0) i n) = updAt (fun _ => 0) i (n / 2) := by
  funext j; simp only [halve, updAt]; split <;> rfl

theorem zero_updAt_zero (i : Nat) : updAt (fun _ => 0) i 0 = fun _ => 0 := by
  funext j; simp only [updAt]; split <;> rfl

theorem any_attach_iff {α : Type} (l : List α) (f : α → Bool) :
    (l.attach.any fun t => f t.1) = true ↔ ∃ a ∈ l, f a = true := by
  simp only [List.any_eq_true, List.mem_attach, true_and, Subtype.exists]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩

/-- **At zero, a formula is its `atZero`.** -/
theorem holds_zero : ∀ (s : QFml) (x : Nat → Nat), (∀ j ∈ s.free, x j = 0) →
    (s.holds x ↔ s.atZero = true)
  | .atom φ m, x, h => by
    rw [atZero]
    exact AFml.holds_zero _ φ fun j hj => h _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  | .not s, x, h => by
    rw [atZero, holds, holds_zero s x h, Bool.not_eq_true', Bool.eq_false_iff]
  | .and s t, x, h => by
    rw [atZero, holds, holds_zero s x fun j hj => h j (List.mem_append_left _ hj),
      holds_zero t x fun j hj => h j (List.mem_append_right _ hj), Bool.and_eq_true]
  | .ex i ss, x, h => by
    have IH : ∀ t ∈ zeroReach i ss, (t.holds (fun _ => 0) ↔ t.atZero = true) :=
      fun t ht => holds_zero t (fun _ => 0) (fun _ _ => rfl)
    rw [atZero, Bool.or_eq_true, any_attach_iff, any_attach_iff]
    have hx : ∀ n, holdsL ss (updAt x i n) ↔ holdsL ss (updAt (fun _ => 0) i n) := fun n =>
      holdsL_congr ss _ _ fun j hj => by
        simp only [updAt]
        split
        · rfl
        · next hji => exact h j (List.mem_filter.2 ⟨hj, by simp only [ne_eq, hji, not_false_eq_true, decide_true]⟩)
    simp only [holds, hx]
    let Inv : QFml → Prop := fun t =>
      ∀ n, t.holds (updAt (fun _ => 0) i n) → ∃ n', holdsL ss (updAt (fun _ => 0) i n')
    have hInv : ∀ a, Inv a → ∀ b ∈ zeroStep i a, Inv b := by
      intro a ha b hb n hn
      simp only [zeroStep, List.mem_cons, List.not_mem_nil, or_false] at hb
      have key : ∀ bb : Bool, (a.deriv (zeroBits i bb)).holds (updAt (fun _ => 0) i n) →
          a.holds (updAt (fun _ => 0) i ((if bb then 1 else 0) + 2 * n)) := by
        intro bb hd
        rw [holds_deriv, bitsAt_zero_updAt, halve_zero_updAt]
        have h1 : (((if bb then 1 else 0) + 2 * n) % 2 == 1) = bb := by
          cases bb
          · rw [show ((if false = true then 1 else 0) + 2 * n) % 2 = 0 by simp only [Bool.false_eq_true, ↓reduceIte]; omega]; rfl
          · rw [show ((if true = true then 1 else 0) + 2 * n) % 2 = 1 by simp only [↓reduceIte]; omega]; rfl
        have h2 : ((if bb then 1 else 0) + 2 * n) / 2 = n := by cases bb <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
        rw [h1, h2]; exact hd
      rcases hb with rfl | rfl
      · exact ha _ (key false hn)
      · exact ha _ (key true hn)
    have hI : ∀ a ∈ ss, Inv a := fun a ha n hn => ⟨n, (holdsL_iff _ ss).2 ⟨a, ha, hn⟩⟩
    obtain ⟨hseen, hR, hclosed⟩ := zeroReach_spec i ss Inv hInv hI
    rw [or_iff_right_of_imp fun ⟨s, hs, hz⟩ => ⟨s, hseen s hs, hz⟩]
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨s, hs, hsn⟩ := (holdsL_iff _ ss).1 hn
      suffices C : ∀ n, ∀ t ∈ zeroReach i ss, t.holds (updAt (fun _ => 0) i n) →
          ∃ t' ∈ zeroReach i ss, t'.atZero = true from C n s (hseen s hs) hsn
      intro n
      induction n using Nat.strongRecOn with
      | _ n ihn =>
        intro t ht htn
        by_cases h0 : n = 0
        · subst h0
          rw [zero_updAt_zero] at htn
          exact ⟨t, ht, (IH t ht).1 htn⟩
        · rw [holds_deriv, bitsAt_zero_updAt, halve_zero_updAt] at htn
          have hmem : t.deriv (zeroBits i (n % 2 == 1)) ∈ zeroReach i ss := by
            apply hclosed t ht
            cases n % 2 == 1 <;> simp only [zeroStep, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
          exact ihn (n / 2) (by omega) _ hmem htn
    · rintro ⟨t, ht, hz⟩
      have h0 : t.holds (updAt (fun _ => 0) i 0) := by rw [zero_updAt_zero]; exact (IH t ht).2 hz
      exact (hR t ht).1 0 h0
termination_by s => (s.depth, sizeOf s)
decreasing_by
  · exact lex_lt (Nat.le_refl _) (by simp only [not.sizeOf_spec]; omega)
  · exact lex_lt (Nat.le_max_left _ _) (by simp only [and.sizeOf_spec]; omega)
  · exact lex_lt (Nat.le_max_right _ _) (by simp only [and.sizeOf_spec]; omega)
  · exact .left _ _ (Nat.lt_succ_of_le (depth_of_mem_univL ss t ((zeroReach_spec i ss (fun _ => True)
      (fun _ _ _ _ => trivial) (fun _ _ => trivial)).2.1 t ht).2))

/-! ## The search -/

/-- The bits `B` put back below the halved assignment `y`. -/
def withBitsAt (B : Nat → Bool) (y : Nat → Nat) : Nat → Nat := fun j => (if B j then 1 else 0) + 2 * y j

theorem bitsAt_withBitsAt (B : Nat → Bool) (y : Nat → Nat) : bitsAt (withBitsAt B y) = B := by
  funext j
  simp only [bitsAt, withBitsAt]
  cases B j
  · rw [show ((if false = true then 1 else 0) + 2 * y j) % 2 = 0 by simp only [Bool.false_eq_true, ↓reduceIte]; omega]; rfl
  · rw [show ((if true = true then 1 else 0) + 2 * y j) % 2 = 1 by simp only [↓reduceIte]; omega]; rfl

theorem halve_withBitsAt (B : Nat → Bool) (y : Nat → Nat) : halve (withBitsAt B y) = y := by
  funext j
  simp only [halve, withBitsAt]
  cases B j <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A reachable state with the reconstruction of its assignments: the
proof is erased, the computation keeps the formula and the function. -/
structure Node (root : QFml) where
  state : QFml
  back : (Nat → Nat) → Nat → Nat
  correct : ∀ y, state.holds y ↔ root.holds (back y)

namespace Node

variable {root : QFml}

/-- The formula itself. -/
def initial (root : QFml) : Node root := ⟨root, id, fun _ => Iff.rfl⟩

/-- Reading the bits `B`. -/
def child (n : Node root) (B : Nat → Bool) : Node root where
  state := n.state.deriv B
  back := fun y => n.back (withBitsAt B y)
  correct := by
    intro y
    have h := holds_deriv n.state (withBitsAt B y)
    rw [bitsAt_withBitsAt, halve_withBitsAt] at h
    exact h.symm.trans (n.correct _)

end Node

/-- The bits `v` given to the variables `L`, in order; `false` elsewhere. -/
def assignBits (L : List Nat) (v : List Bool) : Nat → Bool := fun j => ((L.zip v).lookup j).getD false

theorem assignBits_map (B : Nat → Bool) : ∀ (L : List Nat), ∀ j ∈ L, assignBits L (L.map B) j = B j
  | [], _, h => nomatch h
  | a :: L, j, h => by
    simp only [assignBits, List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases hj : j = a
    · subst hj; simp only [beq_self_eq_true, Option.getD_some]
    · have := assignBits_map B L j ((List.mem_cons.1 h).resolve_left hj)
      simp only [assignBits] at this
      have hb : (j == a) = false := by simp only [beq_eq_false_iff_ne, ne_eq, hj, not_false_eq_true]
      rw [hb]; exact this

/-- The free variables, once each. -/
def vars (root : QFml) : List Nat := uniq root.free

/-- Every bit successor. -/
def step (root : QFml) (n : Node root) : List (Node root) :=
  (vecs (vars root).length).map fun v => n.child (assignBits (vars root) v)

theorem step_mem (root : QFml) :
    ∀ a : Node root, a.state ∈ root.univ → ∀ b ∈ step root a, b.state ∈ root.univ := by
  intro a ha b hb
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hb
  exact deriv_mem_univ _ root a.state ha

theorem initial_nodup (root : QFml) : ([Node.initial root].map Node.state).Nodup :=
  List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩

/-- **Every state reachable from the formula**, with reconstructions. -/
def nodes (root : QFml) : List (Node root) :=
  reach Node.state (step root) (· ∈ root.univ) (step_mem root) ⟨root.univ, fun _ h => h⟩
    [Node.initial root] [Node.initial root]
    (fun a ha => by rw [List.mem_singleton.1 ha]; exact self_mem_univ root)
    (initial_nodup root) (fun _ h => h)

theorem nodes_spec (root : QFml) :
    Node.initial root ∈ nodes root ∧ (∀ n ∈ nodes root, n.state ∈ root.univ) ∧
      ∀ n ∈ nodes root, ∀ c ∈ step root n, c.state ∈ (nodes root).map Node.state := by
  have h := reach_spec Node.state (step root) (· ∈ root.univ) (step_mem root) ⟨root.univ, fun _ h => h⟩
    (fun n => n.state ∈ root.univ) (step_mem root) [Node.initial root] [Node.initial root]
    (fun a ha => by rw [List.mem_singleton.1 ha]; exact self_mem_univ root)
    (initial_nodup root) (fun _ h => h)
    (fun a ha => by rw [List.mem_singleton.1 ha]; exact self_mem_univ root)
    (fun a ha => .inl ha)
  exact ⟨h.1 _ List.mem_cons_self, h.2.1, h.2.2⟩

/-- The sum of the variables `L`. -/
def sumOn : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | j :: L, x => x j + sumOn L x

theorem sumOn_eq_zero : ∀ (L : List Nat) (x : Nat → Nat), sumOn L x = 0 → ∀ j ∈ L, x j = 0
  | [], _, _, _, h => nomatch h
  | a :: L, x, h, j, hj => by
    simp only [sumOn] at h
    rcases List.mem_cons.1 hj with rfl | hj
    · omega
    · exact sumOn_eq_zero L x (by omega) j hj

theorem sumOn_halve_le : ∀ (L : List Nat) (x : Nat → Nat), sumOn L (halve x) ≤ sumOn L x
  | [], _ => Nat.le_refl _
  | a :: L, x => by
    have := sumOn_halve_le L x
    simp only [sumOn, halve] at *
    omega

theorem sumOn_halve_lt : ∀ (L : List Nat) (x : Nat → Nat), 0 < sumOn L x → sumOn L (halve x) < sumOn L x
  | [], _, h => absurd h (Nat.lt_irrefl 0)
  | a :: L, x, h => by
    have hle := sumOn_halve_le L x
    simp only [sumOn, halve] at *
    by_cases h0 : x a = 0
    · have := sumOn_halve_lt L x (by omega)
      omega
    · omega

/-- Collect every reachable state, and check each at zero. -/
def search (root : QFml) : Bool := (nodes root).all (·.state.atZero)

/-- **The search decides validity.**  A valid formula's reachable states
are valid (each is the formula at reconstructed assignments), so hold at
zero; conversely the states found are closed under reading bits, so by
induction on the sum of the free variables every one holds everywhere. -/
theorem search_iff (root : QFml) : root.search = true ↔ root.Valid := by
  obtain ⟨hinit, huniv, hclosed⟩ := nodes_spec root
  constructor
  · intro hall
    have hz : ∀ n ∈ nodes root, n.state.atZero = true := fun n hn => List.all_eq_true.1 hall n hn
    have hfree : ∀ n ∈ nodes root, ∀ j ∈ n.state.free, j ∈ vars root := fun n hn j hj =>
      (mem_uniq j _).2 (free_of_mem_univ root n.state (huniv n hn) j hj)
    suffices H : ∀ m (x : Nat → Nat), sumOn (vars root) x = m → ∀ n ∈ nodes root, n.state.holds x from
      fun x => H _ x rfl _ hinit
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro x hm n hn
      by_cases h0 : m = 0
      · subst h0
        exact (holds_zero n.state x fun j hj => sumOn_eq_zero _ x hm j (hfree n hn j hj)).2 (hz n hn)
      · rw [holds_deriv]
        have he : n.state.deriv (bitsAt x) =
            n.state.deriv (assignBits (vars root) ((vars root).map (bitsAt x))) :=
          deriv_congr _ _ _ fun j hj => (assignBits_map _ _ j (hfree n hn j hj)).symm
        have hc : (n.child (assignBits (vars root) ((vars root).map (bitsAt x)))) ∈ step root n :=
          List.mem_map.2 ⟨_, mem_vecs (List.length_map _), rfl⟩
        obtain ⟨n', hn', he'⟩ := List.mem_map.1 (hclosed n hn _ hc)
        rw [he]
        show (n.child _).state.holds (halve x)
        rw [← he']
        exact ih _ (hm ▸ sumOn_halve_lt _ x (by omega)) _ rfl n' hn'
  · intro hv
    exact List.all_eq_true.2 fun n _ =>
      (holds_zero n.state (fun _ => 0) fun _ _ => rfl).1 ((n.correct _).2 (hv _))

mutual
/-- Every atom simplified (`AFml.simp`). -/
def simp : QFml → QFml
  | .atom φ m => mkAtom φ.simp m
  | .not s => mkNot s.simp
  | .and s t => mkAnd s.simp t.simp
  | .ex i ss => mkEx i (simpL ss)
/-- Every formula of a list simplified. -/
def simpL : List QFml → List QFml
  | [] => []
  | s :: ss => s.simp :: simpL ss
end

mutual
/-- **Simplifying keeps the meaning.** -/
theorem holds_simp : ∀ (s : QFml) (x : Nat → Nat), s.simp.holds x ↔ s.holds x
  | .atom φ m, x => (holds_mkAtom _ m x).trans (AFml.holds_simp _ φ)
  | .not s, x => by simp only [simp, holds_mkNot, holds]; exact not_congr (holds_simp s x)
  | .and s t, x => by
    simp only [simp, holds_mkAnd, holds]; exact and_congr (holds_simp s x) (holds_simp t x)
  | .ex i ss, x => by
    simp only [simp, holds_mkEx, holds]; exact exists_congr fun n => holdsL_simp ss _
theorem holdsL_simp : ∀ (ss : List QFml) (x : Nat → Nat), holdsL (simpL ss) x ↔ holdsL ss x
  | [], _ => Iff.rfl
  | s :: ss, x => by simp only [simpL, holdsL]; exact or_congr (holds_simp s x) (holdsL_simp ss x)
end

/-- **Decide** a quantified formula: simplify its atoms, then search. -/
def decide (root : QFml) : Bool := root.simp.search

/-- **`decide` decides validity**: `true` exactly for the valid formulas. -/
theorem decide_iff (root : QFml) : root.decide = true ↔ root.Valid :=
  (search_iff root.simp).trans (forall_congr' fun x => holds_simp root x)

/-- **Proof or counterassignment** from one traversal: a reachable state
false at zero is false at `0`, so the formula is false at its
reconstruction. -/
def verifyCore (root : QFml) : Sum (PLift root.Valid) { x : Nat → Nat // ¬ root.holds x } :=
  match h : (nodes root).find? (fun n => !n.state.atZero) with
  | some n => .inr ⟨n.back (fun _ => 0), fun hv => by
      have hn : n.state.atZero = false := by simpa only [Bool.not_eq_true'] using List.find?_some h
      have ht := (holds_zero n.state (fun _ => 0) fun _ _ => rfl).1 ((n.correct _).2 hv)
      exact Bool.noConfusion (hn.symm.trans ht)⟩
  | none => .inl ⟨(search_iff root).1 (List.all_eq_true.2 fun n hn => by
      have hx := List.find?_eq_none.1 h n hn
      cases he : n.state.atZero with
      | true => rfl
      | false => exact (hx (by rw [he]; rfl)).elim)⟩


/-- **Proof or counterassignment**, from one traversal of the simplified
formula's states. -/
def verify (root : QFml) : Sum (PLift root.Valid) { x : Nat → Nat // ¬ root.holds x } :=
  match verifyCore root.simp with
  | .inl h => .inl ⟨fun x => (holds_simp root x).1 (h.down x)⟩
  | .inr cm => .inr ⟨cm.1, fun h => cm.2 ((holds_simp root cm.1).2 h)⟩

end QFml

/-- info: 'Solidity.Linear.QFml.decide_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QFml.decide_iff

/-- info: 'Solidity.Linear.QFml.verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QFml.verify

end Solidity.Linear

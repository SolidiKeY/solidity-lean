/-!
# Hash collisions: the per-run premise and the birthday bound

The user's decision on hash collisions (G01 Q3 / G04 Q1,
`docs/solidity-scope.md`, "User decisions (2026-10-29)") has two halves, and
this module states both, dependency-free:

* **The per-run premise.** `CollisionFree f xs` says that the hash `f` does not
  collide on the preimages `xs` an execution prefix hashed. It is closed under
  sublists, prefixes and `[]`, so a premise about a whole run gives one about
  every prefix (`CollisionFree.sublist`, `CollisionFree.of_prefix`). Global
  injectivity of `f` stays forbidden: `no_injective_slot_encoding`
  (`Bridge/SolidityBridge/ExternalEvm/Obstructions.lean`) proves no
  injective numeric encoding of slots exists.
* **The random-oracle bound.** A random function into `N` values, restricted
  to `q` distinct inputs, is modelled as one of the `N ^ q` output tuples
  (`tuples N q`), each equally likely; that a uniform function on a larger
  domain gives the same bound is the non-adaptive case of
  `eagerAdaptiveBound` (`Solidity/Hash/Adaptive.lean`). At most
  `q(q-1)/2 · N^(q-1)` of them collide
  (`collisions_le`), so the collision probability is at most
  `q(q-1)/(2N) ≤ q²/(2N)` (`collision_prob_le`, `collision_prob_le_sq`), that is
  `q²/2²⁵⁷` for a 256-bit hash (`keccak_collision_prob_le`).

* **The region premise.** The second-round decision extends the premise to
  the regions above hashed slots: `RegionsDisjoint N L f roots xs` says the
  length-`L` regions at the hashes of `xs` pairwise do not overlap modulo `N`
  and cover no root slot (`Near`, `Covers`, read by `near_of_overlap` and
  `covers_of_hit`). It implies `CollisionFree` for `L > 0`. Its bound,
  `q(q-1)(2L-1)/(2N) + q·|roots|·L/N`, is `keccak_region_prob_le`, about
  `q²L/2²⁵⁶ + q·R·L/2²⁵⁶` for keccak.

The counting is a union bound over pairs, done incrementally: a tuple
`a :: t` collides if `t` already does (a pair among the first `q` outputs) or if
`a` equals one of the `q` outputs of `t` (the `q` pairs with the new index), so
`C(q+1) ≤ N · C(q) + q · N^q` (`collisions_succ_le`). Probabilities are stated
cross-multiplied over `Nat` (`2 * N * bad ≤ q * (q - 1) * N ^ q` reads
`bad / N^q ≤ q(q-1)/(2N)`), so no rationals are needed; every proof is by
induction, with no `decide` tactic.

**Scope of the bound.** The main bound fixes the `q` inputs before the
oracle is sampled (non-adaptive queries); a run that hashes a preimage twice
counts it once (`keccak_premise_fails_prob_le_dedup`). Queries that depend on
earlier answers are covered here under lazy sampling for strategies that
never repeat a query (`adaptive_lazy_collision_prob_le`, where the event
reduces to the non-adaptive one). An oracle fixed before an adaptive game is
`EagerAdaptiveBound` below; `Solidity/Hash/Adaptive.lean` proves it, together
with repeated queries, early stopping and the region premise
(`docs/feature-work/hash-collision-bound.md`, "Adaptive queries").
-/

namespace Solidity.Hash

/-! ## The per-run premise -/

/-- `f` does not collide on the preimages `xs`: equal images on `xs` come from
equal preimages. This is the shape assigned to the G01 contract revision for
the per-run hash premise. -/
def CollisionFree {α β : Type _} (f : α → β) (xs : List α) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y

section Premise
variable {α β : Type _} {f : α → β}

@[simp] theorem CollisionFree.nil : CollisionFree f [] := by
  intro x hx; cases hx

theorem CollisionFree.singleton (x : α) : CollisionFree f [x] := by
  intro a ha b hb _
  simp only [List.mem_singleton] at ha hb
  rw [ha, hb]

/-- Collision freedom on `ys` gives it on every list whose elements are in
`ys`; sublists, prefixes and suffixes are instances. -/
theorem CollisionFree.mono {xs ys : List α} (h : CollisionFree f ys)
    (hsub : ∀ x ∈ xs, x ∈ ys) : CollisionFree f xs :=
  fun x hx y hy hxy => h x (hsub x hx) y (hsub y hy) hxy

theorem CollisionFree.sublist {xs ys : List α} (h : CollisionFree f ys)
    (hs : xs.Sublist ys) : CollisionFree f xs :=
  h.mono fun _ hx => hs.subset hx

theorem CollisionFree.of_prefix {xs ys : List α} (h : CollisionFree f ys)
    (hp : xs <+: ys) : CollisionFree f xs :=
  h.sublist hp.sublist

theorem CollisionFree.of_suffix {xs ys : List α} (h : CollisionFree f ys)
    (hp : xs <:+ ys) : CollisionFree f xs :=
  h.sublist hp.sublist

theorem CollisionFree.append_left {xs ys : List α} (h : CollisionFree f (xs ++ ys)) :
    CollisionFree f xs :=
  h.mono fun _ hx => List.mem_append_left ys hx

theorem CollisionFree.append_right {xs ys : List α} (h : CollisionFree f (xs ++ ys)) :
    CollisionFree f ys :=
  h.mono fun _ hy => List.mem_append_right xs hy

/-- Two collision-free lists join when no image of one meets an image of the
other at a different preimage. -/
theorem collisionFree_append {xs ys : List α} :
    CollisionFree f (xs ++ ys) ↔
      CollisionFree f xs ∧ CollisionFree f ys ∧
        ∀ x ∈ xs, ∀ y ∈ ys, f x = f y → x = y := by
  constructor
  · intro h
    exact ⟨h.append_left, h.append_right, fun x hx y hy =>
      h x (List.mem_append_left ys hx) y (List.mem_append_right xs hy)⟩
  · intro ⟨hx, hy, hxy⟩ a ha b hb hab
    rcases List.mem_append.mp ha with ha | ha <;>
      rcases List.mem_append.mp hb with hb | hb
    · exact hx a ha b hb hab
    · exact hxy a ha b hb hab
    · exact (hxy b hb a ha hab.symm).symm
    · exact hy a ha b hb hab

theorem collisionFree_cons {x : α} {xs : List α} :
    CollisionFree f (x :: xs) ↔
      CollisionFree f xs ∧ ∀ y ∈ xs, f x = f y → x = y := by
  have h : CollisionFree f ([x] ++ xs) ↔ CollisionFree f [x] ∧ CollisionFree f xs ∧
      ∀ a ∈ [x], ∀ y ∈ xs, f a = f y → a = y := collisionFree_append
  simp only [List.singleton_append] at h
  rw [h]
  constructor
  · intro ⟨_, hxs, hxy⟩
    exact ⟨hxs, hxy x (List.mem_singleton_self x)⟩
  · intro ⟨hxs, hxy⟩
    refine ⟨CollisionFree.singleton x, hxs, fun a ha y hy => ?_⟩
    rw [List.mem_singleton.mp ha]
    exact hxy y hy

/-- Collision freedom depends only on which preimages occur, not on their
order or repetitions. -/
theorem collisionFree_congr {xs ys : List α} (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    CollisionFree f xs ↔ CollisionFree f ys :=
  ⟨fun hx => hx.mono fun x hy => (h x).mpr hy, fun hy => hy.mono fun x hx => (h x).mp hx⟩

/-- On distinct preimages, collision freedom is distinctness of the images. -/
theorem collisionFree_iff_nodup_map {xs : List α} (hxs : xs.Nodup) :
    CollisionFree f xs ↔ (xs.map f).Nodup := by
  induction xs with
  | nil => simp only [CollisionFree.nil, List.map_nil, List.nodup_nil]
  | cons x xs ih =>
    rw [List.nodup_cons] at hxs
    rw [collisionFree_cons, ih hxs.2, List.map_cons, List.nodup_cons, List.mem_map]
    constructor
    · intro ⟨hn, hx⟩
      refine ⟨fun ⟨y, hy, hfy⟩ => hxs.1 ?_, hn⟩
      rw [hx y hy hfy.symm]; exact hy
    · intro ⟨hx, hn⟩
      exact ⟨hn, fun y hy hfy => absurd ⟨y, hy, hfy.symm⟩ hx⟩

instance {xs : List α} [DecidableEq α] [DecidableEq β] : Decidable (CollisionFree f xs) :=
  inferInstanceAs (Decidable (∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y))

end Premise

/-! ## The region premise

The second-round decision extends the per-run premise from preimages to the
regions above hashed slots: an array's elements or a struct's members sit at
`keccak(p) + i`, `i < L`, modulo the word size `N`. Words are values below
`N`; a region is `[a, a + L)` read modulo `N`. -/

/-- The length-`L` regions at words `a, b < N` overlap modulo `N`
(`near_of_overlap`): their distance, read around the circle, is below `L`. -/
def Near (N L a b : Nat) : Prop :=
  (a < b + L ∧ b < a + L) ∨ a + N < b + L ∨ b + N < a + L

/-- The length-`L` region at word `a < N` covers the word `r < N` modulo `N`
(`covers_of_hit`). -/
def Covers (N L a r : Nat) : Prop :=
  (a ≤ r ∧ r < a + L) ∨ r + N < a + L

instance {N L a b : Nat} : Decidable (Near N L a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

instance {N L a r : Nat} : Decidable (Covers N L a r) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem Near.symm {N L a b : Nat} (h : Near N L a b) : Near N L b a := by
  unfold Near at h ⊢; omega

/-- Overlapping regions are `Near`. -/
theorem near_of_overlap {N L a b i j : Nat} (ha : a < N) (hb : b < N) (hL : L ≤ N)
    (hi : i < L) (hj : j < L) (h : (a + i) % N = (b + j) % N) : Near N L a b := by
  have hu : (a + i) / N < 2 := Nat.div_lt_of_lt_mul (by omega)
  have hv : (b + j) / N < 2 := Nat.div_lt_of_lt_mul (by omega)
  have eu : N * ((a + i) / N) + (a + i) % N = a + i := Nat.div_add_mod (a + i) N
  have ev : N * ((b + j) / N) + (b + j) % N = b + j := Nat.div_add_mod (b + j) N
  generalize (a + i) / N = u at hu eu
  generalize (b + j) / N = v at hv ev
  generalize (a + i) % N = m at eu h
  generalize (b + j) % N = n at ev h
  unfold Near
  rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl <;>
    rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl <;> omega

/-- A region that reaches a word covers it (the word is below `N`, as
`(a + i) % N` is). -/
theorem covers_of_hit {N L a r i : Nat} (ha : a < N) (hL : L ≤ N)
    (hi : i < L) (h : (a + i) % N = r) : Covers N L a r := by
  have hu : (a + i) / N < 2 := Nat.div_lt_of_lt_mul (by omega)
  have eu : N * ((a + i) / N) + (a + i) % N = a + i := Nat.div_add_mod (a + i) N
  generalize (a + i) / N = u at hu eu
  generalize (a + i) % N = m at eu h
  unfold Covers
  rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl <;> omega

section Regions
variable {α : Type _}

/-- The region premise on the preimages `xs` hashed by a run: the length-`L`
regions at their hashes `f x` pairwise do not overlap, and none covers a
root slot in `roots`. -/
def RegionsDisjoint (N L : Nat) (f : α → Nat) (roots : List Nat) (xs : List α) : Prop :=
  (∀ x ∈ xs, ∀ y ∈ xs, x ≠ y → ¬ Near N L (f x) (f y)) ∧
    ∀ x ∈ xs, ∀ r ∈ roots, ¬ Covers N L (f x) r

variable {N L : Nat} {f : α → Nat} {roots : List Nat}

instance {xs : List α} [DecidableEq α] : Decidable (RegionsDisjoint N L f roots xs) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem RegionsDisjoint.nil : RegionsDisjoint N L f roots [] :=
  ⟨fun _ hx => (by cases hx), fun _ hx => (by cases hx)⟩

theorem RegionsDisjoint.mono {xs ys : List α} (h : RegionsDisjoint N L f roots ys)
    (hsub : ∀ x ∈ xs, x ∈ ys) : RegionsDisjoint N L f roots xs :=
  ⟨fun x hx y hy => h.1 x (hsub x hx) y (hsub y hy), fun x hx => h.2 x (hsub x hx)⟩

theorem RegionsDisjoint.of_prefix {xs ys : List α} (h : RegionsDisjoint N L f roots ys)
    (hp : xs <+: ys) : RegionsDisjoint N L f roots xs :=
  h.mono fun _ hx => hp.sublist.subset hx

/-- Disjoint nonempty regions have distinct bases: the region premise implies
the preimage premise. -/
theorem RegionsDisjoint.collisionFree {xs : List α} (hL : 0 < L)
    (h : RegionsDisjoint N L f roots xs) : CollisionFree f xs := by
  intro x hx y hy hxy
  apply Classical.byContradiction
  intro hne
  apply h.1 x hx y hy hne
  rw [hxy]; unfold Near; omega

theorem regionsDisjoint_cons {x : α} {xs : List α} (hx : x ∉ xs) :
    RegionsDisjoint N L f roots (x :: xs) ↔
      RegionsDisjoint N L f roots xs ∧ (∀ y ∈ xs, ¬ Near N L (f x) (f y)) ∧
        ∀ r ∈ roots, ¬ Covers N L (f x) r := by
  constructor
  · intro h
    refine ⟨h.mono fun _ hy => List.mem_cons_of_mem x hy, fun y hy => ?_,
      h.2 x (List.mem_cons_self ..)⟩
    exact h.1 x (List.mem_cons_self ..) y (List.mem_cons_of_mem x hy) (fun e => hx (e ▸ hy))
  · intro ⟨h, hn, hc⟩
    refine ⟨fun a ha b hb hab => ?_, fun a ha => ?_⟩
    · rcases List.mem_cons.mp ha with ea | ha' <;> rcases List.mem_cons.mp hb with eb | hb'
      · exact absurd (ea.trans eb.symm) hab
      · rw [ea]; exact hn b hb'
      · rw [eb]; exact fun hn' => hn a ha' hn'.symm
      · exact h.1 a ha' b hb' hab
    · rcases List.mem_cons.mp ha with ea | ha'
      · rw [ea]; exact hc
      · exact h.2 a ha'

end Regions

/-! ## Output tuples of a random function -/

/-- All `q`-tuples (as lists) of outputs below `N`: the `N ^ q` equally likely
restrictions of a uniformly random function into `N` values to `q` inputs. -/
def tuples (N : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | q + 1 => (List.range N).flatMap fun a => (tuples N q).map (a :: ·)

/-- Whether a tuple repeats a value. -/
def hasDup : List Nat → Bool
  | [] => false
  | a :: t => t.contains a || hasDup t

/-- The number of `q`-tuples below `N` that collide. -/
def collisions (N q : Nat) : Nat := (tuples N q).countP hasDup

theorem hasDup_eq_false_iff {t : List Nat} : hasDup t = false ↔ t.Nodup := by
  induction t with
  | nil => simp only [hasDup, List.nodup_nil]
  | cons a t ih =>
    simp only [hasDup, ← ih, List.nodup_cons, Bool.eq_false_iff, ne_eq, Bool.or_eq_true, not_or,
      List.contains_iff_mem]

/-- Sum of `g` over a list. Kept local so the counting below needs no
library sum lemmas. -/
def sumOver {γ : Type _} (l : List γ) (g : γ → Nat) : Nat := (l.map g).sum

section Counting

theorem sumOver_cons {γ : Type _} (a : γ) (l : List γ) (g : γ → Nat) :
    sumOver (a :: l) g = g a + sumOver l g := by
  simp only [sumOver, List.map_cons, List.sum_cons]

theorem sumOver_nil {γ : Type _} (g : γ → Nat) : sumOver ([] : List γ) g = 0 := rfl

theorem sumOver_add {γ : Type _} (l : List γ) (g h : γ → Nat) :
    sumOver l (fun a => g a + h a) = sumOver l g + sumOver l h := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [sumOver_cons, ih]; omega

theorem sumOver_le {γ : Type _} (l : List γ) {g h : γ → Nat} (hle : ∀ a ∈ l, g a ≤ h a) :
    sumOver l g ≤ sumOver l h := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
    simp only [sumOver_cons]
    exact Nat.add_le_add (hle a (List.mem_cons_self ..))
      (ih fun b hb => hle b (List.mem_cons_of_mem a hb))

theorem sumOver_const {γ : Type _} (l : List γ) (c : Nat) :
    sumOver l (fun _ => c) = l.length * c := by
  induction l with
  | nil => simp only [sumOver_nil, List.length_nil, Nat.zero_mul]
  | cons a l ih => simp only [sumOver_cons, ih, List.length_cons, Nat.succ_mul]; omega

theorem sumOver_ite {γ : Type _} (A : List γ) (p : γ → Bool) :
    sumOver A (fun a => if p a = true then 1 else 0) = A.countP p := by
  induction A with
  | nil => rfl
  | cons a A ih => simp only [sumOver_cons, List.countP_cons, ih, Nat.add_comm]

/-- Double counting: summing a two-place count either way gives the same
total. -/
theorem sumOver_swap {γ δ : Type _} (A : List γ) (T : List δ) (P : γ → δ → Bool) :
    sumOver A (fun a => T.countP (P a)) = sumOver T (fun t => A.countP (P · t)) := by
  induction T with
  | nil => simp only [List.countP_nil, sumOver_nil]; exact sumOver_const A 0 ▸ Nat.mul_zero _
  | cons t T ih =>
    simp only [List.countP_cons, sumOver_cons]
    rw [sumOver_add, ih, sumOver_ite, Nat.add_comm]

theorem countP_flatMap {γ δ : Type _} (A : List γ) (F : γ → List δ) (p : δ → Bool) :
    (A.flatMap F).countP p = sumOver A (fun a => (F a).countP p) := by
  induction A with
  | nil => rfl
  | cons a A ih => simp only [List.flatMap_cons, List.countP_append, ih, sumOver_cons]

theorem countP_or_le {γ : Type _} (l : List γ) (p r : γ → Bool) :
    l.countP (fun a => p a || r a) ≤ l.countP p + l.countP r := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases r a <;> simp only [Bool.or_self, Bool.or_true, Bool.or_false,
      if_true] <;> omega

theorem countP_le_of_imp {γ : Type _} (l : List γ) {p r : γ → Bool}
    (h : ∀ a ∈ l, p a = true → r a = true) : l.countP p ≤ l.countP r := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
    have ih' : l.countP p ≤ l.countP r := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    have ha : p a = true → r a = true := h a (List.mem_cons_self ..)
    simp only [List.countP_cons]
    cases hp : p a with
    | false => cases r a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    | true => simp only [ha hp, ↓reduceIte]; omega

theorem length_tuples (N q : Nat) : (tuples N q).length = N ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [tuples, List.length_flatMap, List.length_map, ih]
    rw [show (List.map (fun _ => N ^ q) (List.range N)).sum = sumOver (List.range N) fun _ => N ^ q
      from rfl, sumOver_const, List.length_range, Nat.pow_succ, Nat.mul_comm]

theorem length_of_mem_tuples {N q : Nat} {t : List Nat} (h : t ∈ tuples N q) :
    t.length = q := by
  induction q generalizing t with
  | zero => simp only [tuples, List.mem_singleton] at h; rw [h]; rfl
  | succ q ih =>
    simp only [tuples, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, _, u, hu, rfl⟩ := h
    simp only [List.length_cons, ih hu]

/-- At most `|t|` of the distinct values of a duplicate-free list `A` occur
in `t`. -/
theorem countP_contains_le {A : List Nat} (hA : A.Nodup) (t : List Nat) :
    A.countP (fun a => t.contains a) ≤ t.length := by
  induction t with
  | nil => simp only [List.contains_nil, List.countP_false, List.length_nil]; exact Nat.le_refl 0
  | cons x t ih =>
    have hx : A.countP (fun a => a == x) ≤ 1 := by
      rw [List.countP_eq_length_filter]
      have hnd : (A.filter fun a => a == x).Nodup := hA.filter _
      have hall : ∀ b ∈ A.filter (fun a => a == x), b = x := by
        intro b hb
        simpa only [List.mem_filter, beq_iff_eq] using (List.mem_filter.mp hb).2
      match hf : A.filter (fun a => a == x) with
      | [] => simp only [List.length_nil]; omega
      | [_] => exact Nat.le_refl 1
      | b :: c :: r =>
        rw [hf] at hnd hall
        have hb : b = x := hall b (List.mem_cons_self ..)
        have hc : c = x := hall c (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        exact absurd (show b ∈ c :: r by rw [hb, ← hc]; exact List.mem_cons_self ..)
          (List.nodup_cons.mp hnd).1
    have hsplit : A.countP (fun a => (x :: t).contains a) =
        A.countP (fun a => (a == x) || t.contains a) := by
      congr 1
    rw [hsplit, List.length_cons]
    have hor : A.countP (fun a => (a == x) || t.contains a) ≤
        A.countP (fun a => a == x) + A.countP (fun a => t.contains a) :=
      countP_or_le A (fun a => a == x) (fun a => t.contains a)
    omega

/-- The incremental union bound: `C(q+1) ≤ N · C(q) + q · N^q`. -/
theorem collisions_succ_le (N q : Nat) :
    collisions N (q + 1) ≤ N * collisions N q + q * N ^ q := by
  simp only [collisions, tuples, countP_flatMap, List.countP_map]
  have step : sumOver (List.range N) (fun a => (tuples N q).countP (hasDup ∘ (a :: ·))) ≤
      sumOver (List.range N) (fun a =>
        (tuples N q).countP (fun t => t.contains a) + (tuples N q).countP hasDup) :=
    sumOver_le _ fun a _ => countP_or_le _ _ _
  rw [sumOver_add, sumOver_const, List.length_range,
    sumOver_swap (List.range N) (tuples N q) (fun a t => t.contains a)] at step
  have hpairs : sumOver (tuples N q) (fun t => (List.range N).countP (fun a => t.contains a)) ≤
      sumOver (tuples N q) (fun _ => q) :=
    sumOver_le _ fun t ht => length_of_mem_tuples ht ▸ countP_contains_le List.nodup_range t
  rw [sumOver_const, length_tuples] at hpairs
  have hc : (tuples N q).countP hasDup = collisions N q := rfl
  rw [hc] at step ⊢
  rw [Nat.mul_comm q]
  omega

/-- The birthday bound, cross-multiplied: `2 · N · C(q) ≤ q(q-1) · N^q`. -/
theorem two_mul_collisions_le (N q : Nat) :
    2 * N * collisions N q ≤ q * (q - 1) * N ^ q := by
  induction q with
  | zero => simp only [collisions, tuples, List.countP_singleton, hasDup, Bool.false_eq_true,
      ↓reduceIte, Nat.mul_zero, Nat.zero_le]
  | succ q ih =>
    have hs : 2 * N * collisions N (q + 1) ≤ 2 * N * (N * collisions N q + q * N ^ q) :=
      Nat.mul_le_mul_left (2 * N) (collisions_succ_le N q)
    have hpow : N ^ (q + 1) = N ^ q * N := by rw [Nat.pow_succ]
    have e1 : 2 * N * (N * collisions N q + q * N ^ q) =
        N * (2 * N * collisions N q) + 2 * q * N ^ (q + 1) := by
      rw [hpow]; simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have e2 : N * (q * (q - 1) * N ^ q) + 2 * q * N ^ (q + 1) = (q + 1) * q * N ^ (q + 1) := by
      rw [hpow]
      cases q <;> grind
    have hih : N * (2 * N * collisions N q) ≤ N * (q * (q - 1) * N ^ q) :=
      Nat.mul_le_mul_left N ih
    rw [Nat.add_sub_cancel, ← e2]
    omega

/-- At most `q(q-1)/2 · N^(q-1)` of the `N^q` tuples collide (stated as
`2 · C(q) ≤ q(q-1) · N^(q-1)`). -/
theorem collisions_le (N q : Nat) :
    2 * collisions N q ≤ q * (q - 1) * N ^ (q - 1) := by
  cases q with
  | zero => simp only [collisions, tuples, List.countP_singleton, hasDup, Bool.false_eq_true,
      ↓reduceIte, Nat.mul_zero, Nat.zero_le]
  | succ k =>
    cases N with
    | zero =>
      have : collisions 0 (k + 1) = 0 := by
        simp only [collisions, tuples, List.range_zero, List.flatMap_nil, List.countP_nil]
      rw [this]; exact Nat.zero_le _
    | succ n =>
      have h : 2 * (n + 1) * collisions (n + 1) (k + 1) ≤ (k + 1) * (k + 1 - 1) * (n + 1) ^ (k + 1) :=
        two_mul_collisions_le (n + 1) (k + 1)
      rw [Nat.add_sub_cancel, Nat.pow_succ] at h
      rw [Nat.add_sub_cancel]
      apply Nat.le_of_mul_le_mul_right (c := n + 1) _ (Nat.succ_pos n)
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] at h ⊢
      exact h

/-- The collision probability over a uniformly random function is at most
`q(q-1)/(2N)`: `bad / N^q ≤ q(q-1)/(2N)`, cross-multiplied. -/
theorem collision_prob_le (N q : Nat) :
    2 * N * collisions N q ≤ q * (q - 1) * (tuples N q).length := by
  rw [length_tuples]; exact two_mul_collisions_le N q

/-- The `q²/(2N)` form. -/
theorem collision_prob_le_sq (N q : Nat) :
    2 * N * collisions N q ≤ q ^ 2 * (tuples N q).length := by
  have h : 2 * N * collisions N q ≤ q * (q - 1) * (tuples N q).length := collision_prob_le N q
  have : q * (q - 1) ≤ q ^ 2 := by
    rw [Nat.pow_two]; exact Nat.mul_le_mul_left q (Nat.sub_le q 1)
  exact Nat.le_trans h (Nat.mul_le_mul_right _ this)

/-- For a `k`-bit hash (`N = 2^k`) the collision probability among `q`
hashes is at most `q²/2^(k+1)`: `bad / 2^(k q) ≤ q² / 2^(k+1)`. -/
theorem pow_two_collision_prob_le (k q : Nat) :
    2 ^ (k + 1) * collisions (2 ^ k) q ≤ q ^ 2 * 2 ^ (k * q) := by
  have h : 2 * 2 ^ k * collisions (2 ^ k) q ≤ q ^ 2 * (tuples (2 ^ k) q).length :=
    collision_prob_le_sq (2 ^ k) q
  rw [length_tuples, ← Nat.pow_mul, ← Nat.pow_succ'] at h
  exact h

/-- Keccak-256 (`N = 2^256`): the collision probability among `q` hashes is
at most `q²/2²⁵⁷` (written `2 ^ (256 + 1)`: the elaborator warns before
evaluating the literal `2 ^ 257`, above its exponentiation threshold). -/
theorem keccak_collision_prob_le (q : Nat) :
    2 ^ (256 + 1) * collisions (2 ^ 256) q ≤ q ^ 2 * 2 ^ (256 * q) :=
  pow_two_collision_prob_le 256 q

end Counting

/-! ## The oracle reading -/

section Oracle
variable {α : Type _} [DecidableEq α]

/-- The function that answers the `i`-th input of `xs` with the `i`-th entry
of the tuple `t` (and `0` elsewhere): the random oracle with outputs `t`. -/
def oracleOf : List α → List Nat → α → Nat
  | x :: xs, a :: t, y => if y = x then a else oracleOf xs t y
  | _, _, _ => 0

theorem map_oracleOf {xs : List α} (hxs : xs.Nodup) {t : List Nat}
    (hl : t.length = xs.length) : xs.map (oracleOf xs t) = t := by
  induction xs generalizing t with
  | nil => cases t with
    | nil => rfl
    | cons _ _ => simp only [List.length_cons, List.length_nil] at hl; omega
  | cons x xs ih =>
    cases t with
    | nil => simp only [List.length_nil, List.length_cons] at hl; omega
    | cons a t =>
      rw [List.nodup_cons] at hxs
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.map_cons, oracleOf, if_pos]
      congr 1
      refine Eq.trans (List.map_congr_left fun y hy => ?_) (ih hxs.2 hl)
      have : y ≠ x := fun h => hxs.1 (h ▸ hy)
      simp only [if_neg this]

/-- The list without repetitions, keeping each element's last occurrence. -/
def dedup : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then dedup xs else x :: dedup xs

theorem mem_dedup {xs : List α} {y : α} : y ∈ dedup xs ↔ y ∈ xs := by
  induction xs with
  | nil => simp only [dedup]
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · simp only [dedup, if_pos hx, ih, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun e => e ▸ hx) id⟩
    · simp only [dedup, if_neg hx, List.mem_cons, ih]

theorem nodup_dedup (xs : List α) : (dedup xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · simp only [dedup, if_pos hx]; exact ih
    · simp only [dedup, if_neg hx]
      exact List.nodup_cons.mpr ⟨fun h => hx (mem_dedup.mp h), ih⟩

theorem length_dedup_le (xs : List α) : (dedup xs).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · simp only [dedup, if_pos hx, List.length_cons]; omega
    · simp only [dedup, if_neg hx, List.length_cons]; omega

/-- A run may hash the same preimage twice; the premise is that of its
distinct preimages. -/
theorem collisionFree_dedup {β : Type _} {f : α → β} (xs : List α) :
    CollisionFree f (dedup xs) ↔ CollisionFree f xs :=
  collisionFree_congr fun _ => mem_dedup

/-- For `q` distinct inputs, the tuples whose oracle collides on them are
exactly the colliding tuples, so `keccak_collision_prob_le` bounds the
probability that a uniformly random 256-bit oracle breaks the per-run premise
on `q` fixed preimages. -/
theorem oracle_collides_iff {xs : List α} (hxs : xs.Nodup) {t : List Nat}
    (hl : t.length = xs.length) :
    ¬ CollisionFree (oracleOf xs t) xs ↔ hasDup t = true := by
  rw [collisionFree_iff_nodup_map hxs, map_oracleOf hxs hl, ← hasDup_eq_false_iff]
  simp only [Bool.not_eq_false]

/-- The bound read on the per-run premise: among all `2^(256 q)` oracles on
`q` fixed distinct preimages `xs`, those under which `CollisionFree` fails
number `bad`, and `2^257 · bad ≤ q² · 2^(256 q)`. This is the
non-adaptive reading: `xs` is fixed before the oracle is drawn. -/
theorem keccak_premise_fails_prob_le {xs : List α} (hxs : xs.Nodup) :
    2 ^ (256 + 1) * (tuples (2 ^ 256) xs.length).countP
        (fun t => decide (¬ CollisionFree (oracleOf xs t) xs)) ≤
      xs.length ^ 2 * 2 ^ (256 * xs.length) := by
  have hcount : (tuples (2 ^ 256) xs.length).countP
      (fun t => decide (¬ CollisionFree (oracleOf xs t) xs)) = collisions (2 ^ 256) xs.length := by
    apply List.countP_congr
    intro t ht
    rw [decide_eq_true_iff, oracle_collides_iff hxs (length_of_mem_tuples ht)]
  rw [hcount]
  exact keccak_collision_prob_le xs.length

/-- The bound for a preimage list with repetitions: `q` is the number of
distinct preimages, `(dedup xs).length ≤ xs.length` (`length_dedup_le`), and
the oracle is drawn on those (`oracleOf (dedup xs)`). -/
theorem keccak_premise_fails_prob_le_dedup (xs : List α) :
    2 ^ (256 + 1) * (tuples (2 ^ 256) (dedup xs).length).countP
        (fun t => decide (¬ CollisionFree (oracleOf (dedup xs) t) xs)) ≤
      (dedup xs).length ^ 2 * 2 ^ (256 * (dedup xs).length) := by
  have e : (tuples (2 ^ 256) (dedup xs).length).countP
        (fun t => decide (¬ CollisionFree (oracleOf (dedup xs) t) xs)) =
      (tuples (2 ^ 256) (dedup xs).length).countP
        (fun t => decide (¬ CollisionFree (oracleOf (dedup xs) t) (dedup xs))) := by
    apply List.countP_congr
    intro t _
    simp only [decide_eq_true_iff, collisionFree_dedup]
  rw [e]
  exact keccak_premise_fails_prob_le (xs := dedup xs) (nodup_dedup xs)

end Oracle

/-! ## The region bound

The same counting with "equal" replaced by `Near`: a tuple `a :: t` is bad if
`t` is, if `a`'s region overlaps one of the `q` regions of `t` (at most
`2L - 1` values of `a` each, `countP_near_le`), or if it covers one of the
roots (at most `L` values each, `countP_covers_le`). -/

section RegionCounting

/-- Whether a tuple of hash words breaks the region premise. -/
def regionBad (N L : Nat) (roots : List Nat) : List Nat → Bool
  | [] => false
  | a :: t => t.any (fun b => decide (Near N L a b)) || roots.any (fun r => decide (Covers N L a r)) ||
      regionBad N L roots t

/-- The number of `q`-tuples below `N` that break the region premise. -/
def regionCollisions (N L : Nat) (roots : List Nat) (q : Nat) : Nat :=
  (tuples N q).countP (regionBad N L roots)

theorem countP_range_interval (N lo hi : Nat) :
    (List.range N).countP (fun a => decide (lo ≤ a ∧ a < hi)) = min hi N - lo := by
  induction N with
  | zero => simp only [List.range_zero, List.countP_nil]; omega
  | succ N ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
    by_cases h : lo ≤ N ∧ N < hi
    · simp only [h, and_self, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]; omega

theorem countP_near_le {N L b : Nat} (hb : b < N) :
    (List.range N).countP (fun a => decide (Near N L a b)) ≤ 2 * L - 1 := by
  have himp : (List.range N).countP (fun a => decide (Near N L a b)) ≤
      (List.range N).countP (fun a => decide (b + 1 - L ≤ a ∧ a < b + L) ||
        decide (0 ≤ a ∧ a < b + L - N) || decide (b + N + 1 - L ≤ a ∧ a < N)) := by
    apply countP_le_of_imp
    intro a ha hn
    have ha' : a < N := List.mem_range.mp ha
    simp only [decide_eq_true_eq, Near] at hn
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  have h1 := countP_or_le (List.range N)
    (fun a => decide (b + 1 - L ≤ a ∧ a < b + L) || decide (0 ≤ a ∧ a < b + L - N))
    (fun a => decide (b + N + 1 - L ≤ a ∧ a < N))
  have h2 := countP_or_le (List.range N) (fun a => decide (b + 1 - L ≤ a ∧ a < b + L))
    (fun a => decide (0 ≤ a ∧ a < b + L - N))
  rw [countP_range_interval] at h1
  rw [countP_range_interval, countP_range_interval] at h2
  omega

theorem countP_covers_le {N L r : Nat} (hr : r < N) :
    (List.range N).countP (fun a => decide (Covers N L a r)) ≤ L := by
  have himp : (List.range N).countP (fun a => decide (Covers N L a r)) ≤
      (List.range N).countP (fun a => decide (r + 1 - L ≤ a ∧ a < r + 1) ||
        decide (r + N + 1 - L ≤ a ∧ a < N)) := by
    apply countP_le_of_imp
    intro a ha hn
    have ha' : a < N := List.mem_range.mp ha
    simp only [decide_eq_true_eq, Covers] at hn
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  have h1 := countP_or_le (List.range N) (fun a => decide (r + 1 - L ≤ a ∧ a < r + 1))
    (fun a => decide (r + N + 1 - L ≤ a ∧ a < N))
  rw [countP_range_interval, countP_range_interval] at h1
  omega

/-- The union bound over a list: an `any` is counted at most once per
witness. -/
theorem countP_any_le {γ δ : Type _} (A : List γ) (t : List δ) (P : γ → δ → Bool) :
    A.countP (fun a => t.any (P a)) ≤ sumOver t (fun b => A.countP (P · b)) := by
  induction t with
  | nil => simp only [List.any_nil, List.countP_false, sumOver_nil]; exact Nat.le_refl 0
  | cons b t ih =>
    simp only [List.any_cons, sumOver_cons]
    have h : A.countP (fun a => P a b || t.any (P a)) ≤
        A.countP (P · b) + A.countP (fun a => t.any (P a)) := countP_or_le A _ _
    omega

theorem lt_of_mem_tuples {N q : Nat} {t : List Nat} (h : t ∈ tuples N q) :
    ∀ b ∈ t, b < N := by
  induction q generalizing t with
  | zero =>
    simp only [tuples, List.mem_singleton] at h
    rw [h]; intro b hb; cases hb
  | succ q ih =>
    simp only [tuples, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, ha, u, hu, rfl⟩ := h
    intro b hb
    rcases List.mem_cons.mp hb with e | hb'
    · rw [e]; exact List.mem_range.mp ha
    · exact ih hu b hb'

/-- The incremental bound: `B(q+1) ≤ N · B(q) + (q (2L-1) + |roots| L) · N^q`. -/
theorem regionCollisions_succ_le {N L : Nat} {roots : List Nat} (hroots : ∀ r ∈ roots, r < N)
    (q : Nat) :
    regionCollisions N L roots (q + 1) ≤
      N * regionCollisions N L roots q + (q * (2 * L - 1) + roots.length * L) * N ^ q := by
  simp only [regionCollisions, tuples, countP_flatMap, List.countP_map]
  have hT : (tuples N q).countP (regionBad N L roots) = regionCollisions N L roots q := rfl
  have step : sumOver (List.range N)
        (fun a => (tuples N q).countP (regionBad N L roots ∘ (a :: ·))) ≤
      sumOver (List.range N) (fun a =>
        (tuples N q).countP (fun t => t.any (fun b => decide (Near N L a b))) +
        (tuples N q).countP (fun t => roots.any (fun r => decide (Covers N L a r))) +
        (tuples N q).countP (regionBad N L roots)) := by
    apply sumOver_le
    intro a _
    have h1 := countP_or_le (tuples N q)
      (fun t => t.any (fun b => decide (Near N L a b)) || roots.any (fun r => decide (Covers N L a r)))
      (regionBad N L roots)
    have h2 := countP_or_le (tuples N q) (fun t => t.any (fun b => decide (Near N L a b)))
      (fun t => roots.any (fun r => decide (Covers N L a r)))
    exact Nat.le_trans h1 (Nat.add_le_add_right h2 _)
  rw [sumOver_add, sumOver_add, sumOver_const (List.range N), List.length_range,
    sumOver_swap (List.range N) (tuples N q) (fun a t => t.any (fun b => decide (Near N L a b))),
    sumOver_swap (List.range N) (tuples N q)
      (fun a t => roots.any (fun r => decide (Covers N L a r)))] at step
  have hnear : sumOver (tuples N q) (fun t => (List.range N).countP
        (fun a => t.any (fun b => decide (Near N L a b)))) ≤
      sumOver (tuples N q) (fun _ => q * (2 * L - 1)) := by
    apply sumOver_le
    intro t ht
    have hu := countP_any_le (List.range N) t (fun a b => decide (Near N L a b))
    have hv : sumOver t (fun b => (List.range N).countP (fun a => decide (Near N L a b))) ≤
        sumOver t (fun _ => 2 * L - 1) :=
      sumOver_le t fun b hb => countP_near_le (lt_of_mem_tuples ht b hb)
    rw [sumOver_const, length_of_mem_tuples ht] at hv
    exact Nat.le_trans hu hv
  have hcov : sumOver (tuples N q) (fun t => (List.range N).countP
        (fun a => roots.any (fun r => decide (Covers N L a r)))) ≤
      sumOver (tuples N q) (fun _ => roots.length * L) := by
    apply sumOver_le
    intro t _
    have hu := countP_any_le (List.range N) roots (fun a r => decide (Covers N L a r))
    have hv : sumOver roots (fun r => (List.range N).countP (fun a => decide (Covers N L a r))) ≤
        sumOver roots (fun _ => L) :=
      sumOver_le roots fun r hr => countP_covers_le (hroots r hr)
    rw [sumOver_const] at hv
    exact Nat.le_trans hu hv
  rw [sumOver_const (tuples N q) (q * (2 * L - 1)), length_tuples] at hnear
  rw [sumOver_const (tuples N q) (roots.length * L), length_tuples] at hcov
  simp only [hT] at step ⊢
  rw [Nat.add_mul, Nat.mul_comm (q * (2 * L - 1)), Nat.mul_comm (roots.length * L)]
  omega

/-- The region bound, cross-multiplied:
`2 · N · B(q) ≤ (q(q-1)(2L-1) + 2 q |roots| L) · N^q`, that is, a probability
of at most `q(q-1)(2L-1)/(2N) + q |roots| L / N`. -/
theorem two_mul_regionCollisions_le {N L : Nat} {roots : List Nat}
    (hroots : ∀ r ∈ roots, r < N) (q : Nat) :
    2 * N * regionCollisions N L roots q ≤
      (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * N ^ q := by
  induction q with
  | zero =>
    simp only [regionCollisions, tuples, List.countP_singleton, regionBad, Bool.false_eq_true,
      ↓reduceIte, Nat.mul_zero, Nat.zero_le]
  | succ q ih =>
    have hs : 2 * N * regionCollisions N L roots (q + 1) ≤
        2 * N * (N * regionCollisions N L roots q +
          (q * (2 * L - 1) + roots.length * L) * N ^ q) :=
      Nat.mul_le_mul_left (2 * N) (regionCollisions_succ_le hroots q)
    have hih : N * (2 * N * regionCollisions N L roots q) ≤
        N * ((q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * N ^ q) :=
      Nat.mul_le_mul_left N ih
    have hpow : N ^ (q + 1) = N ^ q * N := by rw [Nat.pow_succ]
    have e1 : 2 * N * (N * regionCollisions N L roots q +
          (q * (2 * L - 1) + roots.length * L) * N ^ q) =
        N * (2 * N * regionCollisions N L roots q) +
          (2 * q * (2 * L - 1) + 2 * roots.length * L) * N ^ (q + 1) := by
      rw [hpow]; grind
    have e2 : N * ((q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * N ^ q) +
          (2 * q * (2 * L - 1) + 2 * roots.length * L) * N ^ (q + 1) =
        ((q + 1) * (q + 1 - 1) * (2 * L - 1) + 2 * (q + 1) * roots.length * L) * N ^ (q + 1) := by
      rw [hpow]
      cases q <;> grind
    omega

/-- A `k`-bit hash (`N = 2^k`). -/
theorem pow_two_region_prob_le {k L : Nat} {roots : List Nat} (hroots : ∀ r ∈ roots, r < 2 ^ k)
    (q : Nat) :
    2 ^ (k + 1) * regionCollisions (2 ^ k) L roots q ≤
      (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * 2 ^ (k * q) := by
  have h : 2 * 2 ^ k * regionCollisions (2 ^ k) L roots q ≤
      (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * (2 ^ k) ^ q :=
    two_mul_regionCollisions_le hroots q
  rw [← Nat.pow_mul, ← Nat.pow_succ'] at h
  exact h

/-- Keccak-256 (`N = 2^256`): regions of length `L` at `q` hashed slots
overlap each other or one of the `roots` with probability at most
`q(q-1)(2L-1)/2²⁵⁷ + q |roots| L / 2²⁵⁶ ≤ (q² L + q |roots| L) / 2²⁵⁶`. -/
theorem keccak_region_prob_le {L : Nat} {roots : List Nat} (hroots : ∀ r ∈ roots, r < 2 ^ 256)
    (q : Nat) :
    2 ^ (256 + 1) * regionCollisions (2 ^ 256) L roots q ≤
      (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * 2 ^ (256 * q) :=
  @pow_two_region_prob_le 256 L roots hroots q

end RegionCounting

section RegionOracle
variable {α : Type _} {N L : Nat} {roots : List Nat}

theorem regionsDisjoint_iff_regionBad {f : α → Nat} {xs : List α} (hxs : xs.Nodup) :
    RegionsDisjoint N L f roots xs ↔ regionBad N L roots (xs.map f) = false := by
  induction xs with
  | nil => simp only [List.map_nil, regionBad, iff_true]; exact RegionsDisjoint.nil
  | cons x xs ih =>
    rw [List.nodup_cons] at hxs
    rw [regionsDisjoint_cons hxs.1, ih hxs.2, List.map_cons, regionBad]
    simp only [Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro ⟨h, hn, hc⟩; exact ⟨⟨hn, hc⟩, h⟩
    · intro ⟨⟨hn, hc⟩, h⟩; exact ⟨h, hn, hc⟩

variable [DecidableEq α]

/-- The region bound read on the premise: among all `2^(256 q)` oracles on
`q` fixed distinct preimages `xs`, those under which `RegionsDisjoint` fails
number `bad`, and
`2^257 · bad ≤ (q(q-1)(2L-1) + 2 q |roots| L) · 2^(256 q)`. -/
theorem keccak_region_premise_fails_prob_le {xs : List α} (hxs : xs.Nodup)
    (hroots : ∀ r ∈ roots, r < 2 ^ 256) :
    2 ^ (256 + 1) * (tuples (2 ^ 256) xs.length).countP
        (fun t => decide (¬ RegionsDisjoint (2 ^ 256) L (oracleOf xs t) roots xs)) ≤
      (xs.length * (xs.length - 1) * (2 * L - 1) + 2 * xs.length * roots.length * L) *
        2 ^ (256 * xs.length) := by
  have hcount : (tuples (2 ^ 256) xs.length).countP
      (fun t => decide (¬ RegionsDisjoint (2 ^ 256) L (oracleOf xs t) roots xs)) =
      regionCollisions (2 ^ 256) L roots xs.length := by
    apply List.countP_congr
    intro t ht
    rw [decide_eq_true_iff, regionsDisjoint_iff_regionBad hxs,
      map_oracleOf hxs (length_of_mem_tuples ht), Bool.not_eq_false]
  rw [hcount]
  exact @keccak_region_prob_le L roots hroots xs.length

omit [DecidableEq α] in
/-- Like `CollisionFree`, the region premise depends only on membership. -/
theorem regionsDisjoint_congr {f : α → Nat} {xs ys : List α} (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    RegionsDisjoint N L f roots xs ↔ RegionsDisjoint N L f roots ys :=
  ⟨fun hx => hx.mono fun x hy => (h x).mpr hy, fun hy => hy.mono fun x hx => (h x).mp hx⟩

/-- A run may hash the same preimage twice; the region premise is that of its
distinct preimages. -/
theorem regionsDisjoint_dedup {f : α → Nat} (xs : List α) :
    RegionsDisjoint N L f roots (dedup xs) ↔ RegionsDisjoint N L f roots xs :=
  regionsDisjoint_congr fun _ => mem_dedup

/-- The region bound for a preimage list with repetitions: `q` is the number
of distinct preimages and the oracle is drawn on those. -/
theorem keccak_region_premise_fails_prob_le_dedup (xs : List α)
    (hroots : ∀ r ∈ roots, r < 2 ^ 256) :
    2 ^ (256 + 1) * (tuples (2 ^ 256) (dedup xs).length).countP
        (fun t => decide (¬ RegionsDisjoint (2 ^ 256) L (oracleOf (dedup xs) t) roots xs)) ≤
      ((dedup xs).length * ((dedup xs).length - 1) * (2 * L - 1) +
          2 * (dedup xs).length * roots.length * L) * 2 ^ (256 * (dedup xs).length) := by
  have e : (tuples (2 ^ 256) (dedup xs).length).countP
        (fun t => decide (¬ RegionsDisjoint (2 ^ 256) L (oracleOf (dedup xs) t) roots xs)) =
      (tuples (2 ^ 256) (dedup xs).length).countP
        (fun t => decide (¬ RegionsDisjoint (2 ^ 256) L (oracleOf (dedup xs) t) roots
          (dedup xs))) := by
    apply List.countP_congr
    intro t _
    simp only [decide_eq_true_iff, regionsDisjoint_dedup]
  rw [e]
  exact @keccak_region_premise_fails_prob_le α L roots _ (dedup xs) (nodup_dedup xs) hroots

end RegionOracle

/-! ## Adaptive queries -/

section Adaptive
variable {α : Type _} [DecidableEq α]

/-- The queries an adaptive strategy makes when the lazily sampled oracle
answers `t`: the `i`-th query is `s` of the first `i` answers. -/
def lazyQueries (s : List Nat → α) (t : List Nat) : List α :=
  (List.range t.length).map fun i => s (t.take i)

omit [DecidableEq α] in
theorem length_lazyQueries (s : List Nat → α) (t : List Nat) :
    (lazyQueries s t).length = t.length := by
  simp only [lazyQueries, List.length_map, List.length_range]

/-- The bound for adaptive queries under lazy sampling: each answer is a
fresh uniform value, drawn when the query is made, and the `i`-th query may
depend on the earlier answers. Among the `N^q` answer sequences, those whose
queries are distinct yet collide under the oracle number at most
`q(q-1)/(2N) · N^q`. -/
theorem adaptive_lazy_collision_prob_le (s : List Nat → α) (N q : Nat) :
    2 * N * (tuples N q).countP (fun t =>
        decide ((lazyQueries s t).Nodup ∧
          ¬ CollisionFree (oracleOf (lazyQueries s t) t) (lazyQueries s t))) ≤
      q * (q - 1) * N ^ q := by
  have hle : (tuples N q).countP (fun t =>
        decide ((lazyQueries s t).Nodup ∧
          ¬ CollisionFree (oracleOf (lazyQueries s t) t) (lazyQueries s t))) ≤
      collisions N q := by
    apply countP_le_of_imp
    intro t _ ht
    rw [decide_eq_true_iff] at ht
    exact (oracle_collides_iff ht.1 (length_lazyQueries s t).symm).mp ht.2
  exact Nat.le_trans (Nat.mul_le_mul_left (2 * N) hle) (two_mul_collisions_le N q)

/-- The queries an adaptive strategy makes against a fixed oracle `g`. -/
def eagerQueries (s : List Nat → α) (g : α → Nat) : Nat → List α
  | 0 => []
  | k + 1 => let qs := eagerQueries s g k; qs ++ [s (qs.map g)]

/-- The adaptive bound for an eagerly sampled oracle: a uniformly random
function on a finite domain `dom` (one of the `N^|dom|` tuples, read by
`oracleOf dom`) is queried `q` times by an adaptive strategy; the functions
under which distinct queries collide are at most a `q(q-1)/(2N)` fraction.
Proved as `eagerAdaptiveBound` in `Solidity/Hash/Adaptive.lean`, which
imports this module (`docs/feature-work/hash-collision-bound.md`, "Adaptive
queries"). -/
def EagerAdaptiveBound.{u} : Prop :=
  ∀ (β : Type u) [DecidableEq β] (dom : List β), dom.Nodup →
    ∀ (s : List Nat → β), (∀ t, s t ∈ dom) → ∀ N q : Nat,
      2 * N * (tuples N dom.length).countP (fun g =>
          decide ((eagerQueries s (oracleOf dom g) q).Nodup ∧
            ¬ CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) q))) ≤
        q * (q - 1) * N ^ dom.length

end Adaptive

end Solidity.Hash

/-- info: 'Solidity.Hash.keccak_premise_fails_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.keccak_premise_fails_prob_le

/-- info: 'Solidity.Hash.adaptive_lazy_collision_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.adaptive_lazy_collision_prob_le

/-- info: 'Solidity.Hash.collisions_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.collisions_le

/-- info: 'Solidity.Hash.keccak_premise_fails_prob_le_dedup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.keccak_premise_fails_prob_le_dedup

/-- info: 'Solidity.Hash.keccak_region_premise_fails_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.keccak_region_premise_fails_prob_le

/-- info: 'Solidity.Hash.near_of_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.near_of_overlap

/-- info: 'Solidity.Hash.keccak_region_premise_fails_prob_le_dedup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.keccak_region_premise_fails_prob_le_dedup

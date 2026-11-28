

namespace Solidity.Hash

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

theorem collisionFree_congr {xs ys : List α} (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    CollisionFree f xs ↔ CollisionFree f ys :=
  ⟨fun hx => hx.mono fun x hy => (h x).mpr hy, fun hy => hy.mono fun x hx => (h x).mp hx⟩

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

def Near (N L a b : Nat) : Prop :=
  (a < b + L ∧ b < a + L) ∨ a + N < b + L ∨ b + N < a + L

def Covers (N L a r : Nat) : Prop :=
  (a ≤ r ∧ r < a + L) ∨ r + N < a + L

instance {N L a b : Nat} : Decidable (Near N L a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

instance {N L a r : Nat} : Decidable (Covers N L a r) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem Near.symm {N L a b : Nat} (h : Near N L a b) : Near N L b a := by
  unfold Near at h ⊢; omega

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

example {N L i j : Nat} (a b : Fin N) (hL : L ≤ N) (hi : i < L) (hj : j < L)
    (h : (a.val + i) % N = (b.val + j) % N) : Near N L a.val b.val :=
  near_of_overlap a.isLt b.isLt hL hi hj h

theorem covers_of_hit {N L a r i : Nat} (ha : a < N) (hL : L ≤ N)
    (hi : i < L) (h : (a + i) % N = r) : Covers N L a r := by
  have hu : (a + i) / N < 2 := Nat.div_lt_of_lt_mul (by omega)
  have eu : N * ((a + i) / N) + (a + i) % N = a + i := Nat.div_add_mod (a + i) N
  generalize (a + i) / N = u at hu eu
  generalize (a + i) % N = m at eu h
  unfold Covers
  rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl <;> omega

example {N L i : Nat} (a r : Fin N) (hL : L ≤ N) (hi : i < L)
    (h : (a.val + i) % N = r.val) : Covers N L a.val r.val :=
  covers_of_hit a.isLt hL hi h

section Regions
variable {α : Type _}

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

def tuples (N : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | q + 1 => (List.range N).flatMap fun a => (tuples N q).map (a :: ·)

def hasDup : List Nat → Bool
  | [] => false
  | a :: t => t.contains a || hasDup t

def collisions (N q : Nat) : Nat := (tuples N q).countP hasDup

theorem hasDup_eq_false_iff {t : List Nat} : hasDup t = false ↔ t.Nodup := by
  induction t with
  | nil => simp only [hasDup, List.nodup_nil]
  | cons a t ih =>
    simp only [hasDup, ← ih, List.nodup_cons, Bool.eq_false_iff, ne_eq, Bool.or_eq_true, not_or,
      List.contains_iff_mem]

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
      ite_true] <;> omega

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
      simp only [List.contains_cons]
    rw [hsplit, List.length_cons]
    have hor : A.countP (fun a => (a == x) || t.contains a) ≤
        A.countP (fun a => a == x) + A.countP (fun a => t.contains a) :=
      countP_or_le A (fun a => a == x) (fun a => t.contains a)
    omega

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

theorem collision_prob_le (N q : Nat) :
    2 * N * collisions N q ≤ q * (q - 1) * (tuples N q).length := by
  rw [length_tuples]; exact two_mul_collisions_le N q

theorem collision_prob_le_sq (N q : Nat) :
    2 * N * collisions N q ≤ q ^ 2 * (tuples N q).length := by
  have h : 2 * N * collisions N q ≤ q * (q - 1) * (tuples N q).length := collision_prob_le N q
  have : q * (q - 1) ≤ q ^ 2 := by
    rw [Nat.pow_two]; exact Nat.mul_le_mul_left q (Nat.sub_le q 1)
  exact Nat.le_trans h (Nat.mul_le_mul_right _ this)

theorem pow_two_collision_prob_le (k q : Nat) :
    2 ^ (k + 1) * collisions (2 ^ k) q ≤ q ^ 2 * 2 ^ (k * q) := by
  have h : 2 * 2 ^ k * collisions (2 ^ k) q ≤ q ^ 2 * (tuples (2 ^ k) q).length :=
    collision_prob_le_sq (2 ^ k) q
  rw [length_tuples, ← Nat.pow_mul, ← Nat.pow_succ'] at h
  exact h

theorem keccak_collision_prob_le (q : Nat) :
    2 ^ (256 + 1) * collisions (2 ^ 256) q ≤ q ^ 2 * 2 ^ (256 * q) :=
  pow_two_collision_prob_le 256 q

end Counting

section Oracle
variable {α : Type _} [DecidableEq α]

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
      simp only [List.map_cons, oracleOf, ite_true]
      congr 1
      refine Eq.trans (List.map_congr_left fun y hy => ?_) (ih hxs.2 hl)
      have : y ≠ x := fun h => hxs.1 (h ▸ hy)
      simp only [this, ite_false]

def dedup : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then dedup xs else x :: dedup xs

theorem mem_dedup {xs : List α} {y : α} : y ∈ dedup xs ↔ y ∈ xs := by
  induction xs with
  | nil => simp only [dedup]
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · simp only [dedup, hx, ite_true, ih, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun e => e ▸ hx) id⟩
    · simp only [dedup, hx, ite_false, List.mem_cons, ih]

theorem nodup_dedup (xs : List α) : (dedup xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · simp only [dedup, hx, ite_true]; exact ih
    · simp only [dedup, hx, ite_false]
      exact List.nodup_cons.mpr ⟨fun h => hx (mem_dedup.mp h), ih⟩

theorem length_dedup_le (xs : List α) : (dedup xs).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    by_cases hx : x ∈ xs
    · simp only [dedup, hx, ite_true, List.length_cons]; omega
    · simp only [dedup, hx, ite_false, List.length_cons]; omega

theorem collisionFree_dedup {β : Type _} {f : α → β} (xs : List α) :
    CollisionFree f (dedup xs) ↔ CollisionFree f xs :=
  collisionFree_congr fun _ => mem_dedup

theorem oracle_collides_iff {xs : List α} (hxs : xs.Nodup) {t : List Nat}
    (hl : t.length = xs.length) :
    ¬ CollisionFree (oracleOf xs t) xs ↔ hasDup t = true := by
  rw [collisionFree_iff_nodup_map hxs, map_oracleOf hxs hl, ← hasDup_eq_false_iff]
  simp only [Bool.not_eq_false]

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

section RegionCounting

def regionBad (N L : Nat) (roots : List Nat) : List Nat → Bool
  | [] => false
  | a :: t => t.any (fun b => decide (Near N L a b)) || roots.any (fun r => decide (Covers N L a r)) ||
      regionBad N L roots t

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
    have hn' : Near N L a b := of_decide_eq_true hn
    unfold Near at hn'
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
    have hn' : Covers N L a r := of_decide_eq_true hn
    unfold Covers at hn'
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  have h1 := countP_or_le (List.range N) (fun a => decide (r + 1 - L ≤ a ∧ a < r + 1))
    (fun a => decide (r + N + 1 - L ≤ a ∧ a < N))
  rw [countP_range_interval, countP_range_interval] at h1
  omega

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

theorem pow_two_region_prob_le {k L : Nat} {roots : List Nat} (hroots : ∀ r ∈ roots, r < 2 ^ k)
    (q : Nat) :
    2 ^ (k + 1) * regionCollisions (2 ^ k) L roots q ≤
      (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * 2 ^ (k * q) := by
  have h : 2 * 2 ^ k * regionCollisions (2 ^ k) L roots q ≤
      (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * (2 ^ k) ^ q :=
    two_mul_regionCollisions_le hroots q
  rw [← Nat.pow_mul, ← Nat.pow_succ'] at h
  exact h

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

theorem regionsDisjoint_congr {f : α → Nat} {xs ys : List α} (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    RegionsDisjoint N L f roots xs ↔ RegionsDisjoint N L f roots ys :=
  ⟨fun hx => hx.mono fun x hy => (h x).mpr hy, fun hy => hy.mono fun x hx => (h x).mp hx⟩

theorem regionsDisjoint_dedup {f : α → Nat} (xs : List α) :
    RegionsDisjoint N L f roots (dedup xs) ↔ RegionsDisjoint N L f roots xs :=
  regionsDisjoint_congr fun _ => mem_dedup

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

section Adaptive
variable {α : Type _} [DecidableEq α]

def lazyQueries (s : List Nat → α) (t : List Nat) : List α :=
  (List.range t.length).map fun i => s (t.take i)

omit [DecidableEq α] in
theorem length_lazyQueries (s : List Nat → α) (t : List Nat) :
    (lazyQueries s t).length = t.length := by
  simp only [lazyQueries, List.length_map, List.length_range]

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

def eagerQueries (s : List Nat → α) (g : α → Nat) : Nat → List α
  | 0 => []
  | k + 1 => let qs := eagerQueries s g k; qs ++ [s (qs.map g)]

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

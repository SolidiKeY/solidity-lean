import Solidity.Hash.CollisionBound

/-!
# Adaptive queries against a fixed random function

`EagerAdaptiveBound` (`Solidity/Hash/CollisionBound.lean`) states the
birthday bound for an oracle drawn once, as one of the `N^|dom|` tuples on a
finite domain `dom`, and queried by an adaptive strategy `s`: query `i + 1`
is `s` of the first `i` answers. This module proves it (`eagerAdaptiveBound`)
and two strengthenings: queries may repeat (a repeat gets the same answer,
so it is no collision) and the run may stop early (`two_mul_eager_stopped_le`);
and the same holds for the region premise `RegionsDisjoint`
(`two_mul_eagerRegionsFail_le`, `keccak_eager_region_prob_le`).

The proof is a union bound over the first query that goes wrong, counted
over functions rather than answer sequences. `firstHit bad k g` holds when
query `k + 1` under `g` is at a new point `x` and its answer is a bad value
given the first `k` answers: equal to one of them (`repeatBad`), or near one
of them or over a root word (`regionBadValue`). A failing run has such a
step (`collides_succ_imp`, `regionsFail_succ_imp`). For one step, group the
functions by their values off `x`: changing `g` at `x` changes none of the
first `k` answers, so the first `k + 1` queries and `x` itself stay the same
(`eagerQueries_upd`). Each group has `N` members (`le_countP_group`) and at
most `c` of them go wrong when at most `c` values are bad
(`countP_firstHit_group_le`), so `N · |firstHit| ≤ c · N^|dom|`
(`eager_step_le`); the double count over groups is `sumOver_swap`. With
`c = k` (resp. `k(2L-1) + |roots| L`) and summing over `k < q` gives the
bounds of `CollisionBound.lean` for adaptive runs. No probability monad or
sampling equivalence is needed.
-/

namespace Solidity.Hash

section Upd
variable {α : Type _} [DecidableEq α]

/-- `t` with the entry for `x` (its first occurrence in `dom`) replaced by
`b`: the oracle `oracleOf dom t` redefined at `x`. -/
def upd : List α → List Nat → α → Nat → List Nat
  | y :: ys, a :: t, x, b => if x = y then b :: t else a :: upd ys t x b
  | [], t, _, _ => t
  | _ :: _, [], _, _ => []

theorem length_upd (dom : List α) (t : List Nat) (x : α) (b : Nat) :
    (upd dom t x b).length = t.length := by
  induction dom generalizing t with
  | nil => rfl
  | cons y ys ih =>
    cases t with
    | nil => rfl
    | cons a t =>
      by_cases h : x = y
      · simp only [upd, if_pos h, List.length_cons]
      · simp only [upd, if_neg h, List.length_cons, ih]

theorem mem_upd {dom : List α} {t : List Nat} {x : α} {b c : Nat}
    (h : c ∈ upd dom t x b) : c = b ∨ c ∈ t := by
  induction dom generalizing t with
  | nil => exact Or.inr h
  | cons y ys ih =>
    cases t with
    | nil => exact Or.inr h
    | cons a t =>
      by_cases hx : x = y
      · simp only [upd, if_pos hx, List.mem_cons] at h
        rcases h with e | e
        · exact Or.inl e
        · exact Or.inr (List.mem_cons_of_mem a e)
      · simp only [upd, if_neg hx, List.mem_cons] at h
        rcases h with e | e
        · exact Or.inr (e ▸ List.mem_cons_self ..)
        · rcases ih e with e' | e'
          · exact Or.inl e'
          · exact Or.inr (List.mem_cons_of_mem a e')

theorem oracleOf_upd_ne {dom : List α} {t : List Nat} {x y : α} {b : Nat} (hy : y ≠ x) :
    oracleOf dom (upd dom t x b) y = oracleOf dom t y := by
  induction dom generalizing t with
  | nil => rfl
  | cons z zs ih =>
    cases t with
    | nil => rfl
    | cons a t =>
      by_cases hx : x = z
      · have hyz : y ≠ z := hx ▸ hy
        simp only [upd, if_pos hx, oracleOf, if_neg hyz]
      · simp only [upd, if_neg hx, oracleOf, ih]

theorem oracleOf_upd_self {dom : List α} {t : List Nat} {x : α} {b : Nat} (hx : x ∈ dom)
    (hl : t.length = dom.length) : oracleOf dom (upd dom t x b) x = b := by
  induction dom generalizing t with
  | nil => cases hx
  | cons z zs ih =>
    cases t with
    | nil => simp only [List.length_nil, List.length_cons] at hl; omega
    | cons a t =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      by_cases h : x = z
      · simp only [upd, if_pos h, oracleOf]
      · have hx' : x ∈ zs := (List.mem_cons.mp hx).resolve_left h
        simp only [upd, if_neg h, oracleOf, ih hx' hl]

theorem oracleOf_mem {dom : List α} {t : List Nat} {x : α} (hx : x ∈ dom)
    (hl : t.length = dom.length) : oracleOf dom t x ∈ t := by
  induction dom generalizing t with
  | nil => cases hx
  | cons z zs ih =>
    cases t with
    | nil => simp only [List.length_nil, List.length_cons] at hl; omega
    | cons a t =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      by_cases h : x = z
      · simp only [oracleOf, if_pos h]; exact List.mem_cons_self ..
      · have hx' : x ∈ zs := (List.mem_cons.mp hx).resolve_left h
        simp only [oracleOf, if_neg h]
        exact List.mem_cons_of_mem a (ih hx' hl)

theorem upd_upd (dom : List α) (t : List Nat) (x : α) (b c : Nat) :
    upd dom (upd dom t x b) x c = upd dom t x c := by
  induction dom generalizing t with
  | nil => rfl
  | cons z zs ih =>
    cases t with
    | nil => rfl
    | cons a t =>
      by_cases h : x = z
      · simp only [upd, if_pos h]
      · simp only [upd, if_neg h, ih]

theorem upd_oracleOf (dom : List α) (t : List Nat) (x : α) :
    upd dom t x (oracleOf dom t x) = t := by
  induction dom generalizing t with
  | nil => rfl
  | cons z zs ih =>
    cases t with
    | nil => rfl
    | cons a t =>
      by_cases h : x = z
      · simp only [upd, oracleOf, if_pos h]
      · simp only [upd, oracleOf, if_neg h, ih]

end Upd

/-! ## Tuples: membership and distinctness -/

section Tuples

theorem mem_tuples_of {N : Nat} : ∀ {q : Nat} {t : List Nat}, t.length = q →
    (∀ b ∈ t, b < N) → t ∈ tuples N q
  | 0, [], _, _ => List.mem_singleton_self _
  | q + 1, a :: t, hl, hb => by
    have hl' : t.length = q := by simp only [List.length_cons] at hl; omega
    have ht : t ∈ tuples N q := mem_tuples_of hl' fun b h => hb b (List.mem_cons_of_mem a h)
    have ha : a < N := hb a (List.mem_cons_self ..)
    simp only [tuples, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨a, ha, t, ht, rfl⟩

theorem nodup_tuples (N : Nat) : ∀ q : Nat, (tuples N q).Nodup
  | 0 => List.pairwise_singleton _ _
  | q + 1 => by
    have ih : (tuples N q).Nodup := nodup_tuples N q
    simp only [tuples]
    refine List.pairwise_flatMap.mpr ⟨fun a _ => ?_, ?_⟩
    · exact List.pairwise_map.mpr (ih.imp fun h e => h (List.cons.inj e).2)
    · refine (List.nodup_range (n := N)).imp fun hab x hx y hy e => hab ?_
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
      exact (List.cons.inj e).1

theorem upd_mem_tuples {α : Type _} [DecidableEq α] {N : Nat} {dom : List α} {t : List Nat}
    {x : α} {b : Nat} (ht : t ∈ tuples N dom.length) (hb : b < N) :
    upd dom t x b ∈ tuples N dom.length := by
  apply mem_tuples_of
  · rw [length_upd]; exact length_of_mem_tuples ht
  · intro c hc
    rcases mem_upd hc with e | e
    · exact e ▸ hb
    · exact lt_of_mem_tuples ht c e

/-- A duplicate-free list inside another is no longer. -/
theorem length_le_of_nodup_subset {γ : Type _} [DecidableEq γ] :
    ∀ {M L : List γ}, M.Nodup → (∀ x ∈ M, x ∈ L) → M.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | a :: M, L, hM, h => by
    have ha : a ∈ L := h a (List.mem_cons_self ..)
    have hM' : M.Nodup := (List.nodup_cons.mp hM).2
    have hsub : ∀ x ∈ M, x ∈ L.erase a := fun x hx =>
      (List.mem_erase_of_ne fun e => (List.nodup_cons.mp hM).1 (by rw [← e]; exact hx)).mpr
        (h x (List.mem_cons_of_mem a hx))
    have hle : M.length ≤ (L.erase a).length := length_le_of_nodup_subset hM' hsub
    have hlen : (L.erase a).length = L.length - 1 := List.length_erase_of_mem ha
    have hpos : 0 < L.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

theorem sumOver_ite_const {γ : Type _} (l : List γ) (p : γ → Bool) (c : Nat) :
    sumOver l (fun a => if p a = true then c else 0) = c * l.countP p := by
  induction l with
  | nil => simp only [sumOver_nil, List.countP_nil, Nat.mul_zero]
  | cons a l ih =>
    simp only [sumOver_cons, List.countP_cons, ih]
    cases p a <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_add, Nat.mul_one] <;>
      omega

end Tuples

/-! ## The eager game -/

section Eager
variable {α : Type _} [DecidableEq α] (s : List Nat → α) (dom : List α)

omit [DecidableEq α] in
theorem length_eagerQueries (o : α → Nat) (k : Nat) :
    (eagerQueries s o k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [eagerQueries, List.length_append, ih, List.length_singleton]

omit [DecidableEq α] in
theorem eagerQueries_succ (o : α → Nat) (k : Nat) :
    eagerQueries s o (k + 1) = eagerQueries s o k ++ [s ((eagerQueries s o k).map o)] := rfl

omit [DecidableEq α] in
theorem mem_dom_of_mem_eagerQueries {dom : List α} (hs : ∀ t, s t ∈ dom) (o : α → Nat) :
    ∀ {k : Nat} {y : α}, y ∈ eagerQueries s o k → y ∈ dom
  | 0, _, hy => by cases hy
  | k + 1, y, hy => by
    rw [eagerQueries_succ] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact mem_dom_of_mem_eagerQueries hs o hy
    · rw [List.mem_singleton.mp hy]; exact hs _

omit [DecidableEq α] in
theorem mem_eagerQueries_of_le (o : α → Nat) {i k : Nat} (hik : i ≤ k) {y : α}
    (hy : y ∈ eagerQueries s o i) : y ∈ eagerQueries s o k := by
  induction k with
  | zero => rw [Nat.le_zero.mp hik] at hy; exact hy
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hik with h | h
    · rw [eagerQueries_succ]; exact List.mem_append_left _ (ih (Nat.le_of_lt_succ h))
    · rw [← h]; exact hy

/-- The point of query `k + 1` under `g`. -/
def nextQuery (g : List Nat) (k : Nat) : α :=
  s ((eagerQueries s (oracleOf dom g) k).map (oracleOf dom g))

/-- The answers to the first `k` queries under `g`. -/
def answers (g : List Nat) (k : Nat) : List Nat :=
  (eagerQueries s (oracleOf dom g) k).map (oracleOf dom g)

/-- Query `k + 1` goes wrong: its point is new and its answer is a bad value
`bad A b` given the earlier answers `A`. For the preimage premise a bad value
repeats an earlier answer (`repeatBad`); for the region premise it lies near
an earlier answer or covers a root (`regionBadValue`). -/
def firstHit (bad : List Nat → Nat → Bool) (k : Nat) (g : List Nat) : Bool :=
  decide (nextQuery s dom g k ∉ eagerQueries s (oracleOf dom g) k) &&
    bad (answers s dom g k) (oracleOf dom g (nextQuery s dom g k))

/-- A value repeating an earlier answer. -/
def repeatBad (A : List Nat) (b : Nat) : Bool := A.contains b

/-- The first `q` queries under `g` collide; repeated queries are allowed. -/
def eagerCollides (q : Nat) (g : List Nat) : Bool :=
  decide (¬ CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) q))

/-- Redefining `h` at the point of query `k + 1` keeps the answers to the
first `k` queries. -/
theorem map_eagerQueries_upd {h : List Nat} {k : Nat}
    (hnd : nextQuery s dom h k ∉ eagerQueries s (oracleOf dom h) k) (b : Nat) {i : Nat}
    (hik : i ≤ k) :
    (eagerQueries s (oracleOf dom h) i).map (oracleOf dom (upd dom h (nextQuery s dom h k) b)) =
      (eagerQueries s (oracleOf dom h) i).map (oracleOf dom h) := by
  apply List.map_congr_left
  intro y hy
  have hyk : y ∈ eagerQueries s (oracleOf dom h) k := mem_eagerQueries_of_le s _ hik hy
  exact oracleOf_upd_ne fun e => hnd (e ▸ hyk)

/-- …and therefore the first `k + 1` queries. -/
theorem eagerQueries_upd {h : List Nat} {k : Nat}
    (hnd : nextQuery s dom h k ∉ eagerQueries s (oracleOf dom h) k) (b : Nat) :
    ∀ i, i ≤ k + 1 →
      eagerQueries s (oracleOf dom (upd dom h (nextQuery s dom h k) b)) i =
        eagerQueries s (oracleOf dom h) i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih : eagerQueries s (oracleOf dom (upd dom h (nextQuery s dom h k) b)) i =
        eagerQueries s (oracleOf dom h) i := eagerQueries_upd hnd b i (Nat.le_of_succ_le hi)
    rw [eagerQueries_succ, eagerQueries_succ, ih,
      map_eagerQueries_upd s dom hnd b (Nat.le_of_succ_le_succ hi)]

/-- The first `q + 1` queries collide only if the first `q` do or query
`q + 1` is new and repeats an earlier answer. -/
theorem collides_succ_imp (q : Nat) (g : List Nat) (hg : eagerCollides s dom (q + 1) g = true) :
    (eagerCollides s dom q g || firstHit s dom repeatBad q g) = true := by
  simp only [eagerCollides, decide_eq_true_eq] at hg
  simp only [Bool.or_eq_true, eagerCollides, firstHit, repeatBad, answers, Bool.and_eq_true,
    decide_eq_true_eq, List.contains_iff_mem]
  by_cases hq : CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) q)
  · rw [eagerQueries_succ] at hg
    by_cases hx : nextQuery s dom g q ∈ eagerQueries s (oracleOf dom g) q
    · refine absurd (hq.mono fun y hy => ?_) hg
      rcases List.mem_append.mp hy with hy | hy
      · exact hy
      · rw [List.mem_singleton.mp hy]; exact hx
    · refine Or.inr ⟨hx, ?_⟩
      apply Classical.byContradiction
      intro hnot
      apply hg
      refine collisionFree_append.mpr ⟨hq, CollisionFree.singleton _, fun y hy z hz e => ?_⟩
      rw [List.mem_singleton.mp hz] at e
      exact absurd (e ▸ List.mem_map_of_mem hy) hnot
  · exact Or.inl hq

/-- A value whose length-`L` region lies near an earlier answer's region or
covers a root word. -/
def regionBadValue (N L : Nat) (roots : List Nat) (A : List Nat) (b : Nat) : Bool :=
  A.any (fun a => decide (Near N L b a)) || roots.any (fun r => decide (Covers N L b r))

/-- The region premise fails on the first `q` queries under `g`. -/
def eagerRegionsFail (N L : Nat) (roots : List Nat) (q : Nat) (g : List Nat) : Bool :=
  decide (¬ RegionsDisjoint N L (oracleOf dom g) roots (eagerQueries s (oracleOf dom g) q))

/-- The region premise fails on `q + 1` queries only if it fails on the
first `q` or query `q + 1` is new and its region is near an earlier one or
covers a root. -/
theorem regionsFail_succ_imp (N L : Nat) (roots : List Nat) (q : Nat) (g : List Nat)
    (hg : eagerRegionsFail s dom N L roots (q + 1) g = true) :
    (eagerRegionsFail s dom N L roots q g || firstHit s dom (regionBadValue N L roots) q g) =
      true := by
  simp only [eagerRegionsFail, decide_eq_true_eq] at hg
  simp only [Bool.or_eq_true, eagerRegionsFail, firstHit, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hq : RegionsDisjoint N L (oracleOf dom g) roots (eagerQueries s (oracleOf dom g) q)
  · rw [eagerQueries_succ] at hg
    by_cases hx : nextQuery s dom g q ∈ eagerQueries s (oracleOf dom g) q
    · refine absurd (hq.mono fun y hy => ?_) hg
      rcases List.mem_append.mp hy with hy | hy
      · exact hy
      · rw [List.mem_singleton.mp hy]; exact hx
    · refine Or.inr ⟨hx, ?_⟩
      apply Classical.byContradiction
      intro hnot
      have hnot' : regionBadValue N L roots (answers s dom g q)
          (oracleOf dom g (nextQuery s dom g q)) = false := Bool.eq_false_iff.mpr hnot
      simp only [regionBadValue, Bool.or_eq_false_iff, List.any_eq_false,
        decide_eq_true_eq] at hnot'
      apply hg
      refine (regionsDisjoint_congr fun y => ?_).mpr ((regionsDisjoint_cons hx).mpr
        ⟨hq, fun y hy => hnot'.1 _ (List.mem_map_of_mem hy), hnot'.2⟩)
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
      exact Or.comm
  · exact Or.inl hq

variable {s dom}

/-- At most `|A| (2L - 1) + |roots| L` values are bad for the region premise. -/
theorem countP_regionBadValue_le {N L : Nat} {roots : List Nat} (hroots : ∀ r ∈ roots, r < N)
    (A : List Nat) (hA : ∀ a ∈ A, a < N) :
    (List.range N).countP (regionBadValue N L roots A) ≤
      A.length * (2 * L - 1) + roots.length * L := by
  have h1 := countP_or_le (List.range N) (fun b => A.any (fun a => decide (Near N L b a)))
    (fun b => roots.any (fun r => decide (Covers N L b r)))
  have hu := countP_any_le (List.range N) A (fun b a => decide (Near N L b a))
  have hv : sumOver A (fun a => (List.range N).countP (fun b => decide (Near N L b a))) ≤
      sumOver A (fun _ => 2 * L - 1) :=
    sumOver_le A fun a ha => countP_near_le (hA a ha)
  have hu' := countP_any_le (List.range N) roots (fun b r => decide (Covers N L b r))
  have hv' : sumOver roots (fun r => (List.range N).countP (fun b => decide (Covers N L b r))) ≤
      sumOver roots (fun _ => L) :=
    sumOver_le roots fun r hr => countP_covers_le (hroots r hr)
  rw [sumOver_const] at hv hv'
  exact Nat.le_trans h1 (Nat.add_le_add (Nat.le_trans hu hv) (Nat.le_trans hu' hv'))

/-- The group of `h` at step `k`: the `N` functions that agree with `h` off the
point of query `k + 1`. -/
def group (N k : Nat) (h : List Nat) : List (List Nat) :=
  (List.range N).map (upd dom h (nextQuery s dom h k))

/-- A group has `N` members among the tuples. -/
theorem le_countP_group (hs : ∀ t, s t ∈ dom) {N k : Nat} {h : List Nat}
    (hh : h ∈ tuples N dom.length) :
    N ≤ (tuples N dom.length).countP (fun g => decide (g ∈ group (s := s) (dom := dom) N k h)) := by
  have hl : h.length = dom.length := length_of_mem_tuples hh
  have hx : nextQuery s dom h k ∈ dom := hs _
  have hnd : (group (s := s) (dom := dom) N k h).Nodup := by
    refine List.pairwise_map.mpr ((List.nodup_range (n := N)).imp fun hab e => hab ?_)
    have e' := congrArg (fun g => oracleOf dom g (nextQuery s dom h k)) e
    simp only [oracleOf_upd_self hx hl] at e'
    exact e'
  have hsub : ∀ g ∈ group (s := s) (dom := dom) N k h,
      g ∈ (tuples N dom.length).filter (fun g => decide (g ∈ group (s := s) (dom := dom) N k h)) := by
    intro g hg
    refine List.mem_filter.mpr ⟨?_, decide_eq_true hg⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    exact upd_mem_tuples hh (List.mem_range.mp hb)
  have hlen : (group (s := s) (dom := dom) N k h).length = N := by
    simp only [group, List.length_map, List.length_range]
  have hle := length_le_of_nodup_subset hnd hsub
  rw [hlen] at hle
  rw [List.countP_eq_length_filter]
  exact hle

/-- At most `c` members of a group go wrong at query `k + 1`, when at most `c`
values are bad. -/
theorem countP_firstHit_group_le (hs : ∀ t, s t ∈ dom) {bad : List Nat → Nat → Bool}
    {N k c : Nat}
    (hbad : ∀ A : List Nat, A.length = k → (∀ a ∈ A, a < N) → (List.range N).countP (bad A) ≤ c)
    {g : List Nat} (hgT : g ∈ tuples N dom.length) :
    (tuples N dom.length).countP (fun h =>
        firstHit s dom bad k h && decide (g ∈ group (s := s) (dom := dom) N k h)) ≤ c := by
  have hndF : ((tuples N dom.length).filter (fun h =>
      firstHit s dom bad k h && decide (g ∈ group (s := s) (dom := dom) N k h))).Nodup :=
    (nodup_tuples N dom.length).filter _
  have hsub : ∀ h ∈ (tuples N dom.length).filter (fun h =>
        firstHit s dom bad k h && decide (g ∈ group (s := s) (dom := dom) N k h)),
      h ∈ ((List.range N).filter (bad (answers s dom g k))).map
        (upd dom g (nextQuery s dom g k)) := by
    intro h hh
    simp only [List.mem_filter, Bool.and_eq_true, firstHit, decide_eq_true_eq] at hh
    obtain ⟨hhT, ⟨hnd, hhit⟩, hg⟩ := hh
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
    have hq : eagerQueries s (oracleOf dom (upd dom h (nextQuery s dom h k) b)) k =
        eagerQueries s (oracleOf dom h) k := eagerQueries_upd s dom hnd b k (Nat.le_succ k)
    have hans : answers s dom (upd dom h (nextQuery s dom h k) b) k = answers s dom h k := by
      unfold answers; rw [hq]; exact map_eagerQueries_upd s dom hnd b (Nat.le_refl k)
    have hnext : nextQuery s dom (upd dom h (nextQuery s dom h k) b) k = nextQuery s dom h k := by
      unfold answers at hans; unfold nextQuery at hans ⊢; rw [hans]
    have hlt : oracleOf dom h (nextQuery s dom h k) < N :=
      lt_of_mem_tuples hhT _ (oracleOf_mem (hs _) (length_of_mem_tuples hhT))
    rw [hans, hnext]
    refine List.mem_map.mpr ⟨oracleOf dom h (nextQuery s dom h k),
      List.mem_filter.mpr ⟨List.mem_range.mpr hlt, hhit⟩, ?_⟩
    rw [upd_upd]
    exact upd_oracleOf dom h _
  have hlen : (((List.range N).filter (bad (answers s dom g k))).map
      (upd dom g (nextQuery s dom g k))).length ≤ c := by
    rw [List.length_map, ← List.countP_eq_length_filter]
    apply hbad
    · simp only [answers, List.length_map, length_eagerQueries]
    · intro a ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact lt_of_mem_tuples hgT _
        (oracleOf_mem (mem_dom_of_mem_eagerQueries s hs _ hy) (length_of_mem_tuples hgT))
  rw [List.countP_eq_length_filter]
  exact Nat.le_trans (length_le_of_nodup_subset hndF hsub) hlen

/-- One step of the union bound: `N · |E k| ≤ c · N^|dom|` when at most `c`
values are bad. -/
theorem eager_step_le (hs : ∀ t, s t ∈ dom) {bad : List Nat → Nat → Bool} {N k c : Nat}
    (hbad : ∀ A : List Nat, A.length = k → (∀ a ∈ A, a < N) → (List.range N).countP (bad A) ≤ c) :
    N * (tuples N dom.length).countP (firstHit s dom bad k) ≤ c * N ^ dom.length := by
  have hlo : sumOver (tuples N dom.length)
        (fun h => if firstHit s dom bad k h = true then N else 0) ≤
      sumOver (tuples N dom.length) (fun h => (tuples N dom.length).countP (fun g =>
        firstHit s dom bad k h && decide (g ∈ group (s := s) (dom := dom) N k h))) := by
    apply sumOver_le
    intro h hh
    cases hf : firstHit s dom bad k h with
    | false => exact Nat.zero_le _
    | true =>
      simp only [↓reduceIte, Bool.true_and]
      exact le_countP_group hs hh
  have hswap := sumOver_swap (tuples N dom.length) (tuples N dom.length)
    (fun h g => firstHit s dom bad k h && decide (g ∈ group (s := s) (dom := dom) N k h))
  have hhi : sumOver (tuples N dom.length) (fun g => (tuples N dom.length).countP (fun h =>
        firstHit s dom bad k h && decide (g ∈ group (s := s) (dom := dom) N k h))) ≤
      sumOver (tuples N dom.length) (fun _ => c) :=
    sumOver_le _ fun _ hg => countP_firstHit_group_le hs hbad hg
  rw [sumOver_ite_const] at hlo
  rw [sumOver_const, length_tuples] at hhi
  rw [Nat.mul_comm c]
  exact Nat.le_trans hlo (hswap ▸ hhi)

/-- The union bound over the step of the first collision: among the
`N^|dom|` functions, those under which the first `q` adaptive queries collide
number at most `q(q-1)/(2N) · N^|dom|`. Queries may repeat; a repeat gets the
same answer and is no collision. -/
theorem two_mul_eagerCollides_le (hs : ∀ t, s t ∈ dom) (N : Nat) :
    ∀ q, 2 * N * (tuples N dom.length).countP (eagerCollides s dom q) ≤
      q * (q - 1) * N ^ dom.length
  | 0 => by
    have h0 : (tuples N dom.length).countP (eagerCollides s dom 0) = 0 := by
      rw [List.countP_eq_zero]
      intro g _
      simp only [eagerCollides, eagerQueries, decide_eq_true_eq, Classical.not_not]
      exact CollisionFree.nil
    rw [h0]; exact Nat.zero_le _
  | q + 1 => by
    have ih : 2 * N * (tuples N dom.length).countP (eagerCollides s dom q) ≤
        q * (q - 1) * N ^ dom.length := two_mul_eagerCollides_le hs N q
    have hstep : N * (tuples N dom.length).countP (firstHit s dom repeatBad q) ≤
        q * N ^ dom.length :=
      eager_step_le hs fun A hA _ =>
        Nat.le_trans (countP_contains_le List.nodup_range A) (Nat.le_of_eq hA)
    have hsplit : (tuples N dom.length).countP (eagerCollides s dom (q + 1)) ≤
        (tuples N dom.length).countP (eagerCollides s dom q) +
          (tuples N dom.length).countP (firstHit s dom repeatBad q) :=
      Nat.le_trans (countP_le_of_imp _ fun g _ hg => collides_succ_imp s dom q g hg)
        (countP_or_le _ _ _)
    have hmul : 2 * N * (tuples N dom.length).countP (eagerCollides s dom (q + 1)) ≤
        2 * N * (tuples N dom.length).countP (eagerCollides s dom q) +
          2 * N * (tuples N dom.length).countP (firstHit s dom repeatBad q) := by
      have hm := Nat.mul_le_mul_left (2 * N) hsplit
      rw [Nat.mul_add] at hm
      exact hm
    have h2 : 2 * N * (tuples N dom.length).countP (firstHit s dom repeatBad q) ≤
        2 * (q * N ^ dom.length) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 hstep
    have hid : (q + 1) * (q + 1 - 1) * N ^ dom.length =
        q * (q - 1) * N ^ dom.length + 2 * (q * N ^ dom.length) := by
      cases q with
      | zero => simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.zero_sub]
      | succ m =>
        simp only [Nat.add_sub_cancel, ← Nat.mul_assoc, ← Nat.add_mul]
        congr 1
        simp only [Nat.mul_succ, Nat.succ_mul]
        omega
    rw [hid]
    omega

/-- Runs that stop early: if the run under `g` makes `τ g ≤ q` queries (the
stopping point may depend on `g`, hence on the answers), its queries are a
prefix of the first `q`, so the same bound holds. -/
theorem two_mul_eager_stopped_le (hs : ∀ t, s t ∈ dom) (N q : Nat) (τ : List Nat → Nat)
    (hτ : ∀ g, τ g ≤ q) :
    2 * N * (tuples N dom.length).countP (fun g =>
        decide (¬ CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) (τ g)))) ≤
      q * (q - 1) * N ^ dom.length := by
  have hle : (tuples N dom.length).countP (fun g =>
        decide (¬ CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) (τ g)))) ≤
      (tuples N dom.length).countP (eagerCollides s dom q) := by
    apply countP_le_of_imp
    intro g _ hg
    simp only [eagerCollides, decide_eq_true_eq] at hg ⊢
    exact fun hcf => hg (hcf.mono fun y hy => mem_eagerQueries_of_le s _ (hτ g) hy)
  exact Nat.le_trans (Nat.mul_le_mul_left (2 * N) hle) (two_mul_eagerCollides_le hs N q)

/-- For a `k`-bit oracle: probability at most `q(q-1)/2^(k+1)`. -/
theorem pow_two_eager_collision_prob_le (hs : ∀ t, s t ∈ dom) (k q : Nat) :
    2 ^ (k + 1) * (tuples (2 ^ k) dom.length).countP (eagerCollides s dom q) ≤
      q * (q - 1) * 2 ^ (k * dom.length) := by
  have h := two_mul_eagerCollides_le hs (2 ^ k) q
  rw [← Nat.pow_mul, ← Nat.pow_succ'] at h
  exact h

/-- Keccak-256 (`N = 2^256`): an adaptive run of `q` hashes against a uniformly
random function on `dom` collides with probability at most `q(q-1)/2²⁵⁷`. -/
theorem keccak_eager_collision_prob_le (hs : ∀ t, s t ∈ dom) (q : Nat) :
    2 ^ (256 + 1) * (tuples (2 ^ 256) dom.length).countP (eagerCollides s dom q) ≤
      q * (q - 1) * 2 ^ (256 * dom.length) :=
  pow_two_eager_collision_prob_le hs 256 q

/-- The region premise against adaptive queries: among the `N^|dom|`
functions, those under which the region premise fails on the first `q`
queries number at most
`(q(q-1)(2L-1) + 2 q |roots| L) / (2N) · N^|dom|`, the bound of
`two_mul_regionCollisions_le`. Queries may repeat. -/
theorem two_mul_eagerRegionsFail_le (hs : ∀ t, s t ∈ dom) (N L : Nat) {roots : List Nat}
    (hroots : ∀ r ∈ roots, r < N) :
    ∀ q, 2 * N * (tuples N dom.length).countP (eagerRegionsFail s dom N L roots q) ≤
      (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * N ^ dom.length
  | 0 => by
    have h0 : (tuples N dom.length).countP (eagerRegionsFail s dom N L roots 0) = 0 := by
      rw [List.countP_eq_zero]
      intro g _
      simp only [eagerRegionsFail, eagerQueries, decide_eq_true_eq, Classical.not_not]
      exact RegionsDisjoint.nil
    rw [h0]; exact Nat.zero_le _
  | q + 1 => by
    have ih : 2 * N * (tuples N dom.length).countP (eagerRegionsFail s dom N L roots q) ≤
        (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * N ^ dom.length :=
      two_mul_eagerRegionsFail_le hs N L hroots q
    have hstep : N * (tuples N dom.length).countP (firstHit s dom (regionBadValue N L roots) q) ≤
        (q * (2 * L - 1) + roots.length * L) * N ^ dom.length :=
      eager_step_le hs fun A hA hlt => by
        rw [← hA]; exact countP_regionBadValue_le hroots A hlt
    have hsplit : (tuples N dom.length).countP (eagerRegionsFail s dom N L roots (q + 1)) ≤
        (tuples N dom.length).countP (eagerRegionsFail s dom N L roots q) +
          (tuples N dom.length).countP (firstHit s dom (regionBadValue N L roots) q) :=
      Nat.le_trans (countP_le_of_imp _ fun g _ hg => regionsFail_succ_imp s dom N L roots q g hg)
        (countP_or_le _ _ _)
    have hmul : 2 * N * (tuples N dom.length).countP (eagerRegionsFail s dom N L roots (q + 1)) ≤
        2 * N * (tuples N dom.length).countP (eagerRegionsFail s dom N L roots q) +
          2 * N * (tuples N dom.length).countP (firstHit s dom (regionBadValue N L roots) q) := by
      have hm := Nat.mul_le_mul_left (2 * N) hsplit
      rw [Nat.mul_add] at hm
      exact hm
    have h2 : 2 * N * (tuples N dom.length).countP (firstHit s dom (regionBadValue N L roots) q) ≤
        2 * ((q * (2 * L - 1) + roots.length * L) * N ^ dom.length) := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 hstep
    have hid : (q + 1) * (q + 1 - 1) * (2 * L - 1) + 2 * (q + 1) * roots.length * L =
        q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L +
          2 * (q * (2 * L - 1) + roots.length * L) := by
      cases q with
      | zero => simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.zero_sub,
          Nat.mul_one, Nat.add_zero, Nat.mul_assoc]
      | succ m => simp only [Nat.add_sub_cancel]; grind
    rw [hid, Nat.add_mul, Nat.mul_assoc 2 _ (N ^ dom.length)]
    omega

/-- For a `k`-bit oracle: the region premise fails on an adaptive run with
probability at most `(q(q-1)(2L-1) + 2 q R L)/2^(k+1)`. -/
theorem pow_two_eager_region_prob_le (hs : ∀ t, s t ∈ dom) (k L : Nat) {roots : List Nat}
    (hroots : ∀ r ∈ roots, r < 2 ^ k) (q : Nat) :
    2 ^ (k + 1) * (tuples (2 ^ k) dom.length).countP
        (eagerRegionsFail s dom (2 ^ k) L roots q) ≤
      (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * 2 ^ (k * dom.length) := by
  have h := two_mul_eagerRegionsFail_le hs (2 ^ k) L hroots q
  rw [← Nat.pow_mul, ← Nat.pow_succ'] at h
  exact h

/-- Keccak-256: the region premise fails on an adaptive run of `q` hashes with
probability at most `(q(q-1)(2L-1) + 2 q R L)/2²⁵⁷`, `R` root words. -/
theorem keccak_eager_region_prob_le (hs : ∀ t, s t ∈ dom) (L : Nat) {roots : List Nat}
    (hroots : ∀ r ∈ roots, r < 2 ^ 256) (q : Nat) :
    2 ^ (256 + 1) * (tuples (2 ^ 256) dom.length).countP
        (eagerRegionsFail s dom (2 ^ 256) L roots q) ≤
      (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * 2 ^ (256 * dom.length) :=
  pow_two_eager_region_prob_le hs 256 L hroots q

end Eager

/-- **Proved child obligation.** The adaptive birthday bound for an eagerly
sampled oracle, as stated in `CollisionBound.lean`. -/
theorem eagerAdaptiveBound : EagerAdaptiveBound.{u} := by
  intro β _ dom _ s hs N q
  have hle : (tuples N dom.length).countP (fun g =>
        decide ((eagerQueries s (oracleOf dom g) q).Nodup ∧
          ¬ CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) q))) ≤
      (tuples N dom.length).countP (eagerCollides s dom q) := by
    apply countP_le_of_imp
    intro g _ hg
    simp only [eagerCollides, decide_eq_true_eq] at hg ⊢
    exact hg.2
  exact Nat.le_trans (Nat.mul_le_mul_left (2 * N) hle) (two_mul_eagerCollides_le hs N q)

end Solidity.Hash

/-- info: 'Solidity.Hash.keccak_eager_collision_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.keccak_eager_collision_prob_le

/-- info: 'Solidity.Hash.keccak_eager_region_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.keccak_eager_region_prob_le

/-- info: 'Solidity.Hash.two_mul_eager_stopped_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.two_mul_eager_stopped_le

/-- info: 'Solidity.Hash.eagerAdaptiveBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.eagerAdaptiveBound

/-!
# Reachability by saturation (G12)

The checkers of the static frontend (`Solidity/Frontend/Static/`) decide
relations given as least fixpoints over a finite graph: the file-level
scope through `import` chains (G12), the bases of a contract (G14).  This
module gives the one closure they share: `iter succ n S` adds the
successors of `S` to it `n` times, keeping it duplicate-free.

- `iter_sound`: everything added is reachable from the start;
- `iter_complete`: with `n` beyond the size of any list `U` closed under
  `succ` and containing the start, every reachable node is added.  The proof
  is the counting argument: each round either changes nothing (then the set
  is closed) or adds a node of `U`, and a duplicate-free list inside `U` is
  no longer than `U` (`Nodup.length_le_of_subset`).

Cycles are harmless: a revisited node is not added again.  The module
imports nothing and is a static check, never kernel-evaluated hot code.
-/

namespace Solidity.Frontend.Static

variable {α : Type} [DecidableEq α]

/-- Reflexive-transitive reachability along `succ`. -/
inductive Reach (succ : α → List α) : α → α → Prop where
  | refl (a : α) : Reach succ a a
  | step {a b c : α} : b ∈ succ a → Reach succ b c → Reach succ a c

omit [DecidableEq α] in
theorem Reach.trans {succ : α → List α} {a b c : α} (h : Reach succ a b) (h' : Reach succ b c) :
    Reach succ a c := by
  induction h with
  | refl => exact h'
  | step hb _ ih => exact .step hb (ih h')

/-- Append `y` unless present. -/
def insertNew (S : List α) (y : α) : List α := if y ∈ S then S else S ++ [y]

/-- One round: the successors of every node, appended when new. -/
def grow (succ : α → List α) (S : List α) : List α := (S.flatMap succ).foldl insertNew S

/-- `n` rounds. -/
def iter (succ : α → List α) : Nat → List α → List α
  | 0, S => S
  | n + 1, S => iter succ n (grow succ S)

/-- No node of `S` has a successor outside it. -/
def Closed (succ : α → List α) (S : List α) : Prop := ∀ a, a ∈ S → ∀ b, b ∈ succ a → b ∈ S

/-! ## `insertNew` folds -/

theorem foldl_insertNew_superset (ys S : List α) : ∀ a, a ∈ S → a ∈ ys.foldl insertNew S := by
  induction ys generalizing S with
  | nil => intro a h; exact h
  | cons y ys ih =>
    intro a h
    apply ih
    simp only [insertNew]
    split
    · exact h
    · exact List.mem_append_left _ h

theorem foldl_insertNew_mem (ys S : List α) : ∀ a, a ∈ ys → a ∈ ys.foldl insertNew S := by
  induction ys generalizing S with
  | nil => intro a h; cases h
  | cons y ys ih =>
    intro a h
    rcases List.mem_cons.mp h with h | h
    · subst h
      rw [List.foldl_cons]
      apply foldl_insertNew_superset
      simp only [insertNew]
      split
      · assumption
      · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · rw [List.foldl_cons]; exact ih _ a h

theorem foldl_insertNew_sub (ys S : List α) : ∀ a, a ∈ ys.foldl insertNew S → a ∈ S ∨ a ∈ ys := by
  induction ys generalizing S with
  | nil => intro a h; exact .inl h
  | cons y ys ih =>
    intro a h
    rcases ih _ a h with h' | h'
    · simp only [insertNew] at h'
      split at h'
      · exact .inl h'
      · rcases List.mem_append.mp h' with h'' | h''
        · exact .inl h''
        · exact .inr (List.mem_cons.mpr (.inl (List.mem_singleton.mp h'')))
    · exact .inr (List.mem_cons_of_mem _ h')

theorem foldl_insertNew_nodup (ys S : List α) (h : S.Nodup) : (ys.foldl insertNew S).Nodup := by
  induction ys generalizing S with
  | nil => exact h
  | cons y ys ih =>
    apply ih
    simp only [insertNew]
    split
    · exact h
    · rename_i hy
      exact List.nodup_append.mpr ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
        fun a ha b hb => by
          have hb' : b = y := List.mem_singleton.mp hb
          subst hb'
          exact fun e => hy (e ▸ ha)⟩

theorem foldl_insertNew_length (ys S : List α) : S.length ≤ (ys.foldl insertNew S).length := by
  induction ys generalizing S with
  | nil => exact Nat.le_refl _
  | cons y ys ih =>
    refine Nat.le_trans ?_ (ih _)
    simp only [insertNew]
    split
    · exact Nat.le_refl _
    · simp only [List.length_append, List.length_singleton]; exact Nat.le_succ _

theorem foldl_insertNew_grows (ys S : List α) (y : α) (hy : y ∈ ys) (hn : y ∉ S) :
    S.length < (ys.foldl insertNew S).length := by
  induction ys generalizing S with
  | nil => cases hy
  | cons z zs ih =>
    rw [List.foldl_cons]
    by_cases hz : z ∈ S
    · have hne : y ≠ z := fun e => hn (e ▸ hz)
      have hy' : y ∈ zs := (List.mem_cons.mp hy).resolve_left hne
      have e : insertNew S z = S := by simp only [insertNew, hz, if_true]
      rw [e]; exact ih S hy' hn
    · have e : insertNew S z = S ++ [z] := by simp only [insertNew, hz, if_false]
      rw [e]
      refine Nat.lt_of_lt_of_le ?_ (foldl_insertNew_length zs _)
      simp only [List.length_append, List.length_singleton]; exact Nat.lt_succ_self _

theorem foldl_insertNew_same (ys S : List α) (h : ∀ y, y ∈ ys → y ∈ S) : ys.foldl insertNew S = S := by
  induction ys generalizing S with
  | nil => rfl
  | cons y ys ih =>
    have hy : insertNew S y = S := by simp only [insertNew, h y (List.mem_cons_self), if_true]
    rw [List.foldl_cons, hy]
    exact ih S (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-! ## Rounds -/

theorem grow_superset (succ : α → List α) (S : List α) : ∀ a, a ∈ S → a ∈ grow succ S :=
  foldl_insertNew_superset _ _

theorem grow_closed {succ : α → List α} {S : List α} (h : Closed succ S) : grow succ S = S :=
  foldl_insertNew_same _ _ fun y hy => by
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hy
    exact h a ha y hb

theorem grow_grows {succ : α → List α} {S : List α} (h : ¬ Closed succ S) :
    S.length < (grow succ S).length := by
  apply Classical.byContradiction
  intro hlt
  apply h
  intro a ha b hb
  apply Classical.byContradiction
  intro hn
  exact hlt (foldl_insertNew_grows _ S b (List.mem_flatMap.mpr ⟨a, ha, hb⟩) hn)

theorem grow_nodup (succ : α → List α) {S : List α} (h : S.Nodup) : (grow succ S).Nodup :=
  foldl_insertNew_nodup _ _ h

theorem grow_sub {succ : α → List α} {S U : List α} (hS : ∀ a, a ∈ S → a ∈ U)
    (hU : ∀ a, a ∈ U → ∀ b, b ∈ succ a → b ∈ U) : ∀ a, a ∈ grow succ S → a ∈ U := by
  intro a ha
  rcases foldl_insertNew_sub _ _ a ha with h | h
  · exact hS a h
  · obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp h
    exact hU c (hS c hc) a hb

theorem iter_closed {succ : α → List α} {S : List α} (h : Closed succ S) : ∀ n, iter succ n S = S
  | 0 => rfl
  | n + 1 => by simp only [iter, grow_closed h]; exact iter_closed h n

theorem iter_superset (succ : α → List α) : ∀ n S, ∀ a, a ∈ S → a ∈ iter succ n S
  | 0, _, _, h => h
  | n + 1, S, a, h => iter_superset succ n (grow succ S) a (grow_superset succ S a h)

theorem iter_nodup (succ : α → List α) : ∀ n S, S.Nodup → (iter succ n S).Nodup
  | 0, _, h => h
  | n + 1, S, h => iter_nodup succ n (grow succ S) (grow_nodup succ h)

theorem iter_sub {succ : α → List α} {U : List α} (hU : ∀ a, a ∈ U → ∀ b, b ∈ succ a → b ∈ U) :
    ∀ n S, (∀ a, a ∈ S → a ∈ U) → ∀ a, a ∈ iter succ n S → a ∈ U
  | 0, _, h => h
  | n + 1, S, h => iter_sub hU n (grow succ S) (grow_sub h hU)

theorem iter_closed_or_long (succ : α → List α) :
    ∀ n S, Closed succ (iter succ n S) ∨ n + S.length ≤ (iter succ n S).length
  | 0, S => .inr (by simp only [iter, Nat.zero_add]; exact Nat.le_refl _)
  | n + 1, S => by
    by_cases hc : Closed succ S
    · left
      rw [iter_closed hc]
      exact hc
    · rcases iter_closed_or_long succ n (grow succ S) with h | h
      · exact .inl h
      · right
        have hg := grow_grows hc
        simp only [iter]
        omega

/-- A duplicate-free list inside `U` is no longer than `U`. -/
theorem Nodup.length_le_of_subset : ∀ {L U : List α}, L.Nodup → (∀ a, a ∈ L → a ∈ U) →
    L.length ≤ U.length
  | [], _, _, _ => Nat.zero_le _
  | a :: L, U, hn, hs => by
    have hn' := List.nodup_cons.mp hn
    have ha : a ∈ U := hs a (List.mem_cons_self)
    have hsub : ∀ b, b ∈ L → b ∈ U.erase a := fun b hb =>
      (List.mem_erase_of_ne (fun e => hn'.1 (by rw [← e]; exact hb))).mpr (hs b (List.mem_cons_of_mem _ hb))
    have ih := Nodup.length_le_of_subset hn'.2 hsub
    rw [List.length_erase_of_mem ha] at ih
    have hpos : 0 < U.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

omit [DecidableEq α] in
theorem Closed.reach {succ : α → List α} {T : List α} (hT : Closed succ T) {a b : α}
    (h : Reach succ a b) (ha : a ∈ T) : b ∈ T := by
  induction h with
  | refl => exact ha
  | step hb _ ih => exact ih (hT _ ha _ hb)

/-- **Sound**: every node the rounds add is reachable from a start node. -/
theorem iter_sound (succ : α → List α) (a : α) :
    ∀ n S, (∀ b, b ∈ S → Reach succ a b) → ∀ b, b ∈ iter succ n S → Reach succ a b
  | 0, _, h => h
  | n + 1, S, h => by
    apply iter_sound succ a n (grow succ S)
    intro b hb
    rcases foldl_insertNew_sub _ _ b hb with h' | h'
    · exact h b h'
    · obtain ⟨c, hc, hbc⟩ := List.mem_flatMap.mp h'
      exact (h c hc).trans (.step hbc (.refl b))

/-- **Complete**: given a list `U` closed under `succ` that contains the
start, `U.length + 1` rounds from the start reach every reachable node. -/
theorem iter_complete {succ : α → List α} {U : List α}
    (hU : ∀ a, a ∈ U → ∀ b, b ∈ succ a → b ∈ U) {a b : α} (ha : a ∈ U) (h : Reach succ a b) :
    b ∈ iter succ (U.length + 1) [a] := by
  have hsub : ∀ c, c ∈ iter succ (U.length + 1) [a] → c ∈ U :=
    iter_sub hU _ [a] (fun c hc => (List.mem_singleton.mp hc) ▸ ha)
  have hnd : (iter succ (U.length + 1) [a]).Nodup :=
    iter_nodup succ _ [a] (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
  have hle := Nodup.length_le_of_subset hnd hsub
  rcases iter_closed_or_long succ (U.length + 1) [a] with hc | hc
  · exact hc.reach h (iter_superset succ _ [a] a (List.mem_singleton.mpr rfl))
  · simp only [List.length_singleton] at hc
    omega

/-- The nodes reachable from `a`, given a closed bound `U`. -/
def reachable (succ : α → List α) (U : List α) (a : α) : List α := iter succ (U.length + 1) [a]

theorem mem_reachable {succ : α → List α} {U : List α}
    (hU : ∀ a, a ∈ U → ∀ b, b ∈ succ a → b ∈ U) {a b : α} (ha : a ∈ U) :
    b ∈ reachable succ U a ↔ Reach succ a b :=
  ⟨iter_sound succ a _ [a] (fun c hc => by rw [List.mem_singleton.mp hc]; exact .refl a) b,
   iter_complete hU ha⟩

end Solidity.Frontend.Static

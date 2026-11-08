import Solidity.Hash.Adaptive
import Solidity.Hash.Bridge

/-!
# The adaptive random-oracle bridge (H112)

Oracles are uniformly counted as tuples on a finite domain containing every
query the strategy can produce. The query budget includes offline attacker
queries. Contract runs must supply their actual preimage membership in the
strategy transcript; the abstract EVM interface does not manufacture it.
-/

namespace Solidity.Hash.CollisionBridge

open Solidity.Roadmap

/-- The sum of the collision and region union-bound numerators. -/
def numerator (q L R : Nat) : Nat :=
  q * (q - 1) + (q * (q - 1) * (2 * L - 1) + 2 * q * R * L)

section Counts
variable {α : Type _} [DecidableEq α]

/-- Failure of the combined premise on all queried preimages. -/
def eagerPremiseFails (s : List Nat → α) (dom : List α)
    (N L : Nat) (roots : List Nat) (q : Nat) (g : List Nat) : Bool :=
  decide (¬ (CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) q) ∧
    RegionsDisjoint N L (oracleOf dom g) roots (eagerQueries s (oracleOf dom g) q)))

/-- The bad-oracle set is bounded by the union of the existing adaptive
collision and region events. Repeated preimages need no extra premise. -/
theorem combined_count_le (s : List Nat → α) (dom : List α)
    (N L : Nat) (roots : List Nat) (q : Nat) :
    (tuples N dom.length).countP (eagerPremiseFails s dom N L roots q) ≤
      (tuples N dom.length).countP (eagerCollides s dom q) +
      (tuples N dom.length).countP (eagerRegionsFail s dom N L roots q) := by
  apply Nat.le_trans (countP_le_of_imp _ ?_) (countP_or_le _ _ _)
  intro g _ hg
  simp only [eagerPremiseFails, decide_eq_true_eq] at hg
  apply Bool.or_eq_true_iff.mpr
  by_cases hc : CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) q)
  · exact Or.inr (show eagerRegionsFail s dom N L roots q g = true from
      decide_eq_true (fun hr => hg ⟨hc, hr⟩))
  · exact Or.inl (show eagerCollides s dom q g = true from decide_eq_true hc)

/-- Combined bound, cross-multiplied over Nat. -/
theorem two_mul_combined_le {s : List Nat → α} {dom : List α}
    (hs : ∀ t, s t ∈ dom) (N L : Nat) {roots : List Nat}
    (hroots : ∀ r ∈ roots, r < N) (q : Nat) :
    2 * N * (tuples N dom.length).countP (eagerPremiseFails s dom N L roots q) ≤
      numerator q L roots.length * N ^ dom.length := by
  calc
    _ ≤ 2 * N * ((tuples N dom.length).countP (eagerCollides s dom q) +
        (tuples N dom.length).countP (eagerRegionsFail s dom N L roots q)) :=
      Nat.mul_le_mul_left _ (combined_count_le s dom N L roots q)
    _ = 2 * N * (tuples N dom.length).countP (eagerCollides s dom q) +
        2 * N * (tuples N dom.length).countP (eagerRegionsFail s dom N L roots q) :=
      Nat.mul_add ..
    _ ≤ q * (q - 1) * N ^ dom.length +
        (q * (q - 1) * (2 * L - 1) + 2 * q * roots.length * L) * N ^ dom.length :=
      Nat.add_le_add (two_mul_eagerCollides_le hs N q)
        (two_mul_eagerRegionsFail_le hs N L hroots q)
    _ = _ := (Nat.add_mul ..).symm

/-- k-bit reading, leaving powers symbolic during elaboration. -/
theorem pow_two_combined_le {s : List Nat → α} {dom : List α}
    (hs : ∀ t, s t ∈ dom) (k L : Nat) {roots : List Nat}
    (hroots : ∀ r ∈ roots, r < 2 ^ k) (q : Nat) :
    2 ^ (k + 1) *
      (tuples (2 ^ k) dom.length).countP (eagerPremiseFails s dom (2 ^ k) L roots q) ≤
      numerator q L roots.length * (2 ^ k) ^ dom.length := by
  have h := two_mul_combined_le hs (2 ^ k) L hroots q
  rw [← Nat.pow_succ'] at h
  exact h

/-- 256-bit reading: collision contribution q(q-1)/2^257 plus regions. -/
theorem keccak_combined_le {s : List Nat → α} {dom : List α}
    (hs : ∀ t, s t ∈ dom) (L : Nat) {roots : List Nat}
    (hroots : ∀ r ∈ roots, r < 2 ^ 256) (q : Nat) :
    2 ^ (256 + 1) *
      (tuples (2 ^ 256) dom.length).countP (eagerPremiseFails s dom (2 ^ 256) L roots q) ≤
      numerator q L roots.length * (2 ^ 256) ^ dom.length :=
  pow_two_combined_le hs 256 L hroots q

/-- Count inclusion preserves any cross-multiplied bound. -/
theorem scale_count_le {a b c d : Nat} (hincl : a ≤ b) (hbound : c * b ≤ d) :
    c * a ≤ d :=
  Nat.le_trans (Nat.mul_le_mul_left c hincl) hbound

/-- Stopped collision-only runs reuse the existing stopped adaptive theorem. -/
theorem stopped_collision_le {s : List Nat → α} {dom : List α}
    (hs : ∀ t, s t ∈ dom) (N q : Nat) (τ : List Nat → Nat) (hτ : ∀ g, τ g ≤ q) :
    2 * N * (tuples N dom.length).countP (fun g =>
      decide (¬ CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) (τ g)))) ≤
      q * (q - 1) * N ^ dom.length :=
  two_mul_eager_stopped_le hs N q τ hτ

/-- No queries: combined failure has zero oracles. -/
theorem zero_queries (s : List Nat → α) (dom : List α) (N L : Nat) (roots : List Nat) :
    (tuples N dom.length).countP (eagerPremiseFails s dom N L roots 0) = 0 := by
  apply List.countP_eq_zero.mpr
  intro g _ hg
  exact (of_decide_eq_true hg) ⟨CollisionFree.nil, RegionsDisjoint.nil⟩

/-- One query: collision failure has zero oracles, without discarding roots
from the region event. Coordinator correction E4-Q1 (#168). -/
theorem one_query_collision (s : List Nat → α) (dom : List α) (N : Nat) :
    (tuples N dom.length).countP (eagerCollides s dom 1) = 0 := by
  apply List.countP_eq_zero.mpr
  intro g _ hg
  have hc : CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) 1) :=
    CollisionFree.singleton _
  exact (of_decide_eq_true hg) hc

/-- Tiny positive root-hit control: of the two functions on one point,
one fails the combined premise after one query. -/
theorem one_query_root_hit :
    (tuples 2 1).countP (eagerPremiseFails (fun _ => (0 : Nat)) [0] 2 1 [0] 1) = 1 := by
  decide

/-- Direct region-only version of the positive one-query root-hit control. -/
theorem one_query_region_hit :
    (tuples 2 1).countP (eagerRegionsFail (fun _ => (0 : Nat)) [0] 2 1 [0] 1) = 1 := by
  decide

end Counts

/-- The eager oracle is bounded everywhere, including its default zero
outside the finite domain. -/
theorem oracleOf_lt {N : Nat} (hN : 0 < N) (dom : List Bytes) (g : List Nat)
    (hg : ∀ b ∈ g, b < N) (x : Bytes) : oracleOf dom g x < N := by
  induction dom generalizing g with
  | nil => exact hN
  | cons a dom ih =>
    cases g with
    | nil => exact hN
    | cons b g =>
      by_cases he : x = a
      · simp only [oracleOf, if_pos he]
        exact hg b (List.mem_cons_self ..)
      · simp only [oracleOf, if_neg he]
        exact ih g (fun c hc => hg c (List.mem_cons_of_mem b hc))

/-- Replace only keccak; modulo makes the family total even for tuples that
are not sampled. On every sampled tuple this is exactly oracleOf, not a
modified distribution (oracleFixed_hash_val). -/
def oracleFixed (F : Fixed) (dom : List Bytes) (g : List Nat) : Fixed :=
  { F with
    evm := { F.evm with
      keccak := fun b => oracleOf dom g b % 2 ^ 256
      keccak_lt := fun _ => Nat.mod_lt _
        (Nat.lt_of_le_of_lt (Nat.zero_le _) (F.evm.keccak_lt [])) } }

/-- The sampled fixed hash agrees with the eager oracle on all bytes. -/
theorem oracleFixed_hash_val (F : Fixed) (dom : List Bytes) {g : List Nat}
    (hg : g ∈ tuples (2 ^ 256) dom.length) (b : Bytes) :
    ((oracleFixed F dom g).hash b).val = oracleOf dom g b :=
  Nat.mod_eq_of_lt (oracleOf_lt
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (F.evm.keccak_lt [])) dom g
    (fun c hc => lt_of_mem_tuples hg c hc) b)

/-- The contract premise is exactly the oracle's collision and region
premises, on its actual two lists. -/
theorem oracleFixed_premise_iff (F : Fixed) (dom : List Bytes) {g : List Nat}
    (hg : g ∈ tuples (2 ^ 256) dom.length) (xs ys : List Bytes) :
    HashPremise (oracleFixed F dom g) xs ys ↔
      CollisionFree (oracleOf dom g) xs ∧
      RegionsDisjoint (2 ^ 256) F.regionLen (oracleOf dom g) (List.range F.rootSlots) ys := by
  simp only [HashPremise, CollisionFree, RegionsDisjoint, Fin.ext_iff,
    oracleFixed_hash_val F dom hg]
  rfl

instance (F : Fixed) (xs ys : List Bytes) : Decidable (HashPremise F xs ys) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Good transcript premises descend to the run's actual preimage lists,
which may repeat, stop early, or exclude offline strategy queries. -/
theorem premise_of_transcript {F : Fixed} {s : List Nat → Bytes} {dom : List Bytes}
    {g : List Nat} (hg : g ∈ tuples (2 ^ 256) dom.length) {q : Nat} {xs ys : List Bytes}
    (hx : ∀ b ∈ xs, b ∈ eagerQueries s (oracleOf dom g) q)
    (hy : ∀ b ∈ ys, b ∈ eagerQueries s (oracleOf dom g) q)
    (hc : CollisionFree (oracleOf dom g) (eagerQueries s (oracleOf dom g) q))
    (hr : RegionsDisjoint (2 ^ 256) F.regionLen (oracleOf dom g)
      (List.range F.rootSlots) (eagerQueries s (oracleOf dom g) q)) :
    HashPremise (oracleFixed F dom g) xs ys :=
  (oracleFixed_premise_iff F dom hg xs ys).mpr ⟨hc.mono hx, hr.mono hy⟩

/-- The actual run-premise failure event for a hash-replaced family. -/
def runPremiseFails (F : Fixed) (dom : List Bytes)
    (xs ys : List Nat → List Bytes) (g : List Nat) : Bool :=
  decide (¬ HashPremise (oracleFixed F dom g) (xs g) (ys g))

/-- Compiler-independent contract bridge: all actual preimages are among
at most q total strategy queries, including offline attacker queries. -/
theorem run_premise_le (F : Fixed) {s : List Nat → Bytes} {dom : List Bytes}
    (hs : ∀ t, s t ∈ dom) (hroots : ∀ r ∈ List.range F.rootSlots, r < 2 ^ 256)
    (q : Nat) (xs ys : List Nat → List Bytes)
    (hx : ∀ g ∈ tuples (2 ^ 256) dom.length, ∀ b ∈ xs g,
      b ∈ eagerQueries s (oracleOf dom g) q)
    (hy : ∀ g ∈ tuples (2 ^ 256) dom.length, ∀ b ∈ ys g,
      b ∈ eagerQueries s (oracleOf dom g) q) :
    2 ^ (256 + 1) *
      (tuples (2 ^ 256) dom.length).countP (runPremiseFails F dom xs ys) ≤
      numerator q F.regionLen (List.range F.rootSlots).length * (2 ^ 256) ^ dom.length := by
  have hsub : (tuples (2 ^ 256) dom.length).countP (runPremiseFails F dom xs ys) ≤
      (tuples (2 ^ 256) dom.length).countP
        (eagerPremiseFails s dom (2 ^ 256) F.regionLen (List.range F.rootSlots) q) := by
    apply countP_le_of_imp
    intro g hg hbad
    simp only [runPremiseFails, decide_eq_true_eq] at hbad
    apply decide_eq_true
    intro hgood
    exact hbad (premise_of_transcript hg (hx g hg) (hy g hg) hgood.1 hgood.2)
  apply scale_count_le hsub
  exact keccak_combined_le hs F.regionLen hroots q

/-- Deduplication preserves the actual failure event pointwise, hence
also its count over the same sampled oracle domain. -/
theorem runPremiseFails_dedup (F : Fixed) (dom : List Bytes)
    (xs ys : List Nat → List Bytes) (g : List Nat) :
    runPremiseFails F dom (fun h => dedup (xs h)) (fun h => dedup (ys h)) g =
      runPremiseFails F dom xs ys g := by
  simp only [runPremiseFails, Bridge.premise_dedup]

/-- The actual collision-only event. -/
def runCollisionFails (F : Fixed) (dom : List Bytes)
    (xs : List Nat → List Bytes) (g : List Nat) : Bool :=
  decide (¬ CollisionFree (oracleFixed F dom g).hash (xs g))

/-- Collision-only actual-run bound, without a region-clearance assumption. -/
theorem run_collision_le (F : Fixed) {s : List Nat → Bytes} {dom : List Bytes}
    (hs : ∀ t, s t ∈ dom) (q : Nat) (xs : List Nat → List Bytes)
    (hx : ∀ g ∈ tuples (2 ^ 256) dom.length, ∀ b ∈ xs g,
      b ∈ eagerQueries s (oracleOf dom g) q) :
    2 ^ (256 + 1) * (tuples (2 ^ 256) dom.length).countP (runCollisionFails F dom xs) ≤
      q * (q - 1) * (2 ^ 256) ^ dom.length := by
  have hsub : (tuples (2 ^ 256) dom.length).countP (runCollisionFails F dom xs) ≤
      (tuples (2 ^ 256) dom.length).countP (eagerCollides s dom q) := by
    apply countP_le_of_imp
    intro g hg hbad
    simp only [runCollisionFails, decide_eq_true_eq] at hbad
    apply decide_eq_true
    intro hgood
    have hp : HashPremise (oracleFixed F dom g) (xs g) [] :=
      (oracleFixed_premise_iff F dom hg (xs g) []).mpr
        ⟨hgood.mono (hx g hg), RegionsDisjoint.nil⟩
    exact hbad hp.1
  apply scale_count_le hsub
  have h := keccak_eager_collision_prob_le hs q
  rw [Nat.pow_mul] at h
  exact h

/-- The actual region-only event. -/
def runRegionsFail (F : Fixed) (dom : List Bytes)
    (ys : List Nat → List Bytes) (g : List Nat) : Bool :=
  decide (¬ RegionsDisjoint (2 ^ 256) F.regionLen
    (fun b => ((oracleFixed F dom g).hash b).val) (List.range F.rootSlots) (ys g))

/-- Region-only actual-run bound. The root-hit contribution remains present
at q=1, as required by the corrected controls. -/
theorem run_regions_le (F : Fixed) {s : List Nat → Bytes} {dom : List Bytes}
    (hs : ∀ t, s t ∈ dom) (hroots : ∀ r ∈ List.range F.rootSlots, r < 2 ^ 256)
    (q : Nat) (ys : List Nat → List Bytes)
    (hy : ∀ g ∈ tuples (2 ^ 256) dom.length, ∀ b ∈ ys g,
      b ∈ eagerQueries s (oracleOf dom g) q) :
    2 ^ (256 + 1) * (tuples (2 ^ 256) dom.length).countP (runRegionsFail F dom ys) ≤
      (q * (q - 1) * (2 * F.regionLen - 1) +
        2 * q * (List.range F.rootSlots).length * F.regionLen) * (2 ^ 256) ^ dom.length := by
  have hsub : (tuples (2 ^ 256) dom.length).countP (runRegionsFail F dom ys) ≤
      (tuples (2 ^ 256) dom.length).countP
        (eagerRegionsFail s dom (2 ^ 256) F.regionLen (List.range F.rootSlots) q) := by
    apply countP_le_of_imp
    intro g hg hbad
    simp only [runRegionsFail, decide_eq_true_eq] at hbad
    apply decide_eq_true
    intro hgood
    have hp : HashPremise (oracleFixed F dom g) [] (ys g) :=
      (oracleFixed_premise_iff F dom hg [] (ys g)).mpr
        ⟨CollisionFree.nil, hgood.mono (hy g hg)⟩
    exact hbad hp.2
  apply scale_count_le hsub
  have h := keccak_eager_region_prob_le hs F.regionLen hroots q
  rw [Nat.pow_mul] at h
  exact h

end Solidity.Hash.CollisionBridge

/-- info: 'Solidity.Hash.CollisionBridge.two_mul_combined_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CollisionBridge.two_mul_combined_le
/-- info: 'Solidity.Hash.CollisionBridge.run_premise_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CollisionBridge.run_premise_le
/-- info: 'Solidity.Hash.CollisionBridge.stopped_collision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CollisionBridge.stopped_collision_le

/-- info: 'Solidity.Hash.CollisionBridge.run_collision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CollisionBridge.run_collision_le
/-- info: 'Solidity.Hash.CollisionBridge.run_regions_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.CollisionBridge.run_regions_le

import Solidity.Hash.CollisionBound
import Solidity.Roadmap.Contracts

/-!
# H112: the ideal and per-run hash readings

The ideal machine still stores symbolic slots. These lemmas apply existing
hash-parametric guarded statements to concrete runs; they do not assert a
simulation of that machine by word-addressed storage. Run injectivity gives
collision freedom. Region clearance is separate, even for sane parameters.
-/

namespace Solidity.Hash.Bridge

open Solidity.Roadmap

/-- Run injectivity supplies exactly the collision part of the premise.
The region part is still required; sane parameters alone do not supply it. -/
theorem premise_of_run_injective {F : Fixed} {xs ys : List Bytes}
    (hinj : ∀ a ∈ xs, ∀ b ∈ xs, F.hash a = F.hash b → a = b)
    (regions : RegionsDisjoint (2 ^ 256) F.regionLen (fun b => (F.hash b).val)
      (List.range F.rootSlots) ys) : HashPremise F xs ys :=
  ⟨hinj, regions⟩

/-- Precisely the extra requirements beyond run injectivity. -/
theorem premise_iff_clearance {F : Fixed} {xs ys : List Bytes}
    (hinj : CollisionFree F.hash xs) :
    HashPremise F xs ys ↔
      (∀ a ∈ ys, ∀ b ∈ ys, a ≠ b →
        ¬ Near (2 ^ 256) F.regionLen (F.hash a).val (F.hash b).val) ∧
      (∀ a ∈ ys, ∀ r ∈ List.range F.rootSlots,
        ¬ Covers (2 ^ 256) F.regionLen (F.hash a).val r) :=
  ⟨fun h => h.2, fun h => ⟨hinj, h⟩⟩

/-- Root-free unit regions: bounded distinct hash words suffice. This is
an ideal-on-the-run special case, not global injectivity of keccak. -/
theorem premise_unit_rootFree {F : Fixed} {xs ys : List Bytes}
    (hL : F.regionLen = 1) (hR : F.rootSlots = 0)
    (hx : CollisionFree F.hash xs) (hy : CollisionFree F.hash ys) :
    HashPremise F xs ys := by
  refine ⟨hx, ?_, ?_⟩
  · intro a ha b hb hne hn
    have haN := (F.hash a).isLt
    have hbN := (F.hash b).isLt
    have he : (F.hash a).val = (F.hash b).val := by
      unfold Near at hn
      rw [hL] at hn
      dsimp only at hn
      omega
    exact hne (hy a ha b hb (Fin.ext he))
  · intro a _ r hr
    rw [hR] at hr
    cases hr

/-- Any statement guarded by the contract's own guard transfers on exactly
those runs meeting its own hash premise. -/
theorem transfer {V : EvmSpec} {p : V.lang.Prog} {e : V.lang.Env}
    {r : V.lang.Res} {P : Prop} (guarded : V.lang.Guard p e r → P)
    (premise : HashPremise V.fixed (V.hashed p e r) (V.slotHashed p e r)) : P :=
  guarded ((V.guard_iff p e r).mpr premise)

/-- List-prefix inheritance. No EVM resource-prefix consistency is assumed:
the caller supplies the relations between the actual preimage lists. -/
theorem transfer_prefix {V : EvmSpec} {p : V.lang.Prog} {e : V.lang.Env}
    {r r' : V.lang.Res} {P : Prop} (guarded : V.lang.Guard p e r → P)
    (hx : V.hashed p e r <+: V.hashed p e r')
    (hy : V.slotHashed p e r <+: V.slotHashed p e r')
    (premise : HashPremise V.fixed (V.hashed p e r') (V.slotHashed p e r')) : P :=
  transfer guarded (HashPremise.of_prefix hx hy premise)

/-- A distinct colliding pair falsifies the premise; no transfer is claimed
for that run. -/
theorem not_premise_of_collision {F : Fixed} {xs ys : List Bytes} {a b : Bytes}
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) (he : F.hash a = F.hash b) :
    ¬ HashPremise F xs ys :=
  fun h => hne (h.1 a ha b hb he)

/-- Even one query may hit a root. Collision freedom of the singleton
cannot remove this obstruction, whatever the other run preimages are. -/
theorem not_premise_of_root_hit {F : Fixed} {xs ys : List Bytes} {a : Bytes} {r : Nat}
    (ha : a ∈ ys) (hr : r ∈ List.range F.rootSlots)
    (hit : Covers (2 ^ 256) F.regionLen (F.hash a).val r) :
    ¬ HashPremise F xs ys :=
  fun h => h.2.2 a ha r hr hit

/-- Empty preimages supply an inhabited premise; admissibility of an actual
execution remains a separate requirement of a compiler corollary. -/
theorem empty (F : Fixed) : HashPremise F [] [] := HashPremise.nil F

/-- A concrete constant hash, retaining all other fixed parameters. Only a
negative control, never the hash used by the ideal machine. -/
def constantHash (F : Fixed) : Fixed :=
  { F with
    evm := { F.evm with
      keccak := fun _ => 0
      keccak_lt := fun _ => Nat.lt_of_le_of_lt (Nat.zero_le _) (F.evm.keccak_lt []) } }

/-- Two distinct byte preimages collide under the constant-hash control. -/
theorem constantHash_collision (F : Fixed) :
    ¬ HashPremise (constantHash F) [[], [0]] [] := by
  apply not_premise_of_collision (a := []) (b := [0])
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · intro h
    cases h
  · rfl

/-- Only membership, not order or multiplicity, determines the premise. -/
theorem premise_congr {F : Fixed} {xs xs' ys ys' : List Bytes}
    (hx : ∀ b, b ∈ xs ↔ b ∈ xs') (hy : ∀ b, b ∈ ys ↔ b ∈ ys') :
    HashPremise F xs ys ↔ HashPremise F xs' ys' :=
  ⟨fun h => ⟨(collisionFree_congr hx).mp h.1, (regionsDisjoint_congr hy).mp h.2⟩,
    fun h => ⟨(collisionFree_congr hx).mpr h.1, (regionsDisjoint_congr hy).mpr h.2⟩⟩

/-- Deduplicating the actual collision and slot lists keeps exactly the
same guard; it does not excuse any colliding distinct pair. -/
theorem premise_dedup (F : Fixed) (xs ys : List Bytes) :
    HashPremise F (dedup xs) (dedup ys) ↔ HashPremise F xs ys :=
  premise_congr (fun _ => mem_dedup) (fun _ => mem_dedup)

/-- Repeating an entire transcript gives the same premise. -/
theorem premise_repeat (F : Fixed) (xs ys : List Bytes) :
    HashPremise F (xs ++ xs) (ys ++ ys) ↔ HashPremise F xs ys :=
  premise_congr
    (fun _ => ⟨fun h => (List.mem_append.mp h).elim id id,
      fun h => List.mem_append_left _ h⟩)
    (fun _ => ⟨fun h => (List.mem_append.mp h).elim id id,
      fun h => List.mem_append_left _ h⟩)

end Solidity.Hash.Bridge

/-- info: 'Solidity.Hash.Bridge.premise_unit_rootFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Hash.Bridge.premise_unit_rootFree
/-- info: 'Solidity.Hash.Bridge.transfer_prefix' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Hash.Bridge.transfer_prefix

/-- info: 'Solidity.Hash.Bridge.premise_dedup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Hash.Bridge.premise_dedup

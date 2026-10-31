import Solidity.Roadmap.Contracts

/-!
# Per-run history premises at transaction boundaries

Consume the approved G01 HashPremise, retaining cross-transaction collision and
region obligations. Separate local premises are not substituted for history.
-/
namespace Solidity.Roadmap.V16

/-- A continuation inherits its own local premise from the full history;
this direction does not assert independent local premises can be joined. -/
theorem hash_history_tail {F : Fixed} {xs ys ss ts : List Bytes}
    (h : HashPremise F (xs ++ ys) (ss ++ ts)) : HashPremise F ys ts :=
  ⟨h.1.append_right, h.2.mono (fun _ hx => List.mem_append_right ss hx)⟩

/-- The history premise explicitly constrains past/future cross-preimages. -/
theorem hash_history_cross {F : Fixed} {xs ys ss ts : List Bytes}
    (h : HashPremise F (xs ++ ys) (ss ++ ts)) :
    ∀ x ∈ xs, ∀ y ∈ ys, F.hash x = F.hash y → x = y :=
  (Solidity.Hash.collisionFree_append.mp h.1).2.2

/-- Negative control over the existing collision predicate: even two
inhabited singleton premises need not join. This is not a claim about Keccak
collisions; it refutes a logically invalid premise-composition rule. -/
theorem local_hash_premises_do_not_join :
    Solidity.Hash.CollisionFree (fun _ : Bool => false) [false] ∧
    Solidity.Hash.CollisionFree (fun _ : Bool => false) [true] ∧
    ¬ Solidity.Hash.CollisionFree (fun _ : Bool => false) ([false] ++ [true]) := by
  refine ⟨Solidity.Hash.CollisionFree.singleton _, Solidity.Hash.CollisionFree.singleton _, ?_⟩
  intro h
  have cross := (Solidity.Hash.collisionFree_append.mp h).2.2
  have impossible : false = true := cross false (by decide) true (by decide) rfl
  cases impossible
end Solidity.Roadmap.V16

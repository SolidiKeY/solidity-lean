import Init

/-! Isolated exact subgoal from CollisionBound line 407. This does not import
or repair the owner module, or establish the two remaining arithmetic proofs. -/
namespace MigrateRoadmapFixtures

theorem contains_cons_function (x : Nat) (t : List Nat) :
    (fun a => (x :: t).contains a) = (fun a => (a == x) || t.contains a) := by
  funext a
  exact List.contains_cons

theorem countP_split (A t : List Nat) (x : Nat) :
    A.countP (fun a => (x :: t).contains a) =
      A.countP (fun a => (a == x) || t.contains a) := by
  congr 1
  exact contains_cons_function x t

theorem rejects_dropped_head :
    ([1, 2].countP (fun a => ([1] : List Nat).contains a)) ≠
      ([1, 2].countP (fun a => ([] : List Nat).contains a)) := by decide

theorem rejects_dropped_tail :
    ([1, 2].countP (fun a => ([1, 2] : List Nat).contains a)) ≠
      ([1, 2].countP (fun a => a == 1)) := by decide

#print axioms MigrateRoadmapFixtures.contains_cons_function
#print axioms MigrateRoadmapFixtures.countP_split
end MigrateRoadmapFixtures

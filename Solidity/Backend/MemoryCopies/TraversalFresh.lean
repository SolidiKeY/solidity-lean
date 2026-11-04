import Solidity.Backend.MemoryCopies.TraversalInterface

/-! Identity separation of siblings in the existing typed copy fold. -/
namespace Solidity.Backend.MemoryCopies

theorem traversalFresh {R : RefTy} {n : Nat} (values : SVec (.ref R) n)
    (memory : (Ty.ref R).mapFree = true) {H : HTy} (heap : Heap H) :
    TraversalFreshCertificate heap values memory := by
  cases values with
  | nil =>
    constructor
    · intro identity member
      simp only [SVec.copyStToM_nil, List.map_nil, List.not_mem_nil] at member
    · rw [SVec.copyStToM_nil]; exact List.Pairwise.nil
  | cons value rest =>
    let first := value.copyStToM heap memory
    let tail := rest.copyStToM first.heap memory
    have certificate : TraversalFreshCertificate first.heap rest memory := traversalFresh rest memory first.heap
    have freshFirst : H.length ≤ first.val.id := SVal.copyStToM_id_ge heap value memory
    have oldLength : H.length ≤ first.H'.length := first.ext.length_le
    have rootBound : first.val.id < first.H'.length := first.val.id_lt
    constructor
    · intro identity member
      rw [SVec.copyStToM_cons] at member
      change identity ∈ first.val.id :: tail.val.1.map (fun reference => reference.id) at member
      rcases List.mem_cons.mp member with equal | later
      · exact equal ▸ freshFirst
      · exact Nat.le_trans oldLength (certificate.fresh identity later)
    · rw [SVec.copyStToM_cons]
      change (first.val.id :: tail.val.1.map (fun reference => reference.id)).Pairwise (· < ·)
      apply List.pairwise_cons.mpr
      constructor
      · intro identity member
        exact Nat.lt_of_lt_of_le rootBound (certificate.fresh identity member)
      · exact certificate.ordered

termination_by n

/-- Distinct source positions never become aliases merely because their
storage values happen to be equal. -/
theorem traversal_no_duplicate_ids {R : RefTy} {n : Nat} (values : SVec (.ref R) n)
    (memory : (Ty.ref R).mapFree = true) {H : HTy} (heap : Heap H) :
    ((values.copyStToM heap memory).val.1.map (fun reference => reference.id)).Nodup :=
  (traversalFresh values memory heap).ordered.imp (fun less => Nat.ne_of_lt less)

#print axioms traversalFresh
#print axioms traversal_no_duplicate_ids
end Solidity.Backend.MemoryCopies

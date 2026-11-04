import Solidity.Backend.MemoryCopies.TraversalFresh

/-! Populated nested siblings, equal inputs and negative identity controls. -/
namespace Solidity.Backend.MemoryCopies.TraversalControls
private def child : Ty := .ref (.array (.prim .uint))
private def seven : SVal (.prim .uint) := .prim ⟨7, by decide⟩
private def array (n : Nat) (bound : n < 2^256) : SVal child :=
  .array (SVec.replicate seven n) .nil bound
private def nested : SVal (.ref (.array child)) :=
  .array (.cons (array 2 (by decide)) (.cons (array 0 (by decide)) (.cons (array 64 (by decide)) .nil))) .nil (by decide)
private def empty : SVal (.ref (.array child)) := .array .nil .nil (by decide)
private def values : SVec (.ref (.array child)) 3 := .cons nested (.cons nested (.cons empty .nil))
private def initial : Heap [] := ()
private def seed := (array 1 (by decide)).copyStToM initial rfl

/-- Repeated equal storage trees become separate deep copies, after an old
object. Every nested child allocation contributes to the sibling root ids. -/
theorem nested_identities :
    ((values.copyStToM seed.heap rfl).val.1.map (fun reference => reference.id)) = [4,8,9] := by
  decide +kernel

theorem populated_certificate : Nonempty (TraversalFreshCertificate seed.heap values rfl) :=
  ⟨traversalFresh values rfl seed.heap⟩

theorem wrong_shared_identity :
    ((values.copyStToM seed.heap rfl).val.1.map (fun reference => reference.id)) ≠ [4,4,9] := by
  rw [nested_identities]
  decide

theorem empty_certificate {H : HTy} (heap : Heap H) :
    Nonempty (TraversalFreshCertificate heap (SVec.nil (E := .ref (.array child))) rfl) :=
  ⟨traversalFresh .nil rfl heap⟩

/-- The generic traversal covers long vectors without evaluating copy loops. -/
theorem long_distinct {H : HTy} (heap : Heap H) :
    (((SVec.replicate nested 64).copyStToM heap rfl).val.1.map (fun reference => reference.id)).Nodup :=
  traversal_no_duplicate_ids (SVec.replicate nested 64) rfl heap

#print axioms nested_identities
#print axioms populated_certificate
#print axioms wrong_shared_identity
#print axioms empty_certificate
#print axioms long_distinct
end Solidity.Backend.MemoryCopies.TraversalControls

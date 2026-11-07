import Solidity.Lowering.V07.P12Controls

/-! Guards the inherited BindingRel fixture against absent references and weakened
reference identity. Uses the existing inhabited P12 relation at its fixed witness
heap; does not define/unify relations or establish source/world/compiler adequacy.
These additive isolated controls leave all producer and original controls read-only.
-/
namespace Solidity.H62.BindingFixtures
open Lowering.V07 Source.SemanticsExamples

/-- Two related memory bindings must be the same pair, not merely have equal
contents. Both values and references live in the existing fixed witness layout. -/
theorem memory_pair_unique
    (v w : Source.Val P12Controls.E.layout (.bytes .memory))
    (r s : (LTy.mem bytesR).TDenote P12Controls.C P12Controls.target.H)
    (left : P12Controls.BindingRel (.bytes .memory) (.mem bytesR) v r)
    (right : P12Controls.BindingRel (.bytes .memory) (.mem bytesR) w s) :
    v = w ∧ r = s :=
  ⟨left.1.trans right.1.symm, left.2.trans right.2.symm⟩

/-- The storage witness is rigid in the same fixed layout; this does not identify
arbitrary equal-content storage locations or relate different heaps. -/
theorem storage_pair_unique
    (v w : Source.Val P12Controls.E.layout (.bytes .storage))
    (r s : (LTy.alias bytesR).TDenote P12Controls.C P12Controls.target.H)
    (left : P12Controls.BindingRel (.bytes .storage) (.alias bytesR) v r)
    (right : P12Controls.BindingRel (.bytes .storage) (.alias bytesR) w s) :
    v = w ∧ r = s :=
  ⟨left.1.trans right.1.symm, left.2.trans right.2.symm⟩

/-- Absence cannot satisfy the memory reference fixture, for any source value. -/
theorem memory_absent_refused
    (v : Source.Val P12Controls.E.layout (.bytes .memory)) :
    ¬ P12Controls.BindingRel (.bytes .memory) (.mem bytesR) v none :=
  fun related => Option.noConfusion related.2

/-- Absence cannot satisfy the storage reference fixture, for any source value. -/
theorem storage_absent_refused
    (v : Source.Val P12Controls.E.layout (.bytes .storage)) :
    ¬ P12Controls.BindingRel (.bytes .storage) (.alias bytesR) v none :=
  fun related => Option.noConfusion related.2

/-- Both uniqueness controls have actual related pairs; no empty-relation or
contradictory hypothesis supplies their positive witness. -/
theorem reference_pairs_inhabited :
    (∃ (v : Source.Val P12Controls.E.layout (.bytes .memory))
       (r : (LTy.mem bytesR).TDenote P12Controls.C P12Controls.target.H),
       P12Controls.BindingRel (.bytes .memory) (.mem bytesR) v r) ∧
    (∃ (v : Source.Val P12Controls.E.layout (.bytes .storage))
       (r : (LTy.alias bytesR).TDenote P12Controls.C P12Controls.target.H),
       P12Controls.BindingRel (.bytes .storage) (.alias bytesR) v r) :=
  ⟨⟨.memRef rfl 0, some P12Controls.memoryRef, rfl, rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path,
     some MixedAssignmentControls.storageRef, rfl, rfl⟩⟩

#print axioms memory_pair_unique
#print axioms storage_pair_unique
#print axioms memory_absent_refused
#print axioms storage_absent_refused
#print axioms reference_pairs_inhabited

-- Compare with the unchanged imported fixture's existing trust footprint.
#print axioms P12Controls.BindingRel
#print axioms P12Controls.initial

end Solidity.H62.BindingFixtures

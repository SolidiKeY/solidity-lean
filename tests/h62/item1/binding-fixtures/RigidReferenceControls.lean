import Solidity.Lowering.V07.P12Controls
import Solidity.Lowering.V07.AddressConversionControls
import Solidity.Lowering.V07.AddressQualifierControls
import Solidity.Lowering.V07.EnumConversionControls
import Solidity.Lowering.V07.EnumSignedCastControls
import Solidity.Lowering.V07.FixedBytesAssignmentControls
import Solidity.Lowering.V07.UdvtAddressAssignmentControls
import Solidity.Lowering.V07.UdvtAssignmentControls
import Solidity.Lowering.V07.UdvtBoolAssignmentControls
import Solidity.Lowering.V07.UdvtFixedBytesAssignmentControls

/-! Guards the inherited BindingRel reference arms against identity broadening,
absent targets and empty-relation vacuity. One general fixed-reference lemma
family covers memory and storage arms of all ten unchanged V07 fixtures,
including their qualifier/integer/width parameters. This is isolated proof
backfill, not fixture extraction, relation unification or source/world transport.
No producer module or existing theorem is edited. -/
namespace Solidity.H62.BindingFixtures.RigidReferences
open Lowering.V07 Source.SemanticsExamples

/-- A branch relates exactly one source identity and one present target identity.
The witnesses are explicit; arbitrary equal-content references are not related. -/
def FixedReferenceBranch {α : Type u} {β : Type v}
    (R : α → Option β → Prop) : Prop :=
  ∃ (source : α) (target : β), ∀ x y, R x y ↔ x = source ∧ y = some target

/-- Exact identity branches are inhabited without contradictory premises. -/
theorem inhabited {α : Type u} {β : Type v} {R : α → Option β → Prop}
    (fixed : FixedReferenceBranch R) : ∃ x y, R x y :=
  fixed.elim fun source remaining => remaining.elim fun target shape =>
    ⟨source, some target, (shape source (some target)).mpr ⟨rfl, rfl⟩⟩

/-- Any two related pairs in this branch have identical source and target values. -/
theorem pair_unique {α : Type u} {β : Type v} {R : α → Option β → Prop}
    (fixed : FixedReferenceBranch R) (x x' : α) (y y' : Option β)
    (left : R x y) (right : R x' y') : x = x' ∧ y = y' :=
  fixed.elim fun _ remaining => remaining.elim fun _ shape =>
    ⟨((shape x y).mp left).1.trans ((shape x' y').mp right).1.symm,
     ((shape x y).mp left).2.trans ((shape x' y').mp right).2.symm⟩

/-- An absent target cannot satisfy a branch with a present identity witness. -/
theorem absent_refused {α : Type u} {β : Type v} {R : α → Option β → Prop}
    (fixed : FixedReferenceBranch R) (x : α) : ¬ R x none :=
  fixed.elim fun _ remaining => remaining.elim fun _ shape =>
    fun related => Option.noConfusion ((shape x none).mp related).2

/-- Both exact reference branches of P12Controls; primitive arms are untouched. -/
theorem P12Controls_reference_branches  :
    FixedReferenceBranch (P12Controls.BindingRel (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (P12Controls.BindingRel (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

/-- Both exact reference branches of AddressConversionControls; primitive arms are untouched. -/
theorem AddressConversionControls_reference_branches  :
    FixedReferenceBranch (AddressConversionControls.BindingRel (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (AddressConversionControls.BindingRel (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

/-- Both exact reference branches of AddressQualifierControls; primitive arms are untouched. -/
theorem AddressQualifierControls_reference_branches  :
    FixedReferenceBranch (AddressQualifierControls.BindingRel (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (AddressQualifierControls.BindingRel (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

/-- Both exact reference branches of EnumConversionControls; primitive arms are untouched. -/
theorem EnumConversionControls_reference_branches  :
    FixedReferenceBranch (EnumConversionControls.BindingRel (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (EnumConversionControls.BindingRel (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

/-- Both exact reference branches of EnumSignedCastControls; primitive arms are untouched. -/
theorem EnumSignedCastControls_reference_branches  :
    FixedReferenceBranch (EnumSignedCastControls.BindingRel (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (EnumSignedCastControls.BindingRel (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

/-- Both exact reference branches of FixedBytesAssignmentControls; primitive arms are untouched. -/
theorem FixedBytesAssignmentControls_reference_branches  :
    FixedReferenceBranch (FixedBytesAssignmentControls.BindingRel (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (FixedBytesAssignmentControls.BindingRel (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

/-- Both exact reference branches of UdvtAddressAssignmentControls; primitive arms are untouched. -/
theorem UdvtAddressAssignmentControls_reference_branches (p : Bool) :
    FixedReferenceBranch (UdvtAddressAssignmentControls.BindingRel p (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (UdvtAddressAssignmentControls.BindingRel p (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

/-- Both exact reference branches of UdvtAssignmentControls; primitive arms are untouched. -/
theorem UdvtAssignmentControls_reference_branches (t : Source.IntTy) :
    FixedReferenceBranch (UdvtAssignmentControls.BindingRel t (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (UdvtAssignmentControls.BindingRel t (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

/-- Both exact reference branches of UdvtBoolAssignmentControls; primitive arms are untouched. -/
theorem UdvtBoolAssignmentControls_reference_branches  :
    FixedReferenceBranch (UdvtBoolAssignmentControls.BindingRel (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (UdvtBoolAssignmentControls.BindingRel (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

/-- Both exact reference branches of UdvtFixedBytesAssignmentControls; primitive arms are untouched. -/
theorem UdvtFixedBytesAssignmentControls_reference_branches (n : Nat) (w : 1 ≤ n ∧ n ≤ 32) :
    FixedReferenceBranch (UdvtFixedBytesAssignmentControls.BindingRel n w (.bytes .memory) (.mem bytesR)) ∧
    FixedReferenceBranch (UdvtFixedBytesAssignmentControls.BindingRel n w (.bytes .storage) (.alias bytesR)) :=
  ⟨⟨.memRef rfl 0, P12Controls.memoryRef, fun _ _ => Iff.rfl⟩,
   ⟨.storRef rfl MixedAssignmentControls.path, MixedAssignmentControls.storageRef,
    fun _ _ => Iff.rfl⟩⟩

#print axioms inhabited
#print axioms pair_unique
#print axioms absent_refused
#print axioms P12Controls_reference_branches
#print axioms AddressConversionControls_reference_branches
#print axioms AddressQualifierControls_reference_branches
#print axioms EnumConversionControls_reference_branches
#print axioms EnumSignedCastControls_reference_branches
#print axioms FixedBytesAssignmentControls_reference_branches
#print axioms UdvtAddressAssignmentControls_reference_branches
#print axioms UdvtAssignmentControls_reference_branches
#print axioms UdvtBoolAssignmentControls_reference_branches
#print axioms UdvtFixedBytesAssignmentControls_reference_branches

end Solidity.H62.BindingFixtures.RigidReferences

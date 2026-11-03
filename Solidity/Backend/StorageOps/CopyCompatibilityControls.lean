import Solidity.Backend.StorageOps.CopyCompatibility
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Selected copied-header metadata, including new readability, retained huge
extents and separate source/destination range counterexamples. No source cap. -/
namespace Solidity.Backend.StorageOps.CopyCompatibilityControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private def headers : List (Query CopyDemandControls.graph CopyDemandControls.Outer) :=
  [.length .nil,.length (.cons (.index (ix 0)) .nil),.length (.cons (.index (ix 1)) .nil),
   .length (.cons (.index (ix 2)) .nil),.length (.cons (.index (ix 3)) .nil)]
private def headerView (v : Value CopyDemandControls.graph CopyDemandControls.Outer) :=
  headers.map (fun q => q.read v)
private theorem oldBounds : ∀ q ∈ headers, q.compatible CopyDemandControls.old := by
  intro q member
  simp only [headers,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨by decide,by decide⟩ | exact True.intro
private theorem sourceBounds : ∀ q ∈ ClearDemands.demands CopyDemandControls.src,
    q.compatible CopyDemandControls.src := by
  intro q member
  change q ∈ [.word (.cons (.index (ix 0)) (.cons (.index (ix 0)) .nil)),
    .length (.cons (.index (ix 0)) .nil),.length .nil] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals first | exact True.intro | exact ⟨by decide,by decide⟩

/-- ALL five selected copied header observations derive their compatibility
from old/source evidence, including cleared/retained and failed observations. -/
theorem nested_post_bounds : ∀ q ∈ headers, q.compatible CopyDemandControls.copied := by
  intro q member
  exact CopyCompatibility.copy_compatible CopyDemandControls.old CopyDemandControls.src CopyDemandControls.permit
    q (oldBounds q member) sourceBounds

theorem complete_header_observations :
    (headerView CopyDemandControls.old,headerView CopyDemandControls.src,headerView CopyDemandControls.copied) =
    ([some (lengthWord 2 (by decide)),some (lengthWord 2 (by decide)),some (lengthWord 2 (by decide)),
      some (lengthWord 2 (by decide)),none],
     [some (lengthWord 1 (by decide)),some (lengthWord 1 (by decide)),some (lengthWord 1 (by decide)),none,none],
     [some (lengthWord 1 (by decide)),some (lengthWord 1 (by decide)),some (lengthWord 0 (by decide)),
      some (lengthWord 2 (by decide)),none]) := by rfl

private def freshOld : Value CopyDemandControls.graph CopyDemandControls.Outer :=
  .array ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide) (fun i => nomatch i)
private def newHeader : Query CopyDemandControls.graph CopyDemandControls.Outer := .length (.cons (.index (ix 0)) .nil)

/-- OLD failed header readability constrains no old child extent. Post bounds
are derived using the published default and source, not assumed for the output. -/
theorem fresh_header_bounds : newHeader.read freshOld = none ∧
    newHeader.read (recursiveCopy freshOld CopyDemandControls.src) = some (lengthWord 1 (by decide)) ∧
    newHeader.compatible (recursiveCopy freshOld CopyDemandControls.src) := by
  refine ⟨rfl,rfl,?_⟩
  exact CopyCompatibility.copy_compatible freshOld CopyDemandControls.src CopyDemandControls.permit newHeader
    True.intro sourceBounds

private abbrev Elem : TypeGraph.Ty 0 := .array (.prim .bool)
private def empty : Value CopyDemandControls.graph Elem :=
  .array ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide) (fun i => nomatch i)
private def huge : Index := ⟨lmax+1,by decide⟩
private def hugeExtent : Extent := ⟨lmax+1,by decide⟩
private def longSource : Value CopyDemandControls.graph Elem := .array hugeExtent huge (Nat.le_refl _) (fun _ => .absent)
private def retained : Value CopyDemandControls.graph Elem := .array hugeExtent ⟨0,by decide⟩ (by decide) (fun _ => .absent)
private def header : Query CopyDemandControls.graph Elem := .length .nil
private def permit : CopyPermit CopyDemandControls.graph Elem := CopyPermit.checked (fun i => nomatch i) (by decide)

/-- Dropping SOURCE bounds permits a copied length beyond the owner's range.
The intrinsic operation still has that exact length; no source restriction added. -/
theorem source_bounds_essential : header.compatible empty ∧
    (recursiveCopy empty longSource).length.val = lmax+1 ∧
    ¬ header.compatible (recursiveCopy empty longSource) := by
  refine ⟨⟨by decide,by decide⟩,rfl,?_⟩
  intro bounds
  have impossible : lmax+1 ≤ lmax := bounds.1
  omega

/-- Zero SOURCE length is insufficient when an older destination shadow extent
exceeds the owner's range. Retained extent is not cleared to force the proof. -/
theorem destination_bounds_essential : header.compatible empty ∧
    (recursiveCopy retained empty).length.val = 0 ∧
    (recursiveCopy retained empty).extent.val = lmax+1 ∧
    ¬ header.compatible (recursiveCopy retained empty) := by
  refine ⟨⟨by decide,by decide⟩,rfl,?_,?_⟩
  · change max (lmax+1) 0 = lmax+1
    exact Nat.max_zero _
  · intro bounds
    have impossible : max (lmax+1) 0 ≤ lmax := bounds.2
    have positive : lmax+1 ≤ max (lmax+1) 0 := Nat.le_max_left _ _
    omega

/-- Compatibility is QUERY-local: a selected word does not impose an unstated
bound on every parent extent. Huge retained graphs remain admitted intrinsically. -/
theorem selected_word_only :
    let q : Query CopyDemandControls.graph Elem := .word (.cons (.index (ix 0)) .nil)
    q.compatible retained ∧ q.compatible (recursiveCopy retained empty) ∧
    q.read retained = some ClearDemands.zero ∧ q.read (recursiveCopy retained empty) = some ClearDemands.zero := by
  exact ⟨True.intro,True.intro,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.CopyCompatibilityControls.nested_post_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_post_bounds
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibilityControls.complete_header_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_header_observations
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibilityControls.fresh_header_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_header_bounds
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibilityControls.source_bounds_essential' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms source_bounds_essential
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibilityControls.destination_bounds_essential' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms destination_bounds_essential
/-- info: 'Solidity.Backend.StorageOps.CopyCompatibilityControls.selected_word_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_word_only

end Solidity.Backend.StorageOps.CopyCompatibilityControls

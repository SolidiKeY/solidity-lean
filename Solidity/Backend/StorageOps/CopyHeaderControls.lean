import Solidity.Backend.StorageOps.CopyHeaders
import Solidity.Backend.StorageOps.CopyWriteControls

/-! Actual root-header owner/transport application with complete ordered
nested readbacks and independent bad source header/payload controls. -/
namespace Solidity.Backend.StorageOps.CopyHeaderControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 8,.data 9,.data 10,.data 11]
private noncomputable def locations := CopyDemandControls.locations ++ [Solidity.Storage.Loc.root 1]
private theorem run : FiniteRun 128 4 2 CopyDemandControls.hash preimages locations := by
  refine ⟨CopyDemandControls.run.hash_bound,CopyDemandControls.run.region_bound,
    CopyDemandControls.run.root_bound,CopyDemandControls.run.regions,?_,?_⟩
  · intro l inside
    rcases List.mem_append.mp inside with old | fresh
    · exact CopyDemandControls.run.bounded l old
    · have same := List.mem_singleton.mp fresh
      subst l
      simp only [Solidity.Storage.Loc.Bounded]
      decide
  · intro l inside
    rcases List.mem_append.mp inside with old | fresh
    · exact CopyDemandControls.run.covered l old
    · have same := List.mem_singleton.mp fresh
      subst l
      intro p member
      change p ∈ [] at member
      cases member
private theorem before_dst : Represented CopyDemandControls.old [.length .nil]
    CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  have same := List.mem_singleton.mp member
  subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro word observed
  change some two = some word at observed
  cases observed
  rfl
private theorem before_src : Represented CopyDemandControls.src [.length .nil]
    (.root 1) CopyDemandControls.store := by
  intro q member
  have same := List.mem_singleton.mp member
  subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro word observed
  change some one = some word at observed
  cases observed
  rfl

/-- Actual generated nested copy derives PUBLIC root-header representation and
finite numeric Transport, not from an assumed output relation. -/
theorem actual_header_owner :
    let log := CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src
      CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine
    let after := log.foldl (fun w op => write w op.1 op.2) CopyDemandControls.store
    Represented CopyDemandControls.copied [.length .nil] CopyDemandControls.root after ∧
    Transport 128 CopyDemandControls.hash locations after
      (CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src
        CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine) :=
  CopyHeaders.represented_header CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root
    (.root 1) CopyDemandControls.store CopyDemandControls.machine run before_dst before_src
    (fun _ _ => rfl)
    (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨.length .nil,by
      change (Query.length .nil : Query CopyDemandControls.graph CopyDemandControls.Outer) ∈
        CopyDemandControls.demands ++ CopyDemandControls.queries
      exact List.mem_append.mpr (Or.inl (by
        exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))),rfl⟩)))
    (List.mem_append.mpr (Or.inr (List.mem_singleton_self _)))
    (fun q inside => List.mem_append.mpr (Or.inl (List.mem_map.mpr
      ⟨q,List.mem_append.mpr (Or.inl inside),rfl⟩)))

private noncomputable def result (m : WordStore) := CopyWrites.numericCopy (N := 128)
  CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash m
private def badHeader : WordStore := writeWord CopyDemandControls.machine 1 seven
private def badPayload : WordStore := writeWord CopyDemandControls.machine 64 seven

/-- ALL18 numeric observations for initial and actual correct/header-invalid/
payload-invalid copies, including both retained shadows and source sentinel. -/
theorem complete_header_controls :
    (CopyDemandControls.numericView CopyDemandControls.machine,
      CopyDemandControls.numericView (result CopyDemandControls.machine),
      CopyDemandControls.numericView (result badHeader),
      CopyDemandControls.numericView (result badPayload)) =
    ((two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (one,one,zero,two,zero,zero,one,zero,zero,one,one,one,one,seven,one,one,zero,seven),
     (seven,one,zero,two,zero,zero,one,zero,zero,one,one,one,one,seven,seven,one,zero,seven),
     (one,one,zero,two,seven,zero,one,zero,zero,one,one,one,one,seven,one,one,seven,seven)) := by rfl

/-- Independent graph root length/retained extent is unchanged by numeric
source corruption. No invalid source relation is silently supplied. -/
theorem graph_headers :
    ((CopyDemandControls.old.length.val,CopyDemandControls.old.extent.val),
     (CopyDemandControls.src.length.val,CopyDemandControls.src.extent.val),
     (CopyDemandControls.copied.length.val,CopyDemandControls.copied.extent.val)) =
      ((2,3),(1,2),(1,3)) := by rfl

theorem bad_header_rejected : ¬ Represented CopyDemandControls.src [.length .nil] (.root 1)
    (fun l => badHeader (l.word 128 CopyDemandControls.hash)) := by
  intro represented
  have same := (represented (.length .nil) (List.mem_singleton_self _)).2.2 one rfl
  change seven = one at same
  exact (by decide : seven ≠ one) same

/-- The SELECTED source header relation permits arbitrary unselected payload
words; the root-header theorem therefore deliberately does NOT claim payloads. -/
theorem header_only_payload_boundary :
    Represented CopyDemandControls.src [.length .nil] (.root 1)
      (fun l => badPayload (l.word 128 CopyDemandControls.hash)) ∧
    result badPayload 0 = one ∧ result badPayload 32 = seven ∧
    (Query.word (.cons (.index ⟨0,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil))).read
      CopyDemandControls.copied = some zero := by
  refine ⟨?_,rfl,rfl,rfl⟩
  intro q member
  have same := List.mem_singleton.mp member
  subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro word observed
  change some one = some word at observed
  cases observed
  rfl

/-- info: 'Solidity.Backend.StorageOps.CopyHeaderControls.actual_header_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_header_owner
/-- info: 'Solidity.Backend.StorageOps.CopyHeaderControls.complete_header_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_header_controls
/-- info: 'Solidity.Backend.StorageOps.CopyHeaderControls.graph_headers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graph_headers
/-- info: 'Solidity.Backend.StorageOps.CopyHeaderControls.bad_header_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_header_rejected
/-- info: 'Solidity.Backend.StorageOps.CopyHeaderControls.header_only_payload_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_only_payload_boundary

end Solidity.Backend.StorageOps.CopyHeaderControls

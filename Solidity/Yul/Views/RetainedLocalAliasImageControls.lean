import Solidity.Yul.Views.RetainedLocalAliasImage
import Solidity.Yul.Views.RetainedLocalAliasControls

/-! The actual overwritten/returned alias capture selects BOTH dormant child
layouts. Canonical two-child Source/storage and complementary raw padding are
checked, independently of allocator reachability or compiler correspondence. -/
namespace Solidity.Yul.Views.Controls
open Solidity.Backend.MemoryOps

theorem rai_visits (pipeline : Roadmap.Pipeline) :
    capturedVisitIndices rhLayout [] (raCaptured pipeline).2 (0:Roadmap.Word).val=[1,0] := ra_visits pipeline

theorem rai_elements_ready : (rhLayout.prepareElements? agFixed [1,0]).isSome := by decide
def raiElements := (rhLayout.prepareElements? agFixed [1,0]).get rai_elements_ready

def raiImage (pipeline : Roadmap.Pipeline) : CapturedArrayImage rhLayout agFixed [] (raCaptured pipeline).2 0 :=
  ⟨raiElements,by rw [rai_visits];exact Option.get_mem rai_elements_ready⟩

theorem rai_prepared (pipeline : Roadmap.Pipeline) :
    prepareCapturedArrayImage? rhLayout agFixed [] (raCaptured pipeline).2 0=some (raiImage pipeline) :=
  CapturedArrayImage.prepared _

def raiPaths (pipeline : Roadmap.Pipeline) := (raiImage pipeline).snapshot rhRaw0

theorem rai_indices (pipeline : Roadmap.Pipeline) : (raiImage pipeline).elements.map Sigma.fst=[1,0] := by
  rw [CapturedArrayImage.visited,rai_visits]

theorem rai_coordinates (pipeline : Roadmap.Pipeline) :
    (raiPaths pipeline).map (fun c => (c.path.steps,c.slot.val,c.field.offset,c.field.width))=
      [([],0,0,32),([.index 1,.field 0],102,0,2),([.index 1,.field 1],103,0,32),
       ([.index 1,.field 1,.index 0],2000,0,2),([.index 0,.field 0],100,0,2),
       ([.index 0,.field 1],101,0,32),([.index 0,.field 1,.index 0],1000,0,2),
       ([.index 0,.field 1,.index 1],1000,2,2)] := by
  rfl

/-- Real canonical fields read from the unchanged post-assignment source store. -/
theorem rai_view (pipeline : Roadmap.Pipeline) :
    finiteView (raiPaths pipeline) (raAfter.2.ex.world.accounts account).storage rhRaw0 := by
  intro c member
  have concrete : raiPaths pipeline=raiPaths .legacy := by
    rfl
  rw [concrete] at member
  change c ∈ [_ ,_ ,_ ,_ ,_ ,_ ,_ ,_] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The actual alias producer feeds the computed union into source traversal. -/
theorem rai_source (pipeline : Roadmap.Pipeline) :
    (raiImage pipeline).sourceInventory? (F:=packedStepFrame) raAfter=some (raiPaths pipeline) := by
  have initialView : finiteView (raiImage pipeline).registrations
      (raState.2.ex.world.accounts account).storage rhRaw0 := by
    intro c member
    exact rai_view pipeline c
      (RetainedLocalAliasImage.registration_mem_snapshot (raiImage pipeline) rhRaw0 c member)
  have computed := RetainedLocalAliasImage.source_inventory (raGlobals pipeline) packedStepFrame 0 raState
    .here (.there .here) [] rhLayout agFixed [] 0 (raiImage pipeline) rhRaw0 initialView
  rw [RetainedLocalAlias.value_run] at computed
  exact computed

theorem rai_separated (pipeline : Roadmap.Pipeline) : packedSeparationCheck (raiPaths pipeline)=true := by
  rw [show raiPaths pipeline=raiPaths .legacy from rfl]
  decide

/-- Pure unchanged snapshot writeback preserves the WHOLE administrative store. -/
theorem rai_unchanged (pipeline : Roadmap.Pipeline) :
    capturedSnapshotWriteback (raiImage pipeline) rhRaw0 (raAfter.2.ex.world.accounts account).storage=
      some ((raAfter.2.ex.world.accounts account).storage,packedMask (raiPaths pipeline) rhRaw0) :=
  capturedSnapshot_unchanged (raiImage pipeline) rhRaw0 _ (rai_separated pipeline) (rai_view pipeline)

theorem rai_reencode (pipeline : Roadmap.Pipeline) :
    finiteEncode (raiPaths pipeline) (raAfter.2.ex.world.accounts account).storage
      (packedMask (raiPaths pipeline) rhRaw0)=some rhRaw0 :=
  finiteEncode_fromComplement _ _ _ ((packedSeparationCheck_iff _).mp (rai_separated pipeline)) (rai_view pipeline)

/-- The newly observed child1 word moves into ownership; dirty high bits stay
complementary. This is not a logical Source write or a frame-journal action. -/
theorem rai_complement (pipeline : Roadmap.Pipeline) :
    packedMask rhOld rhRaw0 2000=⟨99+2^240,by decide⟩ ∧
    packedMask (raiPaths pipeline) rhRaw0 2000=⟨2^240,by decide⟩ ∧
    packedMask (raiPaths pipeline) rhRaw0 1000=⟨77*2^32+2^240,by decide⟩ := by
  rw [show raiPaths pipeline=raiPaths .legacy from rfl]
  decide

/-- Reusing the old complement violates the new ownership-mask invariant. -/
theorem rai_stale_mask (pipeline : Roadmap.Pipeline) :
    packedMask rhOld rhRaw0 2000≠packedMask (raiPaths pipeline) rhRaw0 2000 := by
  rw [(rai_complement pipeline).1,(rai_complement pipeline).2.1]
  decide

/-- New ownership does not authorize clearing the retained high padding bits. -/
theorem rai_no_cleaning (pipeline : Roadmap.Pipeline) : packedMask (raiPaths pipeline) rhRaw0 2000≠0 := by
  rw [(rai_complement pipeline).2.1]
  decide
end Solidity.Yul.Views.Controls

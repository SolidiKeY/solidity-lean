import Solidity.Lowering.StorageOps.SourceArrayWriteNumericControls
open Solidity Solidity.TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open Solidity.Backend.StorageOps Solidity.Lowering.StorageOps
open SourceArrayIndexControls SourceArrayWriteControls SourceArrayWriteNumericControls
/-! Nonempty observer-owner frames through an actual Source write and PUBLIC
represented/numeric target update. The retained query is a raw observation,
not fresh indexing. Existing source/target context fixtures are reused unchanged;
no global hash, address compiler, eager recursive or world relation is inferred. -/
namespace Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls

def observers : List (Query graph (.array (.prim .uint))) :=
 [.word (TargetArrayRead.path (ix 0)),.word (TargetArrayRead.path (ix 2))]

theorem owner : Represented old observers base store := by
  intro q member
  simp only [observers,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · refine ⟨⟨by change 0<lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed
    change some w53=some word at observed
    cases observed
    rfl
  · refine ⟨⟨by change 2<lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed
    change some w61=some word at observed
    cases observed
    rfl

theorem separated : ∀ q∈observers, q.apart (TargetArrayRead.path (G:=graph) (p:=.uint) (ix 1)) := by
  intro q member
  simp only [observers,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact Apart.fork (StepApart.index (ix 1) (ix 0) (by decide)) .nil .nil
  · exact Apart.fork (StepApart.index (ix 1) (ix 2) (by decide)) .nil .nil

theorem nonalias : ∀ q∈observers, q.location base≠pathLoc (TargetArrayRead.path (G:=graph) (p:=.uint) (ix 1)) base := by
 decide

def certificate := SourceArrayWrite.complete_numeric run old output (ix 1) w83 performed
 observers base True.intro store numeric target target.stack header owner
 (by exact ⟨by change 1<lmax; decide,True.intro⟩) separated nonalias
 transported (by decide) (by decide) fitting initialized
 env [] writable path .nil state rfl rfl (.int 2 (by decide)) 2 (by decide) rfl rfl
 SourceArrayWriteControls.payload 0 rfl rfl rfl rfl

theorem observations :
 ((Query.word (TargetArrayRead.path (ix 0))).read old,
  (Query.word (TargetArrayRead.path (ix 2))).read old,
  (Query.word (TargetArrayRead.path (ix 1))).read old,
  (Query.word (TargetArrayRead.path (ix 0))).read output,
  (Query.word (TargetArrayRead.path (ix 2))).read output,
  (Query.word (TargetArrayRead.path (ix 1))).read output) =
 (some w53,some w61,some w59,some w53,some w61,some w83) := by rfl

theorem written_read_changes :
 (Query.word (TargetArrayRead.path (ix 1))).read old ≠
 (Query.word (TargetArrayRead.path (ix 1))).read output := by decide
theorem retained_live_none :
 (TargetArrayRead.path (ix 2)).readLive Value.dflt output=none := by rfl
end Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls







/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.owner

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.separated

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.nonalias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.nonalias

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.observations

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.written_read_changes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.written_read_changes

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.retained_live_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceArrayWriteFrameControls.retained_live_none

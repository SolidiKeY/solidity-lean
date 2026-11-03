import Solidity.Backend.StorageOps.CopyReadCapture
import Solidity.Backend.StorageOps.CopyWriteControls

/-! Finite numeric capture, independent source provenance and destination
preservation controls. Existing nested and overlap fixtures remain unchanged. -/
namespace Solidity.Backend.StorageOps.CopyReadCaptureControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def seven : Semantics.Word := ⟨7,by decide⟩
private noncomputable def sourceAddresses : List Nat := CopyReadCapture.addresses (N := 128)
  CopyDemandControls.src (.root 1) CopyDemandControls.hash
private noncomputable def cache := CopyReadCapture.capture sourceAddresses CopyDemandControls.machine
private noncomputable def finiteResult := CopyReadCapture.finiteCopy (N := 128)
  CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
  CopyDemandControls.hash CopyDemandControls.machine
private def cacheView (m : WordStore) := (m 64,m 16,m 1,m 8,m 34,m 127)
private def sourceQueries : List (Query CopyDemandControls.graph CopyDemandControls.Outer) :=
  ClearDemands.demands CopyDemandControls.src
private noncomputable def sourceLocations : List Solidity.Storage.Loc := sourceQueries.map (fun q => q.location (.root 1))
private theorem source_before : Represented CopyDemandControls.src sourceQueries (.root 1) CopyDemandControls.store := by
  intro q member
  change q ∈ [.word (.cons (.index ⟨0,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil)),
    .length (.cons (.index ⟨0,by decide⟩) .nil),.length .nil] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some zero = some word at observed; cases observed; rfl)
    | (intro word observed; change some one = some word at observed; cases observed; rfl)

/-- Exactly THREE live source words feed SEVEN destination writes; uncaptured
cache cells are zero, including old destination shadows and sentinel. -/
theorem finite_capture_observations :
    (sourceAddresses,CopyReadCapture.entries sourceAddresses CopyDemandControls.machine,
      cacheView CopyDemandControls.machine,cacheView cache) =
    ([64,16,1],[(64,zero),(16,one),(1,one)],
      (zero,one,one,lengthWord 2 (by decide),one,seven),(zero,one,one,zero,zero,zero)) := by rfl

/-- The finite read construction realizes the original snapshot operation for
all words, not only an observation projection. -/
theorem entire_nested_result : finiteResult = CopyDemandControls.final :=
  (CopyReadCapture.finiteCopy_eq CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
    CopyDemandControls.hash CopyDemandControls.machine).trans CopyWriteControls.generated_nested_machine

/-- Full selected owner representation from C32 now applies to ACTUAL finite
source capture, retaining all nested inside/outside/failing observations. -/
theorem finite_owner_fixture :
    let writes := CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
      CopyDemandControls.hash cache
    Represented CopyDemandControls.copied (CopyDemands.demands CopyDemandControls.old CopyDemandControls.src ++
      CopyDemandControls.queries) CopyDemandControls.root
      (writes.foldl (fun w op => write w op.1 op.2) CopyDemandControls.store) := by
  dsimp only [cache,sourceAddresses]
  rw [CopyReadCapture.captured_updates]
  exact CopyWriteControls.full_owner_fixture

/-- Actual captured numeric input words match independent SOURCE graph reads;
this is an applied generic input provenance theorem, not output preservation. -/
theorem represented_input_log :
    CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
      CopyDemandControls.hash CopyDemandControls.machine =
    (CopyWrites.queryWrites CopyDemandControls.old CopyDemandControls.src
      (fun q => (q.read CopyDemandControls.src).getD zero)).map
      (fun op => (op.1.location CopyDemandControls.root,op.2)) :=
  CopyReadCapture.represented_log CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
    CopyDemandControls.store CopyDemandControls.machine CopyDemandControls.hash sourceLocations source_before
    (fun _ _ => rfl) (fun q member => List.mem_map.mpr ⟨q,member,rfl⟩)

/-- Starting the destination FROM the read cache wrongly wipes old shadows and
outside storage. The correct finiteCopy writes against ORIGINAL destination state. -/
theorem wrong_destination_cache :
    (finiteResult 34,finiteResult 127,
      CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
        CopyDemandControls.hash cache 34,
      CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
        CopyDemandControls.hash cache 127) = (one,seven,zero,zero) := by rfl

/-- Duplicate physical addresses are captured consistently without a hash
injectivity premise; nonselected raw cache words remain zero. -/
theorem duplicate_addresses :
    let initial : WordStore := fun a => if a = 1 then one else if a = 16 then seven else zero
    (CopyReadCapture.entries [1,1,16,1] initial,
      CopyReadCapture.capture [1,1,16,1] initial 1,
      CopyReadCapture.capture [1,1,16,1] initial 16,
      CopyReadCapture.capture [1,1,16,1] initial 32) =
    ([(1,one),(1,one),(16,seven),(1,one)],one,seven,zero) := by rfl

private noncomputable def overlapAddresses := CopyReadCapture.addresses (N := 128)
  CopyWriteControls.sourceNode CopyWriteControls.overlapSource CopyWriteControls.overlapHash
private noncomputable def overlapCache := CopyReadCapture.capture overlapAddresses CopyWriteControls.overlapMachine
private noncomputable def finiteOverlap := CopyReadCapture.finiteCopy (N := 128)
  CopyWriteControls.oldNode CopyWriteControls.sourceNode (.root 0) CopyWriteControls.overlapSource
  CopyWriteControls.overlapHash CopyWriteControls.overlapMachine

/-- The GOOD-region ancestor/descendant case now uses FOUR materialized source
reads. Cached header9 stays one after destination writes make numeric header9 zero. -/
theorem finite_overlap_observations :
    (overlapAddresses,CopyReadCapture.entries overlapAddresses CopyWriteControls.overlapMachine,
      CopyWriteControls.overlapView finiteOverlap,
      overlapCache 9,finiteOverlap 9,finiteOverlap 1,CopyWriteControls.wrongIncremental 1) =
    ([8,32,33,9],[(8,zero),(32,one),(33,zero),(9,one)],
      (zero,one,one,zero,zero,zero,seven),one,zero,one,zero) := by rfl

/-- The independent captured source relation from the recursive alias fixture
is reused intact; its complete reader footprint consists of successful reads. -/
theorem overlap_source_provenance :
    Represented CopyWriteControls.sourceNode
      (ClearDemands.demands CopyWriteControls.sourceNode) CopyWriteControls.overlapSource CopyWriteControls.overlapStore := by
  intro q member
  apply CopyWriteControls.overlap_source_owner q
  change q ∈ [.word (.cons (.field .here) .nil),
    .word (.cons (.field (.there .here)) (.cons (.index ⟨0,by decide⟩) (.cons (.field .here) .nil))),
    .length (.cons (.field (.there .here)) (.cons (.index ⟨0,by decide⟩) (.cons (.field (.there .here)) .nil))),
    .length (.cons (.field (.there .here)) .nil)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact List.mem_cons_of_mem _ List.mem_cons_self

private def changedOutside : WordStore := writeWord CopyDemandControls.machine 127 zero

/-- Mutating storage outside the finite SOURCE read set leaves the entire
actual generated write sequence unchanged, while destination context may differ. -/
theorem outside_source_log_stability :
    CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
      CopyDemandControls.hash changedOutside =
    CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
      CopyDemandControls.hash CopyDemandControls.machine := by
  apply CopyReadCapture.updates_eq_of_reads
  intro address member
  change address ∈ [64,16,1] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- info: 'Solidity.Backend.StorageOps.CopyReadCaptureControls.finite_capture_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finite_capture_observations
/-- info: 'Solidity.Backend.StorageOps.CopyReadCaptureControls.entire_nested_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms entire_nested_result
/-- info: 'Solidity.Backend.StorageOps.CopyReadCaptureControls.finite_owner_fixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finite_owner_fixture
/-- info: 'Solidity.Backend.StorageOps.CopyReadCaptureControls.represented_input_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_input_log
/-- info: 'Solidity.Backend.StorageOps.CopyReadCaptureControls.wrong_destination_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_destination_cache
/-- info: 'Solidity.Backend.StorageOps.CopyReadCaptureControls.duplicate_addresses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms duplicate_addresses
/-- info: 'Solidity.Backend.StorageOps.CopyReadCaptureControls.finite_overlap_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms finite_overlap_observations
/-- info: 'Solidity.Backend.StorageOps.CopyReadCaptureControls.overlap_source_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlap_source_provenance
/-- info: 'Solidity.Backend.StorageOps.CopyReadCaptureControls.outside_source_log_stability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outside_source_log_stability

end Solidity.Backend.StorageOps.CopyReadCaptureControls

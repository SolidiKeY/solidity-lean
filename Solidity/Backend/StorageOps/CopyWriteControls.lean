import Solidity.Backend.StorageOps.CopyWrites
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Actual generated nested-copy writes, full represented finite fixtures,
fresh initialization and a genuine captured-overlap/order counterexample.
General inside provenance is not inferred from these finite applications. -/
namespace Solidity.Backend.StorageOps.CopyWriteControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- The new runtime-source read generator produces the entire previously
checked seven-write nested fixture, rather than receiving its payload list. -/
theorem generated_nested_writes :
    CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine = CopyDemandControls.writes := rfl

theorem generated_nested_machine :
    CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine = CopyDemandControls.final := by
  rw [CopyWrites.numericCopy,generated_nested_writes]
  rfl

/-- Complete original eighteen-word observations, now produced by the actual
recursive captured-source numeric algorithm, not a supplied write fixture. -/
theorem nested_observations :
    CopyDemandControls.numericView (CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine) =
    (PrimTy.toWord (p := .bool) true,PrimTy.toWord (p := .bool) true,ClearDemands.zero,
      lengthWord 2 (by decide),ClearDemands.zero,ClearDemands.zero,PrimTy.toWord (p := .bool) true,
      ClearDemands.zero,ClearDemands.zero,PrimTy.toWord (p := .bool) true,
      PrimTy.toWord (p := .bool) true,PrimTy.toWord (p := .bool) true,PrimTy.toWord (p := .bool) true,
      ⟨7,by decide⟩,PrimTy.toWord (p := .bool) true,PrimTy.toWord (p := .bool) true,
      ClearDemands.zero,⟨7,by decide⟩) := by rfl

/-- The new generator applies the generic OUTSIDE certificate with every
location justified by its own proved query sequence. -/
theorem outside_owner_numeric :
    let updates := CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine
    let after := updates.foldl (fun w op => write w op.1 op.2) CopyDemandControls.store
    Represented CopyDemandControls.copied CopyDemandControls.queries CopyDemandControls.root after ∧
    Transport 128 CopyDemandControls.hash CopyDemandControls.locations after
      (CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine) ∧
    ∀ q ∈ CopyDemandControls.queries, ∀ word, q.read CopyDemandControls.copied = some word →
      CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine
        ((q.location CopyDemandControls.root).word 128 CopyDemandControls.hash) = word :=
  CopyWrites.outside_numeric CopyDemandControls.old CopyDemandControls.src CopyDemandControls.permit CopyDemandControls.queries CopyDemandControls.root (.root 1) CopyDemandControls.store CopyDemandControls.machine
    CopyDemandControls.run CopyDemandControls.before (fun _ _ => rfl)
    (fun d member => List.mem_map.mpr ⟨d,List.mem_append.mpr (Or.inl member),rfl⟩)
    (fun q member => List.mem_map.mpr ⟨q,List.mem_append.mpr (Or.inr member),rfl⟩) CopyDemandControls.separated

private def allQueries : List (Query CopyDemandControls.graph CopyDemandControls.Outer) := CopyDemandControls.demands ++ CopyDemandControls.queries
private theorem full_readback : ∀ q ∈ allQueries, ∀ word,
    q.read CopyDemandControls.copied = some word →
    CopyDemandControls.final ((q.location CopyDemandControls.root).word 128 CopyDemandControls.hash) = word := by
  intro q member
  change q ∈ [.word (.cons (.index ⟨0,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil)),
    .word (.cons (.index ⟨0,by decide⟩) (.cons (.index ⟨1,by decide⟩) .nil)),
    .length (.cons (.index ⟨0,by decide⟩) .nil),
    .word (.cons (.index ⟨1,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil)),
    .word (.cons (.index ⟨1,by decide⟩) (.cons (.index ⟨1,by decide⟩) .nil)),
    .length (.cons (.index ⟨1,by decide⟩) .nil),.length .nil,
    .word (.cons (.index ⟨0,by decide⟩) (.cons (.index ⟨2,by decide⟩) .nil)),
    .word (.cons (.index ⟨1,by decide⟩) (.cons (.index ⟨2,by decide⟩) .nil)),
    .word (.cons (.index ⟨2,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil)),
    .length (.cons (.index ⟨2,by decide⟩) .nil),
    .word (.cons (.index ⟨3,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil))] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals intro word observed
  all_goals first
    | (change some ClearDemands.zero = some word at observed; cases observed; rfl)
    | (change some (PrimTy.toWord (p := .bool) true) = some word at observed; cases observed; rfl)
    | (change some (lengthWord 2 (by decide)) = some word at observed; cases observed; rfl)
    | (change (none : Option Semantics.Word) = some word at observed; cases observed)

/-- FULL selected post owner representation for this inhabited nested fixture,
including inside values/headers and outside/failing observations. This finite
application does not discharge general recursive inside provenance. -/
theorem full_owner_fixture :
    let updates := CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine
    Represented CopyDemandControls.copied allQueries CopyDemandControls.root
      (updates.foldl (fun w op => write w op.1 op.2) CopyDemandControls.store) := by
  dsimp only
  have transported := transport_sequence CopyDemandControls.run (w := CopyDemandControls.store) (m := CopyDemandControls.machine) (fun _ _ => rfl)
    (CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine) (by
      intro op member
      obtain ⟨q,inside,same⟩ := CopyWrites.generated CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine op member
      rw [same]
      exact List.mem_map.mpr ⟨q,List.mem_append.mpr (Or.inl inside),rfl⟩)
  intro q member
  have properties : q.supported ∧ q.compatible CopyDemandControls.copied := by
    have cases : q ∈ allQueries := member
    change q ∈ [.word (.cons (.index ⟨0,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil)),
    .word (.cons (.index ⟨0,by decide⟩) (.cons (.index ⟨1,by decide⟩) .nil)),
    .length (.cons (.index ⟨0,by decide⟩) .nil),
    .word (.cons (.index ⟨1,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil)),
    .word (.cons (.index ⟨1,by decide⟩) (.cons (.index ⟨1,by decide⟩) .nil)),
    .length (.cons (.index ⟨1,by decide⟩) .nil),.length .nil,
    .word (.cons (.index ⟨0,by decide⟩) (.cons (.index ⟨2,by decide⟩) .nil)),
    .word (.cons (.index ⟨1,by decide⟩) (.cons (.index ⟨2,by decide⟩) .nil)),
    .word (.cons (.index ⟨2,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil)),
    .length (.cons (.index ⟨2,by decide⟩) .nil),
    .word (.cons (.index ⟨3,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil))] at cases
    simp only [List.mem_cons,List.not_mem_nil,or_false] at cases
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals refine ⟨?_,?_⟩
    all_goals first
      | (simp only [Query.supported,PathSupported,StepSupported]; decide)
      | exact True.intro
      | exact ⟨by decide,by decide⟩
  refine ⟨properties.1,properties.2,?_⟩
  intro word observed
  have inLocations : q.location CopyDemandControls.root ∈ CopyDemandControls.locations := List.mem_map.mpr ⟨q,member,rfl⟩
  exact (transported _ inLocations).symm.trans
    ((congrArg (fun m => m ((q.location CopyDemandControls.root).word 128 CopyDemandControls.hash))
      generated_nested_machine).trans (full_readback q member word observed))

private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def seven : Semantics.Word := ⟨7,by decide⟩
private def fixedTwo : FixedSize := ⟨2,by decide⟩
private abbrev FreshInner : TypeGraph.Ty 0 := .fixed (.prim .bool) fixedTwo
private abbrev FreshOuter : TypeGraph.Ty 0 := .array FreshInner
private def freshOld : Value CopyDemandControls.graph FreshOuter :=
  .array ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide) (fun i => nomatch i)
private def freshAbsent : Value CopyDemandControls.graph FreshOuter :=
  .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .absent)
private def freshPresent : Value CopyDemandControls.graph FreshOuter :=
  .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide)
    (fun _ => .present (.fixed (fun _ => .present (.prim true))))
private def freshMachine (present : Bool) : WordStore := fun n =>
  if n = 0 then zero else if n = 8 ∨ n = 9 then seven else
  if n = 16 ∨ n = 17 then (if present then one else zero) else CopyDemandControls.machine n
private def freshView (m : WordStore) := (m 0,m 8,m 9,m 10,m 16,m 17,m 127)
private noncomputable def freshResult (present : Bool) : WordStore :=
  CopyWrites.numericCopy (N := 128) freshOld (if present then freshPresent else freshAbsent)
    (.root 0) (.root 1) CopyDemandControls.hash (freshMachine present)

/-- Both OLD failed fixed leaves become readable. Absent source initializes
zero; present source overwrites initialization with actual captured source words.
All source/outside words are included in the ordered numeric observations. -/
theorem fresh_observations :
    (freshView (freshMachine false),freshView (freshResult false),
     freshView (freshMachine true),freshView (freshResult true),
     (CopyWrites.updates (N := 128) freshOld freshAbsent (.root 0) (.root 1)
       CopyDemandControls.hash (freshMachine false)).length,
     (CopyWrites.updates (N := 128) freshOld freshPresent (.root 0) (.root 1)
       CopyDemandControls.hash (freshMachine true)).length) =
    ((zero,seven,seven,lengthWord 2 (by decide),zero,zero,seven),
     (one,zero,zero,lengthWord 2 (by decide),zero,zero,seven),
     (zero,seven,seven,lengthWord 2 (by decide),one,one,seven),
     (one,one,one,lengthWord 2 (by decide),one,one,seven),3,7) := by rfl

/-- Moving default initialization after present-source copying destroys both
changed true readbacks. The real generator uses the opposite order. -/
theorem wrong_initialization_order :
    (freshResult true 8,freshResult true 9,
     (writeWord (writeWord (freshResult true) 8 zero) 9 zero) 8,
     (writeWord (writeWord (freshResult true) 8 zero) 9 zero) 9) =
    (one,one,zero,zero) := by rfl

def recursiveGraph : Schema 1 where
  origin := "v10-copy-writes-overlap"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; have hi := i.isLt; have hj := j.isLt; omega
  name := fun _ => "Node"
  fields := fun _ => [("flag",.prim .bool),("children",.array (.node 0))]
  rank := fun _ => 1
  nonempty := by intro i; rfl
  distinct := by intro i; decide
  guarded := by
    intro i f member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> decide
abbrev Node : TypeGraph.Ty 1 := .node 0
private def children (value : Value recursiveGraph Node) : Value recursiveGraph (.array Node) :=
  .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present value)
private def emptyChildren : Value recursiveGraph (.array Node) :=
  .array ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide) (fun i => nomatch i)
private def node (flag : Bool) (kids : Value recursiveGraph (.array Node)) : Value recursiveGraph Node :=
  .node (Fields.set (Fields.set (fun {_} _ => Value.dflt _) .here (Value.prim (p := .bool) flag)) (.there .here) kids)
private def leafNode : Value recursiveGraph Node := node true emptyChildren
def sourceNode : Value recursiveGraph Node := node false (children leafNode)
def oldNode : Value recursiveGraph Node := node true (children sourceNode)
private def flagPath : TypeGraph.Path recursiveGraph Node (.prim .bool) := .cons (.field .here) .nil
private def kidsPath : TypeGraph.Path recursiveGraph Node (.array Node) := .cons (.field (.there .here)) .nil
private def childPath : TypeGraph.Path recursiveGraph Node Node := kidsPath.append (.cons (.index ⟨0,by decide⟩) .nil)
private def grandPath : TypeGraph.Path recursiveGraph Node Node := childPath.append childPath
private def nodeView (v : Value recursiveGraph Node) :=
  (v.observe flagPath,v.observe kidsPath,
    v.observe (childPath.append flagPath),v.observe (childPath.append kidsPath),
    v.observe (grandPath.append flagPath),v.observe (grandPath.append kidsPath),
    ((grandPath.append flagPath).readLive Value.dflt v).map Value.head)
def overlapHash (p : Solidity.Storage.Pre) : Nat :=
  if p = .data 1 then 8 else if p = .data 9 then 32 else 0
def overlapSource : Solidity.Storage.Loc := .data (.root 1) 0
def overlapMachine : WordStore := fun n =>
  if n = 0 ∨ n = 1 ∨ n = 9 ∨ n = 32 then one else if n = 8 ∨ n = 33 then zero else seven
private noncomputable def overlapWrites :=
  CopyWrites.updates (N := 128) oldNode sourceNode (.root 0) overlapSource overlapHash overlapMachine
noncomputable def overlapResult :=
  CopyWrites.numericCopy (N := 128) oldNode sourceNode (.root 0) overlapSource overlapHash overlapMachine
def wrongIncremental : WordStore :=
  let m1 := writeWord overlapMachine 0 (overlapMachine 8)
  let m2 := writeWord m1 8 (m1 32)
  let m3 := writeWord m2 32 zero
  let m4 := writeWord m3 33 zero
  let m5 := writeWord m4 9 (m4 33)
  writeWord m5 1 (m5 9)
def overlapView (m : WordStore) := (m 0,m 1,m 8,m 9,m 32,m 33,m 127)

/-- Real source capture from a descendant before writing the ancestor. Both
runtime headers are one, while the last descendant header is zero. -/
theorem overlap_graph_observations :
    (nodeView oldNode,nodeView sourceNode,nodeView (recursiveCopy oldNode sourceNode)) =
    ((some true,some (⟨1,by decide⟩,⟨1,by decide⟩),some false,some (⟨1,by decide⟩,⟨1,by decide⟩),
      some true,some (⟨0,by decide⟩,⟨0,by decide⟩),some true),
     (some false,some (⟨1,by decide⟩,⟨1,by decide⟩),some true,some (⟨0,by decide⟩,⟨0,by decide⟩),none,none,none),
     (some false,some (⟨1,by decide⟩,⟨1,by decide⟩),some true,some (⟨0,by decide⟩,⟨1,by decide⟩),
      some false,some (⟨0,by decide⟩,⟨0,by decide⟩),none)) := by rfl

theorem overlap_capture_and_addresses :
    oldNode.find childPath = some sourceNode ∧
    recursiveCopyAt oldNode .nil childPath = some (recursiveCopy oldNode sourceNode) ∧
    pathLoc childPath (.root 0) = overlapSource ∧
    overlapWrites.map (fun op => (op.1.word 128 overlapHash,op.2)) =
      [(0,zero),(8,one),(32,zero),(33,zero),(9,zero),(1,one)] := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The captured source header at address9 is overwritten during the copy.
Re-reading it at the final iteration wrongly writes zero to the root header;
the actual generated snapshot algorithm correctly preserves initial one. -/
theorem wrong_incremental_source :
    (overlapView overlapMachine,overlapView overlapResult,overlapView wrongIncremental) =
    ((one,one,zero,one,one,zero,seven),
     (zero,one,one,zero,zero,zero,seven),
     (zero,zero,one,zero,zero,zero,seven)) := by rfl

noncomputable def overlapLocations : List Solidity.Storage.Loc :=
  (CopyDemands.demands oldNode sourceNode).map (fun q => q.location (.root 0))

/-- The overlap negative uses a GOOD existing finite per-run region certificate;
this is ancestor/descendant aliasing, not a bad/global hash-injectivity example. -/
theorem overlap_run : FiniteRun 128 4 2 overlapHash [.data 1,.data 9] overlapLocations := by
  constructor
  · intro p; simp only [overlapHash]; split <;> (first | decide | (split <;> decide))
  · decide
  · decide
  · decide
  · intro l member
    change l ∈ [.root 0,.data (.root 1) 0,.data (.data (.root 1) 1) 0,
      .data (.data (.root 1) 1) 1,.data (.root 1) 1,.root 1] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    change l ∈ [.root 0,.data (.root 1) 0,.data (.data (.root 1) 1) 0,
      .data (.data (.root 1) 1) 1,.data (.root 1) 1,.root 1] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def overlapSourceQueries : List (Query recursiveGraph Node) := [.word flagPath,.length kidsPath,
  .word (childPath.append flagPath),.length (childPath.append kidsPath)]
def overlapStore : Store := fun l => overlapMachine (l.word 128 overlapHash)

/-- Independent captured SOURCE primitive/header observations really match
initial numeric storage in the overlap fixture, including the overwritten header. -/
theorem overlap_source_owner : Represented sourceNode overlapSourceQueries overlapSource overlapStore := by
  intro q member
  simp only [overlapSourceQueries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [Query.supported,flagPath,kidsPath,childPath,TypeGraph.Path.append,
        PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some zero = some word at observed; cases observed; rfl)
    | (intro word observed; change some one = some word at observed; cases observed; rfl)

private def badSourceMachine : WordStore := writeWord CopyDemandControls.machine 64 seven
private noncomputable def badSourceResult : WordStore := CopyWrites.numericCopy (N := 128)
  CopyDemandControls.old CopyDemandControls.src CopyDemandControls.root (.root 1)
  CopyDemandControls.hash badSourceMachine

/-- A deliberately INVALID source representation is copied as actual raw
numeric input. Finite region bounds alone do not establish inside provenance;
independent source-word agreement remains necessary. -/
theorem source_representation_boundary :
    ((Query.word (.cons (.index ⟨0,by decide⟩) (.cons (.index ⟨0,by decide⟩) .nil))).read
      CopyDemandControls.src,badSourceMachine 64,badSourceResult 32,badSourceResult 34,badSourceResult 0) =
    (some zero,seven,seven,one,one) := by rfl

/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.generated_nested_writes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generated_nested_writes
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.generated_nested_machine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generated_nested_machine
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.nested_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_observations
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.outside_owner_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outside_owner_numeric
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.full_owner_fixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_owner_fixture
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.fresh_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_observations
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.wrong_initialization_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_initialization_order
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlap_graph_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overlap_graph_observations
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlap_capture_and_addresses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlap_capture_and_addresses
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.wrong_incremental_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_incremental_source
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlap_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overlap_run
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlap_source_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlap_source_owner

/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.source_representation_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_representation_boundary

/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.recursiveGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveGraph
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.Node' depends on axioms: [propext] -/
#guard_msgs in #print axioms Node
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.oldNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms oldNode
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.sourceNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sourceNode
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlapSource' does not depend on any axioms -/
#guard_msgs in #print axioms overlapSource
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlapHash' does not depend on any axioms -/
#guard_msgs in #print axioms overlapHash
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlapMachine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlapMachine
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlapResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overlapResult
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.wrongIncremental' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrongIncremental
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlapView' does not depend on any axioms -/
#guard_msgs in #print axioms overlapView
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlapLocations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlapLocations
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlapSourceQueries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overlapSourceQueries
/-- info: 'Solidity.Backend.StorageOps.CopyWriteControls.overlapStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overlapStore

end Solidity.Backend.StorageOps.CopyWriteControls

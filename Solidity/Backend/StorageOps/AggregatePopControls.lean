import Solidity.Backend.StorageOps.AggregatePop
import Solidity.Backend.StorageOps.PopPush
import Solidity.Backend.StorageOps.CopyDemandControls
import Solidity.Backend.StorageOps.CopyWriteControls

/-! Actual aggregate numeric pop, retained/live observations and discriminating
wrong-slot/whole-array programs. Graph values precede representation proofs. -/
namespace Solidity.Backend.StorageOps.AggregatePopControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open AggregatePop
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private abbrev G := CopyDemandControls.graph
private abbrev Inner := CopyDemandControls.Inner
private abbrev Outer := CopyDemandControls.Outer
private def leaf (i j : Fin 4) : Query G Outer := .word (.cons (.index (ix i)) (.cons (.index (ix j)) .nil))
private def header (i : Fin 4) : Query G Outer := .length (.cons (.index (ix i)) .nil)
private def selected : List (Query G Inner) :=
  [.word (.cons (.index (ix 0)) .nil),.word (.cons (.index (ix 1)) .nil),
   .word (.cons (.index (ix 2)) .nil),.length .nil]
private def popped : Value G Outer := (recursivePop CopyDemandControls.old).getD CopyDemandControls.old
private theorem popped_ok : recursivePop CopyDemandControls.old = some popped := rfl
private noncomputable def final : WordStore := (updates CopyDemandControls.old CopyDemandControls.root).foldl
  (fun w op => writeWord w (op.1.word 128 CopyDemandControls.hash) op.2) CopyDemandControls.machine
private theorem before : Represented CopyDemandControls.old (queries CopyDemandControls.old selected)
    CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  change q ∈ [.length .nil,leaf 1 0,leaf 1 1,leaf 1 2,header 1] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [leaf,header,ix,Query.supported,PathSupported,StepSupported] <;> decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some one = some word at observed; cases observed; rfl)
    | (intro word observed; change some two = some word at observed; cases observed; rfl)
private theorem queryCovered : ∀ q ∈ selected,
    q.location (childBase CopyDemandControls.old CopyDemandControls.root) ∈ CopyDemandControls.locations := by
  intro q member
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem written : ∀ q ∈ ClearDemands.slotDemands (lastSlot CopyDemandControls.old),
    q.location (childBase CopyDemandControls.old CopyDemandControls.root) ∈ CopyDemandControls.locations := by
  intro q member
  change q ∈ [.word (.cons (.index (ix 0)) .nil),.word (.cons (.index (ix 1)) .nil),.length .nil] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private theorem separation : ∀ q ∈ selected, ∀ d ∈ ClearDemands.slotDemands (lastSlot CopyDemandControls.old),
    d.location (childBase CopyDemandControls.old CopyDemandControls.root) =
      q.location (childBase CopyDemandControls.old CopyDemandControls.root) → d = q := by
  intro q member d generated same
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  change d ∈ [.word (.cons (.index (ix 0)) .nil),.word (.cons (.index (ix 1)) .nil),.length .nil] at generated
  simp only [List.mem_cons,List.not_mem_nil,or_false] at generated
  rcases member with rfl | rfl | rfl | rfl <;> rcases generated with rfl | rfl | rfl
  all_goals first | rfl | cases same
private theorem headerSeparate : ∀ q ∈ selected,
    q.location (childBase CopyDemandControls.old CopyDemandControls.root) ≠ CopyDemandControls.root := by
  intro q member
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

/-- General aggregate certificate with independently inhabited OLD owner/run
premises. Successful readback includes a cleared payload and older inner shadow. -/
theorem nested_certificate :
    execute (N := 128) CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root
      CopyDemandControls.machine = some final ∧
    Represented popped (queries CopyDemandControls.old selected) CopyDemandControls.root
      ((updates CopyDemandControls.old CopyDemandControls.root).foldl (fun w op => write w op.1 op.2) CopyDemandControls.store) ∧
    Transport 128 CopyDemandControls.hash CopyDemandControls.locations
      ((updates CopyDemandControls.old CopyDemandControls.root).foldl (fun w op => write w op.1 op.2) CopyDemandControls.store) final := by
  obtain ⟨actual,executed,represented,transported⟩ := complete_numeric CopyDemandControls.old popped popped_ok
    selected CopyDemandControls.root CopyDemandControls.store CopyDemandControls.machine CopyDemandControls.run
    before (fun _ _ => rfl) (by decide) queryCovered written separation headerSeparate
  have equal : actual = final := by
    have expected : execute (N := 128) CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root
        CopyDemandControls.machine = some final := rfl
    exact Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,represented,transported⟩

private def allQueries := CopyDemandControls.demands ++ CopyDemandControls.queries
private def graphView (value : Value G Outer) := allQueries.map (fun q => q.read value)
/-- COMPLETE12 graph observations and COMPLETE18 numeric observations in the
original fixture order, before and after actual pop. Nothing is projected away. -/
theorem complete_observations :
    (graphView CopyDemandControls.old,graphView popped,
      CopyDemandControls.numericView CopyDemandControls.machine,CopyDemandControls.numericView final) =
    ([some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some two,none],
     [some one,some one,some two,some zero,some zero,some zero,some one,some one,some one,some one,some two,none],
     (two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (one,two,zero,two,one,one,one,zero,zero,one,one,one,one,seven,one,one,zero,seven)) := rfl

theorem retained_live :
    (CopyDemandControls.old.observe (.cons (.index (ix 1)) (.cons (.index (ix 0)) .nil)),
     popped.observe (.cons (.index (ix 1)) (.cons (.index (ix 0)) .nil)),
     ((.cons (.index (ix 1)) (.cons (.index (ix 0)) .nil)) : TypeGraph.Path G Outer (.prim .bool)).readLive Value.dflt popped,
     popped.observe (.cons (.index (ix 2)) (.cons (.index (ix 0)) .nil)),
     ((.cons (.index (ix 2)) (.cons (.index (ix 0)) .nil)) : TypeGraph.Path G Outer (.prim .bool)).readLive Value.dflt popped,
     popped.observe (.cons (.index (ix 3)) (.cons (.index (ix 0)) .nil)),final 56) =
      (some true,some false,none,some true,none,none,seven) := rfl

private noncomputable def wrongFirst : WordStore :=
  writeWord (ClearDemands.numericClear (N := 128)
    ((CopyDemandControls.old.slots ⟨0,by decide⟩).getD (Value.dflt Inner)) (.data CopyDemandControls.root 0)
      CopyDemandControls.hash CopyDemandControls.machine) 0 one
private noncomputable def wrongExtent : WordStore :=
  writeWord (ClearDemands.numericClear (N := 128)
    ((CopyDemandControls.old.slots ⟨2,by decide⟩).getD (Value.dflt Inner)) (.data CopyDemandControls.root 2)
      CopyDemandControls.hash final) 10 zero
/-- Wrong last-slot selection and illegal older-shadow clearing have separate
COMPLETE numeric vectors, not just selected unequal cells. -/
theorem wrong_programs :
    (CopyDemandControls.numericView wrongFirst,CopyDemandControls.numericView wrongExtent) =
    ((one,zero,two,two,zero,zero,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (one,two,zero,zero,one,one,one,zero,zero,one,zero,zero,one,seven,one,one,zero,seven)) := rfl

private def emptyRetained : Value G Outer :=
  .array ⟨3,by decide⟩ ⟨0,by decide⟩ (by decide) CopyDemandControls.old.slots
private def emptyMachine : WordStore := writeWord CopyDemandControls.machine 0 zero
/-- Empty retained arrays fail without running a clear sequence. This pure
Option statement does not assert world rollback. -/
theorem empty_failure : recursivePop emptyRetained = none ∧
    execute (N := 128) emptyRetained CopyDemandControls.hash CopyDemandControls.root emptyMachine = none := by
  constructor <;> rfl


private abbrev Map : TypeGraph.Ty 0 := .mapping .bool (.prim .bool)
private def maps : Value G (.array Map) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun _ => .present (.mapping (fun _ => .present (.prim true))))
private def mapResult : Value G (.array Map) := (recursivePop maps).getD maps
private def mapQuery (key : Bool) : Query G Map := .word (.cons (.key key) .nil)
private def mapSelected := [mapQuery false,mapQuery true]
private def mapHash (p : Solidity.Storage.Pre) : Nat :=
  if p = .data 0 then 8 else if p = .entry 0 9 then 32 else if p = .entry 1 9 then 40 else 0
private def mapP : List Solidity.Storage.Pre := [.data 0,.entry 0 9,.entry 1 9]
private def mapRoot : Solidity.Storage.Loc := .root 0
private noncomputable def mapLocations : List Solidity.Storage.Loc :=
  [mapRoot,(mapQuery false).location (childBase maps mapRoot),(mapQuery true).location (childBase maps mapRoot)]
private def mapMachine : WordStore := fun a => if a = 0 then two else if a = 32 ∨ a = 40 then one else seven
private def mapStore : Store := fun l => mapMachine (l.word 128 mapHash)
private noncomputable def mapFinal : WordStore := writeWord mapMachine 0 one
private theorem mapRun : FiniteRun 128 4 1 mapHash mapP mapLocations := by
  constructor
  · intro p
    simp only [mapHash]
    split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))
  · decide
  · decide
  · decide
  · intro l member
    simp only [mapLocations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;>
      simp only [mapRoot,mapQuery,Query.location,childBase,lastPath,lastIndex,maps,Value.length,pathLoc,stepLoc,Loc.Bounded] <;> decide
  · intro l member
    simp only [mapLocations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
private theorem mapBefore : Represented maps (queries maps mapSelected) mapRoot mapStore := by
  intro q member
  change q ∈ [.length .nil,(mapQuery false).prefix (lastPath maps),(mapQuery true).prefix (lastPath maps)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (change (1 < lmax ∧ True ∧ True); decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some one = some word at observed; cases observed; rfl)
    | (intro word observed; change some two = some word at observed; cases observed; rfl)

/-- Pop over present mappings changes only the array header. The GENERAL
certificate observes BOTH keys in the cleared last slot under a GOOD run. -/
theorem mapping_certificate : execute (N := 128) maps mapHash mapRoot mapMachine = some mapFinal ∧
    Represented mapResult (queries maps mapSelected) mapRoot
      ((updates maps mapRoot).foldl (fun w op => write w op.1 op.2) mapStore) := by
  obtain ⟨actual,executed,represented,transported⟩ := complete_numeric maps mapResult rfl mapSelected mapRoot
    mapStore mapMachine mapRun mapBefore (fun _ _ => rfl) (by decide) (by
      intro q member
      simp only [mapSelected,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> decide) (by intro d member; cases member)
      (by intro q member d generated; cases generated) (by
        intro q member
        simp only [mapSelected,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> decide)
  have expected : execute (N := 128) maps mapHash mapRoot mapMachine = some mapFinal := rfl
  have equal := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,represented⟩
private def mapGraphView (v : Value G (.array Map)) :=
  (v.length.val,v.extent.val,([ix 0,ix 1,ix 2].flatMap (fun i => [false,true].map
    (fun k => v.observe (.cons (.index i) (.cons (.key k) .nil))))))
private def mapNumericView (m : WordStore) := (m 0,m 8,m 9,m 10,m 32,m 40,m 64,m 127)
/-- COMPLETE graph fixture: header/extent and BOTH keys at ALL3 retained
indices. Numeric view includes unused raw slot9 and outside sentinels. -/
theorem mapping_complete_observations :
    (mapGraphView maps,mapGraphView mapResult,mapNumericView mapMachine,mapNumericView mapFinal) =
    ((2,3,[some true,some true,some true,some true,some true,some true]),
     (1,3,[some true,some true,some true,some true,some true,some true]),
     (two,seven,seven,seven,one,one,seven,seven),
     (one,seven,seven,seven,one,one,seven,seven)) := rfl

/-- Absent last aggregate: root and default child headers are represented,
but failed payload reads constrain no garbage7. Pop must preserve that7. -/
private def absentOld : Value G Outer := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun i => if i.val = 1 then .absent else CopyDemandControls.old.slots i)
private def absentResult : Value G Outer := (recursivePop absentOld).getD absentOld
private def absentMachine : WordStore := writeWord (writeWord (writeWord (writeWord CopyDemandControls.machine 40 seven) 41 seven) 42 seven) 9 zero
private def absentStore : Store := fun l => absentMachine (l.word 128 CopyDemandControls.hash)
private noncomputable def absentFinal : WordStore := writeWord absentMachine 0 one
private theorem absentBefore : Represented absentOld (queries absentOld [.length .nil]) CopyDemandControls.root absentStore := by
  intro q member
  change q ∈ [.length .nil,.length (lastPath absentOld)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some two = some word at observed; cases observed; rfl
  · refine ⟨by change 1 < lmax ∧ True; decide,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl

theorem absent_certificate : execute (N := 128) absentOld CopyDemandControls.hash CopyDemandControls.root absentMachine = some absentFinal ∧
    Represented absentResult (queries absentOld [.length .nil]) CopyDemandControls.root
      ((updates absentOld CopyDemandControls.root).foldl (fun w op => write w op.1 op.2) absentStore) := by
  obtain ⟨actual,executed,represented,transported⟩ := complete_numeric absentOld absentResult rfl [.length .nil]
    CopyDemandControls.root absentStore absentMachine CopyDemandControls.run absentBefore (fun _ _ => rfl) (by decide)
    (by intro q member; have same := List.mem_singleton.mp member; subst q; decide)
    (by intro d member; cases member) (by intro q member d generated; cases generated)
    (by intro q member; have same := List.mem_singleton.mp member; subst q; decide)
  have expected : execute (N := 128) absentOld CopyDemandControls.hash CopyDemandControls.root absentMachine = some absentFinal := rfl
  have equal := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,represented⟩

theorem absent_complete_observations :
    (graphView absentOld,graphView absentResult,CopyDemandControls.numericView absentMachine,CopyDemandControls.numericView absentFinal) =
    ([some one,some one,some two,none,none,some zero,some two,some one,none,some one,some two,none],
     [some one,some one,some two,none,none,some zero,some one,some one,none,some one,some two,none],
     (two,two,zero,two,one,one,one,seven,seven,seven,one,one,one,seven,one,one,zero,seven),
     (one,two,zero,two,one,one,one,seven,seven,seven,one,one,one,seven,one,one,zero,seven)) := rfl


private abbrev RG := CopyWriteControls.recursiveGraph
private abbrev Nodes := Value RG (.array (.node 0))
private def recursiveNode (children : Nodes) : Value RG (.node 0) :=
  .node (Fields.set (Fields.set (fun {_} _ => Value.dflt _)
    .here (Value.prim (p := .bool) true)) (.there .here) children)
private def tree (width : Nat → Index) : Nat → Nodes
  | 0 => .array ⟨(width 0).val,by have h := (width 0).isLt; omega⟩ (width 0) (Nat.le_refl _)
      (fun _ => .present (recursiveNode (Value.dflt _)))
  | d+1 => .array ⟨(width (d+1)).val,by have h := (width (d+1)).isLt; omega⟩ (width (d+1)) (Nat.le_refl _)
      (fun _ => .present (recursiveNode (tree width d)))
private def deep : Nat → TypeGraph.Path RG (.array (.node 0)) (.prim .bool)
  | 0 => .cons (.index ⟨0,by decide⟩) (.cons (.field .here) .nil)
  | d+1 => .cons (.index ⟨0,by decide⟩) (.cons (.field (.there .here)) (deep d))
private theorem tree_read (width : Nat → Index) (positive : ∀ d, 0 < (width d).val) (d : Nat) :
    (tree width d).find (deep d) = some (.prim true) ∧
    (recursiveClear (tree width d)).find (deep d) = some (.prim false) := by
  rw [recursiveClear_eq_clear]
  induction d with
  | zero =>
    simp only [tree,deep,Value.find,Path.read,Step.get,Value.clear,dif_pos (positive 0),
      Slot.clear,Slot.getD,if_pos (positive 0),Option.bind_some,recursiveNode,Fields.get,Fields.set,
      Field.toNat,dif_neg (by decide : ¬ (0 = 1)),dif_pos True.intro]
    exact ⟨rfl,rfl⟩
  | succ d ih =>
    simp only [tree,deep,Value.find,Path.read,Step.get,Value.clear,dif_pos (positive (d+1)),
      Slot.clear,Slot.getD,if_pos (positive (d+1)),Option.bind_some,recursiveNode,Fields.get,Fields.set,
      Field.toNat,dif_pos True.intro]
    exact ih
private def pairSize : FixedSize := ⟨2,by decide⟩
private abbrev Pair := TypeGraph.Ty.fixed (.array (.node (0 : Fin 1))) pairSize
private def pair (width : Nat → Index) (d : Nat) : Value RG Pair :=
  .fixed (fun _ => .present (tree width d))
private def recursiveRoot (width : Nat → Index) (d : Nat) : Value RG (.array Pair) :=
  .array ⟨2,by decide⟩ (ix 1) (by decide) (fun _ => .present (pair width d))
private def target (outer fixed : Fin 2) (d : Nat) : TypeGraph.Path RG (.array Pair) (.prim .bool) :=
  .cons (.index ⟨outer.val,by have h := outer.isLt; omega⟩)
    (.cons (.fixed ⟨fixed.val,by have h := fixed.isLt; omega⟩) (deep d))
private def localTarget (fixed : Fin 2) (d : Nat) : Query RG Pair :=
  .word (.cons (.fixed ⟨fixed.val,by have h := fixed.isLt; omega⟩) (deep d))

/-- Actual singleton pop of a fixed pair of recursive trees. Every finite
recursive depth and independently varying positive live length at each level
is admitted. BOTH fixed children change; BOTH older-shadow children survive. -/
theorem recursive_fixed_observations (width : Nat → Index) (positive : ∀ d, 0 < (width d).val) (d : Nat) :
    let old := recursiveRoot width d
    let result := (recursivePop old).getD old
    (old.find (target 0 0 d),old.find (target 0 1 d),
      result.find (target 0 0 d),result.find (target 0 1 d),
      result.find (target 1 0 d),result.find (target 1 1 d),result.length.val,result.extent.val) =
      (some (.prim true),some (.prim true),some (.prim false),some (.prim false),
       some (.prim true),some (.prim true),0,2) := by
  have facts := tree_read width positive d
  change ((tree width d).find (deep d),(tree width d).find (deep d),
    (recursiveClear (tree width d)).find (deep d),(recursiveClear (tree width d)).find (deep d),
    (tree width d).find (deep d),(tree width d).find (deep d),0,2) = _
  rw [facts.1,facts.2]

/-- ACTUAL generated recursive clear traces beneath BOTH fixed children, with
changed old one to zero at arbitrary depth. This is trace correspondence;
no all-depth numeric region realization or emitted loop is asserted. -/
theorem recursive_fixed_traces (width : Nat → Index) (positive : ∀ d, 0 < (width d).val) (d : Nat)
    (fixed : Fin 2) :
    CopyReadback.traceWord (localTarget fixed d)
      (CopyWrites.zeros (ClearDemands.slotDemands (lastSlot (recursiveRoot width d)))) one = zero := by
  have facts := tree_read width positive d
  have which : fixed = 0 ∨ fixed = 1 := by omega
  rcases which with rfl | rfl
  all_goals apply CopyOutput.clear_slot_output (lastSlot (recursiveRoot width d)) _ one
  all_goals first
    | (intro word observed
       change (Query.word (deep d)).read (tree width d) = some word at observed
       simp only [Query.read,Value.observe,facts.1,Option.map_some,Value.head] at observed
       exact Option.some.inj observed)
    | (change (Query.word (deep d)).read (recursiveClear (tree width d)) = some zero
       simp only [Query.read,Value.observe,facts.2,Option.map_some,Value.head]
       rfl)


private noncomputable def currentOneFinal : WordStore := writeWord
  ((clearUpdates (CopyDemandControls.old.slots ⟨0,by decide⟩) (.data CopyDemandControls.root 0)).foldl
    (fun w op => writeWord w (op.1.word 128 CopyDemandControls.hash) op.2)
    (writeWord CopyDemandControls.machine 0 one)) 0 zero
/-- EXACT SAME execute reads the changed current header. A stale graph-header
oracle would incorrectly clear slot1 or succeed against a zero numeric header. -/
theorem current_header_negative :
    execute (N := 128) CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root emptyMachine = none ∧
    recursivePop CopyDemandControls.old = some popped ∧
    execute (N := 128) CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root
      (writeWord CopyDemandControls.machine 0 one) = some currentOneFinal ∧
    CopyDemandControls.numericView currentOneFinal =
      (zero,zero,two,two,zero,zero,one,one,one,one,one,one,one,seven,one,one,zero,seven) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem mapping_erasure_negative :
    mapNumericView (writeWord (writeWord mapFinal 32 zero) 40 zero) =
      (one,seven,seven,seven,zero,zero,seven,seven) := rfl

private def regrown : Value G Outer := (operationPush popped).getD popped
private noncomputable def regrownMachine : WordStore := writeWord final 0 two
/-- Real graph pop/push and concrete current-header pop/header-push. Aggregate
reuse preserves the cleared slot and older shadows. This is an inhabited
composition, not a general allocation/identity compiler theorem. -/
theorem regrow_complete_observations : operationPush popped = some regrown ∧
    LifecycleNumeric.pushHeader 128 CopyDemandControls.hash CopyDemandControls.root final = some regrownMachine ∧
    (graphView regrown,CopyDemandControls.numericView regrownMachine) =
    ([some one,some one,some two,some zero,some zero,some zero,some two,some one,some one,some one,some two,none],
     (two,two,zero,two,one,one,one,zero,zero,one,one,one,one,seven,one,one,zero,seven)) := by
  exact ⟨rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.nested_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.retained_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_live
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.wrong_programs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_programs
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.empty_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_failure
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.mapping_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.mapping_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_complete_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.absent_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.absent_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_complete_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.recursive_fixed_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursive_fixed_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.recursive_fixed_traces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms recursive_fixed_traces
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.current_header_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms current_header_negative
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.mapping_erasure_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_erasure_negative
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.regrow_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms regrow_complete_observations
private def mapReused : Value G (.array Map) := (operationPush mapResult).getD mapResult
private noncomputable def mapReusedMachine : WordStore := writeWord mapFinal 0 two
private noncomputable def mapReusedStore := write ((updates maps mapRoot).foldl (fun w op => write w op.1 op.2) mapStore) mapRoot two

/-- Evolving mapping-barrier application of the GENERAL certificate. BOTH
last mapping keys retain1 through pop and regrowth, with independent GOOD run. -/
theorem mapping_pop_push_certificate : PopPush.execute (N := 128) maps mapHash mapRoot mapMachine = some mapReusedMachine ∧
    Represented mapReused (queries maps mapSelected) mapRoot mapReusedStore ∧
    Transport 128 mapHash mapLocations mapReusedStore mapReusedMachine := by
  obtain ⟨actual,executed,owner,transported⟩ := PopPush.complete_numeric maps mapResult mapReused rfl rfl rfl mapSelected [] mapRoot
    mapStore mapMachine mapRun mapBefore (by intro q member; cases member) (fun _ _ => rfl) (by decide)
    (by intro q member; simp only [mapSelected,List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl <;> decide)
    (by intro q member; cases member) (by intro d member; cases member) (by intro q member d generated; cases generated)
    (by intro q member; simp only [mapSelected,List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl <;> decide)
    (by intro group member; cases member) (by intro q member; cases member)
  have expected : PopPush.execute (N := 128) maps mapHash mapRoot mapMachine = some mapReusedMachine := rfl
  have same := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,owner,transported⟩

theorem mapping_pop_push_observations :
    (mapGraphView maps,mapGraphView mapResult,mapGraphView mapReused,mapNumericView mapMachine,mapNumericView mapFinal,mapNumericView mapReusedMachine) =
    ((2,3,[some true,some true,some true,some true,some true,some true]),
     (1,3,[some true,some true,some true,some true,some true,some true]),
     (2,3,[some true,some true,some true,some true,some true,some true]),
     (two,seven,seven,seven,one,one,seven,seven),(one,seven,seven,seven,one,one,seven,seven),(two,seven,seven,seven,one,one,seven,seven)) := rfl

/-- Empty numeric/source failure stays None for the actual two-operation
sequence. No world rollback consequence is asserted. -/
theorem pop_push_empty_failure : recursivePop emptyRetained = none ∧
    PopPush.execute (N := 128) emptyRetained CopyDemandControls.hash CopyDemandControls.root emptyMachine = none := by
  refine ⟨empty_failure.1,?_⟩
  unfold PopPush.execute
  rw [empty_failure.2]
  rfl

private def absentReused := (operationPush absentResult).getD absentResult
private noncomputable def absentReusedMachine : WordStore := writeWord absentFinal 0 two
private noncomputable def absentReusedStore := write ((updates absentOld CopyDemandControls.root).foldl (fun w op => write w op.1 op.2) absentStore) CopyDemandControls.root two

/-- Absent/default aggregate reuse derives postrelation through actual middle
states. Unreadable raw payload7 is untouched rather than assumed zero. -/
theorem absent_pop_push_certificate : PopPush.execute (N := 128) absentOld CopyDemandControls.hash CopyDemandControls.root absentMachine = some absentReusedMachine ∧
    Represented absentReused (queries absentOld [.length .nil]) CopyDemandControls.root absentReusedStore ∧
    Transport 128 CopyDemandControls.hash CopyDemandControls.locations absentReusedStore absentReusedMachine := by
  obtain ⟨actual,executed,owner,transported⟩ := PopPush.complete_numeric absentOld absentResult absentReused rfl rfl rfl [.length .nil] []
    CopyDemandControls.root absentStore absentMachine CopyDemandControls.run absentBefore
    (by intro q member; cases member) (fun _ _ => rfl) (by decide)
    (by intro q member; have same := List.mem_singleton.mp member; subst q; decide)
    (by intro q member; cases member) (by intro d member; cases member) (by intro q member d generated; cases generated)
    (by intro q member; have same := List.mem_singleton.mp member; subst q; decide)
    (by intro group member; cases member) (by intro q member; cases member)
  have expected : PopPush.execute (N := 128) absentOld CopyDemandControls.hash CopyDemandControls.root absentMachine = some absentReusedMachine := rfl
  have same := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,owner,transported⟩

theorem absent_pop_push_observations :
    (graphView absentOld,graphView absentResult,graphView absentReused,
      CopyDemandControls.numericView absentMachine,CopyDemandControls.numericView absentFinal,CopyDemandControls.numericView absentReusedMachine) =
    ([some one,some one,some two,none,none,some zero,some two,some one,none,some one,some two,none],
     [some one,some one,some two,none,none,some zero,some one,some one,none,some one,some two,none],
     [some one,some one,some two,none,none,some zero,some two,some one,none,some one,some two,none],
     (two,two,zero,two,one,one,one,seven,seven,seven,one,one,one,seven,one,one,zero,seven),
     (one,two,zero,two,one,one,one,seven,seven,seven,one,one,one,seven,one,one,zero,seven),
     (two,two,zero,two,one,one,one,seven,seven,seven,one,one,one,seven,one,one,zero,seven)) := rfl

/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.mapping_pop_push_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_pop_push_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.mapping_pop_push_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_pop_push_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.pop_push_empty_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_push_empty_failure
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.absent_pop_push_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_pop_push_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopControls.absent_pop_push_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_pop_push_observations

end Solidity.Backend.StorageOps.AggregatePopControls

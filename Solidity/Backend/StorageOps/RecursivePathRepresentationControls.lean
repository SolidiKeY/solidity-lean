import Solidity.Backend.StorageOps.RecursivePathRepresentation
import Solidity.Backend.StorageOps.CopyOutputControls
import Solidity.Backend.StorageOps.SnapshotCommutation

/-! Actual recursive ROOT copy through a shared mapping-key/fixed prefix,
with independently inhabited representation, finite regions and context frames. -/
namespace Solidity.Backend.StorageOps.RecursivePathRepresentationControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open RecursivePathRepresentation
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private def sizeTwo : FixedSize := ⟨2,by decide⟩
private abbrev Middle : TypeGraph.Ty 0 := .fixed CopyDemandControls.Outer sizeTwo
private abbrev Root : TypeGraph.Ty 0 := .mapping .bool Middle
private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private def leafPath (i j : Fin 4) : TypeGraph.Path CopyDemandControls.graph CopyDemandControls.Outer (.prim .bool) :=
  .cons (.index (ix i)) (.cons (.index (ix j)) .nil)
private def leaf (i j : Fin 4) : Query CopyDemandControls.graph CopyDemandControls.Outer := .word (leafPath i j)
private def header (i : Fin 4) : Query CopyDemandControls.graph CopyDemandControls.Outer := .length (.cons (.index (ix i)) .nil)
private def rootHeader : Query CopyDemandControls.graph CopyDemandControls.Outer := .length .nil
private def childQueries := CopyDemandControls.demands ++ CopyDemandControls.queries
private def innerSlots : Fin sizeTwo.val → Slot CopyDemandControls.graph CopyDemandControls.Outer :=
  fun i => .present (if i.val = 0 then CopyDemandControls.old else CopyDemandControls.src)
private def rootSlots : Bool → Slot CopyDemandControls.graph Middle :=
  fun key => if key then .absent else .present (.fixed innerSlots)
private def root : Value CopyDemandControls.graph Root := .mapping rootSlots
private def result : Value CopyDemandControls.graph Root :=
  .mapping (Slots.write rootSlots false (.fixed (Slots.write innerSlots ⟨0,by decide⟩ CopyDemandControls.copied)))
private def dst : TypeGraph.Path CopyDemandControls.graph Root CopyDemandControls.Outer :=
  .cons (.key false) (.cons (.fixed ⟨0,by decide⟩) .nil)
private def src : TypeGraph.Path CopyDemandControls.graph Root CopyDemandControls.Outer :=
  .cons (.key false) (.cons (.fixed ⟨1,by decide⟩) .nil)
private def other : TypeGraph.Path CopyDemandControls.graph Root CopyDemandControls.Outer :=
  .cons (.key true) (.cons (.fixed ⟨0,by decide⟩) .nil)
private def outside : List (Query CopyDemandControls.graph Root) :=
  [.length other,(leaf 3 0).prefix other]
private def base : Solidity.Storage.Loc := .root 0
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .entry 0 0 then 8 else if p = .entry 1 0 then 80 else if p = .data 8 then 16 else if p = .data 16 then 32 else if p = .data 17 then 40 else if p = .data 18 then 48 else if p = .data 19 then 56 else if p = .data 9 then 24 else if p = .data 24 then 64 else if p = .data 80 then 88 else if p = .data 91 then 96 else 0
private def preimages : List Solidity.Storage.Pre :=
  [.entry 0 0,.entry 1 0,.data 8,.data 16,.data 17,.data 18,.data 19,.data 9,.data 24,.data 80,.data 91]
private def machine : WordStore := fun a =>
  if a = 8 ∨ a = 16 ∨ a = 17 ∨ a = 18 then two else
  if a = 32 ∨ a = 33 ∨ a = 34 ∨ a = 40 ∨ a = 41 ∨ a = 42 ∨ a = 48 ∨ a = 49 ∨ a = 50 ∨ a = 9 ∨ a = 24 then one else
  if a = 64 ∨ a = 80 then zero else seven
private def store : Store := fun l => machine (l.word 128 hash)
private noncomputable def destinationLocations := childQueries.map (fun q => (q.prefix dst).location base)
private noncomputable def sourceLocations := (ClearDemands.demands CopyDemandControls.src).map
  (fun q => (q.prefix src).location base)
private noncomputable def outsideLocations := outside.map (fun q => q.location base)
private noncomputable def locations := destinationLocations ++ sourceLocations ++ outsideLocations
private def dbase : Solidity.Storage.Loc := .hash 0 (.root 0) 0
private def sbase : Solidity.Storage.Loc := .hash 0 (.root 0) 1
private def obase : Solidity.Storage.Loc := .hash 1 (.root 0) 0
private def dl (i j : Nat) : Solidity.Storage.Loc := .data (.data dbase i) j
private def dh (i : Nat) : Solidity.Storage.Loc := .data dbase i
private def concreteLocations : List Solidity.Storage.Loc :=
  [dl 0 0,dl 0 1,dh 0,dl 1 0,dl 1 1,dh 1,dbase,dl 0 2,dl 1 2,dl 2 0,dh 2,dl 3 0,
   .data (.data sbase 0) 0,.data sbase 0,sbase,obase,.data (.data obase 3) 0]
private theorem run : FiniteRun 128 4 1 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (decide))))))))))))))))))))))
  · decide
  · decide
  · decide
  · intro l member
    change l ∈ concreteLocations at member
    simp only [concreteLocations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dl,dh,dbase,sbase,obase,Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    change l ∈ concreteLocations at member
    simp only [concreteLocations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem read_dst : root.find dst = some CopyDemandControls.old := rfl
private theorem read_src : root.find src = some CopyDemandControls.src := rfl
private theorem copied : recursiveCopyAt root dst src = some result := rfl
private theorem before_dst : Represented root (childQueries.map (Query.prefix dst)) base store := by
  intro parent member
  obtain ⟨q,inside,rfl⟩ := List.mem_map.mp member
  change q ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader,
    leaf 0 2,leaf 1 2,leaf 2 0,header 2,leaf 3 0] at inside
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [Query.prefix,Query.supported,TypeGraph.Path.append,leaf,leafPath,header,rootHeader,ix,dst,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some one = some word at observed; cases observed; rfl)
    | (intro word observed; change some two = some word at observed; cases observed; rfl)
    | (intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed)
private theorem before_src : Represented root
    ((ClearDemands.demands CopyDemandControls.src).map (Query.prefix src)) base store := by
  intro parent member
  obtain ⟨q,inside,rfl⟩ := List.mem_map.mp member
  change q ∈ [leaf 0 0,header 0,rootHeader] at inside
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [Query.prefix,Query.supported,TypeGraph.Path.append,leaf,leafPath,header,rootHeader,ix,src,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some zero = some word at observed; cases observed; rfl)
    | (intro word observed; change some one = some word at observed; cases observed; rfl)
private theorem before_outside : Represented root outside base store := by
  intro q member
  simp only [outside,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [Query.prefix,Query.supported,TypeGraph.Path.append,leaf,leafPath,ix,other,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some zero = some word at observed; cases observed; rfl)
    | (intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed)
private theorem source_covered : ∀ q ∈ ClearDemands.demands CopyDemandControls.src,
    (q.prefix src).location base ∈ locations := by
  intro q member
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨q,member,rfl⟩))))
private theorem queries_covered : ∀ q ∈ childQueries, (q.prefix dst).location base ∈ locations := by
  intro q member
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨q,member,rfl⟩))))
private theorem writes_covered : ∀ d ∈ CopyDemands.demands CopyDemandControls.old CopyDemandControls.src,
    (d.prefix dst).location base ∈ locations := by
  intro d member
  exact queries_covered d (List.mem_append.mpr (Or.inl member))
private theorem outside_covered : ∀ q ∈ outside, q.location base ∈ locations := by
  intro q member
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨q,member,rfl⟩))
private theorem separated : ∀ q ∈ childQueries,
    ∀ d ∈ CopyDemands.demands CopyDemandControls.old CopyDemandControls.src,
    (d.prefix dst).location base = (q.prefix dst).location base → d.prefix dst = q.prefix dst := by
  intro q member d written same
  change q ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader,
    leaf 0 2,leaf 1 2,leaf 2 0,header 2,leaf 3 0] at member
  change d ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader] at written
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member written
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases written with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | cases same
private theorem apart : ∀ q ∈ outside, q.apart dst := by
  intro q member
  simp only [outside,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals exact Apart.fork (StepApart.key (K := .bool) (V := Middle) false true (by intro same; cases same)) _ _
private theorem nonalias : ∀ q ∈ outside,
    ∀ d ∈ CopyDemands.demands CopyDemandControls.old CopyDemandControls.src,
    q.location base ≠ (d.prefix dst).location base := by
  intro q member d written
  simp only [outside,List.mem_cons,List.not_mem_nil,or_false] at member
  change d ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader] at written
  simp only [List.mem_cons,List.not_mem_nil,or_false] at written
  rcases member with rfl | rfl <;> rcases written with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals intro same
  all_goals cases same

/-- Actual root capture/save through nonempty shared key prefix and distinct
fixed children, with ALL12 destination observations and default/failing context.
All original owner, finite region/query and logical frame premises are inhabited. -/
theorem full_root_context :
    let log := CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src
      (pathLoc dst base) (pathLoc src base) hash machine
    let after := log.foldl (fun w op => write w op.1 op.2) store
    Represented result (childQueries.map (Query.prefix dst) ++ outside) base after ∧
    Transport 128 hash locations after
      (CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src
        (pathLoc dst base) (pathLoc src base) hash machine) :=
  copy_at_context root result dst src CopyDemandControls.old CopyDemandControls.src CopyDemandControls.permit
    read_dst read_src copied childQueries outside base store machine run before_dst before_src before_outside
    (fun _ _ => rfl) source_covered queries_covered outside_covered writes_covered separated apart nonalias

private noncomputable def program : WordStore := CopyWrites.numericCopy (N := 128)
  CopyDemandControls.old CopyDemandControls.src (pathLoc dst base) (pathLoc src base) hash machine
private noncomputable def selfProgram : WordStore := CopyWrites.numericCopy (N := 128)
  CopyDemandControls.old CopyDemandControls.old (pathLoc dst base) (pathLoc dst base) hash machine
private def numericView (m : WordStore) :=
  (m 8,m 16,m 17,m 18,m 32,m 33,m 34,m 40,m 41,m 42,m 48,m 49,m 50,m 56,m 9,m 24,m 64,m 80,m 96,m 0,m 127)
private def allRootQueries := childQueries.map (Query.prefix dst) ++ outside

/-- COMPLETE14 ROOT old/post graph observations, including a defaulted mapping
header and failed mapping-path query; COMPLETE21 initial/copied/self numeric
observations include all selected addresses, source words and outside sentinels. -/
theorem complete_observations :
    (allRootQueries.map (Query.read root),allRootQueries.map (Query.read result),
      numericView machine,numericView program,numericView selfProgram) =
    ([some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some two,none,some zero,none],
     [some zero,some zero,some one,some zero,some zero,some zero,some one,some one,some one,some one,some two,none,some zero,none],
     (two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,zero,seven,seven,seven),
     (one,one,zero,two,zero,zero,one,zero,zero,one,one,one,one,seven,one,one,zero,zero,seven,seven,seven),
     (two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,zero,seven,seven,seven)) := by rfl

/-- The other mapping slot stays ABSENT, its default value is observed through
existing paths, and the captured source sibling remains unchanged. -/
theorem defaulted_mapping_identity :
    rootSlots true = Slot.absent ∧
    (Slots.write rootSlots false (.fixed (Slots.write innerSlots ⟨0,by decide⟩ CopyDemandControls.copied))) true = Slot.absent ∧
    root.find (.cons (.key true) .nil) = some (Value.dflt Middle) ∧
    result.find (.cons (.key true) .nil) = some (Value.dflt Middle) ∧
    root.find src = some CopyDemandControls.src ∧ result.find src = some CopyDemandControls.src := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Raw retained reads and live reads are separate through the ACTUAL prefix.
Shrunk target is cleared0 but no longer live; older shadow stays1 and failed
query remains None with numeric garbage7, without any zero-cell inference. -/
theorem retained_live_observations :
    (((leaf 1 0).prefix dst).read root,((leaf 1 0).prefix dst).read result,
     ((dst.append (leafPath 1 0)).readLive Value.dflt root).map Value.head,
     ((dst.append (leafPath 1 0)).readLive Value.dflt result).map Value.head,
     ((leaf 2 0).prefix dst).read root,((leaf 2 0).prefix dst).read result,
     ((dst.append (leafPath 2 0)).readLive Value.dflt root).map Value.head,
     ((dst.append (leafPath 2 0)).readLive Value.dflt result).map Value.head,
     ((leaf 3 0).prefix dst).read result,program 40,program 48,program 56,program 96) =
      (some one,some zero,some true,none,some one,some one,none,none,none,zero,one,seven,seven) := by rfl

/-- Both actual capture failures match the existing graph semantics; raw numeric
slot10 is7. No assertion that Option failure rolls back a world is made. -/
theorem malformed_captures :
    let bad : TypeGraph.Path CopyDemandControls.graph Root CopyDemandControls.Outer :=
      .cons (.key false) (.cons (.fixed ⟨2,by decide⟩) .nil)
    (root.find bad,recursiveCopyAt root dst bad,recursiveCopyAt root bad src,machine 10) =
      (none,none,none,seven) := by rfl

private def nestedDst : TypeGraph.Path CopyDemandControls.graph Root CopyDemandControls.Inner :=
  dst.append (.cons (.index (ix 0)) .nil)
private def nestedSrc : TypeGraph.Path CopyDemandControls.graph Root CopyDemandControls.Inner :=
  src.append (.cons (.index (ix 0)) .nil)
private def oldInner : Value CopyDemandControls.graph CopyDemandControls.Inner :=
  (CopyDemandControls.old.find (.cons (.index (ix 0)) .nil)).getD (Value.dflt _)
private def srcInner : Value CopyDemandControls.graph CopyDemandControls.Inner :=
  (CopyDemandControls.src.find (.cons (.index (ix 0)) .nil)).getD (Value.dflt _)
private def nestedResult : Value CopyDemandControls.graph Root :=
  (root.save nestedDst (recursiveCopy oldInner srcInner)).getD root
private noncomputable def nestedProgram : WordStore := CopyWrites.numericCopy (N := 128)
  oldInner srcInner (pathLoc nestedDst base) (pathLoc nestedSrc base) hash machine
private theorem nestedCopied : recursiveCopyAt root nestedDst nestedSrc = some nestedResult := rfl
private theorem parent_owner : Represented root [.length dst] base store := by
  intro q member
  have same := List.mem_singleton.mp member
  subst q
  refine ⟨?_,⟨by decide,by decide⟩,?_⟩
  · simp only [dst,Query.supported,PathSupported,StepSupported]; decide
  · intro word observed
    change some two = some word at observed
    cases observed
    rfl
private theorem nested_writes_covered : ∀ d ∈ CopyDemands.demands oldInner srcInner,
    (d.prefix nestedDst).location base ∈ locations := by
  intro d member
  change d ∈ [.word (.cons (.index (ix 0)) .nil),.word (.cons (.index (ix 1)) .nil),.length .nil] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact queries_covered (leaf 0 0) (by
      change leaf 0 0 ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader,leaf 0 2,leaf 1 2,leaf 2 0,header 2,leaf 3 0]
      exact List.mem_cons_self)
  · exact queries_covered (leaf 0 1) (by
      change leaf 0 1 ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader,leaf 0 2,leaf 1 2,leaf 2 0,header 2,leaf 3 0]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
  · exact queries_covered (header 0) (by
      change header 0 ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader,leaf 0 2,leaf 1 2,leaf 2 0,header 2,leaf 3 0]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- A distinct actual nested copy instantiates the ANCESTOR header theorem,
preserving the parent's length AND extent while the child's header shrinks. -/
theorem ancestor_header_certificate :
    let log := CopyWrites.updates (N := 128) oldInner srcInner (pathLoc nestedDst base) (pathLoc nestedSrc base) hash machine
    let after := log.foldl (fun w op => write w op.1 op.2) store
    Represented nestedResult [.length dst] base after ∧ Transport 128 hash locations after nestedProgram := by
  apply header_frame_at root nestedResult nestedDst nestedSrc oldInner srcInner rfl rfl nestedCopied
    dst (ix 0) .nil rfl base store machine run parent_owner (fun _ _ => rfl)
  · exact queries_covered rootHeader (by
      change rootHeader ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader,leaf 0 2,leaf 1 2,leaf 2 0,header 2,leaf 3 0]
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl True.intro)))))))
  · exact nested_writes_covered
  · intro d member
    change d ∈ [.word (.cons (.index (ix 0)) .nil),.word (.cons (.index (ix 1)) .nil),.length .nil] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> intro same <;> cases same

/-- COMPLETE parent/child observations distinguish preserved ancestor metadata
from changed child payloads/length, shadows and outside failed-query garbage. -/
theorem ancestor_complete_observations :
    (root.observe dst,nestedResult.observe dst,
     (machine 8,machine 16,machine 32,machine 33,machine 34,machine 24,machine 64,machine 80,machine 96),
     (nestedProgram 8,nestedProgram 16,nestedProgram 32,nestedProgram 33,nestedProgram 34,nestedProgram 24,nestedProgram 64,nestedProgram 80,nestedProgram 96)) =
      (some (⟨2,by decide⟩,⟨3,by decide⟩),some (⟨2,by decide⟩,⟨3,by decide⟩),
       (two,two,one,one,one,one,zero,zero,seven),
       (two,one,zero,zero,one,one,zero,zero,seven)) := by rfl

private abbrev AliasNode : TypeGraph.Ty 1 := .node 0
private def aFlag : TypeGraph.Path CopyWriteControls.recursiveGraph AliasNode (.prim .bool) := .cons (.field .here) .nil
private def aKids : TypeGraph.Path CopyWriteControls.recursiveGraph AliasNode (.array AliasNode) := .cons (.field (.there .here)) .nil
private def aSource : TypeGraph.Path CopyWriteControls.recursiveGraph AliasNode AliasNode :=
  aKids.append (.cons (.index ⟨0,by decide⟩) .nil)
private def af : Query CopyWriteControls.recursiveGraph AliasNode := .word aFlag
private def acf : Query CopyWriteControls.recursiveGraph AliasNode := .word (aSource.append aFlag)
private def agf : Query CopyWriteControls.recursiveGraph AliasNode := .word (aSource.append (aSource.append aFlag))
private def ak : Query CopyWriteControls.recursiveGraph AliasNode := .length aKids
private def ack : Query CopyWriteControls.recursiveGraph AliasNode := .length (aSource.append aKids)
private def agk : Query CopyWriteControls.recursiveGraph AliasNode := .length (aSource.append (aSource.append aKids))
private def aQueries := CopyDemands.demands CopyWriteControls.oldNode CopyWriteControls.sourceNode
private def aPermit : CopyPermit CopyWriteControls.recursiveGraph AliasNode :=
  CopyPermit.checked (fun _ => true) (by decide)
private def aResult := recursiveCopy CopyWriteControls.oldNode CopyWriteControls.sourceNode
private theorem aRead : CopyWriteControls.oldNode.find aSource = some CopyWriteControls.sourceNode := rfl
private theorem aCopied : recursiveCopyAt CopyWriteControls.oldNode .nil aSource = some aResult := rfl
private theorem aOld : Represented CopyWriteControls.oldNode aQueries (.root 0) CopyWriteControls.overlapStore := by
  intro q member
  change q ∈ [af,acf,agf,agk,ack,ak] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [af,acf,agf,ak,ack,agk,aFlag,aKids,aSource,Query.supported,PathSupported,StepSupported,TypeGraph.Path.append]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some zero = some word at observed; cases observed; rfl)
    | (intro word observed; change some one = some word at observed; cases observed; rfl)
private theorem aSrc : Represented CopyWriteControls.sourceNode (ClearDemands.demands CopyWriteControls.sourceNode)
    CopyWriteControls.overlapSource CopyWriteControls.overlapStore := by
  intro q member
  apply CopyWriteControls.overlap_source_owner q
  change q ∈ [af,acf,ack,ak] at member
  change q ∈ [af,ak,acf,ack]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
  rcases member with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inl rfl)
private theorem aSourceCovered : ∀ q ∈ ClearDemands.demands CopyWriteControls.sourceNode,
    (q.prefix aSource).location (.root 0) ∈ CopyWriteControls.overlapLocations := by
  intro q member
  change q ∈ [af,acf,ack,ak] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨acf,by
      change acf ∈ [af,acf,agf,agk,ack,ak]
      exact List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  · exact List.mem_map.mpr ⟨agf,by
      change agf ∈ [af,acf,agf,agk,ack,ak]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩
  · exact List.mem_map.mpr ⟨agk,by
      change agk ∈ [af,acf,agf,agk,ack,ak]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),rfl⟩
  · exact List.mem_map.mpr ⟨ack,by
      change ack ∈ [af,acf,agf,agk,ack,ak]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),rfl⟩
private theorem aQueriesCovered : ∀ q ∈ aQueries, (q.prefix .nil).location (.root 0) ∈ CopyWriteControls.overlapLocations := by
  intro q member
  simpa only [Query.location_prefix,pathLoc] using (List.mem_map.mpr ⟨q,member,rfl⟩ : q.location (.root 0) ∈ CopyWriteControls.overlapLocations)
private theorem aSeparate : ∀ q ∈ aQueries, ∀ d ∈ CopyDemands.demands CopyWriteControls.oldNode CopyWriteControls.sourceNode,
    (d.prefix .nil).location (.root 0) = (q.prefix .nil).location (.root 0) → d.prefix .nil = q.prefix .nil := by
  intro q member d written same
  change q ∈ [af,acf,agf,agk,ack,ak] at member
  change d ∈ [af,acf,agf,agk,ack,ak] at written
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member written
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases written with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | cases same

/-- The ROOT theorem applies to actual descendant/ancestor aliasing with GOOD
regions and original ROOT old relations, not merely assumed child results. -/
theorem aliased_root_certificate :
    let log := CopyWrites.updates (N := 128) CopyWriteControls.oldNode CopyWriteControls.sourceNode
      (.root 0) CopyWriteControls.overlapSource CopyWriteControls.overlapHash CopyWriteControls.overlapMachine
    let after := log.foldl (fun w op => write w op.1 op.2) CopyWriteControls.overlapStore
    Represented aResult (aQueries.map (Query.prefix .nil)) (.root 0) after ∧
    Transport 128 CopyWriteControls.overlapHash CopyWriteControls.overlapLocations after CopyWriteControls.overlapResult := by
  apply copy_at CopyWriteControls.oldNode aResult .nil aSource CopyWriteControls.oldNode CopyWriteControls.sourceNode
    aPermit rfl aRead aCopied aQueries (.root 0) CopyWriteControls.overlapStore CopyWriteControls.overlapMachine
    CopyWriteControls.overlap_run
  · exact Represented.prefix .nil rfl True.intro aOld
  · exact Represented.prefix aSource aRead (by simp only [aSource,aKids,TypeGraph.Path.append,PathSupported,StepSupported]; decide) aSrc
  · exact fun _ _ => rfl
  · exact aSourceCovered
  · exact aQueriesCovered
  · exact aQueriesCovered
  · exact aSeparate

/-- Actual capture/save is observed alongside COMPLETE7 initial/captured/wrong
incremental numeric words. The source path's payload/header changes after copy,
so its old snapshot and its post-operation live contents are distinct. -/
theorem aliased_capture_observations :
    recursiveCopyAt CopyWriteControls.oldNode .nil aSource = some aResult ∧
    (CopyWriteControls.oldNode.observe (aSource.append aFlag),aResult.observe (aSource.append aFlag),
     CopyWriteControls.oldNode.observe (aSource.append aKids),aResult.observe (aSource.append aKids),
     CopyWriteControls.overlapView CopyWriteControls.overlapMachine,
     CopyWriteControls.overlapView CopyWriteControls.overlapResult,
     CopyWriteControls.overlapView CopyWriteControls.wrongIncremental) =
      (some false,some true,some (⟨1,by decide⟩,⟨1,by decide⟩),some (⟨0,by decide⟩,⟨1,by decide⟩),
       (one,one,zero,one,one,zero,seven),(zero,one,one,zero,zero,zero,seven),(zero,zero,one,zero,zero,zero,seven)) := by
  exact ⟨rfl,rfl⟩

/-- The success decomposition is instantiated on a genuinely changing alias
operation. It exposes actual reads/save rather than a desired postcondition. -/
theorem actual_capture_decomposition :
    ∃ old snapshot, CopyWriteControls.oldNode.find (.nil : TypeGraph.Path CopyWriteControls.recursiveGraph AliasNode AliasNode) = some old ∧
      CopyWriteControls.oldNode.find aSource = some snapshot ∧
      CopyWriteControls.oldNode.save .nil (recursiveCopy old snapshot) = some aResult :=
  capture_success CopyWriteControls.oldNode aResult .nil aSource aCopied

private def sizeOne : FixedSize := ⟨1,by decide⟩
private def wrapTy : Nat → TypeGraph.Ty 0
  | 0 => Root
  | d+1 => .fixed (wrapTy d) sizeOne
private def wrapped (value : Value CopyDemandControls.graph Root) : (d : Nat) → Value CopyDemandControls.graph (wrapTy d)
  | 0 => value
  | d+1 => .fixed (fun _ => .present (wrapped value d))
private def wrapPath : (d : Nat) → TypeGraph.Path CopyDemandControls.graph (wrapTy d) Root
  | 0 => .nil
  | d+1 => .cons (.fixed (ix 0)) (wrapPath d)
private theorem wrap_read (value : Value CopyDemandControls.graph Root) (d : Nat) :
    (wrapped value d).find (wrapPath d) = some value := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simpa only [wrapped,wrapPath,Value.find,TypeGraph.Path.read,TypeGraph.Step.get,ix,
      dif_pos (show 0 < sizeOne.val by decide),Slot.getD,Option.bind_some] using ih
private theorem wrap_supported (d : Nat) : PathSupported (wrapPath d) := by
  induction d with
  | zero => exact True.intro
  | succ d ih => exact ⟨by change 0 < 1; decide,ih⟩
private theorem wrap_location (d : Nat) (l : Solidity.Storage.Loc) : pathLoc (wrapPath d) l = l := by
  induction d generalizing l with
  | zero => rfl
  | succ d ih =>
    change pathLoc (wrapPath d) (stepLoc (Step.fixed (G := CopyDemandControls.graph) (E := wrapTy d) (m := sizeOne) (ix 0)) l) = l
    have step : stepLoc (Step.fixed (G := CopyDemandControls.graph) (E := wrapTy d) (m := sizeOne) (ix 0)) l = l := by
      change l.add (0 * inlineSize CopyDemandControls.graph (wrapTy d)) = l
      rw [Nat.zero_mul,Solidity.Storage.Loc.add_zero]
    rw [step]
    exact ih l

/-- Actual root operation plus GENERAL selected representation/numeric transport
at EVERY finite shared-prefix depth. All premises are concretely inhabited;
fixed-one zero offsets reuse the SAME GOOD hash/run and actual copied words. -/
theorem arbitrary_prefix_numeric (depth : Nat) :
    let pre := wrapPath depth
    let log := CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src
      (pathLoc (pre.append dst) base) (pathLoc (pre.append src) base) hash machine
    let after := log.foldl (fun w op => write w op.1 op.2) store
    ∃ changed : Value CopyDemandControls.graph (wrapTy depth),
      recursiveCopyAt (wrapped root depth) (pre.append dst) (pre.append src) = some changed ∧
      Represented changed (allRootQueries.map (Query.prefix pre)) base after ∧
      Transport 128 hash locations after
        (CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src
          (pathLoc (pre.append dst) base) (pathLoc (pre.append src) base) hash machine) := by
  dsimp only
  simp only [pathLoc_append,wrap_location]
  obtain ⟨changed,saved⟩ := prefix_save_exists (wrapPath depth) (wrapped root depth) root result (wrap_read root depth)
  have actual : recursiveCopyAt (wrapped root depth) ((wrapPath depth).append dst) ((wrapPath depth).append src) = some changed := by
    rw [recursiveCopyAt_append]
    simpa only [modifyAt,Option.bind_eq_bind,wrap_read,copied,Option.bind_some] using saved
  refine ⟨changed,actual,?_,full_root_context.2⟩
  apply Represented.prefix (wrapPath depth)
    (Value.find_save (wrapped root depth) changed (wrapPath depth) result saved) (wrap_supported depth)
  simpa only [wrap_location] using full_root_context.1

/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.full_root_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_root_context
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_observations
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.defaulted_mapping_identity' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms defaulted_mapping_identity
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.retained_live_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms retained_live_observations
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.malformed_captures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms malformed_captures
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.ancestor_header_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ancestor_header_certificate
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.ancestor_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ancestor_complete_observations
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.aliased_root_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms aliased_root_certificate
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.aliased_capture_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms aliased_capture_observations
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.actual_capture_decomposition' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms actual_capture_decomposition
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentationControls.arbitrary_prefix_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms arbitrary_prefix_numeric

end Solidity.Backend.StorageOps.RecursivePathRepresentationControls

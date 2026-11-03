import Solidity.Backend.StorageOps.CopyOutputInduction
import Solidity.Backend.StorageOps.CopyWriteControls

/-! Independent output and actual numeric representation applications.
All-depth witnesses have independently varying old/new runtime lengths. -/
namespace Solidity.Backend.StorageOps.CopyOutputControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open CopyReadback CopyOutput
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def seven : Semantics.Word := ⟨7,by decide⟩
private def i0 : Index := ⟨0,by decide⟩
private abbrev Nodes := Value CopyWriteControls.recursiveGraph (.array (.node 0))
private abbrev Node := Value CopyWriteControls.recursiveGraph (.node 0)
private def node (flag : Bool) (children : Nodes) : Node :=
  .node (Fields.set (Fields.set (fun {_} _ => Value.dflt _)
    .here (Value.prim (p := .bool) flag)) (.there .here) children)
private def tree (width : Nat → Index) (flag : Bool) : Nat → Nodes
  | 0 => .array ⟨(width 0).val,by have h := (width 0).isLt; omega⟩ (width 0) (Nat.le_refl _)
      (fun _ => .present (node flag (Value.dflt _)))
  | d+1 => .array ⟨(width (d+1)).val,by have h := (width (d+1)).isLt; omega⟩ (width (d+1)) (Nat.le_refl _)
      (fun _ => .present (node flag (tree width flag d)))
private def deep : Nat → TypeGraph.Path CopyWriteControls.recursiveGraph (.array (.node 0)) (.prim .bool)
  | 0 => .cons (.index i0) (.cons (.field .here) .nil)
  | d+1 => .cons (.index i0) (.cons (.field (.there .here)) (deep d))
private def permit : CopyPermit CopyWriteControls.recursiveGraph (.array (.node 0)) :=
  CopyPermit.checked (fun _ => true) (by decide)

/-- Real mapping-free recursive source values, arbitrary finite depth and
independently varying runtime widths. Both old and copied payloads are observed. -/
theorem recursive_observations (ow nw : Nat → Index)
    (op : ∀ d, 0 < (ow d).val) (np : ∀ d, 0 < (nw d).val) (d : Nat) :
    (tree ow true d).find (deep d) = some (.prim (p := .bool) true) ∧
    (recursiveCopy (tree ow true d) (tree nw false d)).find (deep d) = some (.prim (p := .bool) false) := by
  rw [recursiveCopy_eq_overlay]
  induction d with
  | zero =>
    simp only [tree,deep,Value.find,TypeGraph.Path.read,TypeGraph.Step.get,Value.overlay,i0,
      dif_pos (op 0),dif_pos (np 0),dif_pos (show 0 < max (ow 0).val (nw 0).val by have h := op 0; omega),
      Slot.overlay,Slot.getD,Option.bind_some,node,Fields.get,Fields.set,Field.toNat,dif_neg (by decide : ¬ (0 = 1)),dif_pos True.intro]
    exact ⟨rfl,rfl⟩
  | succ d ih =>
    simp only [tree,deep,Value.find,TypeGraph.Path.read,TypeGraph.Step.get,Value.overlay,i0,
      dif_pos (op (d+1)),dif_pos (np (d+1)),dif_pos (show 0 < max (ow (d+1)).val (nw (d+1)).val by have h := op (d+1); omega),
      Slot.overlay,Slot.getD,Option.bind_some,node,Fields.get,Fields.set,Field.toNat,dif_pos True.intro]
    exact ih

/-- GENERAL copied-output theorem applied at every finite recursive depth.
The ACTUAL generated trace changes an inhabited old true word to false. -/
theorem recursive_trace_output (ow nw : Nat → Index)
    (op : ∀ d, 0 < (ow d).val) (np : ∀ d, 0 < (nw d).val) (d : Nat) :
    traceWord (.word (deep d)) (CopyWrites.queryWrites (tree ow true d) (tree nw false d)
      (fun q => (q.read (tree nw false d)).getD zero)) one = zero := by
  obtain ⟨oldObserved,postObserved⟩ := recursive_observations ow nw op np d
  apply copy_output (tree ow true d) (tree nw false d) permit (.word (deep d)) one
  · intro word observed
    simp only [Query.read,Value.observe,oldObserved,Option.map_some,Value.head] at observed
    exact Option.some.inj observed
  · simp only [Query.read,Value.observe,postObserved,Option.map_some,Value.head]
    rfl

/-- An absent RETAINED slot clears with NO writes; its default graph read is0
but an unrepresented old cell7 remains7. Fresh absent copy DOES initialize0.
Thus the old successful-read premise of clear_slot_output cannot be removed. -/
theorem absent_retained_counterexample :
    let old : Slot CopyDemandControls.graph (.prim .bool) := .absent
    let q : Query CopyDemandControls.graph (.prim .bool) := .word .nil
    (traceWord q (CopyWrites.zeros (ClearDemands.slotDemands old)) seven,
     q.read ((recursiveClearSlot old).getD (Value.dflt _)),
     traceWord q (CopyWrites.slotWrites old .absent (fun _ => seven)) seven) =
      (seven,some zero,zero) := by
  change (seven,some zero,traceWord (.word .nil : Query CopyDemandControls.graph (.prim .bool))
    [(.word .nil,zero)] seven) = _
  simp only [traceWord,List.foldl_cons,List.foldl_nil,ite_true]

private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private def leaf (i j : Fin 4) : Query CopyDemandControls.graph CopyDemandControls.Outer :=
  .word (.cons (.index (ix i)) (.cons (.index (ix j)) .nil))
private def header (i : Fin 4) : Query CopyDemandControls.graph CopyDemandControls.Outer :=
  .length (.cons (.index (ix i)) .nil)
private def rootHeader : Query CopyDemandControls.graph CopyDemandControls.Outer := .length .nil
private def allQueries := CopyDemandControls.demands ++ CopyDemandControls.queries
private noncomputable def sourceLocations := (ClearDemands.demands CopyDemandControls.src).map
  (fun q => q.location (.root 1))
private noncomputable def locations := CopyDemandControls.locations ++ sourceLocations
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 8,.data 9,.data 10,.data 11,.data 1,.data 16]
private theorem run : FiniteRun 128 4 2 CopyDemandControls.hash preimages locations := by
  refine ⟨CopyDemandControls.run.hash_bound,CopyDemandControls.run.region_bound,
    CopyDemandControls.run.root_bound,?_,?_,?_⟩
  · decide
  · intro l member
    rcases List.mem_append.mp member with old | source
    · exact CopyDemandControls.run.bounded l old
    · change l ∈ [.data (.data (.root 1) 0) 0,.data (.root 1) 0,.root 1] at source
      simp only [List.mem_cons,List.not_mem_nil,or_false] at source
      rcases source with rfl | rfl | rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    rcases List.mem_append.mp member with old | source
    · intro p inside
      have basic := CopyDemandControls.run.covered l old p inside
      change p ∈ [.data 0,.data 8,.data 9,.data 10,.data 11] at basic
      simp only [List.mem_cons,List.not_mem_nil,or_false] at basic
      rcases basic with rfl | rfl | rfl | rfl | rfl <;> decide
    · change l ∈ [.data (.data (.root 1) 0) 0,.data (.root 1) 0,.root 1] at source
      simp only [List.mem_cons,List.not_mem_nil,or_false] at source
      rcases source with rfl | rfl | rfl <;> decide
private theorem old_owner : Represented CopyDemandControls.old allQueries CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  change q ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader,
    leaf 0 2,leaf 1 2,leaf 2 0,header 2,leaf 3 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [leaf,header,rootHeader,ix,Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some one = some word at observed; cases observed; rfl)
    | (intro word observed; change some (lengthWord 2 (by decide)) = some word at observed; cases observed; rfl)
    | (intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed)
private theorem source_owner : Represented CopyDemandControls.src (ClearDemands.demands CopyDemandControls.src)
    (.root 1) CopyDemandControls.store := by
  intro q member
  change q ∈ [leaf 0 0,header 0,rootHeader] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [leaf,header,rootHeader,ix,Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some zero = some word at observed; cases observed; rfl)
    | (intro word observed; change some one = some word at observed; cases observed; rfl)
private theorem separation : ∀ q ∈ allQueries, ∀ d ∈ CopyDemands.demands CopyDemandControls.old CopyDemandControls.src,
    d.location CopyDemandControls.root = q.location CopyDemandControls.root → d = q := by
  intro q member d written same
  change q ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader,
    leaf 0 2,leaf 1 2,leaf 2 0,header 2,leaf 3 0] at member
  change d ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,rootHeader] at written
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member written
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases written with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | cases same

/-- GENERAL theorem applied to ALL12 selected nested observations, including
inside payloads/headers, clear tails, older shadows and a failed query. Both
OLD owner relations and finite query-separation are independently inhabited. -/
theorem full_nested_owner :
    let log := CopyWrites.updates (N := 128) CopyDemandControls.old CopyDemandControls.src
      CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine
    let after := log.foldl (fun w op => write w op.1 op.2) CopyDemandControls.store
    Represented CopyDemandControls.copied allQueries CopyDemandControls.root after ∧
    Transport 128 CopyDemandControls.hash locations after
      (CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src
        CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine) :=
  represented_copy CopyDemandControls.old CopyDemandControls.src CopyDemandControls.permit allQueries
    CopyDemandControls.root (.root 1) CopyDemandControls.store CopyDemandControls.machine run old_owner source_owner
    (fun _ _ => rfl)
    (fun q member => List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨q,member,rfl⟩)))
    (fun q member => List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨q,member,rfl⟩)))
    (fun q member => List.mem_append.mpr (Or.inl (List.mem_map.mpr
      ⟨q,List.mem_append.mpr (Or.inl member),rfl⟩))) separation

/-- COMPLETE12 independent old/source/post graph query observations. Source
raw retained reads remain distinct from its processed live footprint. -/
theorem complete_graph_observations :
    (allQueries.map (Query.read CopyDemandControls.old),
     allQueries.map (Query.read CopyDemandControls.src),
     allQueries.map (Query.read CopyDemandControls.copied)) =
    ([some one,some one,some (lengthWord 2 (by decide)),some one,some one,some (lengthWord 2 (by decide)),some (lengthWord 2 (by decide)),some one,some one,some one,some (lengthWord 2 (by decide)),none],
     [some zero,some one,some one,some zero,some one,some one,some one,some one,some one,none,none,none],
     [some zero,some zero,some one,some zero,some zero,some zero,some one,some one,some one,some one,some (lengthWord 2 (by decide)),none]) := by rfl

/-- COMPLETE18 numeric old/actual generated output observations, unchanged
from the original nested fixture. The generic proof now supplies its INSIDE law. -/
theorem complete_numeric_observations :
    (CopyDemandControls.numericView CopyDemandControls.machine,
     CopyDemandControls.numericView (CopyWrites.numericCopy (N := 128) CopyDemandControls.old CopyDemandControls.src
       CopyDemandControls.root (.root 1) CopyDemandControls.hash CopyDemandControls.machine)) =
    ((lengthWord 2 (by decide),lengthWord 2 (by decide),lengthWord 2 (by decide),lengthWord 2 (by decide),one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (one,one,zero,lengthWord 2 (by decide),zero,zero,one,zero,zero,one,one,one,one,seven,one,one,zero,seven)) := by rfl

private def nodeFlag : TypeGraph.Path CopyWriteControls.recursiveGraph (.node 0) (.prim .bool) :=
  .cons (.field .here) .nil
private def nodeKids : TypeGraph.Path CopyWriteControls.recursiveGraph (.node 0) (.array (.node 0)) :=
  .cons (.field (.there .here)) .nil
private def childNode : TypeGraph.Path CopyWriteControls.recursiveGraph (.node 0) (.node 0) :=
  nodeKids.append (.cons (.index i0) .nil)
private def rootFlag : Query CopyWriteControls.recursiveGraph (.node 0) := .word nodeFlag
private def childFlag : Query CopyWriteControls.recursiveGraph (.node 0) := .word (childNode.append nodeFlag)
private def grandFlag : Query CopyWriteControls.recursiveGraph (.node 0) := .word (childNode.append (childNode.append nodeFlag))
private def rootKids : Query CopyWriteControls.recursiveGraph (.node 0) := .length nodeKids
private def childKids : Query CopyWriteControls.recursiveGraph (.node 0) := .length (childNode.append nodeKids)
private def grandKids : Query CopyWriteControls.recursiveGraph (.node 0) := .length (childNode.append (childNode.append nodeKids))
private def aliasQueries := CopyDemands.demands CopyWriteControls.oldNode CopyWriteControls.sourceNode
private def aliasPermit : CopyPermit CopyWriteControls.recursiveGraph (.node 0) :=
  CopyPermit.checked (fun _ => true) (by decide)
private theorem alias_old_owner : Represented CopyWriteControls.oldNode aliasQueries (.root 0) CopyWriteControls.overlapStore := by
  intro q member
  change q ∈ [rootFlag,childFlag,grandFlag,grandKids,childKids,rootKids] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [rootFlag,childFlag,grandFlag,rootKids,childKids,grandKids,nodeFlag,nodeKids,childNode,i0,
        Query.supported,PathSupported,StepSupported,TypeGraph.Path.append]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some zero = some word at observed; cases observed; rfl)
    | (intro word observed; change some one = some word at observed; cases observed; rfl)
private theorem alias_source_owner : Represented CopyWriteControls.sourceNode
    (ClearDemands.demands CopyWriteControls.sourceNode) CopyWriteControls.overlapSource CopyWriteControls.overlapStore := by
  intro q member
  apply CopyWriteControls.overlap_source_owner q
  change q ∈ [rootFlag,childFlag,childKids,rootKids] at member
  change q ∈ [rootFlag,rootKids,childFlag,childKids]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
  rcases member with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inl rfl)
private theorem alias_separation : ∀ q ∈ aliasQueries,
    ∀ d ∈ CopyDemands.demands CopyWriteControls.oldNode CopyWriteControls.sourceNode,
    d.location (.root 0) = q.location (.root 0) → d = q := by
  intro q member d written same
  change q ∈ [rootFlag,childFlag,grandFlag,grandKids,childKids,rootKids] at member
  change d ∈ [rootFlag,childFlag,grandFlag,grandKids,childKids,rootKids] at written
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member written
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases written with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | cases same
private theorem alias_source_covered : ∀ q ∈ ClearDemands.demands CopyWriteControls.sourceNode,
    q.location CopyWriteControls.overlapSource ∈ CopyWriteControls.overlapLocations := by
  intro q member
  change q ∈ [rootFlag,childFlag,childKids,rootKids] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact List.mem_map.mpr ⟨childFlag,by
      change childFlag ∈ [rootFlag,childFlag,grandFlag,grandKids,childKids,rootKids]
      exact List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  · exact List.mem_map.mpr ⟨grandFlag,by
      change grandFlag ∈ [rootFlag,childFlag,grandFlag,grandKids,childKids,rootKids]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩
  · exact List.mem_map.mpr ⟨grandKids,by
      change grandKids ∈ [rootFlag,childFlag,grandFlag,grandKids,childKids,rootKids]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),rfl⟩
  · exact List.mem_map.mpr ⟨childKids,by
      change childKids ∈ [rootFlag,childFlag,grandFlag,grandKids,childKids,rootKids]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),rfl⟩

/-- GENERAL post representation applies to a real captured descendant/ancestor
copy. Source read locations are actual destination writes, so no disjoint
source/destination premise is concealed. The GOOD run is the published fixture. -/
theorem alias_full_owner :
    let log := CopyWrites.updates (N := 128) CopyWriteControls.oldNode CopyWriteControls.sourceNode
      (.root 0) CopyWriteControls.overlapSource CopyWriteControls.overlapHash CopyWriteControls.overlapMachine
    let after := log.foldl (fun w op => write w op.1 op.2) CopyWriteControls.overlapStore
    Represented (recursiveCopy CopyWriteControls.oldNode CopyWriteControls.sourceNode) aliasQueries (.root 0) after ∧
    Transport 128 CopyWriteControls.overlapHash CopyWriteControls.overlapLocations after CopyWriteControls.overlapResult :=
  represented_copy CopyWriteControls.oldNode CopyWriteControls.sourceNode aliasPermit aliasQueries (.root 0)
    CopyWriteControls.overlapSource CopyWriteControls.overlapStore CopyWriteControls.overlapMachine
    CopyWriteControls.overlap_run alias_old_owner alias_source_owner (fun _ _ => rfl) alias_source_covered
    (fun q member => List.mem_map.mpr ⟨q,member,rfl⟩)
    (fun q member => List.mem_map.mpr ⟨q,member,rfl⟩) alias_separation

/-- COMPLETE6 old/source/post independent recursive graph observations and
COMPLETE7 initial/captured/wrong-incremental numeric observations. -/
theorem alias_complete_observations :
    (aliasQueries.map (Query.read CopyWriteControls.oldNode),
     aliasQueries.map (Query.read CopyWriteControls.sourceNode),
     aliasQueries.map (Query.read (recursiveCopy CopyWriteControls.oldNode CopyWriteControls.sourceNode)),
     CopyWriteControls.overlapView CopyWriteControls.overlapMachine,
     CopyWriteControls.overlapView CopyWriteControls.overlapResult,
     CopyWriteControls.overlapView CopyWriteControls.wrongIncremental) =
    ([some one,some zero,some one,some zero,some one,some one],
     [some zero,some one,none,none,some zero,some one],
     [some zero,some one,some zero,some zero,some zero,some one],
     (one,one,zero,one,one,zero,seven),
     (zero,one,one,zero,zero,zero,seven),
     (zero,zero,one,zero,zero,zero,seven)) := by rfl

/-- All four present/absent primitive slot combinations apply the GENERAL
slot output proof. Fresh garbage7 is initialized; old present true1 clears. -/
theorem slot_combinations :
    let q : Query CopyDemandControls.graph (.prim .bool) := .word .nil
    let absent : Slot CopyDemandControls.graph (.prim .bool) := .absent
    let yes : Slot CopyDemandControls.graph (.prim .bool) := .present (.prim (p := .bool) true)
    let no : Slot CopyDemandControls.graph (.prim .bool) := .present (.prim (p := .bool) false)
    (traceWord q (CopyWrites.slotWrites absent absent (fun _ => seven)) seven,
     traceWord q (CopyWrites.slotWrites absent yes (fun _ => one)) seven,
     traceWord q (CopyWrites.slotWrites yes absent (fun _ => seven)) one,
     traceWord q (CopyWrites.slotWrites yes no (fun _ => zero)) one) = (zero,one,zero,zero) := by
  let q : Query CopyDemandControls.graph (.prim .bool) := .word .nil
  let p : CopyPermit CopyDemandControls.graph (.prim .bool) := CopyPermit.checked (fun i => nomatch i) (by decide)
  have before : ∀ (value : Value CopyDemandControls.graph (.prim .bool)),
      Slot.present (.prim (p := .bool) true) = .present value → ∀ w, q.read value = some w → one = w := by
    intro value same w observed
    cases same
    change some one = some w at observed
    exact Option.some.inj observed
  have aa := slot_output (Slot.absent : Slot CopyDemandControls.graph (.prim .bool)) .absent p q seven
    (by intro value same; cases same) zero rfl
  have ay := slot_output (Slot.absent : Slot CopyDemandControls.graph (.prim .bool)) (.present (.prim (p := .bool) true)) p q seven
    (by intro value same; cases same) one rfl
  have ya := slot_output (Slot.present (.prim (p := .bool) true) : Slot CopyDemandControls.graph (.prim .bool)) .absent p q one before zero rfl
  have yn := slot_output (Slot.present (.prim (p := .bool) true) : Slot CopyDemandControls.graph (.prim .bool)) (.present (.prim (p := .bool) false)) p q one before zero rfl
  change (traceWord q _ seven,traceWord q _ seven,traceWord q _ one,traceWord q _ one) = _
  have first : traceWord q (CopyWrites.slotWrites (.absent : Slot CopyDemandControls.graph (.prim .bool)) .absent (fun _ => seven)) seven = zero := aa
  have third : traceWord q (CopyWrites.slotWrites (Slot.present (.prim (p := .bool) true) : Slot CopyDemandControls.graph (.prim .bool)) .absent (fun _ => seven)) one = zero := ya
  have second : traceWord q (CopyWrites.slotWrites (.absent : Slot CopyDemandControls.graph (.prim .bool))
      (.present (.prim true)) (fun _ => one)) seven = one := by
    change traceWord q [(q,zero),(q,one)] seven = one
    change traceWord q [(q,zero),(q,one)] seven = one at ay
    exact ay
  have fourth : traceWord q (CopyWrites.slotWrites (Slot.present (.prim true) : Slot CopyDemandControls.graph (.prim .bool))
      (.present (.prim false)) (fun _ => zero)) one = zero := by
    change traceWord q [(q,zero)] one = zero
    change traceWord q [(q,zero)] one = zero at yn
    exact yn
  rw [first,second,third,fourth]

private def twoSize : FixedSize := ⟨2,by decide⟩
private abbrev FixedNodes : TypeGraph.Ty 1 := .fixed (.array (.node 0)) twoSize
private def fixedOld (width : Nat → Index) (d : Nat) : Value CopyWriteControls.recursiveGraph FixedNodes :=
  .fixed (fun _ => .present (tree width true d))
private def fixedSrc (width : Nat → Index) (d : Nat) : Value CopyWriteControls.recursiveGraph FixedNodes :=
  .fixed (fun _ => .present (tree width false d))
private def fixedQuery (index : Index) (d : Nat) : Query CopyWriteControls.recursiveGraph FixedNodes :=
  .word (.cons (.fixed index) (deep d))
private def fixedPermit : CopyPermit CopyWriteControls.recursiveGraph FixedNodes :=
  CopyPermit.checked (fun _ => true) (by decide)

/-- Populated fixed arrays, nodes and runtime arrays compose at every finite
recursive depth. BOTH selected fixed children change true-to-false through the
GENERAL output theorem, with complete old/post graph and trace observations. -/
theorem fixed_recursive_combination (ow nw : Nat → Index)
    (op : ∀ d, 0 < (ow d).val) (np : ∀ d, 0 < (nw d).val) (d : Nat) :
    let old := fixedOld ow d
    let src := fixedSrc nw d
    let q0 := fixedQuery ⟨0,by decide⟩ d
    let q1 := fixedQuery ⟨1,by decide⟩ d
    let log := CopyWrites.queryWrites old src (fun q => (q.read src).getD zero)
    (q0.read old,q1.read old,q0.read (recursiveCopy old src),q1.read (recursiveCopy old src),
      traceWord q0 log one,traceWord q1 log one) =
      (some one,some one,some zero,some zero,zero,zero) := by
  obtain ⟨oldObserved,postObserved⟩ := recursive_observations ow nw op np d
  have old0 : (fixedQuery ⟨0,by decide⟩ d).read (fixedOld ow d) = some one := by
    change (((tree ow true d).find (deep d)).map Value.head).map (PrimTy.toWord (p := .bool)) = _
    rw [oldObserved]
    rfl
  have old1 : (fixedQuery ⟨1,by decide⟩ d).read (fixedOld ow d) = some one := old0
  have post0 : (fixedQuery ⟨0,by decide⟩ d).read (recursiveCopy (fixedOld ow d) (fixedSrc nw d)) = some zero := by
    change (((recursiveCopy (tree ow true d) (tree nw false d)).find (deep d)).map Value.head).map (PrimTy.toWord (p := .bool)) = _
    rw [postObserved]
    rfl
  have post1 : (fixedQuery ⟨1,by decide⟩ d).read (recursiveCopy (fixedOld ow d) (fixedSrc nw d)) = some zero := post0
  have trace0 := copy_output (fixedOld ow d) (fixedSrc nw d) fixedPermit (fixedQuery ⟨0,by decide⟩ d) one
    (by intro word observed; rw [old0] at observed; exact Option.some.inj observed) zero post0
  have trace1 := copy_output (fixedOld ow d) (fixedSrc nw d) fixedPermit (fixedQuery ⟨1,by decide⟩ d) one
    (by intro word observed; rw [old1] at observed; exact Option.some.inj observed) zero post1
  change traceWord (fixedQuery ⟨0,by decide⟩ d)
    (CopyWrites.queryWrites (fixedOld ow d) (fixedSrc nw d) (fun q => (q.read (fixedSrc nw d)).getD zero)) one = zero at trace0
  change traceWord (fixedQuery ⟨1,by decide⟩ d)
    (CopyWrites.queryWrites (fixedOld ow d) (fixedSrc nw d) (fun q => (q.read (fixedSrc nw d)).getD zero)) one = zero at trace1
  dsimp only
  rw [old0,old1,post0,post1,trace0,trace1]

/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.fixed_recursive_combination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixed_recursive_combination

/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.recursive_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursive_observations
/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.recursive_trace_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms recursive_trace_output
/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.absent_retained_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_retained_counterexample
/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.full_nested_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_nested_owner
/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.complete_graph_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_graph_observations
/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.complete_numeric_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric_observations
/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.alias_full_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms alias_full_owner
/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.alias_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms alias_complete_observations
/-- info: 'Solidity.Backend.StorageOps.CopyOutputControls.slot_combinations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms slot_combinations

end Solidity.Backend.StorageOps.CopyOutputControls

import Solidity.Backend.StorageOps.AggregatePopRootFrames
import Solidity.Backend.StorageOps.AggregatePopFrameControls

/-! Actual outer-root context and ancestor pop controls. Source graph values,
OLD owner evidence and GOOD runs are independently inhabited. -/
namespace Solidity.Backend.StorageOps.AggregatePopRootFrameControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open AggregatePopFrames AggregatePopRootFrames
private abbrev G := CopyDemandControls.graph
private abbrev Inner := CopyDemandControls.Inner
private abbrev Outer := CopyDemandControls.Outer
private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private def word (i : Fin 4) : Query G Inner := .word (.cons (.index (ix i)) .nil)
private def leaf (i j : Fin 4) : Query G Outer := .word (.cons (.index (ix i)) (.cons (.index (ix j)) .nil))
private def header (i : Fin 4) : Query G Outer := .length (.cons (.index (ix i)) .nil)
private def selected : List (Query G Inner) := [word 0,word 1,word 2,.length .nil]
private def groups : List (Index × List (Query G Inner)) :=
  [(ix 0,selected),(ix 2,[word 0,.length .nil]),(ix 3,[word 0])]
private def popped : Value G Outer := (recursivePop CopyDemandControls.old).getD CopyDemandControls.old
private noncomputable def final : WordStore := (AggregatePop.updates CopyDemandControls.old CopyDemandControls.root).foldl
  (fun w op => writeWord w (op.1.word 128 CopyDemandControls.hash) op.2) CopyDemandControls.machine
private noncomputable def after : Store := (AggregatePop.updates CopyDemandControls.old CopyDemandControls.root).foldl
  (fun w op => write w op.1 op.2) CopyDemandControls.store
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def zero : Semantics.Word := ClearDemands.zero
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private theorem targetBefore : Represented CopyDemandControls.old (AggregatePop.queries CopyDemandControls.old selected)
    CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  change q ∈ [.length .nil,leaf 1 0,leaf 1 1,leaf 1 2,header 1] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [leaf,header,Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)
private theorem contextBefore : Represented CopyDemandControls.old (contexts groups)
    CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  change q ∈ [leaf 0 0,leaf 0 1,leaf 0 2,header 0,leaf 2 0,header 2,leaf 3 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [leaf,header,Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)
    | (intro value observed; change (none : Option Semantics.Word) = some value at observed; cases observed)
private theorem targetCovered : ∀ q ∈ selected,
    q.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) ∈ CopyDemandControls.locations := by
  intro q member
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem contextCovered : ∀ q ∈ contexts groups, q.location CopyDemandControls.root ∈ CopyDemandControls.locations := by
  intro q member
  change q ∈ [leaf 0 0,leaf 0 1,leaf 0 2,header 0,leaf 2 0,header 2,leaf 3 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem written : ∀ q ∈ ClearDemands.slotDemands (AggregatePop.lastSlot CopyDemandControls.old),
    q.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) ∈ CopyDemandControls.locations := by
  intro q member
  change q ∈ [word 0,word 1,.length .nil] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private theorem separated : ∀ q ∈ selected, ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot CopyDemandControls.old),
    d.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) =
      q.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) → d = q := by
  intro q member d generated same
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  change d ∈ [word 0,word 1,.length .nil] at generated
  simp only [List.mem_cons,List.not_mem_nil,or_false] at generated
  rcases member with rfl | rfl | rfl | rfl <;> rcases generated with rfl | rfl | rfl
  all_goals first | rfl | cases same
private theorem headerSeparated : ∀ q ∈ selected,
    q.location (AggregatePop.childBase CopyDemandControls.old CopyDemandControls.root) ≠ CopyDemandControls.root := by
  intro q member
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem otherIndices : ∀ group ∈ groups, group.1.val ≠ CopyDemandControls.old.length.val - 1 := by
  intro group member
  simp only [groups,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private theorem noAlias : ∀ q ∈ contexts groups, ∀ op ∈ AggregatePop.updates CopyDemandControls.old CopyDemandControls.root,
    q.location CopyDemandControls.root ≠ op.1 := by
  intro q member op generated same
  change q ∈ [leaf 0 0,leaf 0 1,leaf 0 2,header 0,leaf 2 0,header 2,leaf 3 0] at member
  change op ∈ [(leaf 1 0 |>.location CopyDemandControls.root,zero),(leaf 1 1 |>.location CopyDemandControls.root,zero),
    (header 1 |>.location CopyDemandControls.root,zero),(CopyDemandControls.root,one)] at generated
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member generated
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases generated with rfl | rfl | rfl | rfl <;> cases same


private def size : FixedSize := ⟨2,by decide⟩
private abbrev RootTy : TypeGraph.Ty 0 := .fixed Outer size
private def slots (i : Fin 2) : Slot G Outer := if i.val = 0 then .present CopyDemandControls.old else .present CopyDemandControls.src
private def root : Value G RootTy := .fixed slots
private def dst : TypeGraph.Path G RootTy Outer := .cons (.fixed (ix 0)) .nil
private def sibling : TypeGraph.Path G RootTy Outer := .cons (.fixed (ix 1)) .nil
private def result : Value G RootTy := (popAt root dst).getD root
private def siblingQueries : List (Query G Outer) := [leaf 0 0,header 0,.length .nil,header 3]
private def outside := siblingQueries.map (Query.prefix sibling)
private def insideQueries := AggregatePop.queries CopyDemandControls.old selected ++ contexts groups
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 8,.data 9,.data 10,.data 11,.data 1,.data 16]
private def extras : List Solidity.Storage.Loc :=
  [.root 1,.data (.root 1) 0,.data (.data (.root 1) 0) 0,.data (.root 1) 3,.data (.data (.root 0) 2) 1]
private noncomputable def locations := CopyDemandControls.locations ++ extras
private theorem run : FiniteRun 128 4 2 CopyDemandControls.hash preimages locations := by
  refine ⟨CopyDemandControls.run.hash_bound,CopyDemandControls.run.region_bound,CopyDemandControls.run.root_bound,?_,?_,?_⟩
  · decide
  · intro l member
    rcases List.mem_append.mp member with old | extra
    · exact CopyDemandControls.run.bounded l old
    · simp only [extras,List.mem_cons,List.not_mem_nil,or_false] at extra
      rcases extra with rfl | rfl | rfl | rfl | rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    rcases List.mem_append.mp member with old | extra
    · intro p member
      have basic := CopyDemandControls.run.covered l old p member
      change p ∈ [.data 0,.data 8,.data 9,.data 10,.data 11] at basic
      simp only [List.mem_cons,List.not_mem_nil,or_false] at basic
      rcases basic with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [extras,List.mem_cons,List.not_mem_nil,or_false] at extra
      rcases extra with rfl | rfl | rfl | rfl | rfl <;> decide
private theorem arrayBefore : Represented CopyDemandControls.old insideQueries CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  rcases List.mem_append.mp member with target | context
  · exact targetBefore q target
  · exact contextBefore q context
private theorem beforeInside : Represented root (insideQueries.map (Query.prefix dst)) CopyDemandControls.root CopyDemandControls.store := by
  exact Represented.prefix dst rfl (by change 0 < size.val ∧ True; decide) arrayBefore
private theorem sourceBefore : Represented CopyDemandControls.src siblingQueries (.root 1) CopyDemandControls.store := by
  intro q member
  simp only [siblingQueries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [leaf,header,Query.supported,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro value observed; change some zero = some value at observed; cases observed; rfl)
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change (none : Option Semantics.Word) = some value at observed; cases observed)
private theorem beforeOutside : Represented root outside CopyDemandControls.root CopyDemandControls.store := by
  exact Represented.prefix sibling rfl (by change 1 < size.val ∧ True; decide) sourceBefore
private theorem outsideApart : ∀ q ∈ outside, q.apart dst := by
  intro q member
  obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp member
  simp only [siblingQueries,List.mem_cons,List.not_mem_nil,or_false] at childMember
  rcases childMember with rfl | rfl | rfl | rfl
  all_goals exact Apart.fork (StepApart.fixed (ix 0) (ix 1) (by decide)) _ _
private theorem outsideCovered : ∀ q ∈ outside, q.location CopyDemandControls.root ∈ locations := by
  intro q member
  obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp member
  simp only [siblingQueries,List.mem_cons,List.not_mem_nil,or_false] at childMember
  rcases childMember with rfl | rfl | rfl | rfl <;> apply List.mem_append.mpr <;> right <;> decide
private theorem outsideNonalias : ∀ q ∈ outside, ∀ op ∈ AggregatePop.updates CopyDemandControls.old (pathLoc dst CopyDemandControls.root),
    q.location CopyDemandControls.root ≠ op.1 := by
  intro q member op generated same
  obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp member
  simp only [siblingQueries,List.mem_cons,List.not_mem_nil,or_false] at childMember
  change op ∈ [((leaf 1 0).location CopyDemandControls.root,zero),((leaf 1 1).location CopyDemandControls.root,zero),
    ((header 1).location CopyDemandControls.root,zero),(CopyDemandControls.root,one)] at generated
  simp only [List.mem_cons,List.not_mem_nil,or_false] at generated
  rcases childMember with rfl | rfl | rfl | rfl <;> rcases generated with rfl | rfl | rfl | rfl <;> cases same

/-- GENERAL combined root certificate with ALL target/context queries and
an outside sibling, including a supported failed header read/raw garbage7. -/
theorem combined_certificate :
    AggregatePop.execute (N := 128) CopyDemandControls.old CopyDemandControls.hash (pathLoc dst CopyDemandControls.root)
      CopyDemandControls.machine = some final ∧
    Represented result ((insideQueries.map (Query.prefix dst)) ++ outside) CopyDemandControls.root after ∧
    Transport 128 CopyDemandControls.hash locations after final := by
  obtain ⟨child,actual,changed,readback,executed,represented,transported⟩ := complete_at_context root result dst CopyDemandControls.old rfl rfl
    selected groups outside CopyDemandControls.root CopyDemandControls.store CopyDemandControls.machine run beforeInside beforeOutside
    (fun _ _ => rfl) (List.mem_append.mpr (Or.inl (by decide)))
    (fun q member => List.mem_append.mpr (Or.inl (targetCovered q member)))
    (fun q member => List.mem_append.mpr (Or.inl (contextCovered q member))) outsideCovered
    (fun q member => List.mem_append.mpr (Or.inl (written q member))) separated headerSeparated otherIndices noAlias outsideApart outsideNonalias
  have expected : AggregatePop.execute (N := 128) CopyDemandControls.old CopyDemandControls.hash (pathLoc dst CopyDemandControls.root)
      CopyDemandControls.machine = some final := rfl
  have equal := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,represented,transported⟩
private def originalQueries := CopyDemandControls.demands ++ CopyDemandControls.queries
private def rootView (v : Value G RootTy) :=
  ((originalQueries.map (Query.prefix dst)) ++ outside).map (fun q => q.read v)
/-- COMPLETE selected ROOT vector: original12 plus FOUR outside queries,
including failure. COMPLETE original18 numeric words plus raw outside19. -/
theorem complete_observations :
    (rootView root,rootView result,(CopyDemandControls.numericView CopyDemandControls.machine,CopyDemandControls.machine 19),
      (CopyDemandControls.numericView final,final 19)) =
    ([some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some two,none,some zero,some one,some one,none],
     [some one,some one,some two,some zero,some zero,some zero,some one,some one,some one,some one,some two,none,some zero,some one,some one,none],
     ((two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),seven),
     ((one,two,zero,two,one,one,one,zero,zero,one,one,one,one,seven,one,one,zero,seven),seven)) := rfl

/-- Outside sibling identity is actual root.find equality; the failed query
is None with raw7, never a zero-storage assertion. -/
theorem sibling_identity : root.find sibling = some CopyDemandControls.src ∧
    result.find sibling = some CopyDemandControls.src ∧
    ((header 3).prefix sibling).read root = none ∧ ((header 3).prefix sibling).read result = none ∧
    CopyDemandControls.machine 19 = seven ∧ final 19 = seven := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩


private def ancestorIndex (retained : Bool) : Index := if retained then ix 2 else ix 0
private def ancestorPre (retained : Bool) : TypeGraph.Path G Outer Inner := .cons (.index (ancestorIndex retained)) .nil
private def inner : Value G Inner := (CopyDemandControls.old.slots ⟨0,by decide⟩).getD (Value.dflt Inner)
private def ancestorResult (retained : Bool) : Value G Outer := (popAt CopyDemandControls.old (ancestorPre retained)).getD CopyDemandControls.old
private noncomputable def ancestorFinal (retained : Bool) : WordStore :=
  (AggregatePop.updates inner (pathLoc (ancestorPre retained) CopyDemandControls.root)).foldl
    (fun w op => writeWord w (op.1.word 128 CopyDemandControls.hash) op.2) CopyDemandControls.machine
private theorem beforeCurrent (retained : Bool) : Represented CopyDemandControls.old
    (([.length .nil] : List (Query G Inner)).map (Query.prefix (ancestorPre retained))) CopyDemandControls.root CopyDemandControls.store := by
  cases retained <;> intro q member
  all_goals have same := List.mem_singleton.mp member
  all_goals subst q
  all_goals refine ⟨?_,⟨by decide,by decide⟩,?_⟩
  all_goals first
    | (change (_ < lmax ∧ True); decide)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)
private theorem beforeAncestor : Represented CopyDemandControls.old [.length .nil] CopyDemandControls.root CopyDemandControls.store := by
  intro q member
  have same := List.mem_singleton.mp member
  subst q
  refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
  intro value observed; change some two = some value at observed; cases observed; rfl
private theorem ancestorUpdates (retained : Bool) :
    AggregatePop.updates inner (pathLoc (ancestorPre retained) CopyDemandControls.root) =
      [(.data (pathLoc (ancestorPre retained) CopyDemandControls.root) 1,zero),
       (pathLoc (ancestorPre retained) CopyDemandControls.root,one)] := by cases retained <;> rfl

/-- GENERAL ancestor law instantiated for BOTH a live index0 and retained but
non-live index2. Captured logical reachability is not ordinary Source indexing. -/
theorem ancestor_certificate (retained : Bool) :
    AggregatePop.execute (N := 128) inner CopyDemandControls.hash (pathLoc (ancestorPre retained) CopyDemandControls.root)
      CopyDemandControls.machine = some (ancestorFinal retained) ∧
    Represented (ancestorResult retained) [.length .nil] CopyDemandControls.root
      ((AggregatePop.updates inner (pathLoc (ancestorPre retained) CopyDemandControls.root)).foldl
        (fun w op => write w op.1 op.2) CopyDemandControls.store) ∧
    Transport 128 CopyDemandControls.hash locations
      ((AggregatePop.updates inner (pathLoc (ancestorPre retained) CopyDemandControls.root)).foldl
        (fun w op => write w op.1 op.2) CopyDemandControls.store) (ancestorFinal retained) := by
  obtain ⟨actual,executed,represented,transported⟩ := header_frame_at CopyDemandControls.old (ancestorResult retained)
    (ancestorPre retained) inner (by cases retained <;> rfl) (by cases retained <;> rfl)
    .nil (ancestorIndex retained) .nil rfl CopyDemandControls.root CopyDemandControls.store CopyDemandControls.machine run
    (beforeCurrent retained) beforeAncestor (fun _ _ => rfl)
    (by cases retained <;> exact List.mem_append.mpr (Or.inl (by decide)))
    (List.mem_append.mpr (Or.inl (by decide))) (by
      intro d member
      change d ∈ [Query.word .nil] at member
      have same := List.mem_singleton.mp member
      subst d
      cases retained <;> decide) (by
      intro op member
      rw [ancestorUpdates] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> intro same <;> cases retained <;> cases same)
  have expected : AggregatePop.execute (N := 128) inner CopyDemandControls.hash
      (pathLoc (ancestorPre retained) CopyDemandControls.root) CopyDemandControls.machine = some (ancestorFinal retained) := by
    cases retained <;> rfl
  have same := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,represented,transported⟩
private def ancestorQueries := originalQueries ++ [leaf 2 1]
private def ancestorView (v : Value G Outer) := ancestorQueries.map (fun q => q.read v)
/-- COMPLETE original12 plus changed retained-target leaf; original18 numeric
words plus raw outside19. BOTH actual ancestor executions are fully pinned. -/
theorem ancestor_complete_observations :
    (ancestorView CopyDemandControls.old,ancestorView (ancestorResult false),ancestorView (ancestorResult true),
      (CopyDemandControls.numericView CopyDemandControls.machine,CopyDemandControls.machine 19),
      (CopyDemandControls.numericView (ancestorFinal false),ancestorFinal false 19),
      (CopyDemandControls.numericView (ancestorFinal true),ancestorFinal true 19)) =
    ([some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some two,none,some one],
     [some one,some zero,some one,some one,some one,some two,some two,some one,some one,some one,some two,none,some one],
     [some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some one,none,some zero],
     ((two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),seven),
     ((two,one,two,two,one,zero,one,one,one,one,one,one,one,seven,one,one,zero,seven),seven),
     ((two,two,two,one,one,one,one,one,one,one,one,zero,one,seven,one,one,zero,seven),seven)) := rfl

/-- Exact ancestor length/extent, child metadata and raw-versus-live aliases.
The child last word changes, its older shadow survives, no outer header changes. -/
theorem ancestor_alias_observations (retained : Bool) :
    let old := CopyDemandControls.old
    let next := ancestorResult retained
    let pre := ancestorPre retained
    let last : TypeGraph.Path G Outer (.prim .bool) := pre.append (.cons (.index (ix 1)) .nil)
    let shadow : TypeGraph.Path G Outer (.prim .bool) := pre.append (.cons (.index (ix 2)) .nil)
    (old.length.val,old.extent.val,next.length.val,next.extent.val,
     (old.find pre).map (fun a => (a.length.val,a.extent.val)),
     (next.find pre).map (fun a => (a.length.val,a.extent.val)),
     old.observe last,next.observe last,old.observe shadow,next.observe shadow,
     (last.readLive Value.dflt old).map Value.head,(last.readLive Value.dflt next).map Value.head) =
      (2,3,2,3,some (2,3),some (1,3),some true,some false,some true,some true,
       (if retained then none else some true),none) := by cases retained <;> rfl

private noncomputable def wrongAncestor (retained : Bool) : WordStore := writeWord (ancestorFinal retained) 0 zero
/-- Wrong parent-header clearing differs in COMPLETE numeric vectors even
though the correct graph ancestor header remains length2/extent3. -/
theorem wrong_ancestor_negative :
    ((CopyDemandControls.numericView (wrongAncestor false),wrongAncestor false 19),
      (CopyDemandControls.numericView (wrongAncestor true),wrongAncestor true 19)) =
    (((zero,one,two,two,one,zero,one,one,one,one,one,one,one,seven,one,one,zero,seven),seven),
     ((zero,two,two,one,one,one,one,one,one,one,one,zero,one,seven,one,one,zero,seven),seven)) := rfl


/-- The actual numeric outside-frame law also protects the supported failed
query's raw word. PUBLIC None representation alone would not imply this. -/
theorem failed_numeric_frame : final 19 = CopyDemandControls.machine 19 := by
  apply AggregatePop.outside CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root
    CopyDemandControls.machine final rfl rfl 19
  intro op member
  change op ∈ [((leaf 1 0).location CopyDemandControls.root,zero),((leaf 1 1).location CopyDemandControls.root,zero),
    ((header 1).location CopyDemandControls.root,zero),(CopyDemandControls.root,one)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private noncomputable def wrongSibling : WordStore := writeWord final 1 zero
private noncomputable def wrongFailed : WordStore := writeWord final 19 zero
/-- COMPLETE numeric views discriminate corrupting a successful sibling header
from silently zeroing an unrepresented failed-read word. -/
theorem wrong_outside_negatives :
    ((CopyDemandControls.numericView wrongSibling,wrongSibling 19),
      (CopyDemandControls.numericView wrongFailed,wrongFailed 19)) =
    (((one,two,zero,two,one,one,one,zero,zero,one,one,one,one,seven,zero,one,zero,seven),seven),
     ((one,two,zero,two,one,one,one,zero,zero,one,one,one,one,seven,one,one,zero,seven),zero)) := rfl

/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrameControls.combined_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms combined_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrameControls.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrameControls.sibling_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms sibling_identity
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrameControls.ancestor_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ancestor_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrameControls.ancestor_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ancestor_complete_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrameControls.ancestor_alias_observations' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms ancestor_alias_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrameControls.wrong_ancestor_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_ancestor_negative
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrameControls.failed_numeric_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failed_numeric_frame
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrameControls.wrong_outside_negatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_outside_negatives
end Solidity.Backend.StorageOps.AggregatePopRootFrameControls

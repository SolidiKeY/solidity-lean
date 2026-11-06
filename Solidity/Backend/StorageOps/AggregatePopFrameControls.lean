import Solidity.Backend.StorageOps.AggregatePopFrames
import Solidity.Backend.StorageOps.PopPush
import Solidity.Backend.StorageOps.AggregatePopControls

/-! Full selected aggregate pop fixture context and physical-alias negative.
All original C40 ordered observations are reused unchanged. -/
namespace Solidity.Backend.StorageOps.AggregatePopFrameControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open AggregatePopFrames
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

/-- ALL12 original root queries, including last-slot changes, live siblings,
older shadows and a failed out-of-extent read, share one actual numeric pop. -/
theorem whole_fixture_certificate : AggregatePop.execute (N := 128) CopyDemandControls.old CopyDemandControls.hash
    CopyDemandControls.root CopyDemandControls.machine = some final ∧
    Represented popped (CopyDemandControls.demands ++ CopyDemandControls.queries) CopyDemandControls.root after ∧
    Transport 128 CopyDemandControls.hash CopyDemandControls.locations after final := by
  obtain ⟨actual,executed,represented,transported⟩ := complete_all CopyDemandControls.old popped rfl selected groups
    CopyDemandControls.root CopyDemandControls.store CopyDemandControls.machine CopyDemandControls.run
    targetBefore contextBefore (fun _ _ => rfl) (by decide) targetCovered contextCovered written separated headerSeparated otherIndices noAlias
  have expected : AggregatePop.execute (N := 128) CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root
      CopyDemandControls.machine = some final := rfl
  have equal := Option.some.inj (executed.symm.trans expected)
  subst actual
  refine ⟨executed,?_,transported⟩
  intro q member
  change q ∈ [leaf 0 0,leaf 0 1,header 0,leaf 1 0,leaf 1 1,header 1,.length .nil,
    leaf 0 2,leaf 1 2,leaf 2 0,header 2,leaf 3 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply represented
  all_goals change _ ∈ [.length .nil,leaf 1 0,leaf 1 1,leaf 1 2,header 1,leaf 0 0,leaf 0 1,leaf 0 2,header 0,leaf 2 0,header 2,leaf 3 0]
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,true_or,or_true]
  all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl))

/-- Preserve the COMPLETE original observation vectors, not a reduced context
projection. C40 controls and their expected verdicts remain unchanged. -/
theorem complete_observations :
    let view := fun v : Value G Outer => (CopyDemandControls.demands ++ CopyDemandControls.queries).map (fun q => q.read v)
    (view CopyDemandControls.old,view popped,CopyDemandControls.numericView CopyDemandControls.machine,CopyDemandControls.numericView final) =
    ([some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some two,none],
     [some one,some one,some two,some zero,some zero,some zero,some one,some one,some one,some one,some two,none],
     (two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (one,two,zero,two,one,one,one,zero,zero,one,one,one,one,seven,one,one,zero,seven)) :=
  AggregatePopControls.complete_observations


private def size : FixedSize := ⟨2,by decide⟩
private abbrev Fixed : TypeGraph.Ty 0 := TypeGraph.Ty.fixed (.prim .bool) size
private def fixedOld : Value G (.array Fixed) := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun _ => .present (.fixed (fun _ => .present (.prim true))))
private def fixedResult : Value G (.array Fixed) := (recursivePop fixedOld).getD fixedOld
private def fixedWord (i : Fin 4) : Query G Fixed := .word (.cons (.fixed (ix i)) .nil)
private def fixedSelected : List (Query G Fixed) := [fixedWord 0,fixedWord 1]
private def fixedGroups : List (Index × List (Query G Fixed)) := [(ix 0,fixedSelected),(ix 2,fixedSelected)]
private def fixedQueries := AggregatePop.queries fixedOld fixedSelected ++ contexts fixedGroups
private def fixedHash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 8 else 0
private def fixedRoot : Solidity.Storage.Loc := .root 0
private def fixedP : List Solidity.Storage.Pre := [.data 0]
private def fixedLocations : List Solidity.Storage.Loc :=
  [fixedRoot,.data fixedRoot 0,.data fixedRoot 1,.data fixedRoot 2,.data fixedRoot 3,.data fixedRoot 4,.data fixedRoot 5]
private def fixedMachine : WordStore := fun a => if a = 0 then two else if 8 ≤ a ∧ a < 14 then one else seven
private def fixedStore : Store := fun l => fixedMachine (l.word 32 fixedHash)
private noncomputable def fixedFinal : WordStore := (AggregatePop.updates fixedOld fixedRoot).foldl
  (fun w op => writeWord w (op.1.word 32 fixedHash) op.2) fixedMachine
private theorem fixedRun : FiniteRun 32 8 1 fixedHash fixedP fixedLocations := by
  constructor
  · intro p; simp only [fixedHash]; split <;> decide
  · decide
  · decide
  · decide
  · intro l member
    simp only [fixedLocations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [fixedRoot,Loc.Bounded] <;> decide
  · intro l member
    simp only [fixedLocations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private def fixedLeaf (outer inner : Fin 4) : Query G (.array Fixed) :=
  (fixedWord inner).prefix (indexPath (ix outer))
private theorem fixedBefore : Represented fixedOld fixedQueries fixedRoot fixedStore := by
  intro q member
  change q ∈ [.length .nil,fixedLeaf 1 0,fixedLeaf 1 1,fixedLeaf 0 0,fixedLeaf 0 1,fixedLeaf 2 0,fixedLeaf 2 1] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (change (_ < lmax ∧ _ < size.val ∧ True); decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)

/-- A second GOOD-region application with fixed aggregate elements. All six
retained primitive cells and header have public representation after pop. -/
theorem fixed_certificate : AggregatePop.execute (N := 32) fixedOld fixedHash fixedRoot fixedMachine = some fixedFinal ∧
    Represented fixedResult fixedQueries fixedRoot
      ((AggregatePop.updates fixedOld fixedRoot).foldl (fun w op => write w op.1 op.2) fixedStore) := by
  obtain ⟨actual,executed,represented,_⟩ := complete_all fixedOld fixedResult rfl fixedSelected fixedGroups
    fixedRoot fixedStore fixedMachine fixedRun
    (by intro q member; exact fixedBefore q (List.mem_append.mpr (Or.inl member)))
    (by intro q member; exact fixedBefore q (List.mem_append.mpr (Or.inr member)))
    (fun _ _ => rfl) (by decide) (by
      intro q member
      simp only [fixedSelected,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> decide) (by
      intro q member
      change q ∈ [fixedLeaf 0 0,fixedLeaf 0 1,fixedLeaf 2 0,fixedLeaf 2 1] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide) (by
      intro q member
      change q ∈ fixedSelected at member
      simp only [fixedSelected,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> decide) (by
      intro q member d generated same
      change d ∈ fixedSelected at generated
      simp only [fixedSelected,List.mem_cons,List.not_mem_nil,or_false] at member generated
      rcases member with rfl | rfl <;> rcases generated with rfl | rfl
      all_goals first | rfl | cases same) (by
      intro q member
      simp only [fixedSelected,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> decide) (by
      intro group member
      simp only [fixedGroups,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> decide) (by
      intro q member op generated same
      change q ∈ [fixedLeaf 0 0,fixedLeaf 0 1,fixedLeaf 2 0,fixedLeaf 2 1] at member
      change op ∈ [((fixedLeaf 1 0).location fixedRoot,zero),((fixedLeaf 1 1).location fixedRoot,zero),(fixedRoot,one)] at generated
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member generated
      rcases member with rfl | rfl | rfl | rfl <;> rcases generated with rfl | rfl | rfl <;> cases same)
  have expected : AggregatePop.execute (N := 32) fixedOld fixedHash fixedRoot fixedMachine = some fixedFinal := rfl
  have equal := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,represented⟩
private def fixedGraphView (v : Value G (.array Fixed)) :=
  (v.length.val,v.extent.val,[fixedLeaf 0 0,fixedLeaf 0 1,fixedLeaf 1 0,fixedLeaf 1 1,fixedLeaf 2 0,fixedLeaf 2 1,fixedLeaf 0 2].map (fun q => q.read v))
private def fixedNumericView (m : WordStore) := (m 0,m 8,m 9,m 10,m 11,m 12,m 13,m 14,m 31)
/-- COMPLETE fixed fixture: header/extent, six retained cells, malformed suffix
and nine numeric words including outside sentinels. -/
theorem fixed_complete_observations :
    (fixedGraphView fixedOld,fixedGraphView fixedResult,fixedNumericView fixedMachine,fixedNumericView fixedFinal) =
    ((2,3,[some one,some one,some one,some one,some one,some one,none]),
     (1,3,[some one,some one,some zero,some zero,some one,some one,none]),
     (two,one,one,one,one,one,one,seven,seven),
     (one,one,one,zero,zero,one,one,seven,seven)) := rfl

/-- GOOD regions do not imply typed-query injectivity: malformed index0/fixed2
is logically framed but shares the written word with valid index1/fixed0. -/
theorem failed_query_alias_negative :
    (fixedLeaf 0 2).read fixedResult = (fixedLeaf 0 2).read fixedOld ∧
    (fixedLeaf 0 2).read fixedOld = none ∧ (fixedLeaf 0 2).read fixedResult = none ∧
    (fixedLeaf 0 2).location fixedRoot = (fixedLeaf 1 0).location fixedRoot ∧
    fixedMachine (((fixedLeaf 0 2).location fixedRoot).word 32 fixedHash) = one ∧
    fixedFinal (((fixedLeaf 0 2).location fixedRoot).word 32 fixedHash) = zero ∧
    ¬ (fixedLeaf 0 2).supported := by
  refine ⟨read_other fixedOld fixedResult rfl (ix 0) (by decide) (fixedWord 2),rfl,rfl,rfl,rfl,rfl,?_⟩
  change ¬ (0 < lmax ∧ 2 < size.val ∧ True)
  decide

/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.whole_fixture_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms whole_fixture_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.fixed_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixed_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.fixed_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixed_complete_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.failed_query_alias_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failed_query_alias_negative
private def reused : Value G Outer := (operationPush popped).getD popped
private noncomputable def reusedMachine : WordStore := writeWord final 0 two
private noncomputable def reusedStore : Store := write after CopyDemandControls.root two

/-- General evolving certificate applied to the independently GOOD nested
fixture: the intermediate relation comes from pop, never a caller postpremise. -/
theorem pop_push_certificate : PopPush.execute (N := 128) CopyDemandControls.old CopyDemandControls.hash
    CopyDemandControls.root CopyDemandControls.machine = some reusedMachine ∧
    Represented reused (AggregatePop.queries CopyDemandControls.old selected ++ contexts groups) CopyDemandControls.root reusedStore ∧
    Transport 128 CopyDemandControls.hash CopyDemandControls.locations reusedStore reusedMachine := by
  obtain ⟨actual,executed,owner,transported⟩ := PopPush.complete_numeric CopyDemandControls.old popped reused rfl rfl rfl selected groups
    CopyDemandControls.root CopyDemandControls.store CopyDemandControls.machine CopyDemandControls.run targetBefore contextBefore
    (fun _ _ => rfl) (by decide) targetCovered contextCovered written separated headerSeparated otherIndices noAlias
  have expected : PopPush.execute (N := 128) CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root CopyDemandControls.machine = some reusedMachine := rfl
  have same := Option.some.inj (executed.symm.trans expected)
  subst actual
  exact ⟨executed,owner,transported⟩
private def popPushView (v : Value G Outer) := (CopyDemandControls.demands ++ CopyDemandControls.queries).map (fun q => q.read v)

/-- COMPLETE original12 graph/18 numeric observations at ALL THREE stages.
Restoring the outer header does NOT restore cleared inner payload/header. -/
theorem pop_push_complete_observations :
    (popPushView CopyDemandControls.old,popPushView popped,popPushView reused,
      CopyDemandControls.numericView CopyDemandControls.machine,CopyDemandControls.numericView final,CopyDemandControls.numericView reusedMachine) =
    ([some one,some one,some two,some one,some one,some two,some two,some one,some one,some one,some two,none],
     [some one,some one,some two,some zero,some zero,some zero,some one,some one,some one,some one,some two,none],
     [some one,some one,some two,some zero,some zero,some zero,some two,some one,some one,some one,some two,none],
     (two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (one,two,zero,two,one,one,one,zero,zero,one,one,one,one,seven,one,one,zero,seven),
     (two,two,zero,two,one,one,one,zero,zero,one,one,one,one,seven,one,one,zero,seven)) := rfl

/-- Outer alias shrinks/regrows while its inner cleared length remains0.
Older retained shadows remain raw true and non-live; no heap identity assertion. -/
theorem pop_push_aliases :
    let outer : TypeGraph.Path G Outer Inner := .cons (.index (ix 1)) .nil
    let payload : TypeGraph.Path G Outer (.prim .bool) := .cons (.index (ix 1)) (.cons (.index (ix 0)) .nil)
    let shadow : TypeGraph.Path G Outer (.prim .bool) := .cons (.index (ix 1)) (.cons (.index (ix 2)) .nil)
    ((outer.readLive Value.dflt CopyDemandControls.old).map (fun v => v.length.val),
      (outer.readLive Value.dflt popped).map (fun v => v.length.val),(outer.readLive Value.dflt reused).map (fun v => v.length.val),
      CopyDemandControls.old.observe payload,popped.observe payload,reused.observe payload,
      (payload.readLive Value.dflt reused).map Value.head,CopyDemandControls.old.observe shadow,popped.observe shadow,reused.observe shadow,
      (shadow.readLive Value.dflt reused).map Value.head) =
    (some 2,none,some 0,some true,some false,some false,none,some true,some true,some true,none) := rfl

/-- Wrong identity implementation differs in COMPLETE original vectors even
though the final outer header is restored. -/
theorem pop_push_identity_negative : popPushView reused ≠ popPushView CopyDemandControls.old ∧
    reusedMachine 40 ≠ CopyDemandControls.machine 40 := by
  constructor
  · intro same
    have different := congrArg (fun xs => xs[3]?) same
    change (some (some zero) : Option (Option Semantics.Word)) = some (some one) at different
    exact (by decide : (some (some zero) : Option (Option Semantics.Word)) ≠ some (some one)) different
  · change zero ≠ one; decide

/-- Actual two-step outside frame, including the failed query's garbage7. -/
theorem pop_push_outside_frame : reusedMachine 56 = CopyDemandControls.machine 56 :=
  PopPush.outside CopyDemandControls.old CopyDemandControls.hash CopyDemandControls.root CopyDemandControls.machine reusedMachine rfl rfl 56 (by
    intro op member
    change op ∈ [(leaf 1 0 |>.location CopyDemandControls.root,zero),(leaf 1 1 |>.location CopyDemandControls.root,zero),
      (header 1 |>.location CopyDemandControls.root,zero),(CopyDemandControls.root,one)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide)

/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.pop_push_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_push_certificate
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.pop_push_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_push_complete_observations
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.pop_push_aliases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pop_push_aliases
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.pop_push_identity_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_push_identity_negative
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrameControls.pop_push_outside_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_push_outside_frame

end Solidity.Backend.StorageOps.AggregatePopFrameControls

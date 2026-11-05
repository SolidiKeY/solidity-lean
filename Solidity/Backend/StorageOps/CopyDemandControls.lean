import Solidity.Backend.StorageOps.CopyDemands

/-! Complete nested runtime copy observations and represented outside-demand
numeric frames. The concrete write fixture is not a general target copy compiler;
inside-payload realization remains a separate obligation. -/
namespace Solidity.Backend.StorageOps.CopyDemandControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
def graph : Schema 0 where
  origin := "v10-copy-demand-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
abbrev Inner : TypeGraph.Ty 0 := .array (.prim .bool)
abbrev Outer : TypeGraph.Ty 0 := .array Inner
private def innerOld : Value graph Inner :=
  .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def innerSource : Value graph Inner :=
  .array ⟨3,by decide⟩ ⟨1,by decide⟩ (by decide) (fun i => .present (.prim (i.val != 0)))
def old : Value graph Outer :=
  .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide) (fun _ => .present innerOld)
def src : Value graph Outer :=
  .array ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present innerSource)
def copied : Value graph Outer := recursiveCopy old src
private def innerPath (i : Index) : TypeGraph.Path graph Outer Inner := .cons (.index i) .nil
private def leaf (i j : Index) : TypeGraph.Path graph Outer (.prim .bool) :=
  .cons (.index i) (.cons (.index j) .nil)
private def innerView (v : Value graph Outer) (i : Index) :=
  ((v.find (innerPath i)).map (fun a => (a.length.val,a.extent.val)),
    v.observe (leaf i (ix 0)),v.observe (leaf i (ix 1)),v.observe (leaf i (ix 2)),
    ((leaf i (ix 0)).readLive Value.dflt v).map Value.head)
private def view (v : Value graph Outer) := (v.length.val,v.extent.val,
  innerView v (ix 0),innerView v (ix 1),innerView v (ix 2),innerView v (ix 3))
def demands : List (Query graph Outer) := CopyDemands.demands old src
def root : Solidity.Storage.Loc := .root 0
private def innerLoc (i : Nat) : Solidity.Storage.Loc := .data root i
private def leafLoc (i j : Nat) : Solidity.Storage.Loc := .data (innerLoc i) j
def queries : List (Query graph Outer) := [.word (leaf (ix 0) (ix 2)),
  .word (leaf (ix 1) (ix 2)),.word (leaf (ix 2) (ix 0)),.length (innerPath (ix 2)),
  .word (leaf (ix 3) (ix 0))]
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
def hash (p : Solidity.Storage.Pre) : Nat :=
  if p = .data 0 then 8 else if p = .data 8 then 32 else if p = .data 9 then 40 else
  if p = .data 10 then 48 else if p = .data 11 then 56 else if p = .data 1 then 16 else
  if p = .data 16 then 64 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 8,.data 9,.data 10,.data 11]
noncomputable def locations : List Solidity.Storage.Loc :=
  (demands ++ queries).map (fun q => q.location root)
def machine : WordStore := fun n =>
  if n = 0 ∨ n = 8 ∨ n = 9 ∨ n = 10 then two else
  if n = 1 ∨ n = 16 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨
    n = 48 ∨ n = 49 ∨ n = 50 then one else if n = 64 then zero else seven
-- A symbolic/numeric witness only. The graph source above is independent.
def store : Store := fun l => machine (l.word 128 hash)
private def payload (l : Solidity.Storage.Loc) : Semantics.Word :=
  if l = root then machine 1 else if l = innerLoc 0 then machine 16 else
  if l = leafLoc 0 0 then machine 64 else zero
noncomputable def writes : List (Solidity.Storage.Loc × Semantics.Word) :=
  demands.map (fun q => (q.location root,payload (q.location root)))
noncomputable def final : WordStore :=
  writes.foldl (fun m op => writeWord m (op.1.word 128 hash) op.2) machine
def numericView (m : WordStore) := (m 0,m 8,m 9,m 10,m 32,m 33,m 34,m 40,m 41,m 42,
  m 48,m 49,m 50,m 56,m 1,m 16,m 64,m 127)
def permit : CopyPermit graph Outer := CopyPermit.checked (fun i => nomatch i) (by decide)
theorem run : FiniteRun 128 4 2 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;>
      (first | decide | (split <;> (first | decide | (split <;>
        (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))))))))))
  · decide
  · decide
  · decide
  · intro l member
    change l ∈ [leafLoc 0 0,leafLoc 0 1,innerLoc 0,leafLoc 1 0,leafLoc 1 1,innerLoc 1,root,
      leafLoc 0 2,leafLoc 1 2,leafLoc 2 0,innerLoc 2,leafLoc 3 0] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [leafLoc,innerLoc,root,Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    change l ∈ [leafLoc 0 0,leafLoc 0 1,innerLoc 0,leafLoc 1 0,leafLoc 1 1,innerLoc 1,root,
      leafLoc 0 2,leafLoc 1 2,leafLoc 2 0,innerLoc 2,leafLoc 3 0] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
theorem before : Represented old queries root store := by
  intro q member
  simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (simp only [Query.supported,leaf,innerPath,PathSupported,StepSupported]; decide)
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (intro word observed; change some one = some word at observed; cases observed; rfl)
    | (intro word observed; change some two = some word at observed; cases observed; rfl)
    | (intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed)

private theorem generated : ∀ op ∈ writes, ∃ d ∈ demands, op.1 = d.location root := by
  intro op member
  obtain ⟨q,inside,same⟩ := List.mem_map.mp member
  subst op
  exact ⟨q,inside,rfl⟩
theorem separated : ∀ q ∈ queries, ∀ d ∈ demands, q.location root ≠ d.location root := by
  intro q member d inside
  change d ∈ [.word (leaf (ix 0) (ix 0)),.word (leaf (ix 0) (ix 1)),.length (innerPath (ix 0)),
    .word (leaf (ix 1) (ix 0)),.word (leaf (ix 1) (ix 1)),.length (innerPath (ix 1)),.length .nil] at inside
  simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member inside
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Complete two-level runtime/shadow/live observations. Changed copied cells,
cleared stale tails and older shadows are distinguished in both levels. -/
theorem nested_observations :
    (view old,view src,view copied) =
    ((2,3,(some (2,3),some true,some true,some true,some true),
      (some (2,3),some true,some true,some true,some true),
      (some (2,3),some true,some true,some true,none),(none,none,none,none,none)),
     (1,2,(some (1,3),some false,some true,some true,some false),
      (some (1,3),some false,some true,some true,none),(none,none,none,none,none),(none,none,none,none,none)),
     (1,3,(some (1,3),some false,some false,some true,some false),
      (some (0,3),some false,some false,some true,none),
      (some (2,3),some true,some true,some true,none),(none,none,none,none,none))) := by rfl

/-- The generated demand sequence exposes nested loops and correct header-last
ordering; each restart prefix has the expected child demands. -/
theorem progress_observations :
    (demands.length,
      (CopyDemands.arrayPrefix ⟨3,by decide⟩ (ix 2) (fun _ => Slot.present innerOld)
        ⟨2,by decide⟩ (ix 1) (by decide) (fun _ => Slot.present innerSource) 0).length,
      (CopyDemands.arrayPrefix ⟨3,by decide⟩ (ix 2) (fun _ => Slot.present innerOld)
        ⟨2,by decide⟩ (ix 1) (by decide) (fun _ => Slot.present innerSource) 1).length,
      (CopyDemands.arrayPrefix ⟨3,by decide⟩ (ix 2) (fun _ => Slot.present innerOld)
        ⟨2,by decide⟩ (ix 1) (by decide) (fun _ => Slot.present innerSource) 2).length) = (7,0,3,6) := by rfl

/-- Per-run numeric transport and selected OLD owner relation give actual
POST represented shadow/header/failed-query observations. INSIDE payload
correctness is not a premise smuggled into this outside certificate. -/
theorem outside_owner_numeric :
    Represented copied queries root (writes.foldl (fun w op => write w op.1 op.2) store) ∧
    Transport 128 hash locations (writes.foldl (fun w op => write w op.1 op.2) store) final ∧
    ∀ q ∈ queries, ∀ word, q.read copied = some word → final ((q.location root).word 128 hash) = word := by
  exact CopyDemands.outside_numeric old src permit queries root store machine run before
    (fun _ _ => rfl) writes generated
    (fun d member => List.mem_map.mpr ⟨d,List.mem_append.mpr (Or.inl member),rfl⟩)
    (fun q member => List.mem_map.mpr ⟨q,List.mem_append.mpr (Or.inr member),rfl⟩) separated

/-- Concrete captured source-word and zero-tail writes change both nested
payload cells, retain all old shadows and leave source/sentinel/failed-query
numeric garbage unchanged. This fixture is not the general copy write compiler. -/
theorem numeric_observations :
    (numericView machine,numericView final) =
    ((two,two,two,two,one,one,one,one,one,one,one,one,one,seven,one,one,zero,seven),
     (one,one,zero,two,zero,zero,one,zero,zero,one,one,one,one,seven,one,one,zero,seven)) := by rfl

/-- Clearing the whole retained inner extent would wrongly erase two old
shadows. The failed graph query still does not imply a zero numeric cell. -/
theorem wrong_whole_extent :
    ((writeWord (writeWord final 34 zero) 42 zero) 34,
      (writeWord (writeWord final 34 zero) 42 zero) 42,final 34,final 42,
      copied.observe (leaf (ix 3) (ix 0)),final 56) =
    (zero,zero,one,one,none,seven) := by rfl

private def twoFixed : FixedSize := ⟨2,by decide⟩
private abbrev RootType : TypeGraph.Ty 0 := .fixed Outer twoFixed
private def rootValue : Value graph RootType := .fixed
  (fun i => if i.val = 0 then .present old else .present src)
private def dst : TypeGraph.Path graph RootType Outer := .cons (.fixed (ix 0)) .nil
private def source : TypeGraph.Path graph RootType Outer := .cons (.fixed (ix 1)) .nil
private def copiedRoot : Value graph RootType := (recursiveCopyAt rootValue dst source).getD rootValue

/-- Actual capture/read/save copy under a nonempty typed prefix applies the
PUBLIC selected root owner relation, with no desired intermediate relation. -/
theorem actual_root_owner :
    recursiveCopyAt rootValue dst source = some copiedRoot ∧
    Represented copiedRoot (queries.map (Query.prefix dst)) root
      (writes.foldl (fun w op => write w op.1 op.2) store) := by
  refine ⟨rfl,?_⟩
  exact CopyDemands.copyAt_outside_represented rootValue copiedRoot dst source old src permit
    rfl rfl rfl queries root store (by change (ix 0).val < twoFixed.val ∧ True; decide)
    before writes generated separated

/-- Internal mapping copy can create a new default observation behind a fresh
slot. Existing source CopyPermit refuses it; dropping that original premise
would make the omitted-query frame false. This is not an admitted source copy. -/
theorem mapping_permit_essential :
    let T : TypeGraph.Ty 0 := .mapping .bool (.prim .bool)
    let oldMap : Value graph (.array T) := .array ⟨0,by decide⟩ ⟨0,by decide⟩
      (by decide) (fun i => nomatch i)
    let srcMap : Value graph (.array T) := .array ⟨1,by decide⟩ ⟨1,by decide⟩
      (by decide) (fun _ => .present (.mapping (fun _ => .present (.prim true))))
    let q : Query graph (.array T) := .word (.cons (.index (ix 0)) (.cons (.key false) .nil))
    (CopyDemands.demands oldMap srcMap).length = 1 ∧
    q.read oldMap = none ∧ q.read (recursiveCopy oldMap srcMap) = some zero ∧
    (CopyPermit.check graph (.array T) (fun i => nomatch i)).isNone = true := by
  exact ⟨rfl,rfl,rfl,by decide⟩

private def wrappedType : Nat → TypeGraph.Ty 0
  | 0 => Outer
  | depth+1 => .fixed (wrappedType depth) twoFixed
private def wrapped (value : Value graph Outer) : (depth : Nat) → Value graph (wrappedType depth)
  | 0 => value
  | depth+1 => .fixed (fun _ => .present (wrapped value depth))
private def wrappedPath (p : TypeGraph.Path graph Outer (.prim .bool)) :
    (depth : Nat) → TypeGraph.Path graph (wrappedType depth) (.prim .bool)
  | 0 => p
  | depth+1 => .cons (.fixed (ix 0)) (wrappedPath p depth)

/-- Inhabited actual recursive copy paths at every finite nesting depth retain
older shadows AND change live payloads, over the same two runtime array levels. -/
theorem arbitrary_depth_copy (depth : Nat) :
    ((recursiveCopy (wrapped old depth) (wrapped src depth)).observe
      (wrappedPath (leaf (ix 0) (ix 2)) depth),
     (recursiveCopy (wrapped old depth) (wrapped src depth)).observe
      (wrappedPath (leaf (ix 0) (ix 0)) depth)) = (some true,some false) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    have found : (recursiveCopy (wrapped old (depth+1)) (wrapped src (depth+1))).find
        (.cons (.fixed (ix 0)) .nil) =
        some (recursiveCopy (wrapped old depth) (wrapped src depth)) := rfl
    change ((recursiveCopy (wrapped old (depth+1)) (wrapped src (depth+1))).observe
        ((TypeGraph.Path.cons (.fixed (ix 0)) .nil).append (wrappedPath (leaf (ix 0) (ix 2)) depth)),
      (recursiveCopy (wrapped old (depth+1)) (wrapped src (depth+1))).observe
        ((TypeGraph.Path.cons (.fixed (ix 0)) .nil).append (wrappedPath (leaf (ix 0) (ix 0)) depth))) = _
    rw [Value.observe_append,Value.observe_append,found,Option.bind_some,Option.bind_some]
    exact ih

/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.nested_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nested_observations
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.progress_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms progress_observations
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.outside_owner_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outside_owner_numeric
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.numeric_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_observations
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.wrong_whole_extent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_whole_extent
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.actual_root_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_root_owner
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.mapping_permit_essential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_permit_essential
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.arbitrary_depth_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms arbitrary_depth_copy

/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.graph' does not depend on any axioms -/
#guard_msgs in #print axioms graph
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.Inner' does not depend on any axioms -/
#guard_msgs in #print axioms Inner
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.Outer' does not depend on any axioms -/
#guard_msgs in #print axioms Outer
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.old' does not depend on any axioms -/
#guard_msgs in #print axioms old
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.src' does not depend on any axioms -/
#guard_msgs in #print axioms src
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.copied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copied
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.root' does not depend on any axioms -/
#guard_msgs in #print axioms root
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.queries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms queries
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.hash' does not depend on any axioms -/
#guard_msgs in #print axioms hash
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.locations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locations
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms machine
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms store
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.permit' does not depend on any axioms -/
#guard_msgs in #print axioms permit
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms before
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms separated
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.demands' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms demands
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms writes
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms final
/-- info: 'Solidity.Backend.StorageOps.CopyDemandControls.numericView' does not depend on any axioms -/
#guard_msgs in #print axioms numericView

end Solidity.Backend.StorageOps.CopyDemandControls

import Solidity.Backend.StorageOps.CopyDefaults
import Solidity.Backend.StorageOps.RecursiveCopy

/-! Fresh default visibility is not old-readable framing. Complete vectors
compare actual recursive graph copy, numeric zero writes and malformed reads.
These are intrinsic graph/numeric controls, not emitted EVM/world tests. -/
namespace Solidity.Backend.StorageOps.CopyDefaultsControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
  origin := "v10-copy-defaults-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def two : FixedSize := ⟨2,by decide⟩
private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private abbrev Inner : TypeGraph.Ty 0 := .fixed (.prim .bool) two
private abbrev Outer : TypeGraph.Ty 0 := .array Inner
private def old : Value graph Outer := .array ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide) (fun i => nomatch i)
private def src : Value graph Outer := .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .absent)
private def copied : Value graph Outer := recursiveCopy old src
private def leaf (outer inner : Index) : TypeGraph.Path graph Outer (.prim .bool) :=
  .cons (.index outer) (.cons (.fixed inner) .nil)
private def view (v : Value graph Outer) :=
  (v.length.val,v.extent.val,v.observe (leaf (ix 0) (ix 0)),v.observe (leaf (ix 0) (ix 1)),
    v.observe (leaf (ix 0) (ix 2)),v.observe (leaf (ix 1) (ix 0)),
    ((leaf (ix 0) (ix 0)).readLive Value.dflt v).map Value.head,
    ((leaf (ix 1) (ix 0)).readLive Value.dflt v).map Value.head)
private def root : Solidity.Storage.Loc := .root 0
private def base : Solidity.Storage.Loc := .data root 0
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 8 else 0
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def seven : Semantics.Word := ⟨7,by decide⟩
private def machine : WordStore := fun n => if n = 0 then zero else if n = 8 ∨ n = 9 ∨ n = 10 then one else seven
private def store : Store := fun l => if l = base ∨ l = base.add 1 then one else seven
private def naive : WordStore := writeWord machine 0 one
private noncomputable def initialized : WordStore := CopyDefaults.numericInit (N := 32) graph Inner base hash naive
private def numericView (m : WordStore) := (m 0,m 8,m 9,m 10,m 31)
private def queries : List (Query graph Inner) := [.word (.cons (.fixed (ix 0)) .nil),
  .word (.cons (.fixed (ix 1)) .nil)]
private noncomputable def covered : List Solidity.Storage.Loc :=
  ((CopyDefaults.demands graph Inner) ++ queries).map (fun q => q.location base)
private def permit : CopyPermit graph Inner := CopyPermit.checked (fun i => nomatch i) (by decide)
private theorem run : FiniteRun 32 4 1 hash [.data 0] covered := by
  constructor
  · intro p; simp only [hash]; split <;> decide
  · decide
  · decide
  · decide
  · intro l member
    change l ∈ [base.add 0,base.add 1,base.add 0,base.add 1] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      simp only [base,root,Solidity.Storage.Loc.add,Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    change l ∈ [base.add 0,base.add 1,base.add 0,base.add 1] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem initial : Transport 32 hash covered store naive := by
  intro l member
  change l ∈ [base.add 0,base.add 1,base.add 0,base.add 1] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

/-- Both old failed reads become successful default reads under an admitted copy.
Malformed fixed and outer paths continue to fail; live observations are explicit. -/
theorem fresh_copy_observations :
    (view old,view src,view copied) =
    ((0,0,none,none,none,none,none,none),
     (1,1,some false,some false,none,none,some false,none),
     (1,1,some false,some false,none,none,some false,none)) := by rfl

/-- Old absent-slot clear demands are empty, whereas initialization demands
include BOTH newly observable fixed cells. Header-only realization is wrong. -/
theorem wrong_absent_clear :
    (ClearDemands.slotDemands (Slot.absent : Slot graph Inner),
      (CopyDefaults.demands graph Inner).length,
      numericView machine,numericView naive,numericView initialized) =
    ([],2,(zero,one,one,one,seven),(one,one,one,one,seven),
      (one,zero,zero,one,seven)) := by rfl

/-- Actual generated initialization has full selected owner representation,
finite transport and both changed successful numeric readbacks. -/
theorem represented_initialization :
    Represented (Value.dflt Inner) queries base
      ((CopyDefaults.updates graph Inner base).foldl (fun w op => write w op.1 op.2) store) ∧
    Transport 32 hash covered
      ((CopyDefaults.updates graph Inner base).foldl (fun w op => write w op.1 op.2) store) initialized ∧
    ∀ q ∈ queries, ∀ word, q.read (Value.dflt Inner) = some word →
      initialized ((q.location base).word 32 hash) = word := by
  exact CopyDefaults.complete_numeric graph Inner permit queries
    (by intro q member; simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;>
          simp only [Query.supported,PathSupported,StepSupported] <;> decide)
    base hash [.data 0] store naive run initial

/-- Mapping algebra remains internal: the published source copy check refuses
this type, while its defaulted mapping read is successful but not enumerated. -/
theorem mapping_boundary :
    (CopyPermit.check graph (.mapping .bool (.prim .bool)) (fun i => nomatch i)).isNone = true ∧
    CopyDefaults.demands graph (.mapping .bool (.prim .bool)) = [] ∧
    (Query.word (.cons (.key (K := .bool) false) .nil)).read
      (Value.dflt (G := graph) (.mapping .bool (.prim .bool))) = some zero := by
  exact ⟨by decide,rfl,rfl⟩

private def nested : Nat → TypeGraph.Ty 0
  | 0 => .prim .bool
  | depth+1 => .fixed (nested depth) two
private def nestedPath : (depth : Nat) → TypeGraph.Path graph (nested depth) (.prim .bool)
  | 0 => .nil
  | depth+1 => .cons (.fixed (ix 0)) (nestedPath depth)

/-- Arbitrary finite inline nesting, with no admitted depth cutoff. The theorem
observes the actual published default through the existing typed path. -/
theorem arbitrary_depth (depth : Nat) :
    (Value.dflt (G := graph) (nested depth)).observe (nestedPath depth) = some false := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change ((TypeGraph.Path.cons (.fixed (ix 0)) (nestedPath depth)).read Value.dflt
      (Value.fixed (fun _ => Slot.absent))).map Value.head = some false
    simpa only [TypeGraph.Path.read,Step.get,dif_pos (show (ix 0).val < two.val by decide),
      Slot.getD,Option.bind_some] using ih

private def nestedPermit : (depth : Nat) → CopyPermit graph (nested depth)
  | 0 => permitBase
  | depth+1 => let p := nestedPermit depth; ⟨p.marked,⟨p.valid.1,p.valid.2⟩⟩
where
  permitBase : CopyPermit graph (.prim .bool) :=
    ⟨(fun i => nomatch i),⟨rfl,by intro i; exact Fin.elim0 i⟩⟩

/-- The generated adapter really covers this arbitrary-depth default read. -/
theorem arbitrary_depth_covered (depth : Nat) :
    Query.word (nestedPath depth) ∈ CopyDefaults.demands graph (nested depth) := by
  apply CopyDefaults.complete graph (nested depth) (nestedPermit depth) _ zero
  change ((Value.dflt (G := graph) (nested depth)).observe (nestedPath depth)).map
    (PrimTy.toWord (p := .bool)) = some zero
  rw [arbitrary_depth]
  rfl

private def emptyNested (depth : Nat) : Value graph (.array (nested depth)) :=
  .array ⟨0,by decide⟩ ⟨0,by decide⟩ (by decide) (fun i => nomatch i)
private def sourceNested (depth : Nat) : Value graph (.array (nested depth)) :=
  .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .absent)

/-- Fresh recursive copy produces the newly readable default at every finite
nested fixed depth; the prefix was genuinely unreadable before. -/
theorem arbitrary_depth_fresh_copy (depth : Nat) :
    (emptyNested depth).find (.cons (.index (ix 0)) .nil) = none ∧
    (recursiveCopy (emptyNested depth) (sourceNested depth)).find
      (.cons (.index (ix 0)) .nil) = some (Value.dflt (nested depth)) ∧
    (recursiveCopy (emptyNested depth) (sourceNested depth)).observe
      (.cons (.index (ix 0)) (nestedPath depth)) = some false := by
  have found : (recursiveCopy (emptyNested depth) (sourceNested depth)).find
      (.cons (.index (ix 0)) .nil) = some (Value.dflt (nested depth)) := by
    rw [recursiveCopy_eq_overlay]
    rfl
  refine ⟨rfl,found,?_⟩
  change (recursiveCopy (emptyNested depth) (sourceNested depth)).observe
    ((TypeGraph.Path.cons (.index (ix 0)) .nil).append (nestedPath depth)) = some false
  rw [Value.observe_append,found,Option.bind_some,arbitrary_depth]

/-- Empty dynamic defaults write only their header; neither data shadows nor
unrelated words are cleared by this adapter. -/
theorem dynamic_default_barrier :
    ((CopyDefaults.demands graph (.array Inner)).length,
      numericView (CopyDefaults.numericInit (N := 32) graph (.array Inner) root hash
        (writeWord machine 0 seven))) = (1,(zero,one,one,one,seven)) := by rfl

private def recursiveGraph : Schema 1 where
  origin := "v10-copy-defaults-recursive-controls"
  declId := fun _ => 0
  declId_injective := by intro i j _; apply Fin.ext; have hi := i.isLt; have hj := j.isLt; omega
  name := fun _ => "Link"
  fields := fun _ => [("flag",.prim .bool),("pair",.fixed (.prim .bool) two),
    ("children",.array (.node 0))]
  rank := fun _ => 2
  nonempty := by intro i; rfl
  distinct := by intro i; decide
  guarded := by
    intro i f member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
private def nodeQueries : List (Query recursiveGraph (.node 0)) :=
  [.word (.cons (.field .here) .nil),
   .word (.cons (.field (.there .here)) (.cons (.fixed (ix 0)) .nil)),
   .word (.cons (.field (.there .here)) (.cons (.fixed (ix 1)) .nil)),
   .length (.cons (.field (.there (.there .here))) .nil)]
private def recursivePermit : CopyPermit recursiveGraph (.node 0) :=
  CopyPermit.checked (fun _ => true) (by decide)

/-- A populated declaration shape combines fields, fixed defaults and a
recursive dynamic edge. The finite default observation set stops at the empty
header, without imposing a stored recursive-depth cap. -/
theorem recursive_node_demands :
    CopyDefaults.demands recursiveGraph (.node 0) = nodeQueries ∧
    nodeQueries.map (fun q => q.read (Value.dflt (.node 0))) =
      [some zero,some zero,some zero,some zero] ∧
    (CopyPermit.check recursiveGraph (.node 0) (fun _ => true)).isSome = true := by
  exact ⟨rfl,rfl,by decide⟩

/-- info: 'Solidity.Backend.StorageOps.CopyDefaultsControls.fresh_copy_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fresh_copy_observations
/-- info: 'Solidity.Backend.StorageOps.CopyDefaultsControls.wrong_absent_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_absent_clear
/-- info: 'Solidity.Backend.StorageOps.CopyDefaultsControls.represented_initialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_initialization
/-- info: 'Solidity.Backend.StorageOps.CopyDefaultsControls.mapping_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_boundary
/-- info: 'Solidity.Backend.StorageOps.CopyDefaultsControls.arbitrary_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms arbitrary_depth
/-- info: 'Solidity.Backend.StorageOps.CopyDefaultsControls.arbitrary_depth_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms arbitrary_depth_covered
/-- info: 'Solidity.Backend.StorageOps.CopyDefaultsControls.arbitrary_depth_fresh_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms arbitrary_depth_fresh_copy
/-- info: 'Solidity.Backend.StorageOps.CopyDefaultsControls.dynamic_default_barrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms dynamic_default_barrier
/-- info: 'Solidity.Backend.StorageOps.CopyDefaultsControls.recursive_node_demands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms recursive_node_demands

end Solidity.Backend.StorageOps.CopyDefaultsControls

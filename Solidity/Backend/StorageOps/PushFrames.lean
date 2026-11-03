import Solidity.Backend.StorageOps.FreshMappingHistory

/-! Exact other-index frames for the existing intrinsic push, composed with
fresh mapping history in ONE current-header numeric execution. The frame laws
place no liveness/extent/depth cap on queries; numeric coverage stays finite. -/
namespace Solidity.Backend.StorageOps.PushFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Every index except the old live length keeps its exact Option outcome,
including retained/defaulted values and out-of-extent failure. -/
theorem get_other {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (i : Index) (other : i.val ≠ old.length.val) :
    Step.get Value.dflt (.index i) result = Step.get Value.dflt (.index i) old := by
  by_cases allocated : i.val < old.extent.val
  · exact operationPush_keeps old result pushed i (Or.inr other) allocated
  · have headers := operationPush_header old result pushed
    have oldBound : old.length.val ≤ old.extent.val := by cases old; assumption
    have later : old.length.val + 1 ≤ i.val := by omega
    have outside : ¬ i.val < result.extent.val := by rw [headers.2]; omega
    cases old with
    | array oldExtent oldLength oldLive oldSlots =>
      cases result with
      | array newExtent newLength newLive newSlots =>
        change ¬ i.val < oldExtent.val at allocated
        change ¬ i.val < newExtent.val at outside
        simp only [Step.get,dif_neg allocated,dif_neg outside]

theorem read_other {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (i : Index) (other : i.val ≠ old.length.val) (q : Query G E) :
    (q.prefix (AggregatePopFrames.indexPath i)).read result = (q.prefix (AggregatePopFrames.indexPath i)).read old := by
  cases q <;> simp only [Query.prefix,AggregatePopFrames.indexPath,Query.read,Value.observe,Value.find,
    TypeGraph.Path.read_append,TypeGraph.Path.read,get_other old result pushed i other]

theorem compatible_other {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (i : Index) (other : i.val ≠ old.length.val) (q : Query G E) :
    (q.prefix (AggregatePopFrames.indexPath i)).compatible result = (q.prefix (AggregatePopFrames.indexPath i)).compatible old := by
  cases q with
  | word path => rfl
  | length path => simp only [Query.prefix,AggregatePopFrames.indexPath,Query.compatible,Value.observe,Value.find,
      TypeGraph.Path.read_append,TypeGraph.Path.read,get_other old result pushed i other]

/-- Other-index PUBLIC observations are derived from OLD owner evidence after
header write. Symbolic header separation is proved, not a new caller premise. -/
theorem represented_contexts {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (groups : List (Index × List (Query G E)))
    (other : ∀ group ∈ groups, group.1.val ≠ old.length.val)
    (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented old (AggregatePopFrames.contexts groups) base store) :
    Represented result (AggregatePopFrames.contexts groups) base
      (write store base (lengthWord result.length.val result.length.isLt)) := by
  intro q member
  obtain ⟨group,groupInside,mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨child,childInside,same⟩ := List.mem_map.mp mapped
  subst q
  have prior := before _ member
  refine ⟨prior.1,?_,?_⟩
  · rw [compatible_other old result pushed group.1 (other group groupInside) child]
    exact prior.2.1
  · intro value observed
    rw [read_other old result pushed group.1 (other group groupInside) child] at observed
    exact (write_other store base _ _ (OperationDepth.indexed_ne_header child group.1 base)).trans
      (prior.2.2 value observed)

/-- One ACTUAL execution covers fresh keys AND selected old-index contexts.
No desired postrelation, fresh-old None zero, or query/global hash injection. -/
theorem complete_fresh {n N L R : Nat} {G : Schema n} {K p : PrimTy}
    (old result : Value G (.array (.mapping K (.prim p))))
    (fresh : old.extent.val = old.length.val) (pushed : operationPush old = some result)
    (keys : List K.Denote) (groups : List (Index × List (Query G (.mapping K (.prim p)))))
    (other : ∀ group ∈ groups, group.1.val ≠ old.length.val) (base : Solidity.Storage.Loc)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (history : List (Solidity.Storage.Loc × Semantics.Word))
    (historyCovered : ∀ op ∈ history, op.1 ∈ locations)
    (covered : ∀ q ∈ (.length .nil :: keys.map (FreshMappingHistory.keyQuery old.length)) ++ AggregatePopFrames.contexts groups,
      q.location base ∈ locations)
    (apart : ∀ key ∈ keys, ∀ op ∈ history, (FreshMappingHistory.keyQuery (G := G) (p := p) old.length key).location base ≠ op.1)
    (coverage : old.length.val + 1 ≤ lmax)
    (header : Represented old [.length .nil] base (FreshMappingHistory.symbolic history))
    (contexts : Represented old (AggregatePopFrames.contexts groups) base (FreshMappingHistory.symbolic history)) :
    ∃ final, LifecycleNumeric.pushHeader N hash base (FreshMappingHistory.numeric N hash history) = some final ∧
      let after := write (FreshMappingHistory.symbolic history) base (lengthWord result.length.val result.length.isLt)
      Represented result ((.length .nil :: keys.map (FreshMappingHistory.keyQuery old.length)) ++ AggregatePopFrames.contexts groups) base after ∧
      Transport N hash locations after final ∧
      (∀ q ∈ ((.length .nil :: keys.map (FreshMappingHistory.keyQuery (G := G) (p := p) old.length)) ++ AggregatePopFrames.contexts groups),
        ∀ value, q.read result = some value → final ((q.location base).word N hash) = value) ∧
      (∀ address, address ≠ base.word N hash → final address = FreshMappingHistory.numeric N hash history address) := by
  have headerCovered : base ∈ locations := covered (.length .nil) (List.mem_append.mpr (Or.inl List.mem_cons_self))
  have keysCovered : ∀ key ∈ keys, (FreshMappingHistory.keyQuery (G := G) (p := p) old.length key).location base ∈ locations := by
    intro key inside
    exact covered _ (List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨key,inside,rfl⟩))))
  obtain ⟨final,executed,newOwner,transported,_,outside⟩ := FreshMappingHistory.complete_numeric old result fresh pushed
    keys base run history historyCovered headerCovered keysCovered apart coverage header
  have oldOwner := represented_contexts old result pushed groups other base (FreshMappingHistory.symbolic history) contexts
  have owner : Represented result ((.length .nil :: keys.map (FreshMappingHistory.keyQuery old.length)) ++ AggregatePopFrames.contexts groups) base
      (write (FreshMappingHistory.symbolic history) base (lengthWord result.length.val result.length.isLt)) := by
    intro q member
    exact (List.mem_append.mp member).elim (newOwner q) (oldOwner q)
  exact ⟨final,executed,owner,transported,fun q member value observed =>
    owner.numeric transported q member (covered q member) value observed,outside⟩

/-- info: 'Solidity.Backend.StorageOps.PushFrames.get_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms get_other
/-- info: 'Solidity.Backend.StorageOps.PushFrames.read_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_other
/-- info: 'Solidity.Backend.StorageOps.PushFrames.compatible_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms compatible_other
/-- info: 'Solidity.Backend.StorageOps.PushFrames.represented_contexts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented_contexts
/-- info: 'Solidity.Backend.StorageOps.PushFrames.complete_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_fresh

end Solidity.Backend.StorageOps.PushFrames

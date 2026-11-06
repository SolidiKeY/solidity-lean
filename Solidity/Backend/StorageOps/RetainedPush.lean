import Solidity.Backend.StorageOps.OperationDepth
import Solidity.Backend.StorageOps.AggregatePopFrames

/-! Actual current-header push for the retained NONPRIMITIVE case. This case
reuses existing aggregate slots unchanged. Fresh allocation/default provenance
is a different obligation; no source admission restriction is introduced. -/
namespace Solidity.Backend.StorageOps.RetainedPush
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def requested {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (groups : List (Index × List (Query G E))) : List (Query G (.array E)) :=
  .length .nil :: AggregatePopFrames.contexts groups

theorem extent_stays {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (retained : old.length.val < old.extent.val) : result.extent.val = old.extent.val := by
  have headers := operationPush_header old result pushed
  have within : old.length.val + 1 ≤ old.extent.val := by omega
  simpa only [Nat.max_eq_left within] using headers.2

/-- Every retained/defaulted/failed index outcome is unchanged. The new live
length changes liveness, not the existing logical contents at any index. -/
theorem get_stays {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (nonprimitive : E.isPrimitive = false) (retained : old.length.val < old.extent.val) (i : Index) :
    Step.get Value.dflt (.index i) result = Step.get Value.dflt (.index i) old := by
  by_cases allocated : i.val < old.extent.val
  · exact operationPush_keeps old result pushed i (Or.inl nonprimitive) allocated
  · have extents := extent_stays old result pushed retained
    cases old with
    | array oldExtent oldLength oldBound oldSlots =>
      cases result with
      | array newExtent newLength newBound newSlots =>
        change newExtent.val = oldExtent.val at extents
        change ¬ i.val < oldExtent.val at allocated
        have outside : ¬ i.val < newExtent.val := by omega
        simp only [Step.get,dif_neg allocated,dif_neg outside]

theorem read_stays {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (nonprimitive : E.isPrimitive = false) (retained : old.length.val < old.extent.val)
    (i : Index) (q : Query G E) :
    (q.prefix (AggregatePopFrames.indexPath i)).read result = (q.prefix (AggregatePopFrames.indexPath i)).read old := by
  cases q <;> simp only [Query.prefix,AggregatePopFrames.indexPath,Query.read,Value.observe,Value.find,
    TypeGraph.Path.read_append,TypeGraph.Path.read,get_stays old result pushed nonprimitive retained i]

theorem compatible_stays {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (nonprimitive : E.isPrimitive = false) (retained : old.length.val < old.extent.val)
    (i : Index) (q : Query G E) :
    (q.prefix (AggregatePopFrames.indexPath i)).compatible result = (q.prefix (AggregatePopFrames.indexPath i)).compatible old := by
  cases q with
  | word path => rfl
  | length path =>
    simp only [Query.prefix,AggregatePopFrames.indexPath,Query.compatible,Value.observe,Value.find,
      TypeGraph.Path.read_append,TypeGraph.Path.read,get_stays old result pushed nonprimitive retained i]

/-- OLD header bounds imply post bounds because the retained extent is unchanged.
No new lmax source cap or post-preservation premise is added. -/
theorem header_compatible {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (retained : old.length.val < old.extent.val)
    (before : (Query.length (.nil : TypeGraph.Path G (.array E) (.array E))).compatible old) :
    (Query.length (.nil : TypeGraph.Path G (.array E) (.array E))).compatible result := by
  have bounds : old.length.val ≤ lmax ∧ old.extent.val ≤ lmax := by cases old; exact before
  have headers := operationPush_header old result pushed
  have extents := extent_stays old result pushed retained
  cases result with
  | array extent length bound slots =>
    change length.val = old.length.val + 1 ∧ extent.val = max old.extent.val (old.length.val + 1) at headers
    change extent.val = old.extent.val at extents
    change length.val ≤ lmax ∧ extent.val ≤ lmax
    constructor <;> omega

/-- Full selected ROOT observations follow from OLD owner evidence. Every
nonheader location is proved distinct by operation-side symbolic depth. -/
theorem represented {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (nonprimitive : E.isPrimitive = false) (retained : old.length.val < old.extent.val)
    (groups : List (Index × List (Query G E))) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented old (requested groups) base store) :
    Represented result (requested groups) base (write store base (lengthWord result.length.val result.length.isLt)) := by
  intro q member
  rcases List.mem_cons.mp member with same | childMember
  · subst q
    refine ⟨True.intro,header_compatible old result pushed retained (before _ List.mem_cons_self).2.1,?_⟩
    intro value observed
    have seen : lengthWord result.length.val result.length.isLt = value := by cases result; exact Option.some.inj observed
    rw [← seen]
    exact write_same store base _
  · obtain ⟨group,groupMember,mapped⟩ := List.mem_flatMap.mp childMember
    obtain ⟨child,childInside,same⟩ := List.mem_map.mp mapped
    subst q
    have prior := before _ (List.mem_cons_of_mem _ childMember)
    refine ⟨prior.1,?_,?_⟩
    · rw [compatible_stays old result pushed nonprimitive retained group.1 child]
      exact prior.2.1
    · intro value observed
      rw [read_stays old result pushed nonprimitive retained group.1 child] at observed
      have different : (child.prefix (AggregatePopFrames.indexPath group.1)).location base ≠ base :=
        OperationDepth.indexed_ne_header child group.1 base
      exact (write_other store base _ _ different).trans (prior.2.2 value observed)

/-- Both actual header-capacity Option outcomes match the existing graph push.
No success-payload or world rollback assertion is made by this failure law. -/
theorem failure_matches {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (before : Represented old [.length .nil] base store)
    (initial : Transport N hash locations store machine) (covered : base ∈ locations) :
    LifecycleNumeric.pushHeader N hash base machine = none ↔ operationPush old = none := by
  rw [LifecycleNumeric.pushHeader_known hash base machine old.length
    (LifecycleNumeric.array_header_numeric old base store machine hash locations before initial covered),operationPush_failure]
  by_cases room : old.length.val + 1 < 2 ^ 256
  · rw [dif_pos room]
    constructor
    · intro impossible; cases impossible
    · intro impossible; omega
  · rw [dif_neg room]
    exact ⟨fun _ => by omega,fun _ => rfl⟩

/-- ACTUAL current-header execution, derived selected postrepresentation,
transport, successful query readbacks and every outside numeric word frame.
No caller-supplied header nonalias or desired preservation is assumed. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (nonprimitive : E.isPrimitive = false) (retained : old.length.val < old.extent.val)
    (groups : List (Index × List (Query G E))) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (before : Represented old (requested groups) base store) (initial : Transport N hash locations store machine)
    (covered : ∀ q ∈ requested groups, q.location base ∈ locations) :
    ∃ final, LifecycleNumeric.pushHeader N hash base machine = some final ∧
      let after := write store base (lengthWord result.length.val result.length.isLt)
      Represented result (requested groups) base after ∧ Transport N hash locations after final ∧
      (∀ q ∈ requested groups, ∀ value, q.read result = some value → final ((q.location base).word N hash) = value) ∧
      (∀ address, address ≠ base.word N hash → final address = machine address) := by
  have headerBefore : Represented old [.length .nil] base store := by
    intro q member
    have same := List.mem_singleton.mp member
    subst q
    exact before _ List.mem_cons_self
  have headerCovered : base ∈ locations := covered (.length .nil) List.mem_cons_self
  have header := LifecycleNumeric.array_header_numeric old base store machine hash locations headerBefore initial headerCovered
  have headers := operationPush_header old result pushed
  have bound := result.length.isLt
  have room : old.length.val + 1 < 2 ^ 256 := by omega
  let final := writeWord machine (base.word N hash) (lengthWord result.length.val result.length.isLt)
  have executed : LifecycleNumeric.pushHeader N hash base machine = some final := by
    rw [LifecycleNumeric.pushHeader_known hash base machine old.length header,dif_pos room]
    apply congrArg some
    apply congrArg (writeWord machine (base.word N hash))
    apply Subtype.ext
    exact congrArg Int.ofNat headers.1.symm
  have owner := represented old result pushed nonprimitive retained groups base store before
  have transported := transport_write run initial base headerCovered (lengthWord result.length.val result.length.isLt)
  refine ⟨final,executed,owner,transported,?_,?_⟩
  · intro q member value observed
    exact owner.numeric transported q member (covered q member) value observed
  · intro address different
    simp only [final,writeWord,if_neg different]

/-- info: 'Solidity.Backend.StorageOps.RetainedPush.extent_stays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms extent_stays
/-- info: 'Solidity.Backend.StorageOps.RetainedPush.get_stays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms get_stays
/-- info: 'Solidity.Backend.StorageOps.RetainedPush.read_stays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_stays
/-- info: 'Solidity.Backend.StorageOps.RetainedPush.compatible_stays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms compatible_stays
/-- info: 'Solidity.Backend.StorageOps.RetainedPush.header_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms header_compatible
/-- info: 'Solidity.Backend.StorageOps.RetainedPush.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.StorageOps.RetainedPush.failure_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.RetainedPush.complete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_numeric
end Solidity.Backend.StorageOps.RetainedPush

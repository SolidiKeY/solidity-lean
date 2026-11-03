import Solidity.Backend.StorageOps.AggregatePop

/-! Other-index context observations of the ACTUAL aggregate numeric pop.
The contexts are lists of existing typed owner queries, not another path/value
language. Logical frames and physical finite nonalias are kept distinct. -/
namespace Solidity.Backend.StorageOps.AggregatePopFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def indexPath {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} (i : Index) :
    TypeGraph.Path G (.array E) E := .cons (.index i) .nil

/-- Exact Option outcomes, including failed and retained/defaulted reads, at
all indices except the former last live index. No live/extent bound is added. -/
theorem read_other {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (popped : recursivePop old = some result)
    (i : Index) (other : i.val ≠ old.length.val - 1) (q : Query G E) :
    (q.prefix (indexPath i)).read result = (q.prefix (indexPath i)).read old := by
  cases q <;> simp only [Query.prefix,indexPath,Query.read,Value.observe,Value.find,TypeGraph.Path.read_append,TypeGraph.Path.read,
    recursivePop_other old result popped i other]

theorem compatible_other {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (popped : recursivePop old = some result)
    (i : Index) (other : i.val ≠ old.length.val - 1) (q : Query G E) :
    (q.prefix (indexPath i)).compatible result = (q.prefix (indexPath i)).compatible old := by
  cases q with
  | word path => rfl
  | length path =>
    simp only [Query.prefix,indexPath,Query.compatible,Value.observe,Value.find,TypeGraph.Path.read_append,TypeGraph.Path.read,
      recursivePop_other old result popped i other]

/-- Coverage is generated from the exact slot clear demands plus header. -/
theorem updates_covered {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (base : Solidity.Storage.Loc) (locations : List Solidity.Storage.Loc)
    (header : base ∈ locations)
    (children : ∀ q ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      q.location (AggregatePop.childBase old base) ∈ locations) :
    ∀ op ∈ AggregatePop.updates old base, op.1 ∈ locations := by
  intro op member
  rcases List.mem_append.mp member with child | root
  · obtain ⟨pair,pairMember,same⟩ := List.mem_map.mp child
    obtain ⟨q,generated,samePair⟩ := List.mem_map.mp pairMember
    subst pair
    subst op
    exact children q generated
  · have same := List.mem_singleton.mp root
    subst op
    exact header

/-- Caller-selected existing observations grouped by their outer index.
No new executable operation/state layer is defined. -/
def contexts {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (groups : List (Index × List (Query G E))) : List (Query G (.array E)) :=
  groups.flatMap (fun group => group.2.map (Query.prefix (indexPath group.1)))

/-- Header and ALL caller-selected other-index queries share the SAME actual
execution. Source frames are derived from recursivePop; numeric frames require
finite symbolic nonalias, not merely distinct logical indices. -/
theorem complete_context {n N L R : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (popped : recursivePop old = some result)
    (groups : List (Index × List (Query G E))) (base : Solidity.Storage.Loc)
    (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeHeader : Represented old [.length .nil] base store)
    (beforeContext : Represented old (contexts groups) base store)
    (initial : Transport N hash locations store machine) (headerCovered : base ∈ locations)
    (queriesCovered : ∀ q ∈ contexts groups, q.location base ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old base) ∈ locations)
    (other : ∀ group ∈ groups, group.1.val ≠ old.length.val - 1)
    (nonalias : ∀ q ∈ contexts groups, ∀ op ∈ AggregatePop.updates old base, q.location base ≠ op.1) :
    ∃ final, AggregatePop.execute (N := N) old hash base machine = some final ∧
      let after := (AggregatePop.updates old base).foldl (fun w op => write w op.1 op.2) store
      Represented result (.length .nil :: contexts groups) base after ∧
      Transport N hash locations after final := by
  obtain ⟨final,executed,headerAfter,transported⟩ := AggregatePop.complete_numeric old result popped [] base store machine
    run beforeHeader initial headerCovered (by intro q member; cases member) writesCovered
    (by intro q member; cases member) (by intro q member; cases member)
  have header := LifecycleNumeric.array_header_numeric old base store machine hash locations beforeHeader initial headerCovered
  have generated := updates_covered old base locations headerCovered writesCovered
  refine ⟨final,executed,?_,transported⟩
  intro q member
  rcases List.mem_cons.mp member with same | contextMember
  · subst q
    exact headerAfter _ (List.mem_cons_self)
  · obtain ⟨group,groupMember,queryMember⟩ := List.mem_flatMap.mp contextMember
    obtain ⟨child,childMember,same⟩ := List.mem_map.mp queryMember
    subst q
    have prior := beforeContext _ contextMember
    refine ⟨prior.1,?_,?_⟩
    · rw [compatible_other old result popped group.1 (other group groupMember) child]
      exact prior.2.1
    · intro word observed
      rw [read_other old result popped group.1 (other group groupMember) child] at observed
      have keep := AggregatePop.outside old hash base machine final header executed
        (((child.prefix (indexPath group.1)).location base).word N hash) (by
          intro op written same
          exact nonalias _ contextMember op written
            (run.word_inj (queriesCovered _ contextMember) (generated op written) same))
      exact (transported _ (queriesCovered _ contextMember)).symm.trans
        (keep.trans ((initial _ (queriesCovered _ contextMember)).trans (prior.2.2 word observed)))


/-- Last-slot changes and arbitrary finite other-index context groups compose
around ONE actual current-header execution and ONE generated store update log. -/
theorem complete_all {n N L R : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (popped : recursivePop old = some result)
    (selected : List (Query G E)) (groups : List (Index × List (Query G E)))
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeTarget : Represented old (AggregatePop.queries old selected) base store)
    (beforeContext : Represented old (contexts groups) base store)
    (initial : Transport N hash locations store machine) (headerCovered : base ∈ locations)
    (targetCovered : ∀ q ∈ selected, q.location (AggregatePop.childBase old base) ∈ locations)
    (contextCovered : ∀ q ∈ contexts groups, q.location base ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old base) ∈ locations)
    (separate : ∀ q ∈ selected, ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old base) = q.location (AggregatePop.childBase old base) → d = q)
    (headerSeparate : ∀ q ∈ selected, q.location (AggregatePop.childBase old base) ≠ base)
    (other : ∀ group ∈ groups, group.1.val ≠ old.length.val - 1)
    (nonalias : ∀ q ∈ contexts groups, ∀ op ∈ AggregatePop.updates old base, q.location base ≠ op.1) :
    ∃ final, AggregatePop.execute (N := N) old hash base machine = some final ∧
      let after := (AggregatePop.updates old base).foldl (fun w op => write w op.1 op.2) store
      Represented result (AggregatePop.queries old selected ++ contexts groups) base after ∧
      Transport N hash locations after final := by
  obtain ⟨final,executed,targetAfter,transported⟩ := AggregatePop.complete_numeric old result popped selected
    base store machine run beforeTarget initial headerCovered targetCovered writesCovered separate headerSeparate
  have headerBefore : Represented old [.length .nil] base store := by
    intro q member
    have same := List.mem_singleton.mp member
    subst q
    exact beforeTarget _ List.mem_cons_self
  obtain ⟨framed,executedFrame,contextAfter,_⟩ := complete_context old result popped groups base store machine
    run headerBefore beforeContext initial headerCovered contextCovered writesCovered other nonalias
  have same := Option.some.inj (executed.symm.trans executedFrame)
  subst framed
  refine ⟨final,executed,?_,transported⟩
  intro q member
  rcases List.mem_append.mp member with target | context
  · exact targetAfter q target
  · exact contextAfter q (List.mem_cons_of_mem _ context)

/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrames.read_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_other
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrames.compatible_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms compatible_other
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrames.updates_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms updates_covered
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrames.complete_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_context
/-- info: 'Solidity.Backend.StorageOps.AggregatePopFrames.complete_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_all
end Solidity.Backend.StorageOps.AggregatePopFrames

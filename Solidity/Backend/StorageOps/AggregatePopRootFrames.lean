import Solidity.Backend.StorageOps.AggregatePopPaths

/-! Outside-prefix sibling and ancestor observations for ACTUAL aggregate pop.
Public logical frame laws and finite numeric nonalias are separate premises;
no machine path discovery, emitted traversal or world rollback is asserted. -/
namespace Solidity.Backend.StorageOps.AggregatePopRootFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Actual capture/save and one current-header numeric execution/transport.
Only OLD root header evidence is needed for execution; payload frames follow
separately from OLD observations and generated address separation. -/
theorem execution_at {n N L R : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (found : root.find pre = some old) (popped : popAt root pre = some result)
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeHeader : Represented root (([.length .nil] : List (Query G (.array E))).map (Query.prefix pre)) base store)
    (initial : Transport N hash locations store machine) (headerCovered : pathLoc pre base ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old (pathLoc pre base)) ∈ locations) :
    ∃ child final, recursivePop old = some child ∧ root.save pre child = some result ∧ result.find pre = some child ∧
      AggregatePop.execute (N := N) old hash (pathLoc pre base) machine = some final ∧
      Transport N hash locations
        ((AggregatePop.updates old (pathLoc pre base)).foldl (fun w op => write w op.1 op.2) store) final := by
  obtain ⟨actual,child,read,changed,saved,readback⟩ := AggregatePopPaths.captured root result pre popped
  rw [found] at read
  cases read
  have focused := PathRepresentation.focus root old pre found [.length .nil] base store beforeHeader
  obtain ⟨final,executed,_,transported⟩ := AggregatePop.complete_numeric old child changed [] (pathLoc pre base) store machine
    run focused initial headerCovered (by intro q member; cases member) writesCovered
    (by intro q member; cases member) (by intro q member; cases member)
  exact ⟨child,final,changed,saved,readback,executed,transported⟩

/-- Outside ROOT sibling observations retain exact Option outcomes/metadata,
with actual generated numeric framing under independent finite nonalias. -/
theorem frame_at {n N L R : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (found : root.find pre = some old) (popped : popAt root pre = some result)
    (outside : List (Query G A)) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeHeader : Represented root (([.length .nil] : List (Query G (.array E))).map (Query.prefix pre)) base store)
    (beforeOutside : Represented root outside base store)
    (initial : Transport N hash locations store machine) (headerCovered : pathLoc pre base ∈ locations)
    (outsideCovered : ∀ q ∈ outside, q.location base ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old (pathLoc pre base)) ∈ locations)
    (apart : ∀ q ∈ outside, q.apart pre)
    (nonalias : ∀ q ∈ outside, ∀ op ∈ AggregatePop.updates old (pathLoc pre base), q.location base ≠ op.1) :
    ∃ final, AggregatePop.execute (N := N) old hash (pathLoc pre base) machine = some final ∧
      let after := (AggregatePop.updates old (pathLoc pre base)).foldl (fun w op => write w op.1 op.2) store
      Represented result outside base after ∧ Transport N hash locations after final := by
  obtain ⟨child,final,_,saved,_,executed,transported⟩ := execution_at root result pre old found popped
    base store machine run beforeHeader initial headerCovered writesCovered
  have focused := PathRepresentation.focus root old pre found [.length .nil] base store beforeHeader
  have header := LifecycleNumeric.array_header_numeric old (pathLoc pre base) store machine hash locations focused initial headerCovered
  have covered := AggregatePopFrames.updates_covered old (pathLoc pre base) locations headerCovered writesCovered
  refine ⟨final,executed,?_,transported⟩
  intro q member
  obtain ⟨supported,compatible,oldRead⟩ := beforeOutside q member
  refine ⟨supported,?_,?_⟩
  · rw [Query.compatible_frame root result pre child saved q (apart q member)]
    exact compatible
  · intro word observed
    have oldObserved : q.read root = some word := by
      rwa [Query.read_frame root result pre child saved q (apart q member)] at observed
    have keep := AggregatePop.outside old hash (pathLoc pre base) machine final header executed
      ((q.location base).word N hash) (by
        intro op written same
        exact nonalias q member op written (run.word_inj (outsideCovered q member) (covered op written) same))
    exact (transported _ (outsideCovered q member)).symm.trans
      (keep.trans ((initial _ (outsideCovered q member)).trans (oldRead word oldObserved)))

/-- A pop saved beneath an ancestor array element preserves that ancestor's
length AND retained extent. This is not a sibling Apart premise. -/
theorem header_frame_at {n N L R : Nat} {G : Schema n} {A E T : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (found : root.find pre = some old) (popped : popAt root pre = some result)
    (stem : TypeGraph.Path G A (.array T)) (index : Index) (tail : TypeGraph.Path G T (.array E))
    (shape : pre = stem.append (.cons (.index index) tail))
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeCurrent : Represented root (([.length .nil] : List (Query G (.array E))).map (Query.prefix pre)) base store)
    (beforeAncestor : Represented root [.length stem] base store)
    (initial : Transport N hash locations store machine) (currentCovered : pathLoc pre base ∈ locations)
    (ancestorCovered : pathLoc stem base ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old (pathLoc pre base)) ∈ locations)
    (nonalias : ∀ op ∈ AggregatePop.updates old (pathLoc pre base), pathLoc stem base ≠ op.1) :
    ∃ final, AggregatePop.execute (N := N) old hash (pathLoc pre base) machine = some final ∧
      let after := (AggregatePop.updates old (pathLoc pre base)).foldl (fun w op => write w op.1 op.2) store
      Represented result [.length stem] base after ∧ Transport N hash locations after final := by
  obtain ⟨child,final,_,saved,_,executed,transported⟩ := execution_at root result pre old found popped
    base store machine run beforeCurrent initial currentCovered writesCovered
  have logical := ancestor_header_frame stem index tail root result child (by rw [← shape]; exact saved)
  have focused := PathRepresentation.focus root old pre found [.length .nil] base store beforeCurrent
  have header := LifecycleNumeric.array_header_numeric old (pathLoc pre base) store machine hash locations focused initial currentCovered
  have covered := AggregatePopFrames.updates_covered old (pathLoc pre base) locations currentCovered writesCovered
  refine ⟨final,executed,?_,transported⟩
  intro q member
  have same := List.mem_singleton.mp member
  subst q
  obtain ⟨supported,compatible,oldRead⟩ := beforeAncestor (.length stem) (List.mem_singleton_self _)
  refine ⟨supported,?_,?_⟩
  · simpa only [Query.compatible,logical] using compatible
  · intro word observed
    have oldObserved : (Query.length stem).read root = some word := by
      simpa only [Query.read,logical] using observed
    have keep := AggregatePop.outside old hash (pathLoc pre base) machine final header executed
      ((pathLoc stem base).word N hash) (by
        intro op written same
        exact nonalias op written (run.word_inj ancestorCovered (covered op written) same))
    exact (transported _ ancestorCovered).symm.trans
      (keep.trans ((initial _ ancestorCovered).trans (oldRead word oldObserved)))

/-- Selected changed/inside-array and outside-prefix ROOT observations share
ONE actual execution and generated store log; every postrelation is derived. -/
theorem complete_at_context {n N L R : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (found : root.find pre = some old) (popped : popAt root pre = some result)
    (selected : List (Query G E)) (groups : List (Index × List (Query G E))) (outside : List (Query G A))
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeInside : Represented root
      ((AggregatePop.queries old selected ++ AggregatePopFrames.contexts groups).map (Query.prefix pre)) base store)
    (beforeOutside : Represented root outside base store)
    (initial : Transport N hash locations store machine) (headerCovered : pathLoc pre base ∈ locations)
    (targetCovered : ∀ q ∈ selected, q.location (AggregatePop.childBase old (pathLoc pre base)) ∈ locations)
    (contextCovered : ∀ q ∈ AggregatePopFrames.contexts groups, q.location (pathLoc pre base) ∈ locations)
    (outsideCovered : ∀ q ∈ outside, q.location base ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old (pathLoc pre base)) ∈ locations)
    (separate : ∀ q ∈ selected, ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old (pathLoc pre base)) =
        q.location (AggregatePop.childBase old (pathLoc pre base)) → d = q)
    (headerSeparate : ∀ q ∈ selected, q.location (AggregatePop.childBase old (pathLoc pre base)) ≠ pathLoc pre base)
    (other : ∀ group ∈ groups, group.1.val ≠ old.length.val - 1)
    (insideNonalias : ∀ q ∈ AggregatePopFrames.contexts groups, ∀ op ∈ AggregatePop.updates old (pathLoc pre base),
      q.location (pathLoc pre base) ≠ op.1)
    (apart : ∀ q ∈ outside, q.apart pre)
    (outsideNonalias : ∀ q ∈ outside, ∀ op ∈ AggregatePop.updates old (pathLoc pre base), q.location base ≠ op.1) :
    ∃ child final, recursivePop old = some child ∧ result.find pre = some child ∧
      AggregatePop.execute (N := N) old hash (pathLoc pre base) machine = some final ∧
      let after := (AggregatePop.updates old (pathLoc pre base)).foldl (fun w op => write w op.1 op.2) store
      Represented result
        (((AggregatePop.queries old selected ++ AggregatePopFrames.contexts groups).map (Query.prefix pre)) ++ outside) base after ∧
      Transport N hash locations after final := by
  obtain ⟨child,final,changed,readback,executed,represented,transported⟩ := AggregatePopPaths.complete_at
    root result pre old found popped selected groups base store machine run beforeInside initial headerCovered
    targetCovered contextCovered writesCovered separate headerSeparate other insideNonalias
  have headerBefore : Represented root (([.length .nil] : List (Query G (.array E))).map (Query.prefix pre)) base store := by
    intro q member
    have same := List.mem_singleton.mp member
    subst q
    exact beforeInside _ (List.mem_map.mpr ⟨.length .nil,List.mem_append.mpr (Or.inl List.mem_cons_self),rfl⟩)
  obtain ⟨framed,executedFrame,outsideAfter,_⟩ := frame_at root result pre old found popped outside base store machine
    run headerBefore beforeOutside initial headerCovered outsideCovered writesCovered apart outsideNonalias
  have same := Option.some.inj (executed.symm.trans executedFrame)
  subst framed
  refine ⟨child,final,changed,readback,executed,?_,transported⟩
  intro q member
  rcases List.mem_append.mp member with inside | context
  · exact represented q inside
  · exact outsideAfter q context

/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrames.execution_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms execution_at
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrames.frame_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frame_at
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrames.header_frame_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_frame_at
/-- info: 'Solidity.Backend.StorageOps.AggregatePopRootFrames.complete_at_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_at_context
end Solidity.Backend.StorageOps.AggregatePopRootFrames

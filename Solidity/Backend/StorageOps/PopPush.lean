import Solidity.Backend.StorageOps.RetainedPush

/-! Evolving pop/reuse composition over the existing intrinsic values and
WordStore. The intermediate owner/transport are proved by the actual pop, then
consumed by the actual current-header push. No heap identity/world claim. -/
namespace Solidity.Backend.StorageOps.PopPush
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

noncomputable def execute {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) : Option WordStore := do
  let middle ← AggregatePop.execute (N := N) old hash base machine
  LifecycleNumeric.pushHeader N hash base middle

theorem retained {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old middle : Value G (.array E)) (popped : recursivePop old = some middle) :
    middle.length.val < middle.extent.val := by
  have headers := recursivePop_header old middle popped
  have bound : old.length.val ≤ old.extent.val := by cases old; assumption
  rw [headers.2]
  omega

theorem headers {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old middle result : Value G (.array E)) (popped : recursivePop old = some middle)
    (pushed : operationPush middle = some result) :
    result.length.val = old.length.val ∧ result.extent = old.extent := by
  have popHeaders := recursivePop_header old middle popped
  have pushHeaders := operationPush_header middle result pushed
  have extent := RetainedPush.extent_stays middle result pushed (retained old middle popped)
  refine ⟨by omega,?_⟩
  apply Fin.ext
  rw [extent,popHeaders.2]

/-- Every logical slot outcome after regrowth equals the ACTUAL popped value,
including mapping barriers and retained shadows. It need not equal the OLD value. -/
theorem read_middle {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old middle result : Value G (.array E)) (popped : recursivePop old = some middle)
    (pushed : operationPush middle = some result) (nonprimitive : E.isPrimitive = false)
    (i : Index) (q : Query G E) :
    (q.prefix (AggregatePopFrames.indexPath i)).read result = (q.prefix (AggregatePopFrames.indexPath i)).read middle :=
  RetainedPush.read_stays middle result pushed nonprimitive (retained old middle popped) i q

/-- Composition through derived intermediate owner/Transport, for ONE evolving
numeric sequence. Every original finite region/shape/query premise is retained. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old middle result : Value G (.array E)) (popped : recursivePop old = some middle)
    (pushed : operationPush middle = some result) (nonprimitive : E.isPrimitive = false)
    (selected : List (Query G E)) (groups : List (Index × List (Query G E)))
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeTarget : Represented old (AggregatePop.queries old selected) base store)
    (beforeContext : Represented old (AggregatePopFrames.contexts groups) base store)
    (initial : Transport N hash locations store machine) (headerCovered : base ∈ locations)
    (targetCovered : ∀ q ∈ selected, q.location (AggregatePop.childBase old base) ∈ locations)
    (contextCovered : ∀ q ∈ AggregatePopFrames.contexts groups, q.location base ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old base) ∈ locations)
    (separate : ∀ q ∈ selected, ∀ d ∈ ClearDemands.slotDemands (AggregatePop.lastSlot old),
      d.location (AggregatePop.childBase old base) = q.location (AggregatePop.childBase old base) → d = q)
    (headerSeparate : ∀ q ∈ selected, q.location (AggregatePop.childBase old base) ≠ base)
    (other : ∀ group ∈ groups, group.1.val ≠ old.length.val - 1)
    (nonalias : ∀ q ∈ AggregatePopFrames.contexts groups, ∀ op ∈ AggregatePop.updates old base, q.location base ≠ op.1) :
    ∃ final, execute (N := N) old hash base machine = some final ∧
      let popStore := (AggregatePop.updates old base).foldl (fun w op => write w op.1 op.2) store
      let after := write popStore base (lengthWord result.length.val result.length.isLt)
      Represented result (AggregatePop.queries old selected ++ AggregatePopFrames.contexts groups) base after ∧
      Transport N hash locations after final := by
  obtain ⟨middleMachine,popExecuted,popOwner,popTransport⟩ := AggregatePopFrames.complete_all old middle popped selected groups
    base store machine run beforeTarget beforeContext initial headerCovered targetCovered contextCovered writesCovered separate headerSeparate other nonalias
  let combined := (AggregatePop.lastIndex old,selected) :: groups
  have middleOwner : Represented middle (RetainedPush.requested combined) base
      ((AggregatePop.updates old base).foldl (fun w op => write w op.1 op.2) store) := by
    change Represented middle (AggregatePop.queries old selected ++ AggregatePopFrames.contexts groups) base _
    exact popOwner
  have covered : ∀ q ∈ RetainedPush.requested combined, q.location base ∈ locations := by
    intro q member
    change q ∈ AggregatePop.queries old selected ++ AggregatePopFrames.contexts groups at member
    rcases List.mem_append.mp member with target | context
    · rcases List.mem_cons.mp target with same | mapped
      · subst q; exact headerCovered
      · obtain ⟨child,inside,rfl⟩ := List.mem_map.mp mapped
        rw [Query.location_prefix]
        exact targetCovered child inside
    · exact contextCovered q context
  obtain ⟨final,pushExecuted,owner,transported,_,_⟩ := RetainedPush.complete_numeric middle result pushed nonprimitive
    (retained old middle popped) combined base _ middleMachine run middleOwner popTransport covered
  refine ⟨final,?_,owner,transported⟩
  unfold execute
  rw [popExecuted]
  exact pushExecuted

/-- Every numeric word outside the ORIGINAL generated pop touched set frames
through BOTH actual operations. The second write is the already-touched header. -/
theorem outside {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
    (machine final : WordStore) (header : machine (base.word N hash) = lengthWord old.length.val old.length.isLt)
    (executed : execute (N := N) old hash base machine = some final) (address : Nat)
    (apart : ∀ op ∈ AggregatePop.updates old base, address ≠ op.1.word N hash) : final address = machine address := by
  have headerApart : address ≠ base.word N hash := apart
    (base,lengthWord (old.length.val - 1) (by have h := old.length.isLt; omega))
    (List.mem_append.mpr (Or.inr List.mem_cons_self))
  unfold execute at executed
  cases first : AggregatePop.execute (N := N) old hash base machine with
  | none => rw [first] at executed; cases executed
  | some middle =>
    rw [first] at executed
    change LifecycleNumeric.pushHeader N hash base middle = some final at executed
    unfold LifecycleNumeric.pushHeader at executed
    dsimp only at executed
    split at executed
    · cases executed
      exact (if_neg headerApart).trans (AggregatePop.outside old hash base machine middle header first address apart)
    · cases executed

/-- info: 'Solidity.Backend.StorageOps.PopPush.retained' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms retained
/-- info: 'Solidity.Backend.StorageOps.PopPush.headers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms headers
/-- info: 'Solidity.Backend.StorageOps.PopPush.read_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_middle
/-- info: 'Solidity.Backend.StorageOps.PopPush.complete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_numeric
/-- info: 'Solidity.Backend.StorageOps.PopPush.outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside

end Solidity.Backend.StorageOps.PopPush

import Solidity.Backend.StorageOps.LifecycleNumeric
import Solidity.Backend.StorageOps.PushTransport

/-! Actual primitive lifecycle executions and discriminating PUBLIC-interface
countermodels. Countermodels are not claims about reachable Source worlds. -/
namespace Solidity.Backend.StorageOps.LifecycleNumericControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
  origin := "v10-lifecycle-numeric-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def index0 : Index := ⟨0, by decide⟩
private def index1 : Index := ⟨1, by decide⟩
private def index2 : Index := ⟨2, by decide⟩
private def base : Solidity.Storage.Loc := .root 0
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7, by decide⟩
private def hash (p : Solidity.Storage.Pre) : Nat :=
  if p = .data 0 then 4 else if p = .entry 0 4 then 8 else if p = .entry 1 4 then 12 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0, .entry 0 4, .entry 1 4]
private def locations : List Solidity.Storage.Loc :=
  [.root 0, .data (.root 0) 0, .data (.root 0) 1,
    .hash 0 (.data (.root 0) 0) 0, .hash 1 (.data (.root 0) 0) 0]
private def store : Store := fun l => if l = .root 2 then seven else
  if l = .data (.root 0) 0 ∨ l = .data (.root 0) 1 ∨
    l = .hash 0 (.data (.root 0) 0) 0 ∨ l = .hash 1 (.data (.root 0) 0) 0 then one else zero
private def machine : WordStore := fun a => if a = 2 then seven else
  if a = 4 ∨ a = 5 ∨ a = 8 ∨ a = 12 then one else zero
private def numericView (m : WordStore) := (m 0, m 4, m 5, m 8, m 12, m 2)
private def primitivePath (i : Index) : TypeGraph.Path graph (.array (.prim .bool)) (.prim .bool) :=
  .cons (.index i) .nil
private def fresh : Value graph (.array (.prim .bool)) :=
  .array ⟨0, by decide⟩ index0 (by decide) (fun i => nomatch i)
private def reused : Value graph (.array (.prim .bool)) :=
  .array ⟨2, by decide⟩ index0 (by decide) (fun _ => .present (.prim true))
private def firstFresh : Value graph (.array (.prim .bool)) :=
  .array ⟨1, by decide⟩ index1 (by decide) (fun _ => .absent)
private def firstReused : Value graph (.array (.prim .bool)) :=
  .array ⟨2, by decide⟩ index1 (by decide)
    (fun i => if i.val = 0 then .absent else .present (.prim true))
private def second : Value graph (.array (.prim .bool)) :=
  .array ⟨2, by decide⟩ ⟨2, by decide⟩ (by decide) (fun _ => .absent)
private def firstMachine : WordStore := writeWord (writeWord machine 4 zero) 0 one
private def secondMachine : WordStore := writeWord (writeWord firstMachine 5 zero) 0 two

private theorem run : FiniteRun 16 2 1 hash preimages locations := by
  constructor
  · intro p
    simp only [hash]
    split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initial : Transport 16 hash locations store machine := by
  intro l member
  simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem freshBefore : Represented fresh [.length .nil] base store := by
  intro q member
  simp only [List.mem_singleton] at member
  subst q
  refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
  intro word observed
  change some zero = some word at observed
  cases observed
  rfl
private theorem reusedBefore : Represented reused [.length .nil] base store := by
  intro q member
  simp only [List.mem_singleton] at member
  subst q
  refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
  intro word observed
  change some zero = some word at observed
  cases observed
  rfl

/-- Correct fresh and retained scalar reset; second push reads CURRENT header
and therefore resets the NEXT word. No fixed captured source-length oracle. -/
theorem primitive_executions :
    operationPush fresh = some firstFresh ∧ operationPush reused = some firstReused ∧
    operationPush firstFresh = some second ∧
    LifecycleNumeric.pushPrimitive 16 hash base machine = some firstMachine ∧
    LifecycleNumeric.pushPrimitive 16 hash base firstMachine = some secondMachine := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · simp only [operationPush, fresh, firstFresh, Value.length, Value.extent, Value.slots,
      TypeGraph.Ty.isPrimitive, index0, index1, true_and, dif_pos (by decide : 1 < 2 ^ 256)]
    congr 2
    funext i
    have atZero : i.val = 0 := by have bound := i.isLt; omega
    simp only [atZero, if_true]
  · simp only [operationPush, reused, firstReused, Value.length, Value.extent, Value.slots,
      TypeGraph.Ty.isPrimitive, index0, index1, true_and, dif_pos (by decide : 1 < 2 ^ 256)]
    congr 2
    funext i
    simp only [dif_pos (show i.val < 2 from i.isLt)]
  · simp only [operationPush, firstFresh, second, Value.length, Value.extent, Value.slots,
      TypeGraph.Ty.isPrimitive, index1, true_and, dif_pos (by decide : 2 < 2 ^ 256)]
    congr 2
    funext i
    have cases : i.val = 0 ∨ i.val = 1 := by have h := i.isLt; omega
    rcases cases with h | h <;> simp only [h, Nat.zero_ne_one, ↓reduceIte, dif_pos (by decide : 0 < 1)]

/-- Instantiate the real OLD representation/run certificate, not only raw
execution. Both actual graph and numeric output observations are obtained. -/
theorem fresh_certificate :
    ∃ final : WordStore, LifecycleNumeric.pushPrimitive 16 hash base machine = some final ∧
      (Query.length .nil).read firstFresh = some (final (base.word 16 hash)) ∧
      (Query.word (primitivePath index0)).read firstFresh = some (final ((Solidity.Storage.Loc.data base 0).word 16 hash)) ∧
      ∀ a, a ≠ base.word 16 hash → a ≠ (Solidity.Storage.Loc.data base 0).word 16 hash → final a = machine a :=
  LifecycleNumeric.primitive_push_observations run fresh firstFresh primitive_executions.1 base store machine
    freshBefore initial List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)

theorem reused_certificate :
    ∃ final : WordStore, LifecycleNumeric.pushPrimitive 16 hash base machine = some final ∧
      (Query.length .nil).read firstReused = some (final (base.word 16 hash)) ∧
      (Query.word (primitivePath index0)).read firstReused = some (final ((Solidity.Storage.Loc.data base 0).word 16 hash)) ∧
      ∀ a, a ≠ base.word 16 hash → a ≠ (Solidity.Storage.Loc.data base 0).word 16 hash → final a = machine a :=
  LifecycleNumeric.primitive_push_observations run reused firstReused primitive_executions.2.1 base store machine
    reusedBefore initial List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)

/-- Complete ordered primitive views: headers/extents, BOTH slots, malformed
index, live-vs-retained alias, and all numeric frame/sentinel words. -/
theorem primitive_ordered :
    (fresh.length.val, fresh.extent.val, fresh.observe (primitivePath index0), fresh.observe (primitivePath index1),
      reused.length.val, reused.extent.val, reused.observe (primitivePath index0), reused.observe (primitivePath index1),
      firstFresh.length.val, firstFresh.extent.val, firstFresh.observe (primitivePath index0), firstFresh.observe (primitivePath index1),
      firstReused.length.val, firstReused.extent.val, firstReused.observe (primitivePath index0), firstReused.observe (primitivePath index1),
      firstReused.observe (primitivePath index2),
      ((primitivePath index0).readLive Value.dflt reused).map Value.head,
      ((primitivePath index0).readLive Value.dflt firstReused).map Value.head,
      second.length.val, second.extent.val, second.observe (primitivePath index0), second.observe (primitivePath index1),
      numericView machine, numericView firstMachine, numericView secondMachine) =
    (0, 0, none, none, 0, 2, some true, some true,
      1, 1, some false, none, 1, 2, some false, some true, none, none, some false,
      2, 2, some false, some false, (zero, one, one, one, one, seven),
      (one, zero, one, one, one, seven), (two, zero, zero, one, one, seven)) := rfl

private abbrev MappingArray := Value graph (.array (.mapping .bool (.prim .bool)))
private def aggregateOld : MappingArray :=
  .array ⟨0, by decide⟩ index0 (by decide) (fun i => nomatch i)
private def aggregateNew : MappingArray :=
  .array ⟨1, by decide⟩ index1 (by decide) (fun _ => .absent)
private def aggregateKey (key : Bool) : TypeGraph.Path graph (.array (.mapping .bool (.prim .bool))) (.prim .bool) :=
  .cons (.index index0) (.cons (.key key) .nil)
private def aggregateAt (i : Index) (key : Bool) :
    TypeGraph.Path graph (.array (.mapping .bool (.prim .bool))) (.prim .bool) :=
  .cons (.index i) (.cons (.key key) .nil)
private def aggregateQueries : List (Query graph (.array (.mapping .bool (.prim .bool)))) :=
  [.length .nil, .word (aggregateKey false), .word (aggregateKey true)]
private def headerOnly : WordStore := writeWord machine 0 one
private def headerStore : Store := write store base one

private theorem aggregateBefore : Represented aggregateOld aggregateQueries base store := by
  intro q member
  simp only [aggregateQueries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed
    change some zero = some word at observed
    cases observed
    rfl
  · refine ⟨?_, True.intro, ?_⟩
    · change 0 < lmax ∧ True ∧ True
      exact ⟨by decide, True.intro, True.intro⟩
    · intro word observed
      change (none : Option Semantics.Word) = some word at observed
      cases observed
  · refine ⟨?_, True.intro, ?_⟩
    · change 0 < lmax ∧ True ∧ True
      exact ⟨by decide, True.intro, True.intro⟩
    · intro word observed
      change (none : Option Semantics.Word) = some word at observed
      cases observed

/-- All owner BEFORE representation/finite-run/transport premises hold, and
header-only execution transports its writes, YET fresh mapping defaults are
not represented afterwards. This diagnoses missing allocation initialization;
it is not a reachable-world claim or an authorized extra source premise. -/
theorem fresh_mapping_countermodel :
    Represented aggregateOld aggregateQueries base store ∧
    FiniteRun 16 2 1 hash preimages locations ∧ Transport 16 hash locations store machine ∧
    operationPush aggregateOld = some aggregateNew ∧
    LifecycleNumeric.pushHeader 16 hash base machine = some headerOnly ∧
    Transport 16 hash locations headerStore headerOnly ∧
    ¬ Represented aggregateNew aggregateQueries base headerStore := by
  refine ⟨aggregateBefore, run, initial, rfl, rfl, ?_, ?_⟩
  · exact transport_write run initial base List.mem_cons_self one
  · intro bad
    have wrong := (bad (.word (aggregateKey false)) (List.mem_cons_of_mem _ List.mem_cons_self)).2.2 zero rfl
    change one = zero at wrong
    exact (by decide : one ≠ zero) wrong

theorem aggregate_countermodel_ordered :
    (aggregateOld.length.val, aggregateOld.extent.val,
      aggregateOld.observe (aggregateKey false), aggregateOld.observe (aggregateKey true),
      aggregateNew.length.val, aggregateNew.extent.val,
      aggregateNew.observe (aggregateKey false), aggregateNew.observe (aggregateKey true),
      ((aggregateAt index1 false).read Value.dflt aggregateNew).map Value.head,
      ((aggregateKey false).readLive Value.dflt aggregateOld).map Value.head,
      ((aggregateKey true).readLive Value.dflt aggregateOld).map Value.head,
      ((aggregateKey false).readLive Value.dflt aggregateNew).map Value.head,
      ((aggregateKey true).readLive Value.dflt aggregateNew).map Value.head,
      numericView machine, numericView headerOnly) =
    (0, 0, none, none, 1, 1, some false, some false, none, none, none, some false, some false,
      (zero, one, one, one, one, seven), (one, one, one, one, one, seven)) := rfl

/-- Full word capacity remains the original Option failure. This standalone
known-header control is outside the owner's smaller header-coverage range;
it is not evidence for a represented reachable world or rollback. -/
private def fullIndex : Index := ⟨2 ^ 256 - 1, by decide⟩
private def fullArray : Value graph (.array (.prim .bool)) :=
  .array ⟨fullIndex.val, by have h := fullIndex.isLt; omega⟩ fullIndex (by decide) (fun _ => .absent)
private def fullMachine : WordStore := fun _ => lengthWord fullIndex.val fullIndex.isLt

theorem full_capacity_failure : operationPush fullArray = none ∧
    LifecycleNumeric.pushPrimitive 16 hash base fullMachine = none := by
  constructor
  · exact (operationPush_failure fullArray).mpr (by decide)
  · exact (LifecycleNumeric.pushPrimitive_failure_known hash base fullMachine fullIndex rfl).mpr (by decide)

/-- lmax is published representation coverage, NOT an admitted-source cap.
The actual intrinsic operation succeeds at lmax, while ANY result store fails
the unchanged owner's post-header compatibility requirement. -/
private def coverageIndex : Index := ⟨lmax, by decide⟩
private def coverageArray : Value graph (.array (.prim .bool)) :=
  .array ⟨lmax, by decide⟩ coverageIndex (Nat.le_refl _) (fun _ => .absent)
private def coverageStore : Store := fun _ => lengthWord coverageIndex.val coverageIndex.isLt

private theorem coverageBefore : Represented coverageArray [.length .nil] base coverageStore := by
  intro q member
  simp only [List.mem_singleton] at member
  subst q
  refine ⟨True.intro, ⟨Nat.le_refl _, Nat.le_refl _⟩, ?_⟩
  intro word observed
  change some (lengthWord coverageIndex.val coverageIndex.isLt) = some word at observed
  cases observed
  rfl

theorem representation_coverage_countermodel :
    Represented coverageArray [.length .nil] base coverageStore ∧
    (∃ result, operationPush coverageArray = some result) ∧
    (∀ result, operationPush coverageArray = some result → ∀ after : Store,
      ¬ Represented result [.length .nil] base after) := by
  refine ⟨coverageBefore, ?_, ?_⟩
  · unfold operationPush
    exact ⟨_, rfl⟩
  · intro result executed after represented
    have lengths := (operationPush_header coverageArray result executed).1
    have bounded := (represented (.length .nil) List.mem_cons_self).2.1
    have lengthBound : result.length.val ≤ lmax := by
      cases result
      exact bounded.1
    change result.length.val = lmax + 1 at lengths
    omega

/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.primitive_executions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_executions
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.fresh_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_certificate
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.reused_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reused_certificate
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.primitive_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.fresh_mapping_countermodel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_mapping_countermodel
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.aggregate_countermodel_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms aggregate_countermodel_ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.full_capacity_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_capacity_failure
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.representation_coverage_countermodel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms representation_coverage_countermodel

private def pushIndices : List Index := [index0, index1]
private def pushQueries : List (Query graph (.array (.prim .bool))) := PrimitivePop.queries pushIndices
private def afterPushStore : Store := Representation.write
  (Representation.write store (.data base 0) zero) base one
private theorem freshAllBefore : Represented fresh pushQueries base store := by
  intro q member
  simp only [pushQueries, PrimitivePop.queries, pushIndices, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact freshBefore (.length .nil) List.mem_cons_self
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
private theorem reusedAllBefore : Represented reused pushQueries base store := by
  intro q member
  simp only [pushQueries, PrimitivePop.queries, pushIndices, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact reusedBefore (.length .nil) List.mem_cons_self
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
private theorem pushCovered : ∀ q ∈ pushQueries, q.location base ∈ locations := by
  intro q member
  simp only [pushQueries, PrimitivePop.queries, pushIndices, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

/-- Fresh missing reads become FALSE with real reset of nonzero numeric word;
retained reuse keeps the other represented TRUE word. No new source cap. -/
theorem full_push_bridges :
    (∃ m, LifecycleNumeric.pushPrimitive 16 hash base machine = some m ∧
      Transport 16 hash locations afterPushStore m ∧ Represented firstFresh pushQueries base afterPushStore) ∧
    (∃ m, LifecycleNumeric.pushPrimitive 16 hash base machine = some m ∧
      Transport 16 hash locations afterPushStore m ∧ Represented firstReused pushQueries base afterPushStore) := by
  constructor
  · obtain ⟨m, executed, transported, iffCovered, _⟩ := PushTransport.complete_numeric run fresh firstFresh primitive_executions.1
      pushIndices base store machine freshAllBefore initial List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨m, executed, transported, iffCovered.mpr (by decide)⟩
  · obtain ⟨m, executed, transported, iffCovered, _⟩ := PushTransport.complete_numeric run reused firstReused primitive_executions.2.1
      pushIndices base store machine reusedAllBefore initial List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨m, executed, transported, iffCovered.mpr (by decide)⟩

theorem full_push_numeric_observations :
    (∃ m, LifecycleNumeric.pushPrimitive 16 hash base machine = some m ∧
      ∀ q ∈ pushQueries, ∀ word, q.read firstFresh = some word → m ((q.location base).word 16 hash) = word) ∧
    (∃ m, LifecycleNumeric.pushPrimitive 16 hash base machine = some m ∧
      ∀ q ∈ pushQueries, ∀ word, q.read firstReused = some word → m ((q.location base).word 16 hash) = word) :=
  ⟨PushTransport.selected_numeric run fresh firstFresh primitive_executions.1 pushIndices base store machine freshAllBefore
      initial pushCovered (List.mem_cons_of_mem _ List.mem_cons_self),
    PushTransport.selected_numeric run reused firstReused primitive_executions.2.1 pushIndices base store machine reusedAllBefore
      initial pushCovered (List.mem_cons_of_mem _ List.mem_cons_self)⟩

private def symbolicView (w : Store) := (w base, w (.data base 0), w (.data base 1),
  w (.hash 0 (.data base 0) 0), w (.hash 1 (.data base 0) 0), w (.root 2))
theorem push_symbolic_ordered : (symbolicView store, symbolicView afterPushStore) =
    ((zero,one,one,one,one,seven),(one,zero,one,one,one,seven)) := rfl

/-- The coverage boundary also has an INHABITED actual finite numeric run.
Large values are scalar Nat/Word constants and lazy slots, not huge allocations
or loop bounds tested by enumeration. This is not a reachable-world claim. -/
private def boundaryHash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 2 else 0
private def boundaryLocations : List Solidity.Storage.Loc := [base, .data base lmax]
private def boundaryMachine : WordStore := fun _ => lengthWord coverageIndex.val coverageIndex.isLt
private def boundaryResult : Value graph (.array (.prim .bool)) := (operationPush coverageArray).getD coverageArray
private theorem boundaryPushed : operationPush coverageArray = some boundaryResult := rfl
private theorem boundaryRun : FiniteRun (2 ^ 256) (lmax + 1) 1 boundaryHash [.data 0] boundaryLocations := by
  constructor
  · intro p; simp only [boundaryHash]; split <;> decide
  · decide
  · decide
  · decide
  · intro l member
    simp only [boundaryLocations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp only [base, Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [boundaryLocations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
private theorem boundaryInitial : Transport (2 ^ 256) boundaryHash boundaryLocations coverageStore boundaryMachine := by
  intro l _
  rfl

/-- Push and numeric execution/transport SUCCEED at lmax; the unchanged owner
post-header predicate fails. The interface limit is characterized, not imposed
as a source restriction or assumed preservation premise. -/
theorem numeric_coverage_countermodel :
    Represented coverageArray [.length .nil] base coverageStore ∧
    FiniteRun (2 ^ 256) (lmax + 1) 1 boundaryHash [.data 0] boundaryLocations ∧
    (∃ m, LifecycleNumeric.pushPrimitive (2 ^ 256) boundaryHash base boundaryMachine = some m ∧
      let after := Representation.write (Representation.write coverageStore (.data base lmax) zero)
        base (lengthWord boundaryResult.length.val boundaryResult.length.isLt)
      Transport (2 ^ 256) boundaryHash boundaryLocations after m ∧
        ¬ Represented boundaryResult [.length .nil] base after) := by
  refine ⟨coverageBefore, boundaryRun, ?_⟩
  obtain ⟨m, executed, transported, iffCovered, _⟩ := PushTransport.complete_numeric boundaryRun coverageArray boundaryResult
    boundaryPushed [] base coverageStore boundaryMachine coverageBefore boundaryInitial List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨m, executed, transported, ?_⟩
  intro represented
  have impossible := iffCovered.mp represented
  change lmax + 1 ≤ lmax at impossible
  omega

private def boundaryAfterMachine : WordStore :=
  (LifecycleNumeric.pushPrimitive (2 ^ 256) boundaryHash base boundaryMachine).getD boundaryMachine
private def boundaryNextWord : Semantics.Word := lengthWord (lmax + 1) (by decide)

theorem boundary_ordered :
    (coverageArray.length.val, coverageArray.extent.val, boundaryResult.length.val, boundaryResult.extent.val,
      coverageArray.observe (primitivePath coverageIndex), boundaryResult.observe (primitivePath coverageIndex),
      ((primitivePath coverageIndex).readLive Value.dflt coverageArray).map Value.head,
      ((primitivePath coverageIndex).readLive Value.dflt boundaryResult).map Value.head,
      (Query.word (primitivePath coverageIndex)).read coverageArray,
      (Query.word (primitivePath coverageIndex)).read boundaryResult,
      boundaryMachine 0, boundaryAfterMachine 0, boundaryMachine (lmax + 2), boundaryAfterMachine (lmax + 2),
      boundaryMachine 1, boundaryAfterMachine 1) =
    (lmax,lmax,lmax+1,lmax+1,none,some false,none,some false,none,some zero,
      lengthWord lmax (by decide),boundaryNextWord,lengthWord lmax (by decide),zero,
      lengthWord lmax (by decide),lengthWord lmax (by decide)) ∧
    ¬ PathSupported (primitivePath coverageIndex) := by
  refine ⟨rfl, ?_⟩
  change ¬ (lmax < lmax ∧ True)
  omega

/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.full_push_bridges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_push_bridges
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.full_push_numeric_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_push_numeric_observations
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.push_symbolic_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_symbolic_ordered
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.numeric_coverage_countermodel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_coverage_countermodel
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.boundary_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms boundary_ordered

/-- The actual numeric/header observation bridge remains inhabited beyond
post-metadata coverage; no post-representation premise is smuggled in. -/
theorem boundary_numeric_read_agreement : ∃ m,
    LifecycleNumeric.pushPrimitive (2 ^ 256) boundaryHash base boundaryMachine = some m ∧
    (Query.length .nil).read boundaryResult = some (m 0) := by
  obtain ⟨m,executed,observations⟩ := PushTransport.selected_numeric boundaryRun coverageArray boundaryResult boundaryPushed
    [] base coverageStore boundaryMachine coverageBefore boundaryInitial
    (by
      intro q member
      simp only [PrimitivePop.queries, List.map_nil, List.mem_singleton] at member
      subst q
      exact List.mem_cons_self)
    (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨m,executed,?_⟩
  have actual := observations (.length .nil) List.mem_cons_self
    (lengthWord boundaryResult.length.val boundaryResult.length.isLt) (by cases boundaryResult; rfl)
  change m 0 = lengthWord boundaryResult.length.val boundaryResult.length.isLt at actual
  rw [actual]
  rfl

/-- info: 'Solidity.Backend.StorageOps.LifecycleNumericControls.boundary_numeric_read_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms boundary_numeric_read_agreement

end Solidity.Backend.StorageOps.LifecycleNumericControls

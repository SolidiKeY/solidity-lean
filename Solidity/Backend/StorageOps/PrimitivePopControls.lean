import Solidity.Backend.StorageOps.PrimitivePop
import Solidity.Backend.StorageOps.TargetPrimitivePop
import Solidity.Backend.StorageOps.TargetPrimitivePush
import Solidity.Backend.StorageOps.TargetPrimitivePopPush
import Solidity.Backend.StorageOps.TargetArrayRead
import Solidity.Backend.StorageOps.TargetArrayWrite
import Solidity.Backend.StorageOps.TargetArrayClear
import Solidity.Backend.StorageOps.TargetClearRepresentation

/-! Inhabited complete-query numeric pop control: two live words, one older
shadow, malformed index, retained/live aliases and wrong reset countercontrols. -/
namespace Solidity.Backend.StorageOps.PrimitivePopControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
  origin := "v10-primitive-pop-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val, by have bound := i.isLt; omega⟩
private def indices : List Index := [ix 0, ix 1, ix 2, ix 3]
private def base : Solidity.Storage.Loc := .root 0
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7, by decide⟩
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 4 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0]
private def locations : List Solidity.Storage.Loc := [.root 0, .data (.root 0) 0, .data (.root 0) 1,
  .data (.root 0) 2, .data (.root 0) 3]
private def old : Value graph (.array (.prim .bool)) :=
  .array ⟨3, by decide⟩ ⟨2, by decide⟩ (by decide) (fun _ => .present (.prim true))
private def result : Value graph (.array (.prim .bool)) :=
  .array ⟨3, by decide⟩ ⟨1, by decide⟩ (by decide)
    (fun i => if i.val = 1 then .present (.prim false) else .present (.prim true))
private def store : Store := fun l => if l = .root 0 then two else if l = .root 2 then seven else
  if l = .data (.root 0) 0 ∨ l = .data (.root 0) 1 ∨ l = .data (.root 0) 2 then one else zero
private def machine : WordStore := fun a => if a = 0 then two else if a = 2 then seven else
  if a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 12 then one else zero
private def final : WordStore := writeWord (writeWord machine 5 zero) 0 one
private def after : Store := Representation.write (Representation.write store (.data base 1) zero) base one
private def path (i : Index) : TypeGraph.Path graph (.array (.prim .bool)) (.prim .bool) := .cons (.index i) .nil
private def numericView (m : WordStore) := (m 0, m 4, m 5, m 6, m 7, m 8, m 12, m 2)

private theorem run : FiniteRun 16 4 1 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> decide
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp only [Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initial : Transport 16 hash locations store machine := by
  intro l member
  simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem before : Represented old (PrimitivePop.queries indices) base store := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed
    change some two = some word at observed
    cases observed
    rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed
    change some one = some word at observed
    cases observed
    rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed
    change some one = some word at observed
    cases observed
    rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed
    change some one = some word at observed
    cases observed
    rfl
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed
    change (none : Option Semantics.Word) = some word at observed
    cases observed
private theorem covered : ∀ q ∈ PrimitivePop.queries (G := graph) (p := .bool) indices,
    q.location base ∈ locations := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Both algorithm executions are actual reductions, with a PRESENT cleared
slot rather than an absent-default substitution. -/
theorem executions : recursivePop old = some result ∧ PrimitivePop.execute 16 hash base machine = some final := by
  constructor
  · simp only [recursivePop, old, result, Value.length, Value.extent, Value.slots,
      dif_pos (by decide : 0 < 2)]
    congr 2
  · rfl

/-- Concrete application of the generic FULL selected-query result. -/
theorem full_certificate : ∃ m : WordStore,
    PrimitivePop.execute 16 hash base machine = some m ∧
    Represented result (PrimitivePop.queries indices) base after ∧
    Transport 16 hash locations after m ∧
    (∀ q ∈ PrimitivePop.queries (G := graph) (p := .bool) indices, ∀ word,
      q.read result = some word → m ((q.location base).word 16 hash) = word) ∧
    (∀ a, a ≠ 0 → a ≠ 5 → m a = machine a) :=
  PrimitivePop.complete_numeric run old result executions.1 indices base store machine before initial covered
    (by decide)

/-- All ordered observations: header/extent, BOTH live words and older shadow,
malformed read, retained vs live aliases, numeric map/sentinel frame words. -/
theorem ordered :
    (old.length.val, old.extent.val, old.observe (path (ix 0)), old.observe (path (ix 1)),
      old.observe (path (ix 2)), old.observe (path (ix 3)),
      result.length.val, result.extent.val, result.observe (path (ix 0)), result.observe (path (ix 1)),
      result.observe (path (ix 2)), result.observe (path (ix 3)),
      ((path (ix 1)).readLive Value.dflt old).map Value.head,
      ((path (ix 1)).readLive Value.dflt result).map Value.head,
      ((path (ix 2)).readLive Value.dflt old).map Value.head,
      ((path (ix 2)).readLive Value.dflt result).map Value.head,
      numericView machine, numericView final) =
    (2, 3, some true, some true, some true, none,
      1, 3, some true, some false, some true, none,
      some true, none, none, none,
      (two, one, one, one, zero, one, one, seven), (one, one, zero, one, zero, one, one, seven)) := rfl

private def wrongFirst : WordStore := writeWord (writeWord machine 4 zero) 0 one
private def wrongExtent : WordStore := writeWord (writeWord (writeWord final 4 zero) 6 zero) 0 one
/-- Wrong slot and whole-extent clearing change distinct retained observations. -/
theorem negatives :
    wrongFirst 5 ≠ final 5 ∧ wrongFirst 4 ≠ final 4 ∧ wrongExtent 6 ≠ final 6 ∧
    ¬ (∀ q ∈ PrimitivePop.queries (G := graph) (p := .bool) indices, ∀ word,
      q.read result = some word → wrongFirst ((q.location base).word 16 hash) = word) ∧
    ¬ (∀ q ∈ PrimitivePop.queries (G := graph) (p := .bool) indices, ∀ word,
      q.read result = some word → wrongExtent ((q.location base).word 16 hash) = word) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro bad
    have wrong := bad (PrimitivePop.elementQuery (ix 1))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) zero rfl
    exact (by decide : one ≠ zero) wrong
  · intro bad
    have wrong := bad (PrimitivePop.elementQuery (ix 2))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) one rfl
    exact (by decide : zero ≠ one) wrong

theorem wrong_ordered :
    (numericView wrongFirst, numericView wrongExtent) =
    ((one, zero, one, one, zero, one, one, seven), (one, zero, zero, zero, zero, one, one, seven)) := rfl

private def empty : Value graph (.array (.prim .bool)) :=
  .array ⟨3, by decide⟩ ⟨0, by decide⟩ (by decide) (fun _ => .present (.prim true))
private def emptyMachine : WordStore := writeWord machine 0 zero
private def emptyStore : Store := Representation.write store base zero
private theorem emptyBefore : Represented empty [.length .nil] base emptyStore := by
  intro q member
  simp only [List.mem_singleton] at member
  subst q
  refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
  intro word observed
  change some zero = some word at observed
  cases observed
  rfl

/-- Real represented empty retained array, not a fabricated malformed world.
Both Option failures match; every retained word is still observable. -/
theorem empty_failure : recursivePop empty = none ∧
    PrimitivePop.execute 16 hash base emptyMachine = none ∧
    (PrimitivePop.execute 16 hash base emptyMachine = none ↔ recursivePop empty = none) := by
  refine ⟨rfl, rfl, ?_⟩
  exact PrimitivePop.failure_matches empty base emptyStore emptyMachine hash locations emptyBefore
    (transport_write run initial base List.mem_cons_self zero) List.mem_cons_self

theorem empty_ordered :
    (empty.length.val, empty.extent.val, empty.observe (path (ix 0)), empty.observe (path (ix 1)),
      empty.observe (path (ix 2)), empty.observe (path (ix 3)),
      ((path (ix 0)).readLive Value.dflt empty).map Value.head,
      ((path (ix 1)).readLive Value.dflt empty).map Value.head,
      ((path (ix 2)).readLive Value.dflt empty).map Value.head, numericView emptyMachine) =
    (0, 3, some true, some true, some true, none, none, none, none,
      (zero, one, one, one, zero, one, one, seven)) := rfl

private def regrown : Value graph (.array (.prim .bool)) :=
  .array ⟨3, by decide⟩ ⟨2, by decide⟩ (by decide)
    (fun i => if i.val = 1 then .absent else .present (.prim true))
private def regrownMachine : WordStore := writeWord (writeWord final 5 zero) 0 two

theorem regrow_executions : operationPush result = some regrown ∧
    LifecycleNumeric.pushPrimitive 16 hash base final = some regrownMachine := by
  constructor
  · simp only [operationPush, result, regrown, Value.length, Value.extent, Value.slots,
      TypeGraph.Ty.isPrimitive, true_and, dif_pos (by decide : 1 + 1 < 2 ^ 256)]
    congr 2
    funext i
    have inside : i.val < 3 := i.isLt
    by_cases equal : i.val = 1
    · simp only [if_pos equal]
    · simp only [if_neg equal, dif_pos inside]
  · rfl

theorem regrow_ordered :
    (regrown.length.val, regrown.extent.val,
      regrown.observe (path (ix 0)), regrown.observe (path (ix 1)),
      regrown.observe (path (ix 2)), regrown.observe (path (ix 3)),
      ((path (ix 1)).readLive Value.dflt old).map Value.head,
      ((path (ix 1)).readLive Value.dflt result).map Value.head,
      ((path (ix 1)).readLive Value.dflt regrown).map Value.head,
      result.slots ⟨1, by decide⟩, regrown.slots ⟨1, by decide⟩,
      numericView regrownMachine) =
    (2, 3, some true, some false, some true, none, some true, none, some false,
      Slot.present (Value.prim (G := graph) (p := .bool) false), Slot.absent, (two, one, zero, one, zero, one, one, seven)) := rfl

private def absentOld : Value graph (.array (.prim .bool)) :=
  .array ⟨3, by decide⟩ ⟨2, by decide⟩ (by decide)
    (fun i => if i.val = 1 then .absent else .present (.prim true))
private def absentResult : Value graph (.array (.prim .bool)) :=
  .array ⟨3, by decide⟩ ⟨1, by decide⟩ (by decide)
    (fun i => if i.val = 1 then .absent else .present (.prim true))
private def absentMachine : WordStore := writeWord machine 5 zero

theorem absent_executions : recursivePop absentOld = some absentResult ∧
    PrimitivePop.execute 16 hash base absentMachine = some final := by
  constructor
  · simp only [recursivePop, absentOld, absentResult, Value.length, Value.extent, Value.slots,
      dif_pos (by decide : 0 < 2)]
    congr 2
    funext i
    by_cases equal : i.val = 1
    · simp only [if_pos equal, recursiveClearSlot]
    · simp only [if_neg equal]
  · rw [PrimitivePop.execute_known hash base absentMachine (⟨2, by decide⟩ : Index) rfl,
      dif_pos (by decide : 0 < 2)]
    apply congrArg some
    change writeWord (writeWord (writeWord machine 5 zero) 5 zero) 0 one =
      writeWord (writeWord machine 5 zero) 0 one
    apply congrArg (fun m => writeWord m 0 one)
    funext a
    simp only [writeWord]
    split <;> rfl

theorem absent_ordered :
    (absentOld.length.val, absentOld.extent.val, absentResult.length.val, absentResult.extent.val,
      absentOld.observe (path (ix 0)), absentOld.observe (path (ix 1)), absentOld.observe (path (ix 2)),
      absentOld.observe (path (ix 3)), absentResult.observe (path (ix 0)), absentResult.observe (path (ix 1)),
      absentResult.observe (path (ix 2)), absentResult.observe (path (ix 3)),
      absentOld.slots ⟨1, by decide⟩, absentResult.slots ⟨1, by decide⟩,
      ((path (ix 1)).readLive Value.dflt absentOld).map Value.head,
      ((path (ix 1)).readLive Value.dflt absentResult).map Value.head,
      numericView absentMachine, numericView final) =
    (2, 3, 1, 3, some true, some false, some true, none, some true, some false, some true, none,
      Slot.absent, Slot.absent, some false, none,
      (two, one, zero, one, zero, one, one, seven), (one, one, zero, one, zero, one, one, seven)) := rfl

/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.executions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms executions
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.full_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms full_certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.negatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms negatives
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.wrong_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.empty_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_failure
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.empty_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.regrow_executions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms regrow_executions
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.regrow_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms regrow_ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.absent_executions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_executions
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.absent_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms absent_ordered

private def observedStore : Store := Representation.write store (.data base 3) seven
private def observedNumeric : WordStore := writeWord machine 7 seven
private def observedFinal : WordStore := writeWord (writeWord observedNumeric 5 zero) 0 one
private def observedAfter : Store := Representation.write (Representation.write observedStore (.data base 1) zero) base one
private theorem observedInitial : Transport 16 hash locations observedStore observedNumeric :=
  transport_write run initial (.data base 3) (by decide) seven
private theorem observedBefore : Represented old (PrimitivePop.queries indices) base observedStore := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (change _ < lmax ∧ True; decide)
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)
    | (intro value observed; change (none : Option Semantics.Word) = some value at observed; cases observed)
private noncomputable def target : Evm.Machine :=
  { Evm.Machine.init (fun a => if a.val = 2 then 100 else 50) ⟨2,by decide⟩ with
    store := ⟨fun slot => if slot = .root 8 ∨ slot = .root 12 then TargetOperations.encodeWord one else
      TargetOperations.encodeWord (observedStore (Solidity.Storage.ofSlot slot))⟩
    stack := [.val (TargetOperations.encodeWord seven),.slot (.root 9)]
    mem := fun i => .val (Evm.wmod (i + 11))
    accepts := fun a _ => a.val != 3
    caller := TargetOperations.encodeWord seven
    callvalue := TargetOperations.encodeWord one
    timestamp := TargetOperations.encodeWord two }
private noncomputable def headerTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) 1 }
private noncomputable def resultTarget : Evm.Machine := { headerTarget with store := Evm.WordStore.write headerTarget.store (.data (.root 0) 1) 0 }
private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> exact True.intro
private theorem targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (observedStore l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Header-only published component needs the separate retained-tail clear.
This is a new observation obligation, not a change to its original interface. -/
theorem header_only_counter : Evm.run (TargetPrimitivePop.headerCode (.root 0)) target = .ok headerTarget 0 ∧
    (PrimitivePop.elementQuery (ix 1)).read result = some zero ∧ headerTarget.store (.data (.root 0) 1) = 1 ∧
    ¬ Represented result (PrimitivePop.queries indices) base (Representation.write observedStore base one) := by
  refine ⟨?_,rfl,rfl,?_⟩
  · rw [TargetPrimitivePop.run_header]; rfl
  · intro wrong
    have invalid := (wrong (PrimitivePop.elementQuery (ix 1)) (by
      simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
      exact Or.inr (Or.inr (Or.inl True.intro)))).2.2 zero rfl
    change one = zero at invalid
    exact (by decide : one ≠ zero) invalid

/-- GENERAL actual guarded pop/reset target and independent numeric operation
agree with OLD source/region premises and the full retained-query relation. -/
theorem target_pop_bridge : Evm.run (TargetPrimitivePop.code (.root 0)) target = .ok resultTarget 0 ∧
    PrimitivePop.execute 16 hash base observedNumeric = some observedFinal ∧
    Represented result (PrimitivePop.queries indices) base observedAfter ∧
    Transport 16 hash locations observedAfter observedFinal ∧
    (∀ l (member : l ∈ locations), resultTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (observedFinal (l.word 16 hash))) := by
  obtain ⟨actual,numericExecuted,executed,owner,transported,agreement⟩ := TargetPrimitivePop.complete_numeric run old result executions.1
    indices base True.intro observedStore target observedNumeric fitting observedBefore observedInitial targetInitial covered (by decide)
  have expected : PrimitivePop.execute 16 hash base observedNumeric = some observedFinal := rfl
  have same := Option.some.inj (numericExecuted.symm.trans expected)
  subst actual
  exact ⟨executed,numericExecuted,owner,transported,agreement⟩
private def targetSlots : List Evm.Slot := [.root 0,.data (.root 0) 0,.data (.root 0) 1,.data (.root 0) 2,.data (.root 0) 3,.root 8,.root 12,.root 2]
private def targetView (m : Evm.Machine) := targetSlots.map (fun slot => m.store slot)
private def graphView (v : Value graph (.array (.prim .bool))) :=
  (v.length.val,v.extent.val,v.observe (path (ix 0)),v.observe (path (ix 1)),v.observe (path (ix 2)),v.observe (path (ix 3)),
    ((path (ix 1)).readLive Value.dflt v).map Value.head,((path (ix 2)).readLive Value.dflt v).map Value.head)

/-- COMPLETE graph/raw-live, eight numeric and eight target observations include
header-only midpoint, older shadow and failed-source garbage7. -/
theorem target_pop_complete_observations :
    (graphView old,graphView result,numericView observedNumeric,numericView observedFinal,targetView target,targetView headerTarget,targetView resultTarget) =
    ((2,3,some true,some true,some true,none,some true,none),(1,3,some true,some false,some true,none,none,none),
     (two,one,one,one,seven,one,one,seven),(one,one,zero,one,seven,one,one,seven),
     [2,1,1,1,7,1,1,7],[1,1,1,1,7,1,1,7],[1,1,0,1,7,1,1,7]) := rfl
private def contextView (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.mem 5,m.bal ⟨2,by decide⟩,m.bal ⟨3,by decide⟩,m.bal₀ ⟨2,by decide⟩,m.self,
    m.accepts ⟨3,by decide⟩ ⟨1,by decide⟩,m.caller,m.callvalue,m.timestamp)

theorem target_pop_context : (contextView headerTarget,contextView resultTarget) = (contextView target,contextView target) ∧
    contextView target =
      ([.val (TargetOperations.encodeWord seven),.slot (.root 9)],.val ⟨11,by decide⟩,.val ⟨16,by decide⟩,
       100,50,100,⟨2,by decide⟩,false,TargetOperations.encodeWord seven,TargetOperations.encodeWord one,TargetOperations.encodeWord two) := ⟨rfl,rfl⟩
private noncomputable def wrongFirstTarget : Evm.Machine := { headerTarget with store := Evm.WordStore.write headerTarget.store (.data (.root 0) 0) 0 }
private noncomputable def wrongExtentTarget : Evm.Machine := { resultTarget with store := Evm.WordStore.write (Evm.WordStore.write resultTarget.store (.data (.root 0) 2) 0) (.data (.root 0) 3) 0 }

/-- ACTUAL wrong-slot/whole-extent instruction sequences are discriminated in
COMPLETE target views: both older shadow1 and failed raw7 must survive. -/
theorem target_pop_wrong_slots :
    Evm.run (TargetPrimitivePop.headerCode (.root 0) ++ TargetOperations.writeCode (.data (.root 0) 0) zero) target = .ok wrongFirstTarget 0 ∧
    Evm.run (TargetPrimitivePop.code (.root 0) ++ (TargetOperations.writeCode (.data (.root 0) 2) zero ++ TargetOperations.writeCode (.data (.root 0) 3) zero)) target = .ok wrongExtentTarget 0 ∧
    (targetView wrongFirstTarget,targetView wrongExtentTarget,targetView resultTarget) =
      ([1,0,1,1,7,1,1,7],[1,1,0,0,0,1,1,7],[1,1,0,1,7,1,1,7]) := by
  refine ⟨?_,?_,rfl⟩
  · rw [Evm.run_append_ok header_only_counter.1]
    rfl
  · rw [Evm.run_append_ok target_pop_bridge.1]
    rfl
private noncomputable def emptyTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) 0 }

theorem target_pop_empty_failure : recursivePop empty = none ∧
    Evm.run (TargetPrimitivePop.code (.root 0)) emptyTarget = .revert ∧
    targetView emptyTarget = [0,1,1,1,7,1,1,7] :=
  ⟨empty_failure.1,(TargetPrimitivePop.failure_matches empty (.root 0) emptyTarget rfl).mpr empty_failure.1,rfl⟩
private noncomputable def changedTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) 3 }
private noncomputable def changedResultTarget : Evm.Machine := { changedTarget with store := Evm.WordStore.write (Evm.WordStore.write changedTarget.store (.root 0) 2) (.data (.root 0) 2) 0 }

/-- Changed CURRENT header3 clears index2, not the old fixture's index1.
This raw-machine control asserts no OLD source relation for the changed input. -/
theorem target_pop_changed_current : Evm.run (TargetPrimitivePop.code (.root 0)) changedTarget = .ok changedResultTarget 0 ∧
    (targetView changedTarget,targetView changedResultTarget) = ([3,1,1,1,7,1,1,7],[2,1,1,0,7,1,1,7]) := by
  refine ⟨?_,rfl⟩
  rw [TargetPrimitivePop.run_current]
  rfl

/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.header_only_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_only_counter
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.target_pop_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_pop_bridge
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.target_pop_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_pop_complete_observations
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.target_pop_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_pop_context
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.target_pop_wrong_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_pop_wrong_slots
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.target_pop_empty_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_pop_empty_failure
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.target_pop_changed_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_pop_changed_current

private def three : Semantics.Word := lengthWord 3 (by decide)
private def pushResult : Value graph (.array (.prim .bool)) := (operationPush old).getD old
private def pushNumeric : WordStore := writeWord (writeWord observedNumeric 6 zero) 0 three
private def pushStore : Store := Representation.write (Representation.write observedStore (.data base 2) zero) base three
private noncomputable def pushHeaderTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) 3 }
private noncomputable def pushTarget : Evm.Machine := { pushHeaderTarget with store := Evm.WordStore.write pushHeaderTarget.store (.data (.root 0) 2) 0 }

/-- GENERAL current-header push/reset certificate on a retained true slot.
Exact owner IFF is consumed at the inhabited coverage bound, not assumed post. -/
theorem primitive_reused_push_bridge : Evm.run (TargetPrimitivePush.code (.root 0)) target = .ok pushTarget 0 ∧
    LifecycleNumeric.pushPrimitive 16 hash base observedNumeric = some pushNumeric ∧
    Represented pushResult (PrimitivePop.queries indices) base pushStore ∧ Transport 16 hash locations pushStore pushNumeric := by
  obtain ⟨actual,numericExecuted,executed,ownerIff,transported,_⟩ := TargetPrimitivePush.complete_numeric run old pushResult rfl
    indices base True.intro observedStore target observedNumeric fitting observedBefore observedInitial targetInitial (by decide) (by decide)
  have expected : LifecycleNumeric.pushPrimitive 16 hash base observedNumeric = some pushNumeric := rfl
  have same := Option.some.inj (numericExecuted.symm.trans expected); subst actual
  exact ⟨executed,numericExecuted,ownerIff.mpr (by decide),transported⟩
private def freshPushOld : Value graph (.array (.prim .bool)) := .array ⟨2,by decide⟩ (ix 2) (by decide) (fun _ => .present (.prim true))
private def freshPushResult := (operationPush freshPushOld).getD freshPushOld
private def freshPushStore : Store := Representation.write observedStore (.data base 2) seven
private def freshPushNumeric : WordStore := writeWord observedNumeric 6 seven
private def freshPushAfter : Store := Representation.write (Representation.write freshPushStore (.data base 2) zero) base three
private def freshPushFinal : WordStore := writeWord (writeWord freshPushNumeric 6 zero) 0 three
private noncomputable def freshPushTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.data (.root 0) 2) 7 }
private noncomputable def freshPushHeaderTarget : Evm.Machine := { freshPushTarget with store := Evm.WordStore.write freshPushTarget.store (.root 0) 3 }
private noncomputable def freshPushResultTarget : Evm.Machine := { freshPushHeaderTarget with store := Evm.WordStore.write freshPushHeaderTarget.store (.data (.root 0) 2) 0 }
private theorem freshPushInitial : Transport 16 hash locations freshPushStore freshPushNumeric :=
  transport_write run observedInitial (.data base 2) (by decide) seven
private theorem freshPushBefore : Represented freshPushOld (PrimitivePop.queries indices) base freshPushStore := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (change _ < lmax ∧ True; decide)
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some two = some value at observed; cases observed; rfl)
    | (intro value observed; change (none : Option Semantics.Word) = some value at observed; cases observed)
private theorem freshPushTargetInitial : ∀ l (member : l ∈ locations), freshPushTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (freshPushStore l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Fresh old None/dirty7 becomes0 through ACTUAL reset, without zero-origin
history or an old failed-read-zero assumption. -/
theorem primitive_fresh_push_bridge : Evm.run (TargetPrimitivePush.code (.root 0)) freshPushTarget = .ok freshPushResultTarget 0 ∧
    LifecycleNumeric.pushPrimitive 16 hash base freshPushNumeric = some freshPushFinal ∧
    Represented freshPushResult (PrimitivePop.queries indices) base freshPushAfter ∧ Transport 16 hash locations freshPushAfter freshPushFinal := by
  obtain ⟨actual,numericExecuted,executed,ownerIff,transported,_⟩ := TargetPrimitivePush.complete_numeric run freshPushOld freshPushResult rfl
    indices base True.intro freshPushStore freshPushTarget freshPushNumeric fitting freshPushBefore freshPushInitial freshPushTargetInitial (by decide) (by decide)
  have expected : LifecycleNumeric.pushPrimitive 16 hash base freshPushNumeric = some freshPushFinal := rfl
  have same := Option.some.inj (numericExecuted.symm.trans expected); subst actual
  exact ⟨executed,numericExecuted,ownerIff.mpr (by decide),transported⟩

/-- COMPLETE retained/fresh graph and8numeric/target observations, including
actual header-only midpoint, expose resets of both reused1 and fresh dirty7. -/
theorem primitive_push_complete_observations :
    (graphView old,graphView pushResult,graphView freshPushOld,graphView freshPushResult,
      numericView observedNumeric,numericView pushNumeric,numericView freshPushNumeric,numericView freshPushFinal,
      targetView target,targetView pushHeaderTarget,targetView pushTarget,
      targetView freshPushTarget,targetView freshPushHeaderTarget,targetView freshPushResultTarget) =
    ((2,3,some true,some true,some true,none,some true,none),(3,3,some true,some true,some false,none,some true,some false),
     (2,2,some true,some true,none,none,some true,none),(3,3,some true,some true,some false,none,some true,some false),
     (two,one,one,one,seven,one,one,seven),(three,one,one,zero,seven,one,one,seven),
     (two,one,one,seven,seven,one,one,seven),(three,one,one,zero,seven,one,one,seven),
     [2,1,1,1,7,1,1,7],[3,1,1,1,7,1,1,7],[3,1,1,0,7,1,1,7],
     [2,1,1,7,7,1,1,7],[3,1,1,7,7,1,1,7],[3,1,1,0,7,1,1,7]) := rfl
private def zeroPushResult := (operationPush empty).getD empty
private def zeroPushStore : Store := Representation.write observedStore base zero
private def zeroPushNumeric : WordStore := writeWord observedNumeric 0 zero
private def zeroPushAfter : Store := Representation.write (Representation.write zeroPushStore (.data base 0) zero) base one
private def zeroPushFinal : WordStore := writeWord (writeWord zeroPushNumeric 4 zero) 0 one
private noncomputable def zeroPushTarget : Evm.Machine := { emptyTarget with store := Evm.WordStore.write (Evm.WordStore.write emptyTarget.store (.root 0) 1) (.data (.root 0) 0) 0 }
private theorem zeroPushBefore : Represented empty (PrimitivePop.queries indices) base zeroPushStore := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | exact True.intro
    | exact ⟨by decide,by decide⟩
    | (change _ < lmax ∧ True; decide)
    | (intro value observed; change some one = some value at observed; cases observed; rfl)
    | (intro value observed; change some zero = some value at observed; cases observed; rfl)
    | (intro value observed; change (none : Option Semantics.Word) = some value at observed; cases observed)
private theorem zeroPushInitial : Transport 16 hash locations zeroPushStore zeroPushNumeric :=
  transport_write run observedInitial base List.mem_cons_self zero
private theorem zeroPushTargetInitial : ∀ l (member : l ∈ locations), emptyTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (zeroPushStore l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem primitive_zero_reuse_bridge : Evm.run (TargetPrimitivePush.code (.root 0)) emptyTarget = .ok zeroPushTarget 0 ∧
    Represented zeroPushResult (PrimitivePop.queries indices) base zeroPushAfter ∧ Transport 16 hash locations zeroPushAfter zeroPushFinal := by
  obtain ⟨actual,numericExecuted,executed,ownerIff,transported,_⟩ := TargetPrimitivePush.complete_numeric run empty zeroPushResult rfl
    indices base True.intro zeroPushStore emptyTarget zeroPushNumeric fitting zeroPushBefore zeroPushInitial zeroPushTargetInitial (by decide) (by decide)
  have expected : LifecycleNumeric.pushPrimitive 16 hash base zeroPushNumeric = some zeroPushFinal := rfl
  have same := Option.some.inj (numericExecuted.symm.trans expected); subst actual
  exact ⟨executed,ownerIff.mpr (by decide),transported⟩

/-- Older retained shadows stay true/non-live after zero-length reuse; the one
new live primitive resetsfalse while failed source raw7 survives. -/
theorem primitive_zero_reuse_observations : (graphView empty,graphView zeroPushResult,numericView zeroPushNumeric,numericView zeroPushFinal,
    targetView emptyTarget,targetView zeroPushTarget,(path (ix 0)).readLive Value.dflt zeroPushResult |>.map Value.head) =
    ((0,3,some true,some true,some true,none,none,none),(1,3,some false,some true,some true,none,none,none),
     (zero,one,one,one,seven,one,one,seven),(one,zero,one,one,seven,one,one,seven),
     [0,1,1,1,7,1,1,7],[1,0,1,1,7,1,1,7],some false) := rfl

theorem primitive_push_context :
    (contextView pushHeaderTarget,contextView pushTarget,contextView freshPushTarget,contextView freshPushResultTarget,contextView zeroPushTarget) =
      (contextView target,contextView target,contextView target,contextView target,contextView target) := rfl
private noncomputable def wrongPushFirst : Evm.Machine := { pushHeaderTarget with store := Evm.WordStore.write pushHeaderTarget.store (.data (.root 0) 0) 0 }
private noncomputable def wrongZeroExtent : Evm.Machine := { zeroPushTarget with store := Evm.WordStore.write (Evm.WordStore.write zeroPushTarget.store (.data (.root 0) 1) 0) (.data (.root 0) 2) 0 }
private noncomputable def wrongZeroFailed : Evm.Machine := { zeroPushTarget with store := Evm.WordStore.write zeroPushTarget.store (.data (.root 0) 3) 0 }

theorem primitive_push_wrong_targets :
    Evm.run (TargetHeaderPush.code (.root 0) ++ TargetOperations.writeCode (.data (.root 0) 0) zero) target = .ok wrongPushFirst 0 ∧
    Evm.run (TargetPrimitivePush.code (.root 0) ++ (TargetOperations.writeCode (.data (.root 0) 1) zero ++ TargetOperations.writeCode (.data (.root 0) 2) zero)) emptyTarget = .ok wrongZeroExtent 0 ∧
    Evm.run (TargetPrimitivePush.code (.root 0) ++ TargetOperations.writeCode (.data (.root 0) 3) zero) emptyTarget = .ok wrongZeroFailed 0 ∧
    (targetView wrongPushFirst,targetView wrongZeroExtent,targetView wrongZeroFailed) =
      ([3,0,1,1,7,1,1,7],[1,0,0,0,7,1,1,7],[1,0,1,1,0,1,1,7]) := by
  refine ⟨?_,?_,?_,rfl⟩
  · have head : Evm.run (TargetHeaderPush.code (.root 0)) target = .ok pushHeaderTarget 0 := by rw [TargetHeaderPush.run_current]; rfl
    rw [Evm.run_append_ok head]; rfl
  · rw [Evm.run_append_ok primitive_zero_reuse_bridge.1]; rfl
  · rw [Evm.run_append_ok primitive_zero_reuse_bridge.1]; rfl
private noncomputable def changedPushTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) 1 }
private noncomputable def changedPushResult : Evm.Machine := { changedPushTarget with store := Evm.WordStore.write (Evm.WordStore.write changedPushTarget.store (.root 0) 2) (.data (.root 0) 1) 0 }

theorem primitive_push_changed_current : Evm.run (TargetPrimitivePush.code (.root 0)) changedPushTarget = .ok changedPushResult 0 ∧
    (targetView changedPushTarget,targetView changedPushResult) = ([1,1,1,1,7,1,1,7],[2,1,0,1,7,1,1,7]) := by
  refine ⟨?_,rfl⟩
  rw [TargetPrimitivePush.run_current]; rfl
private def maxIndex : Index := ⟨2 ^ 256 - 1,by decide⟩
private def maxPushOld : Value graph (.array (.prim .bool)) := .array ⟨2 ^ 256,by decide⟩ maxIndex (by decide) (fun _ => .absent)
private noncomputable def maxPushTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) (Evm.W - 1) }

theorem primitive_push_capacity_revert : operationPush maxPushOld = none ∧
    Evm.run (TargetPrimitivePush.code (.root 0)) maxPushTarget = .revert ∧
    targetView maxPushTarget = [Evm.W - 1,1,1,1,7,1,1,7] :=
  ⟨rfl,(TargetPrimitivePush.failure_matches maxPushOld (.root 0) maxPushTarget rfl).mpr rfl,rfl⟩


/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_reused_push_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_reused_push_bridge
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_fresh_push_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_fresh_push_bridge
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_push_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_push_complete_observations
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_zero_reuse_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_zero_reuse_bridge
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_zero_reuse_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_zero_reuse_observations
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_push_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_push_context
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_push_wrong_targets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_push_wrong_targets
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_push_changed_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_push_changed_current
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_push_capacity_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_push_capacity_revert


private def cycleResult := (operationPush result).getD result
private def cycleNumeric : WordStore := writeWord (writeWord observedFinal 5 zero) 0 two
private def cycleStore : Store := Representation.write (Representation.write observedAfter (.data base 1) zero) base two
private noncomputable def cycleTarget : Evm.Machine := { resultTarget with store := Evm.WordStore.write (Evm.WordStore.write resultTarget.store (.root 0) 2) (.data (.root 0) 1) 0 }

/-- Actual concatenated target and numeric execution through DERIVED pop
intermediate evidence; postowner is not an intermediate preservation premise. -/
theorem primitive_cycle_bridge : Evm.run (TargetPrimitivePopPush.code (.root 0)) target = .ok cycleTarget 0 ∧
    TargetPrimitivePopPush.execute 16 hash base observedNumeric = some cycleNumeric ∧
    Represented cycleResult (PrimitivePop.queries indices) base cycleStore ∧ Transport 16 hash locations cycleStore cycleNumeric := by
  obtain ⟨actual,numericExecuted,executed,owner,transported,_⟩ := TargetPrimitivePopPush.complete_numeric run old result cycleResult executions.1 rfl
    indices base True.intro observedStore target observedNumeric fitting observedBefore observedInitial targetInitial covered (by decide)
  have expected : TargetPrimitivePopPush.execute 16 hash base observedNumeric = some cycleNumeric := rfl
  have same := Option.some.inj (numericExecuted.symm.trans expected); subst actual
  exact ⟨executed,numericExecuted,owner,transported⟩

/-- COMPLETE old/pop/regrow graph, numeric and target vectors. The header and
extent return, but last oldtrue becomesfalse, while older shadowtrue and raw7
survive. Thus neither heap identity nor old aggregate restoration is claimed. -/
theorem primitive_cycle_complete_observations :
    (graphView old,graphView result,graphView cycleResult,
     numericView observedNumeric,numericView observedFinal,numericView cycleNumeric,
     targetView target,targetView resultTarget,targetView cycleTarget,
     ((path (ix 1)).readLive Value.dflt old).map Value.head,
     ((path (ix 1)).readLive Value.dflt result).map Value.head,
     ((path (ix 1)).readLive Value.dflt cycleResult).map Value.head,
     contextView cycleTarget) =
    ((2,3,some true,some true,some true,none,some true,none),
     (1,3,some true,some false,some true,none,none,none),
     (2,3,some true,some false,some true,none,some false,none),
     (two,one,one,one,seven,one,one,seven),(one,one,zero,one,seven,one,one,seven),(two,one,zero,one,seven,one,one,seven),
     [2,1,1,1,7,1,1,7],[1,1,0,1,7,1,1,7],[2,1,0,1,7,1,1,7],some true,none,some false,contextView target) := rfl
private def reversedResult := (recursivePop pushResult).getD pushResult
private def reversedNumeric : WordStore := (PrimitivePop.execute 16 hash base pushNumeric).getD pushNumeric
private noncomputable def reversedTarget : Evm.Machine := { pushTarget with store := Evm.WordStore.write (Evm.WordStore.write pushTarget.store (.root 0) 2) (.data (.root 0) 2) 0 }

/-- SAME-target operations do not commute. ACTUAL reversed target instructions
and numeric execution leave last old live celltrue but erase the older shadow. -/
theorem primitive_cycle_wrong_order :
    Evm.run (TargetPrimitivePush.code (.root 0) ++ TargetPrimitivePop.code (.root 0)) target = .ok reversedTarget 0 ∧
    LifecycleNumeric.pushPrimitive 16 hash base observedNumeric = some pushNumeric ∧
    PrimitivePop.execute 16 hash base pushNumeric = some reversedNumeric ∧
    (graphView reversedResult,graphView cycleResult,numericView reversedNumeric,numericView cycleNumeric,
      targetView reversedTarget,targetView cycleTarget,contextView reversedTarget) =
      ((2,3,some true,some true,some false,none,some true,none),
       (2,3,some true,some false,some true,none,some false,none),
       (two,one,one,zero,seven,one,one,seven),(two,one,zero,one,seven,one,one,seven),
       [2,1,1,0,7,1,1,7],[2,1,0,1,7,1,1,7],contextView target) := by
  refine ⟨?_,primitive_reused_push_bridge.2.1,rfl,rfl⟩
  rw [Evm.run_append_ok primitive_reused_push_bridge.1,TargetPrimitivePop.run_current]
  rfl

theorem primitive_cycle_empty : recursivePop empty = none ∧
    TargetPrimitivePopPush.execute 16 hash base zeroPushNumeric = none ∧
    Evm.run (TargetPrimitivePopPush.code (.root 0)) emptyTarget = .revert ∧
    (graphView empty,numericView zeroPushNumeric,targetView emptyTarget,contextView emptyTarget) =
      ((0,3,some true,some true,some true,none,none,none),(zero,one,one,one,seven,one,one,seven),[0,1,1,1,7,1,1,7],contextView target) :=
  ⟨rfl,rfl,TargetPrimitivePopPush.run_empty (.root 0) emptyTarget rfl,rfl⟩
private def maxCycleMiddle := (recursivePop maxPushOld).getD maxPushOld
private def maxCycleResult := (operationPush maxCycleMiddle).getD maxCycleMiddle
private def maxCycleIndex : Index := ⟨Evm.W - 2,by decide⟩
private noncomputable def maxCycleInput : Evm.Machine := { maxPushTarget with store := Evm.WordStore.write maxPushTarget.store (.data (.root 0) (Evm.W - 2)) 7 }
private noncomputable def maxCyclePopTarget : Evm.Machine := { maxCycleInput with store := Evm.WordStore.write (Evm.WordStore.write maxCycleInput.store (.root 0) (Evm.W - 2)) (.data (.root 0) (Evm.W - 2)) 0 }
private noncomputable def maxCycleTarget : Evm.Machine := { maxCyclePopTarget with store := Evm.WordStore.write (Evm.WordStore.write maxCyclePopTarget.store (.root 0) (Evm.W - 1)) (.data (.root 0) (Evm.W - 2)) 0 }

/-- FULL intrinsic capacity is preserved: max-length push alone fails, but pop
then push succeeds. This graph/target control deliberately has NO PUBLIC owner
or finite physical-region claim at this out-of-interface observation bound. -/
theorem primitive_cycle_full_capacity : recursivePop maxPushOld = some maxCycleMiddle ∧
    operationPush maxCycleMiddle = some maxCycleResult ∧
    Evm.run (TargetPrimitivePopPush.code (.root 0)) maxCycleInput = .ok maxCycleTarget 0 ∧
    (maxPushOld.length.val,maxCycleMiddle.length.val,maxCycleResult.length.val,
     targetView maxCycleInput,targetView maxCyclePopTarget,targetView maxCycleTarget,contextView maxCycleTarget,
     maxCycleInput.store (.data (.root 0) (Evm.W-2)),maxCyclePopTarget.store (.data (.root 0) (Evm.W-2)),maxCycleTarget.store (.data (.root 0) (Evm.W-2)),
     maxPushOld.observe (path maxCycleIndex),maxCycleMiddle.observe (path maxCycleIndex),maxCycleResult.observe (path maxCycleIndex),
     ((path maxCycleIndex).readLive Value.dflt maxPushOld).map Value.head,((path maxCycleIndex).readLive Value.dflt maxCycleMiddle).map Value.head,((path maxCycleIndex).readLive Value.dflt maxCycleResult).map Value.head) =
      (Evm.W-1,Evm.W-2,Evm.W-1,[Evm.W-1,1,1,1,7,1,1,7],[Evm.W-2,1,1,1,7,1,1,7],[Evm.W-1,1,1,1,7,1,1,7],contextView target,7,0,0,some false,some false,some false,some false,none,some false) := by
  refine ⟨rfl,rfl,?_,rfl⟩
  have first : Evm.run (TargetPrimitivePop.code (.root 0)) maxCycleInput = .ok maxCyclePopTarget 0 := by
    rw [TargetPrimitivePop.run_current]; rfl
  unfold TargetPrimitivePopPush.code
  rw [Evm.run_append_ok first,TargetPrimitivePush.run_current]
  rfl


/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_cycle_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_cycle_bridge
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_cycle_complete_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_cycle_complete_observations
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_cycle_wrong_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_cycle_wrong_order
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_cycle_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_cycle_empty
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_cycle_full_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_cycle_full_capacity


private theorem singleMember (i : Index) (inside : i ∈ indices) (q : Query graph (.array (.prim .bool)))
    (member : q ∈ PrimitivePop.queries [i]) : q ∈ PrimitivePop.queries indices := by
  simp only [PrimitivePop.queries,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,inside,rfl⟩)
private def readInput (m : Evm.Machine) (i : Index) : Evm.Machine := { m with stack := .val ⟨i.val,i.isLt⟩ :: .slot (.root 0) :: m.stack }
private def readOutput (m : Evm.Machine) (word : Semantics.Word) : Evm.Machine := { m with stack := .val (TargetOperations.encodeWord word) :: m.stack }

/-- OLD GOOD represented/numeric/target evidence is actually applied to a
runtime-index read. Operand evaluation remains an input-stack boundary. -/
theorem primitive_live_read_bridge : Evm.run TargetArrayRead.code (readInput target (ix 1)) = .ok (readOutput target one) 0 ∧
    observedNumeric 5 = one := by
  apply TargetArrayRead.complete_read old (ix 1) (.prim true) rfl base True.intro observedStore target target.stack observedNumeric hash locations
    (fun q member => observedBefore q (singleMember (ix 1) (by decide) q member)) observedInitial (by decide)
  intro q member
  exact targetInitial (q.location base) (covered q (singleMember (ix 1) (by decide) q member))

/-- Same typed runtime path after actual pop→push reads changedfalse. The
DERIVED postowner/Transport/target agreement, not a new post premise, is used. -/
theorem primitive_regrown_read_bridge : Evm.run TargetArrayRead.code (readInput cycleTarget (ix 1)) = .ok (readOutput cycleTarget zero) 0 ∧
    cycleNumeric 5 = zero := by
  obtain ⟨actual,numericExecuted,_,owner,transported,agreement⟩ := TargetPrimitivePopPush.complete_numeric run old result cycleResult executions.1 rfl
    indices base True.intro observedStore target observedNumeric fitting observedBefore observedInitial targetInitial covered (by decide)
  have expected : TargetPrimitivePopPush.execute 16 hash base observedNumeric = some cycleNumeric := rfl
  have same := Option.some.inj (numericExecuted.symm.trans expected); subst actual
  apply TargetArrayRead.complete_read cycleResult (ix 1) (.prim false) rfl base True.intro cycleStore cycleTarget cycleTarget.stack cycleNumeric hash locations
    (fun q member => owner q (singleMember (ix 1) (by decide) q member)) transported (by decide)
  intro q member
  have cover := covered q (singleMember (ix 1) (by decide) q member)
  exact (agreement _ cover).trans (congrArg TargetOperations.encodeWord (transported _ cover))

/-- Retained true, popped retainedfalse, out-of-extent dirty7 and empty retained
slots ALL fail the actual LIVE bound. No failed query is equated to numeric0. -/
theorem primitive_live_read_failures :
    Evm.run TargetArrayRead.code (readInput target (ix 2)) = .revert ∧
    Evm.run TargetArrayRead.code (readInput target (ix 3)) = .revert ∧
    Evm.run TargetArrayRead.code (readInput resultTarget (ix 1)) = .revert ∧
    Evm.run TargetArrayRead.code (readInput emptyTarget (ix 0)) = .revert ∧
    (old.observe (path (ix 2)),old.observe (path (ix 3)),result.observe (path (ix 1)),empty.observe (path (ix 0)),
     ((path (ix 2)).readLive Value.dflt old).map Value.head,((path (ix 3)).readLive Value.dflt old).map Value.head,
     ((path (ix 1)).readLive Value.dflt result).map Value.head,((path (ix 0)).readLive Value.dflt empty).map Value.head,
     observedNumeric 6,observedNumeric 7,observedFinal 5,zeroPushNumeric 4) =
      (some true,none,some false,some true,none,none,none,none,one,seven,zero,one) := by
  exact ⟨(TargetArrayRead.failure_matches old (ix 2) target target.stack (.root 0) rfl).mpr rfl,
    (TargetArrayRead.failure_matches old (ix 3) target target.stack (.root 0) rfl).mpr rfl,
    (TargetArrayRead.failure_matches result (ix 1) resultTarget resultTarget.stack (.root 0) rfl).mpr rfl,
    (TargetArrayRead.failure_matches empty (ix 0) emptyTarget emptyTarget.stack (.root 0) rfl).mpr rfl,rfl⟩

/-- Actual unchecked element-address/SLOAD observes the retained word that the
live guarded program rejects. Runtime index changes also select changed words. -/
theorem primitive_live_read_wrong_controls :
    Evm.run (Evm.elemSlot 1 ++ [.sload]) (readInput target (ix 2)) = .ok (readOutput target one) 0 ∧
    Evm.run TargetArrayRead.code (readInput cycleTarget (ix 0)) = .ok (readOutput cycleTarget one) 0 ∧
    Evm.run TargetArrayRead.code (readInput cycleTarget (ix 1)) = .ok (readOutput cycleTarget zero) 0 ∧
    (targetView target,targetView cycleTarget,targetView (readOutput target one),targetView (readOutput cycleTarget zero),
     (readOutput target one).stack,(readOutput cycleTarget one).stack,(readOutput cycleTarget zero).stack) =
      ([2,1,1,1,7,1,1,7],[2,1,0,1,7,1,1,7],[2,1,1,1,7,1,1,7],[2,1,0,1,7,1,1,7],
       .val (TargetOperations.encodeWord one) :: target.stack,.val (TargetOperations.encodeWord one) :: target.stack,.val (TargetOperations.encodeWord zero) :: target.stack) := by
  refine ⟨?_,?_,primitive_regrown_read_bridge.1,rfl⟩
  · unfold readInput
    rw [Evm.run_append_ok (Evm.elemSlot_run target target.stack (ix 2).val 1 (.root 0) (ix 2).isLt)]
    rfl
  · unfold readInput
    rw [TargetArrayRead.run_current]; rfl
private def defaultReadOld : Value graph (.array (.prim .bool)) := .array ⟨3,by decide⟩ (ix 2) (by decide) (fun _ => .absent)
private def defaultReadStore : Store := Representation.write observedStore (.data base 0) zero
private def defaultReadNumeric : WordStore := writeWord observedNumeric 4 zero
private noncomputable def defaultReadTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.data (.root 0) 0) 0 }
private theorem defaultReadBefore : Represented defaultReadOld (PrimitivePop.queries [ix 0]) base defaultReadStore := by
  intro q member
  simp only [PrimitivePop.queries,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some two = some word at observed; cases observed; rfl
  · refine ⟨?_,True.intro,?_⟩
    · change 0 < lmax ∧ True; decide
    · intro word observed; change some zero = some word at observed; cases observed; rfl

/-- Actual absent live slot defaults tofalse and is represented by its OLD
successful default read. Absence itself never supplies a numeric-zero axiom. -/
theorem primitive_default_live_read : Evm.run TargetArrayRead.code (readInput defaultReadTarget (ix 0)) = .ok (readOutput defaultReadTarget zero) 0 ∧
    defaultReadNumeric 4 = zero ∧
    (graphView defaultReadOld,numericView defaultReadNumeric,targetView defaultReadTarget,targetView (readOutput defaultReadTarget zero),
      (readOutput defaultReadTarget zero).stack) =
      ((2,3,some false,some false,some false,none,some false,none),(two,zero,one,one,seven,one,one,seven),
       [2,0,1,1,7,1,1,7],[2,0,1,1,7,1,1,7],.val (TargetOperations.encodeWord zero) :: target.stack) := by
  refine ⟨?_,rfl,rfl⟩
  apply TargetArrayRead.represented_read defaultReadOld (ix 0) (.prim false) rfl base True.intro defaultReadStore defaultReadTarget defaultReadTarget.stack defaultReadBefore
  intro q member
  simp only [PrimitivePop.queries,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> rfl


/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_live_read_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_live_read_bridge
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_regrown_read_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_regrown_read_bridge
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_live_read_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_live_read_failures
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_live_read_wrong_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_live_read_wrong_controls
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_default_live_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_default_live_read


private def writeContexts : List (Query graph (.array (.prim .bool))) := [PrimitivePop.elementQuery (ix 0),PrimitivePop.elementQuery (ix 2),PrimitivePop.elementQuery (ix 3)]
private theorem writeContextMember (q : Query graph (.array (.prim .bool))) (member : q ∈ writeContexts) : q ∈ PrimitivePop.queries indices := by
  simp only [writeContexts,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals apply List.mem_cons_of_mem; apply List.mem_map.mpr
  · exact ⟨ix 0,by decide,rfl⟩
  · exact ⟨ix 2,by decide,rfl⟩
  · exact ⟨ix 3,by decide,rfl⟩
private theorem writeApart : ∀ q ∈ writeContexts, q.apart (TargetArrayRead.path (G := graph) (p := .bool) (ix 1)) := by
  intro q member
  simp only [writeContexts,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals exact Apart.fork (.index _ _ (by decide)) .nil .nil
private theorem writeNonalias : ∀ q ∈ writeContexts, q.location base ≠ pathLoc (TargetArrayRead.path (G := graph) (p := .bool) (ix 1)) base := by
  intro q member
  simp only [writeContexts,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp only [PrimitivePop.element_location,TargetArrayWrite.location]; decide
private theorem writeSupported : PathSupported (TargetArrayRead.path (G := graph) (p := .bool) (ix 1)) :=
  (observedBefore (PrimitivePop.elementQuery (ix 1)) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ix 1,by decide,rfl⟩))).1
private def writeResult := (TargetArrayWrite.writeAt old (ix 1) false).getD old
private def writeStore : Store := Representation.write observedStore (.data base 1) zero
private def writeNumeric : WordStore := writeWord observedNumeric 5 zero
private noncomputable def writeTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.data (.root 0) 1) 0 }
private def writeSelected : List (Query graph (.array (.prim .bool))) := .length .nil :: .word (TargetArrayRead.path (ix 1)) :: writeContexts
private def writeInput (m : Evm.Machine) (i : Index) (word : Semantics.Word) : Evm.Machine := { m with stack := .val ⟨i.val,i.isLt⟩ :: .slot (.root 0) :: .val (TargetOperations.encodeWord word) :: m.stack }

theorem primitive_live_write_bridge : Evm.run TargetArrayWrite.code (writeInput target (ix 1) zero) = .ok writeTarget 0 ∧
    Represented writeResult writeSelected base writeStore ∧ Transport 16 hash locations writeStore writeNumeric ∧
    (∀ l (member : l ∈ locations), writeTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (writeStore l)) := by
  exact TargetArrayWrite.complete_numeric run old writeResult (ix 1) false rfl writeContexts base True.intro observedStore observedNumeric target target.stack
    (fun q member => by have same := List.mem_singleton.mp member; subst q; exact observedBefore _ List.mem_cons_self)
    (fun q member => observedBefore q (writeContextMember q member)) writeSupported writeApart writeNonalias observedInitial (by decide) (by decide) fitting targetInitial

/-- COMPLETE graph/raw-live, eight numeric/target words and context show the
changed actual write; both old shadowtrue and failed raw7 remain unchanged. -/
theorem primitive_live_write_observations :
    (graphView old,graphView writeResult,numericView observedNumeric,numericView writeNumeric,targetView target,targetView writeTarget,
     ((path (ix 1)).readLive Value.dflt writeResult).map Value.head,contextView writeTarget) =
      ((2,3,some true,some true,some true,none,some true,none),(2,3,some true,some false,some true,none,some false,none),
       (two,one,one,one,seven,one,one,seven),(two,one,zero,one,seven,one,one,seven),
       [2,1,1,1,7,1,1,7],[2,1,0,1,7,1,1,7],some false,contextView target) := rfl
private def retainedRawResult := (old.save (path (ix 2)) (.prim false)).getD old
private noncomputable def uncheckedWriteTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.data (.root 0) 2) 0 }
private noncomputable def wrongIndexWriteTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.data (.root 0) 0) 0 }

/-- Raw retained save succeeds and changes shadow; live operation and ACTUAL
guard reject it. Unchecked SSTORE and wrong runtime index are discriminated. -/
theorem primitive_live_write_negative :
    old.save (path (ix 2)) (.prim false) = some retainedRawResult ∧ TargetArrayWrite.writeAt old (ix 2) false = none ∧
    Evm.run TargetArrayWrite.code (writeInput target (ix 2) zero) = .revert ∧
    Evm.run TargetArrayWrite.code (writeInput target (ix 3) zero) = .revert ∧
    Evm.run TargetArrayWrite.code (writeInput emptyTarget (ix 0) zero) = .revert ∧
    Evm.run (Evm.elemSlot 1 ++ [.sstore]) (writeInput target (ix 2) zero) = .ok uncheckedWriteTarget 0 ∧
    Evm.run TargetArrayWrite.code (writeInput target (ix 0) zero) = .ok wrongIndexWriteTarget 0 ∧
    (graphView retainedRawResult,targetView uncheckedWriteTarget,targetView wrongIndexWriteTarget,targetView writeTarget) =
      ((2,3,some true,some true,some false,none,some true,none),[2,1,1,0,7,1,1,7],[2,0,1,1,7,1,1,7],[2,1,0,1,7,1,1,7]) := by
  refine ⟨rfl,rfl,(TargetArrayWrite.failure_matches old (ix 2) false target target.stack (.root 0) rfl).mpr rfl,
    (TargetArrayWrite.failure_matches old (ix 3) false target target.stack (.root 0) rfl).mpr rfl,
    (TargetArrayWrite.failure_matches empty (ix 0) false emptyTarget emptyTarget.stack (.root 0) rfl).mpr rfl,?_,?_,rfl⟩
  · unfold writeInput
    rw [Evm.run_append_ok (Evm.elemSlot_run target (.val (TargetOperations.encodeWord zero) :: target.stack) (ix 2).val 1 (.root 0) (ix 2).isLt)]
    rfl
  · unfold writeInput
    rw [TargetArrayWrite.run_current]; rfl
private def rewrittenResult := (TargetArrayWrite.writeAt writeResult (ix 1) true).getD writeResult
private def rewrittenStore : Store := Representation.write writeStore (.data base 1) one
private def rewrittenNumeric : WordStore := writeWord writeNumeric 5 one
private noncomputable def rewrittenTarget : Evm.Machine := { writeTarget with store := Evm.WordStore.write writeTarget.store (.data (.root 0) 1) 1 }

/-- Second runtime value is consumed from the evolving stack/store. OLD to
middle evidence is derived by the first actual write, not assumed. -/
theorem primitive_evolving_write_values : Evm.run TargetArrayWrite.code (writeInput writeTarget (ix 1) one) = .ok rewrittenTarget 0 ∧
    Represented rewrittenResult writeSelected base rewrittenStore ∧ Transport 16 hash locations rewrittenStore rewrittenNumeric ∧
    (graphView rewrittenResult,numericView rewrittenNumeric,targetView rewrittenTarget,contextView rewrittenTarget) =
      ((2,3,some true,some true,some true,none,some true,none),(two,one,one,one,seven,one,one,seven),[2,1,1,1,7,1,1,7],contextView target) := by
  have header : Represented writeResult [.length .nil] base writeStore := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact primitive_live_write_bridge.2.1 _ List.mem_cons_self
  have context : Represented writeResult writeContexts base writeStore := by
    intro q member; exact primitive_live_write_bridge.2.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have second := TargetArrayWrite.complete_numeric run writeResult rewrittenResult (ix 1) true rfl writeContexts base True.intro writeStore writeNumeric writeTarget writeTarget.stack
    header context writeSupported writeApart writeNonalias primitive_live_write_bridge.2.2.1 (by decide) (by decide) fitting primitive_live_write_bridge.2.2.2
  exact ⟨second.1,second.2.1,second.2.2.1,rfl⟩
private def absentWriteResult := (TargetArrayWrite.writeAt defaultReadOld (ix 0) true).getD defaultReadOld
private noncomputable def absentWriteTarget : Evm.Machine := { defaultReadTarget with store := Evm.WordStore.write defaultReadTarget.store (.data (.root 0) 0) 1 }

/-- An actual absent LIVE slot is initialized by the runtime value; no old
failed-read-zero inference or whole-aggregate representation claim is made. -/
theorem primitive_absent_live_write : TargetArrayWrite.writeAt defaultReadOld (ix 0) true = some absentWriteResult ∧
    Evm.run TargetArrayWrite.code (writeInput defaultReadTarget (ix 0) one) = .ok absentWriteTarget 0 ∧
    (graphView defaultReadOld,graphView absentWriteResult,targetView defaultReadTarget,targetView absentWriteTarget,contextView absentWriteTarget) =
      ((2,3,some false,some false,some false,none,some false,none),(2,3,some true,some false,some false,none,some false,none),
       [2,0,1,1,7,1,1,7],[2,1,1,1,7,1,1,7],contextView target) := by
  refine ⟨rfl,?_,rfl⟩
  unfold writeInput
  rw [TargetArrayWrite.run_current]; rfl


/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_live_write_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_live_write_bridge
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_live_write_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_live_write_observations
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_live_write_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_live_write_negative
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_evolving_write_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_evolving_write_values
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_absent_live_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_absent_live_write


private noncomputable def runtimeClearTarget := TargetArrayClear.afterClear target target.stack (.root 0)
private def clearValue := recursiveClear old
private def clearPrefixValue (count : Nat) : Value graph (.array (.prim .bool)) :=
  .array ⟨3,by decide⟩ (ix 2) (by decide) (clearArrayPrefix (fun _ => Slot.present (Value.prim true)) count)
private noncomputable def clearIteration (count : Fin Evm.W) := TargetArrayClear.iterationMachine target target.stack (.root 0) ⟨2,by decide⟩ count

theorem primitive_runtime_clear_execution : Evm.run TargetArrayClear.code { target with stack := .slot (.root 0) :: target.stack } = .ok runtimeClearTarget 0 ∧
    (graphView old,graphView clearValue,targetView target,targetView runtimeClearTarget,contextView runtimeClearTarget) =
      ((2,3,some true,some true,some true,none,some true,none),(0,3,some false,some false,some true,none,none,none),
       [2,1,1,1,7,1,1,7],[0,0,0,1,7,1,1,7],contextView target) :=
  ⟨TargetArrayClear.run_current target target.stack (.root 0),rfl⟩

/-- Actual finite prefix and restart of the structured target loop, with COMPLETE
ordered source-prefix/target vectors and live-versus-retained observations. -/
theorem primitive_runtime_clear_prefix_restart :
    Evm.loopIterN (Evm.run TargetArrayClear.condition) (Evm.run TargetArrayClear.body) 1 (clearIteration ⟨0,by decide⟩) = .inl (clearIteration ⟨1,by decide⟩) ∧
    Evm.run [.loop TargetArrayClear.condition TargetArrayClear.body] (clearIteration ⟨1,by decide⟩) = .ok (clearIteration ⟨2,by decide⟩) 0 ∧
    Evm.run TargetArrayClear.finish (clearIteration ⟨2,by decide⟩) = .ok runtimeClearTarget 0 ∧
    (graphView old,graphView (clearPrefixValue 1),graphView (clearPrefixValue 2),graphView clearValue,
     targetView (clearIteration ⟨0,by decide⟩),targetView (clearIteration ⟨1,by decide⟩),targetView (clearIteration ⟨2,by decide⟩),targetView runtimeClearTarget) =
      ((2,3,some true,some true,some true,none,some true,none),(2,3,some false,some true,some true,none,some true,none),
       (2,3,some false,some false,some true,none,some false,none),(0,3,some false,some false,some true,none,none,none),
       [2,1,1,1,7,1,1,7],[2,0,1,1,7,1,1,7],[2,0,0,1,7,1,1,7],[0,0,0,1,7,1,1,7]) := by
  refine ⟨?_,?_,?_,rfl⟩
  · exact TargetArrayClear.iterations_prefix target target.stack (.root 0) ⟨2,by decide⟩ 1 ⟨0,by decide⟩ (by decide)
  · exact TargetArrayClear.run_loop_from target target.stack (.root 0) ⟨2,by decide⟩ ⟨1,by decide⟩ (by decide)
  · exact TargetArrayClear.run_finish target target.stack (.root 0) ⟨2,by decide⟩
private def oneClearValue : Value graph (.array (.prim .bool)) := .array ⟨3,by decide⟩ (ix 1) (by decide) (fun _ => .present (.prim true))
private def threeClearValue : Value graph (.array (.prim .bool)) := .array ⟨3,by decide⟩ (ix 3) (by decide) (fun _ => .present (.prim true))
private noncomputable def oneRuntimeClearTarget := TargetArrayClear.afterClear changedPushTarget target.stack (.root 0)
private noncomputable def threeRuntimeClearTarget := TargetArrayClear.afterClear changedTarget target.stack (.root 0)
private noncomputable def emptyRuntimeClearTarget := TargetArrayClear.afterClear emptyTarget target.stack (.root 0)

theorem primitive_runtime_clear_lengths :
    Evm.run TargetArrayClear.code { emptyTarget with stack := .slot (.root 0) :: target.stack } = .ok emptyRuntimeClearTarget 0 ∧
    Evm.run TargetArrayClear.code { changedPushTarget with stack := .slot (.root 0) :: target.stack } = .ok oneRuntimeClearTarget 0 ∧
    Evm.run TargetArrayClear.code { changedTarget with stack := .slot (.root 0) :: target.stack } = .ok threeRuntimeClearTarget 0 ∧
    (graphView empty,graphView (recursiveClear empty),graphView oneClearValue,graphView (recursiveClear oneClearValue),
     graphView threeClearValue,graphView (recursiveClear threeClearValue),
     targetView emptyTarget,targetView emptyRuntimeClearTarget,targetView changedPushTarget,targetView oneRuntimeClearTarget,targetView changedTarget,targetView threeRuntimeClearTarget) =
      ((0,3,some true,some true,some true,none,none,none),(0,3,some true,some true,some true,none,none,none),
       (1,3,some true,some true,some true,none,none,none),(0,3,some false,some true,some true,none,none,none),
       (3,3,some true,some true,some true,none,some true,some true),(0,3,some false,some false,some false,none,none,none),
       [0,1,1,1,7,1,1,7],[0,1,1,1,7,1,1,7],[1,1,1,1,7,1,1,7],[0,0,1,1,7,1,1,7],[3,1,1,1,7,1,1,7],[0,0,0,0,7,1,1,7]) :=
  ⟨TargetArrayClear.run_current emptyTarget target.stack (.root 0),TargetArrayClear.run_current changedPushTarget target.stack (.root 0),
    TargetArrayClear.run_current changedTarget target.stack (.root 0),rfl⟩
private noncomputable def fourthHeaderTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store (.root 0) 4 }
private noncomputable def fourthRuntimeClearTarget := TargetArrayClear.afterClear fourthHeaderTarget target.stack (.root 0)

/-- ACTUAL wrong programs zero header first, use retained extent3 as live length,
or overrun to failed raw7. Their COMPLETE vectors distinguish all three errors. -/
theorem primitive_runtime_clear_negative :
    Evm.run (TargetOperations.writeCode (.root 0) zero ++ (.push (.slot (.root 0)) :: TargetArrayClear.code)) target = .ok emptyRuntimeClearTarget 0 ∧
    Evm.run (TargetOperations.writeCode (.root 0) three ++ (.push (.slot (.root 0)) :: TargetArrayClear.code)) target = .ok threeRuntimeClearTarget 0 ∧
    Evm.run (TargetOperations.writeCode (.root 0) (lengthWord 4 (by decide)) ++ (.push (.slot (.root 0)) :: TargetArrayClear.code)) target = .ok fourthRuntimeClearTarget 0 ∧
    (targetView emptyRuntimeClearTarget,targetView threeRuntimeClearTarget,targetView fourthRuntimeClearTarget,targetView runtimeClearTarget) =
      ([0,1,1,1,7,1,1,7],[0,0,0,0,7,1,1,7],[0,0,0,0,0,1,1,7],[0,0,0,1,7,1,1,7]) := by
  refine ⟨?_,?_,?_,rfl⟩
  · rw [Evm.run_append_ok (TargetOperations.run_write (.root 0) zero target)]
    exact TargetArrayClear.run_current emptyTarget target.stack (.root 0)
  · rw [Evm.run_append_ok (TargetOperations.run_write (.root 0) three target)]
    exact TargetArrayClear.run_current changedTarget target.stack (.root 0)
  · rw [Evm.run_append_ok (TargetOperations.run_write (.root 0) (lengthWord 4 (by decide)) target)]
    exact TargetArrayClear.run_current fourthHeaderTarget target.stack (.root 0)
private noncomputable def writtenRuntimeClearTarget := TargetArrayClear.afterClear writeTarget writeTarget.stack (.root 0)

theorem primitive_runtime_clear_after_write :
    Evm.run (TargetArrayWrite.code ++ (.push (.slot (.root 0)) :: TargetArrayClear.code)) (writeInput target (ix 1) zero) = .ok writtenRuntimeClearTarget 0 ∧
    (graphView old,graphView writeResult,graphView (recursiveClear writeResult),targetView target,targetView writeTarget,targetView writtenRuntimeClearTarget,contextView writtenRuntimeClearTarget) =
      ((2,3,some true,some true,some true,none,some true,none),(2,3,some true,some false,some true,none,some false,none),
       (0,3,some false,some false,some true,none,none,none),[2,1,1,1,7,1,1,7],[2,1,0,1,7,1,1,7],[0,0,0,1,7,1,1,7],contextView target) := by
  refine ⟨?_,rfl⟩
  rw [Evm.run_append_ok primitive_live_write_bridge.1]
  exact TargetArrayClear.run_current writeTarget writeTarget.stack (.root 0)
private noncomputable def clearFamilyTarget (length : Fin Evm.W) : Evm.Machine :=
  { target with store := Evm.WordStore.write (Evm.WordStore.ofFn (fun _ => 1)) (.root 0) length.val }

/-- ALL finite runtime word lengths, including0 andW-1, have inhabited target
inputs and kernel termination. The boundary shadow is1 and is never cleared.
This is no external evaluation/whole Source or PUBLIC metadata-coverage claim. -/
theorem primitive_runtime_clear_all_lengths (length : Fin Evm.W) :
    Evm.run TargetArrayClear.code { clearFamilyTarget length with stack := .slot (.root 0) :: target.stack } =
      .ok (TargetArrayClear.afterClear (clearFamilyTarget length) target.stack (.root 0)) 0 ∧
    (TargetArrayClear.afterClear (clearFamilyTarget length) target.stack (.root 0)).store (.root 0) = 0 ∧
    (TargetArrayClear.afterClear (clearFamilyTarget length) target.stack (.root 0)).store (.data (.root 0) length.val) = 1 ∧
    (TargetArrayClear.afterClear (clearFamilyTarget length) target.stack (.root 0)).store (.data (.root 0) 0) = (if 0 < length.val then 0 else 1) := by
  have header : (clearFamilyTarget length).store (.root 0) = length.val := Evm.WordStore.write_same_of_lt _ _ _ length.isLt
  refine ⟨TargetArrayClear.run_current (clearFamilyTarget length) target.stack (.root 0),TargetArrayClear.after_header _ _ _,?_,?_⟩
  · rw [TargetArrayClear.after_data,header,if_neg (Nat.lt_irrefl _)]
    rw [clearFamilyTarget,Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
    rfl
  · rw [TargetArrayClear.after_data,header]
    have oldWord : (clearFamilyTarget length).store (.data (.root 0) 0) = 1 := by
      rw [clearFamilyTarget,Evm.WordStore.write_other _ _ (by intro impossible; cases impossible)]
      rfl
    rw [oldWord]


/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_runtime_clear_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_runtime_clear_execution
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_runtime_clear_prefix_restart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_runtime_clear_prefix_restart
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_runtime_clear_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_runtime_clear_lengths
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_runtime_clear_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_runtime_clear_negative
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_runtime_clear_after_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_runtime_clear_after_write
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_runtime_clear_all_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_runtime_clear_all_lengths


private theorem neededClearBefore (value : Value graph (.array (.prim .bool))) (source : Store)
    (before : Represented value (PrimitivePop.queries indices) base source) :
    Represented value (TargetClearRepresentation.oldQueries value indices) base source := by
  intro q member
  apply before q
  simp only [TargetClearRepresentation.oldQueries,PrimitivePop.queries,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨i,inside,rfl⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,(List.mem_filter.mp inside).1,rfl⟩)
private theorem clearGeneratedCovered : ∀ j, j < old.length.val → Solidity.Storage.Loc.data base j ∈ locations := by
  intro j inside
  change j < 2 at inside
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with rfl | rfl <;> decide
private def runtimeClearStore := TargetClearRepresentation.afterStore old base observedStore
private def runtimeClearNumeric := TargetClearRepresentation.execute 16 hash base observedNumeric

theorem primitive_represented_clear_bridge :
    Evm.run TargetArrayClear.code { target with stack := .slot (.root 0) :: target.stack } = .ok runtimeClearTarget 0 ∧
    Represented old.clear (PrimitivePop.queries indices) base runtimeClearStore ∧ Transport 16 hash locations runtimeClearStore runtimeClearNumeric ∧
    (∀ l (member : l ∈ locations), runtimeClearTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (runtimeClearNumeric (l.word 16 hash))) ∧
    (∀ q ∈ PrimitivePop.queries (G := graph) (p := .bool) indices, ∀ word, q.read old.clear = some word → runtimeClearNumeric ((q.location base).word 16 hash) = word) :=
  TargetClearRepresentation.complete run old indices base True.intro observedStore observedNumeric target target.stack
    (neededClearBefore old observedStore observedBefore) observedInitial covered clearGeneratedCovered fitting targetInitial

/-- COMPLETE independent source/numeric/target vector, including retainedtrue
and failed raw7, after actual runtime traversal and PUBLIC composition. -/
theorem primitive_represented_clear_observations :
    (graphView old,graphView old.clear,numericView observedNumeric,numericView runtimeClearNumeric,targetView target,targetView runtimeClearTarget,
     old.clear.observe (path (ix 3)),runtimeClearNumeric 7,contextView runtimeClearTarget) =
      ((2,3,some true,some true,some true,none,some true,none),(0,3,some false,some false,some true,none,none,none),
       (two,one,one,one,seven,one,one,seven),(zero,zero,zero,one,seven,one,one,seven),
       [2,1,1,1,7,1,1,7],[0,0,0,1,7,1,1,7],none,seven,contextView target) := rfl
private def dirtyClearOld : Value graph (.array (.prim .bool)) := .array ⟨3,by decide⟩ (ix 2) (by decide)
  (fun i => if i.val < 2 then .absent else .present (.prim true))
private def dirtyClearStore : Store := Representation.write (Representation.write observedStore (.data base 0) seven) (.data base 1) seven
private def dirtyClearNumeric : WordStore := writeWord (writeWord observedNumeric 4 seven) 5 seven
private noncomputable def dirtyClearTarget : Evm.Machine := { target with store := Evm.WordStore.write (Evm.WordStore.write target.store (.data (.root 0) 0) 7) (.data (.root 0) 1) 7 }
private def dirtyClearedStore := TargetClearRepresentation.afterStore dirtyClearOld base dirtyClearStore
private def dirtyClearedNumeric := TargetClearRepresentation.execute 16 hash base dirtyClearNumeric
private noncomputable def dirtyClearedTarget := TargetArrayClear.afterClear dirtyClearTarget target.stack (.root 0)
private theorem dirtyClearBefore : Represented dirtyClearOld (TargetClearRepresentation.oldQueries dirtyClearOld indices) base dirtyClearStore := by
  intro q member
  change q ∈ [.length .nil,PrimitivePop.elementQuery (ix 2),PrimitivePop.elementQuery (ix 3)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some two = some word at observed; cases observed; rfl
  · refine ⟨?_,True.intro,?_⟩
    · change 2 < lmax ∧ True; decide
    · intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨?_,True.intro,?_⟩
    · change 3 < lmax ∧ True; decide
    · intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
private theorem dirtyClearInitial : Transport 16 hash locations dirtyClearStore dirtyClearNumeric :=
  transport_write run (transport_write run observedInitial (.data base 0) (by decide) seven) (.data base 1) (by decide) seven
private theorem dirtyClearTargetInitial : ∀ l (member : l ∈ locations), dirtyClearTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (dirtyClearStore l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- OLD needed-query relation is explicitly partial: live defaults are0 but
raw bytes7 are overwritten, not assumed represented. Source absence remains
absent. The DERIVED postowner covers every requested successful word. -/
theorem primitive_represented_clear_absent_garbage :
    Evm.run TargetArrayClear.code { dirtyClearTarget with stack := .slot (.root 0) :: target.stack } = .ok dirtyClearedTarget 0 ∧
    Represented dirtyClearOld.clear (PrimitivePop.queries indices) base dirtyClearedStore ∧ Transport 16 hash locations dirtyClearedStore dirtyClearedNumeric ∧
    (∀ l (member : l ∈ locations), dirtyClearedTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (dirtyClearedNumeric (l.word 16 hash))) ∧
    (graphView dirtyClearOld,graphView dirtyClearOld.clear,numericView dirtyClearNumeric,numericView dirtyClearedNumeric,
     targetView dirtyClearTarget,targetView dirtyClearedTarget,dirtyClearOld.slots ⟨0,by decide⟩,dirtyClearOld.clear.slots ⟨0,by decide⟩,contextView dirtyClearedTarget) =
      ((2,3,some false,some false,some true,none,some false,none),(0,3,some false,some false,some true,none,none,none),
       (two,seven,seven,one,seven,one,one,seven),(zero,zero,zero,one,seven,one,one,seven),
       [2,7,7,1,7,1,1,7],[0,0,0,1,7,1,1,7],.absent,.absent,contextView target) := by
  have result := TargetClearRepresentation.complete run dirtyClearOld indices base True.intro dirtyClearStore dirtyClearNumeric dirtyClearTarget target.stack
    dirtyClearBefore dirtyClearInitial covered clearGeneratedCovered fitting dirtyClearTargetInitial
  exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,rfl⟩
private theorem writtenClearBefore : Represented writeResult (TargetClearRepresentation.oldQueries writeResult indices) base writeStore := by
  intro q member
  change q ∈ [.length .nil,PrimitivePop.elementQuery (ix 2),PrimitivePop.elementQuery (ix 3)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact primitive_live_write_bridge.2.1 _ List.mem_cons_self
  · exact primitive_live_write_bridge.2.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact primitive_live_write_bridge.2.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
private def writtenClearedStore := TargetClearRepresentation.afterStore writeResult base writeStore
private def writtenClearedNumeric := TargetClearRepresentation.execute 16 hash base writeNumeric

/-- Mixed actual write→loop, with OLD-to-middle owner/Transport/target evidence
supplied by the FIRST checked runtime write, not a postrelation hypothesis. -/
theorem primitive_represented_clear_after_write :
    Evm.run (TargetArrayWrite.code ++ (.push (.slot (.root 0)) :: TargetArrayClear.code)) (writeInput target (ix 1) zero) = .ok writtenRuntimeClearTarget 0 ∧
    Represented writeResult.clear (PrimitivePop.queries indices) base writtenClearedStore ∧ Transport 16 hash locations writtenClearedStore writtenClearedNumeric ∧
    (graphView writeResult,graphView writeResult.clear,numericView writeNumeric,numericView writtenClearedNumeric,targetView writeTarget,targetView writtenRuntimeClearTarget,contextView writtenRuntimeClearTarget) =
      ((2,3,some true,some false,some true,none,some false,none),(0,3,some false,some false,some true,none,none,none),
       (two,one,zero,one,seven,one,one,seven),(zero,zero,zero,one,seven,one,one,seven),[2,1,0,1,7,1,1,7],[0,0,0,1,7,1,1,7],contextView target) := by
  have result := TargetClearRepresentation.complete run writeResult indices base True.intro writeStore writeNumeric writeTarget writeTarget.stack
    writtenClearBefore primitive_live_write_bridge.2.2.1 covered clearGeneratedCovered fitting primitive_live_write_bridge.2.2.2
  refine ⟨?_,result.2.1,result.2.2.1,rfl⟩
  rw [Evm.run_append_ok primitive_live_write_bridge.1]
  exact result.1
private def wrongClearHeaderNumeric : WordStore := writeWord observedNumeric 0 three

/-- CURRENT header controls numeric traversal; assigning3 clears old shadow2.
This changed raw input does NOT satisfy the OLD length2 Transport premise. -/
theorem primitive_represented_clear_current_header :
    ¬ Transport 16 hash locations observedStore wrongClearHeaderNumeric ∧
    (numericView wrongClearHeaderNumeric,numericView (TargetClearRepresentation.execute 16 hash base wrongClearHeaderNumeric),numericView runtimeClearNumeric,
     targetView changedTarget,targetView threeRuntimeClearTarget,targetView runtimeClearTarget) =
      ((three,one,one,one,seven,one,one,seven),(zero,zero,zero,zero,seven,one,one,seven),(zero,zero,zero,one,seven,one,one,seven),
       [3,1,1,1,7,1,1,7],[0,0,0,0,7,1,1,7],[0,0,0,1,7,1,1,7]) := by
  refine ⟨?_,rfl⟩
  intro transport
  have invalid := transport base (by decide)
  change three = two at invalid
  exact (by decide : (three : Semantics.Word) ≠ two) invalid

private def outsideClearIndex : Index := ⟨16,by decide⟩

/-- Source None is not a physical-byte frame: outside the covered run data16
aliases changed address4. GOOD run remains valid for its ORIGINAL locations;
no global hash injectivity or zero rule is inferred for unrepresented accesses. -/
theorem primitive_represented_clear_failed_boundary :
    old.observe (path outsideClearIndex) = none ∧ old.clear.observe (path outsideClearIndex) = none ∧
    (Solidity.Storage.Loc.data base 16).word 16 hash = 4 ∧
    (observedNumeric ((Solidity.Storage.Loc.data base 16).word 16 hash),runtimeClearNumeric ((Solidity.Storage.Loc.data base 16).word 16 hash),
     observedNumeric 7,runtimeClearNumeric 7) = (one,zero,seven,seven) ∧
    (Solidity.Storage.Loc.data base 16) ∉ locations ∧
    (graphView old,graphView old.clear,numericView observedNumeric,numericView runtimeClearNumeric,targetView target,targetView runtimeClearTarget,
     target.store (.data (.root 0) 16),runtimeClearTarget.store (.data (.root 0) 16)) =
      ((2,3,some true,some true,some true,none,some true,none),(0,3,some false,some false,some true,none,none,none),
       (two,one,one,one,seven,one,one,seven),(zero,zero,zero,one,seven,one,one,seven),
       [2,1,1,1,7,1,1,7],[0,0,0,1,7,1,1,7],0,0) := ⟨rfl,rfl,rfl,rfl,by decide,rfl⟩


/-- Contrasting covered failed-read word7 is framed by explicit generated
physical separation derived from the ORIGINAL GOOD finite run, not from None. -/
theorem primitive_represented_clear_physical_frame : runtimeClearNumeric 7 = observedNumeric 7 ∧
    old.observe (path (ix 3)) = none ∧ old.clear.observe (path (ix 3)) = none ∧
    (numericView observedNumeric,numericView runtimeClearNumeric,targetView target,targetView runtimeClearTarget) =
      ((two,one,one,one,seven,one,one,seven),(zero,zero,zero,one,seven,one,one,seven),[2,1,1,1,7,1,1,7],[0,0,0,1,7,1,1,7]) := by
  refine ⟨?_,rfl,rfl,rfl⟩
  change TargetClearRepresentation.execute 16 hash base observedNumeric ((Solidity.Storage.Loc.data base 3).word 16 hash) = observedNumeric ((Solidity.Storage.Loc.data base 3).word 16 hash)
  apply TargetClearRepresentation.numeric_outside
  · intro same
    have invalid := run.word_inj (by decide : Solidity.Storage.Loc.data base 3 ∈ locations) (by decide : base ∈ locations) same
    exact (by decide : Solidity.Storage.Loc.data base 3 ≠ base) invalid
  · intro j inside same
    have sourceInside : j < old.length.val := inside
    have equal := run.word_inj (by decide : Solidity.Storage.Loc.data base 3 ∈ locations) (clearGeneratedCovered j sourceInside) same
    have indicesEqual := (Solidity.Storage.Loc.data.inj equal).2
    change j < 2 at inside
    omega


/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_represented_clear_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_represented_clear_bridge
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_represented_clear_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_represented_clear_observations
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_represented_clear_absent_garbage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_represented_clear_absent_garbage
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_represented_clear_after_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_represented_clear_after_write
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_represented_clear_current_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_represented_clear_current_header
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_represented_clear_failed_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_represented_clear_failed_boundary
/-- info: 'Solidity.Backend.StorageOps.PrimitivePopControls.primitive_represented_clear_physical_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_represented_clear_physical_frame

end Solidity.Backend.StorageOps.PrimitivePopControls

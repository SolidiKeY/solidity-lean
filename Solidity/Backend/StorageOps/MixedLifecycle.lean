import Solidity.Backend.StorageOps.LifecycleSchedules

/-! Actual mixed lifecycle blocks over existing runtime location lists.
Both phases invoke the checked concrete operations on successive stores. No
new operation AST/IR, state/value representation or source semantics. Counts
and argument lists are arbitrary finite inputs; failure is not world rollback. -/
namespace Solidity.Backend.StorageOps.MixedLifecycle
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open LifecycleSchedules

def pushPop (N : Nat) (hash : Solidity.Storage.Pre → Nat) (front back : List Solidity.Storage.Loc) (initial : WordStore) : Option WordStore :=
  (pushMany N hash front initial).bind (popMany N hash back)

def pushPopAccesses (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore) : List Solidity.Storage.Loc :=
  pushAccesses N hash front initial ++
    match pushMany N hash front initial with
    | none => []
    | some middle => popAccesses N hash back middle

/-- Existing finite Loc×Word certificate follows ACTUAL first-phase state;
no graph/Source evaluator is defined by the target execution. -/
def pushPopLog (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore) : Option (List (Solidity.Storage.Loc × Semantics.Word)) :=
  (pushMany N hash front initial).bind (fun middle =>
    (pushLog N hash front initial).bind (fun left => (popLog N hash back middle).map (fun right => left ++ right)))

theorem pushPop_failed_first (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore) (failed : pushMany N hash front initial = none) :
    pushPop N hash front back initial = none ∧
      pushPopAccesses N hash front back initial = pushAccesses N hash front initial ∧
      pushPopLog N hash front back initial = none := by
  simp only [pushPop,pushPopAccesses,pushPopLog,failed,Option.bind_none,List.append_nil,and_self]

theorem pushPop_failed_second (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial middle : WordStore)
    (first : pushMany N hash front initial = some middle) (failed : popMany N hash back middle = none) :
    pushPop N hash front back initial = none ∧
      pushPopAccesses N hash front back initial = pushAccesses N hash front initial ++ popAccesses N hash back middle := by
  simp only [pushPop,pushPopAccesses,first,Option.bind_some,failed,and_self]

theorem pushPop_realized (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial final : WordStore)
    (success : pushPop N hash front back initial = some final) :
    ∃ ops, pushPopLog N hash front back initial = some ops ∧
      final = ops.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial := by
  cases first : pushMany N hash front initial with
  | none => simp only [pushPop,first,Option.bind_none] at success; cases success
  | some middle =>
    have second : popMany N hash back middle = some final := by simpa only [pushPop,first,Option.bind_some] using success
    obtain ⟨left,leftLog,leftRealized⟩ := push_realized N hash front initial middle first
    obtain ⟨right,rightLog,rightRealized⟩ := pop_realized N hash back middle final second
    refine ⟨left ++ right,?_,?_⟩
    · simp only [pushPopLog,first,Option.bind_some,leftLog,rightLog,Option.map_some]
    · rw [List.foldl_append,← leftRealized]
      exact rightRealized

theorem pushPop_log_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore)
    (ops : List (Solidity.Storage.Loc × Semantics.Word)) (logged : pushPopLog N hash front back initial = some ops)
    (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ ops) :
    op.1 ∈ pushPopAccesses N hash front back initial := by
  cases first : pushMany N hash front initial with
  | none => simp only [pushPopLog,first,Option.bind_none] at logged; cases logged
  | some middle =>
    obtain ⟨left,leftLog,_⟩ := push_realized N hash front initial middle first
    cases rightLog : popLog N hash back middle with
    | none => simp only [pushPopLog,first,leftLog,rightLog,Option.bind_some,Option.map_none] at logged; cases logged
    | some right =>
      simp only [pushPopLog,first,leftLog,rightLog,Option.bind_some,Option.map_some] at logged
      cases logged
      simp only [pushPopAccesses,first,List.mem_append]
      rcases List.mem_append.mp member with earlier | later
      · exact Or.inl (push_log_touched N hash front initial left leftLog op earlier)
      · exact Or.inr (pop_log_touched N hash back middle right rightLog op later)

/-- Whole mixed-block Transport uses OLD evidence and ACTUAL generated coverage;
no intermediate preservation premise or immutable initial-header replay. -/
theorem pushPop_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (front back : List Solidity.Storage.Loc)
    (store : Store) (initial final : WordStore) (before : Transport N hash locations store initial)
    (success : pushPop N hash front back initial = some final)
    (covered : ∀ l ∈ pushPopAccesses N hash front back initial, l ∈ locations) :
    ∃ ops, pushPopLog N hash front back initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final := by
  obtain ⟨ops,logged,realized⟩ := pushPop_realized N hash front back initial final success
  refine ⟨ops,logged,?_⟩
  rw [realized]
  apply transport_sequence run before
  intro op member
  exact covered op.1 (pushPop_log_touched N hash front back initial ops logged op member)

theorem pushPop_frame (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial final : WordStore)
    (success : pushPop N hash front back initial = some final) (address : Nat)
    (outside : ∀ l ∈ pushPopAccesses N hash front back initial, address ≠ l.word N hash) :
    final address = initial address := by
  obtain ⟨ops,logged,realized⟩ := pushPop_realized N hash front back initial final success
  rw [realized]
  apply sequence_outside_frame
  intro op member
  exact outside op.1 (pushPop_log_touched N hash front back initial ops logged op member)


def popPush (N : Nat) (hash : Solidity.Storage.Pre → Nat) (front back : List Solidity.Storage.Loc) (initial : WordStore) : Option WordStore :=
  (popMany N hash front initial).bind (pushMany N hash back)

def popPushAccesses (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore) : List Solidity.Storage.Loc :=
  popAccesses N hash front initial ++
    match popMany N hash front initial with
    | none => []
    | some middle => pushAccesses N hash back middle

/-- Existing finite Loc×Word certificate follows ACTUAL first-phase state;
no graph/Source evaluator is defined by the target execution. -/
def popPushLog (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore) : Option (List (Solidity.Storage.Loc × Semantics.Word)) :=
  (popMany N hash front initial).bind (fun middle =>
    (popLog N hash front initial).bind (fun left => (pushLog N hash back middle).map (fun right => left ++ right)))

theorem popPush_failed_first (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore) (failed : popMany N hash front initial = none) :
    popPush N hash front back initial = none ∧
      popPushAccesses N hash front back initial = popAccesses N hash front initial ∧
      popPushLog N hash front back initial = none := by
  simp only [popPush,popPushAccesses,popPushLog,failed,Option.bind_none,List.append_nil,and_self]

theorem popPush_failed_second (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial middle : WordStore)
    (first : popMany N hash front initial = some middle) (failed : pushMany N hash back middle = none) :
    popPush N hash front back initial = none ∧
      popPushAccesses N hash front back initial = popAccesses N hash front initial ++ pushAccesses N hash back middle := by
  simp only [popPush,popPushAccesses,first,Option.bind_some,failed,and_self]

theorem popPush_realized (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial final : WordStore)
    (success : popPush N hash front back initial = some final) :
    ∃ ops, popPushLog N hash front back initial = some ops ∧
      final = ops.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial := by
  cases first : popMany N hash front initial with
  | none => simp only [popPush,first,Option.bind_none] at success; cases success
  | some middle =>
    have second : pushMany N hash back middle = some final := by simpa only [popPush,first,Option.bind_some] using success
    obtain ⟨left,leftLog,leftRealized⟩ := pop_realized N hash front initial middle first
    obtain ⟨right,rightLog,rightRealized⟩ := push_realized N hash back middle final second
    refine ⟨left ++ right,?_,?_⟩
    · simp only [popPushLog,first,Option.bind_some,leftLog,rightLog,Option.map_some]
    · rw [List.foldl_append,← leftRealized]
      exact rightRealized

theorem popPush_log_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore)
    (ops : List (Solidity.Storage.Loc × Semantics.Word)) (logged : popPushLog N hash front back initial = some ops)
    (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ ops) :
    op.1 ∈ popPushAccesses N hash front back initial := by
  cases first : popMany N hash front initial with
  | none => simp only [popPushLog,first,Option.bind_none] at logged; cases logged
  | some middle =>
    obtain ⟨left,leftLog,_⟩ := pop_realized N hash front initial middle first
    cases rightLog : pushLog N hash back middle with
    | none => simp only [popPushLog,first,leftLog,rightLog,Option.bind_some,Option.map_none] at logged; cases logged
    | some right =>
      simp only [popPushLog,first,leftLog,rightLog,Option.bind_some,Option.map_some] at logged
      cases logged
      simp only [popPushAccesses,first,List.mem_append]
      rcases List.mem_append.mp member with earlier | later
      · exact Or.inl (pop_log_touched N hash front initial left leftLog op earlier)
      · exact Or.inr (push_log_touched N hash back middle right rightLog op later)

/-- Whole mixed-block Transport uses OLD evidence and ACTUAL generated coverage;
no intermediate preservation premise or immutable initial-header replay. -/
theorem popPush_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (front back : List Solidity.Storage.Loc)
    (store : Store) (initial final : WordStore) (before : Transport N hash locations store initial)
    (success : popPush N hash front back initial = some final)
    (covered : ∀ l ∈ popPushAccesses N hash front back initial, l ∈ locations) :
    ∃ ops, popPushLog N hash front back initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final := by
  obtain ⟨ops,logged,realized⟩ := popPush_realized N hash front back initial final success
  refine ⟨ops,logged,?_⟩
  rw [realized]
  apply transport_sequence run before
  intro op member
  exact covered op.1 (popPush_log_touched N hash front back initial ops logged op member)

theorem popPush_frame (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial final : WordStore)
    (success : popPush N hash front back initial = some final) (address : Nat)
    (outside : ∀ l ∈ popPushAccesses N hash front back initial, address ≠ l.word N hash) :
    final address = initial address := by
  obtain ⟨ops,logged,realized⟩ := popPush_realized N hash front back initial final success
  rw [realized]
  apply sequence_outside_frame
  intro op member
  exact outside op.1 (popPush_log_touched N hash front back initial ops logged op member)

theorem graphPops_length {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (count : Nat) (old result : Value G (.array E)) (success : graphPops count old = some result) :
    result.length.val + count = old.length.val ∧ result.extent = old.extent := by
  induction count generalizing old with
  | zero => change some old = some result at success; cases success; exact ⟨by omega,rfl⟩
  | succ count ih =>
    cases first : recursivePop old with
    | none => simp only [graphPops,first,Option.bind_none] at success; cases success
    | some middle =>
      have second : graphPops count middle = some result := by simpa only [graphPops,first,Option.bind_some] using success
      have one := recursivePop_header old middle first
      have tail := ih middle second
      exact ⟨by omega,tail.2.trans one.2⟩

/-- Arbitrary finite repeated mixed blocks derive all intermediate graph/
owner relations. Header coverage is the ORIGINAL owner's range at the push peak,
not an admitted-source restriction. No extra bound is imposed on numeric runs. -/
theorem pushPop_represented {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (frontCount backCount : Nat) (old : Value G (.array (.prim p))) (indices : List Index)
    (base : Solidity.Storage.Loc) (store : Store) (initial final : WordStore)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (transport : Transport N hash locations store initial)
    (success : pushPop N hash (List.replicate frontCount base) (List.replicate backCount base) initial = some final)
    (covered : ∀ l ∈ pushPopAccesses N hash (List.replicate frontCount base) (List.replicate backCount base) initial, l ∈ locations)
    (headerRange : old.length.val + frontCount ≤ lmax) :
    ∃ result ops, (graphPushes frontCount old).bind (graphPops backCount) = some result ∧
      pushPopLog N hash (List.replicate frontCount base) (List.replicate backCount base) initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final ∧
      Represented result (PrimitivePop.queries indices) base (ops.foldl (fun w op => Representation.write w op.1 op.2) store) := by
  cases first : pushMany N hash (List.replicate frontCount base) initial with
  | none => simp only [pushPop,first,Option.bind_none] at success; cases success
  | some middle =>
    have second : popMany N hash (List.replicate backCount base) middle = some final := by
      simpa only [pushPop,first,Option.bind_some] using success
    have firstCovered : ∀ l ∈ pushAccesses N hash (List.replicate frontCount base) initial, l ∈ locations := by
      intro l member
      apply covered l
      simp only [pushPopAccesses,first,List.mem_append]
      exact Or.inl member
    have secondCovered : ∀ l ∈ popAccesses N hash (List.replicate backCount base) middle, l ∈ locations := by
      intro l member
      apply covered l
      simp only [pushPopAccesses,first,List.mem_append]
      exact Or.inr member
    obtain ⟨child,left,graphFirst,leftLog,leftTransport,leftRep⟩ :=
      repeated_push_represented run frontCount old indices base store initial middle before transport first firstCovered headerRange
    obtain ⟨result,right,graphLast,rightLog,rightTransport,rightRep⟩ :=
      repeated_pop_represented run backCount child indices base _ middle final leftRep leftTransport second secondCovered
    refine ⟨result,left ++ right,?_,?_,?_,?_⟩
    · simp only [graphFirst,Option.bind_some,graphLast]
    · simp only [pushPopLog,first,Option.bind_some,leftLog,rightLog,Option.map_some]
    · simpa only [List.foldl_append] using rightTransport
    · simpa only [List.foldl_append] using rightRep

/-- Arbitrary finite repeated mixed blocks derive all intermediate graph/
owner relations. Header coverage is the ORIGINAL owner's range at the push peak,
not an admitted-source restriction. No extra bound is imposed on numeric runs. -/
theorem popPush_represented {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (frontCount backCount : Nat) (old : Value G (.array (.prim p))) (indices : List Index)
    (base : Solidity.Storage.Loc) (store : Store) (initial final : WordStore)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (transport : Transport N hash locations store initial)
    (success : popPush N hash (List.replicate frontCount base) (List.replicate backCount base) initial = some final)
    (covered : ∀ l ∈ popPushAccesses N hash (List.replicate frontCount base) (List.replicate backCount base) initial, l ∈ locations)
    (headerRange : old.length.val - frontCount + backCount ≤ lmax) :
    ∃ result ops, (graphPops frontCount old).bind (graphPushes backCount) = some result ∧
      popPushLog N hash (List.replicate frontCount base) (List.replicate backCount base) initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final ∧
      Represented result (PrimitivePop.queries indices) base (ops.foldl (fun w op => Representation.write w op.1 op.2) store) := by
  cases first : popMany N hash (List.replicate frontCount base) initial with
  | none => simp only [popPush,first,Option.bind_none] at success; cases success
  | some middle =>
    have second : pushMany N hash (List.replicate backCount base) middle = some final := by
      simpa only [popPush,first,Option.bind_some] using success
    have firstCovered : ∀ l ∈ popAccesses N hash (List.replicate frontCount base) initial, l ∈ locations := by
      intro l member
      apply covered l
      simp only [popPushAccesses,first,List.mem_append]
      exact Or.inl member
    have secondCovered : ∀ l ∈ pushAccesses N hash (List.replicate backCount base) middle, l ∈ locations := by
      intro l member
      apply covered l
      simp only [popPushAccesses,first,List.mem_append]
      exact Or.inr member
    obtain ⟨child,left,graphFirst,leftLog,leftTransport,leftRep⟩ :=
      repeated_pop_represented run frontCount old indices base store initial middle before transport first firstCovered
    obtain ⟨result,right,graphLast,rightLog,rightTransport,rightRep⟩ :=
      repeated_push_represented run backCount child indices base _ middle final leftRep leftTransport second secondCovered (by have lengths := graphPops_length frontCount old child graphFirst; omega)
    refine ⟨result,left ++ right,?_,?_,?_,?_⟩
    · simp only [graphFirst,Option.bind_some,graphLast]
    · simp only [popPushLog,first,Option.bind_some,leftLog,rightLog,Option.map_some]
    · simpa only [List.foldl_append] using rightTransport
    · simpa only [List.foldl_append] using rightRep

/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushPop
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPopAccesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushPopAccesses
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPopLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushPopLog
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPop_failed_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushPop_failed_first
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPop_failed_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushPop_failed_second
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPop_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushPop_realized
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPop_log_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushPop_log_touched
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPop_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushPop_transport
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPop_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushPop_frame
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPush' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popPush
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPushAccesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popPushAccesses
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPushLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popPushLog
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPush_failed_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms popPush_failed_first
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPush_failed_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms popPush_failed_second
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPush_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popPush_realized
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPush_log_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms popPush_log_touched
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPush_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms popPush_transport
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPush_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popPush_frame
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.graphPops_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graphPops_length
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.pushPop_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushPop_represented
/-- info: 'Solidity.Backend.StorageOps.MixedLifecycle.popPush_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms popPush_represented

end Solidity.Backend.StorageOps.MixedLifecycle

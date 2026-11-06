import Solidity.Backend.StorageOps.NumericCommutation

/-! Arbitrary finite actual lifecycle schedules over existing locations/stores.
A list of runtime base arguments is NOT a new source AST/IR. Execution invokes
unchanged concrete operations on successive stores. Trace/log functions are
operation-generated finite access/write certificates, not Source semantics.
Every definition recurses structurally on the supplied finite list; no depth,
length, fuel or admission cap. Failure is Option failure, not world rollback. -/
namespace Solidity.Backend.StorageOps.LifecycleSchedules
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def pushMany (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List Solidity.Storage.Loc → WordStore → Option WordStore
  | [], initial => some initial
  | base :: rest, initial => (LifecycleNumeric.pushPrimitive N hash base initial).bind (pushMany N hash rest)

/-- Includes accesses through the FIRST failure, then stops. The failed
operation's actual branch reads only its header, not a fictitious reset. -/
def pushAccesses (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List Solidity.Storage.Loc → WordStore → List Solidity.Storage.Loc
  | [], _ => []
  | base :: rest, initial => NumericCommutation.pushTouches N hash base initial ++
      match LifecycleNumeric.pushPrimitive N hash base initial with
      | none => []
      | some middle => pushAccesses N hash rest middle

/-- Successful generated update log follows ACTUAL successive machine stores.
It is a certificate over the owner's Loc×Word interface, not an evaluator used
to define the independent graph behavior. A failed schedule has no final log. -/
def pushLog (N : Nat) (hash : Solidity.Storage.Pre → Nat) :
    List Solidity.Storage.Loc → WordStore → Option (List (Solidity.Storage.Loc × Semantics.Word))
  | [], _ => some []
  | base :: rest, initial => (LifecycleNumeric.pushPrimitive N hash base initial).bind (fun middle =>
      (pushLog N hash rest middle).map (fun tail => NumericCommutation.pushUpdates N hash base initial ++ tail))

theorem push_append (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore) :
    pushMany N hash (front ++ back) initial = (pushMany N hash front initial).bind (pushMany N hash back) := by
  induction front generalizing initial with
  | nil => rfl
  | cons base rest ih =>
    simp only [List.cons_append,pushMany,Option.bind_assoc]
    congr 1
    funext middle
    exact ih middle

/-- An actual failed prefix prevents executing the suffix. This does not say
that the successful prefix writes never happened in a transactional world. -/
theorem push_failed_prefix (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore)
    (failed : pushMany N hash front initial = none) : pushMany N hash (front ++ back) initial = none := by
  rw [push_append,failed]
  rfl

theorem push_log_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (bases : List Solidity.Storage.Loc) (initial : WordStore)
    (ops : List (Solidity.Storage.Loc × Semantics.Word)) (logged : pushLog N hash bases initial = some ops)
    (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ ops) :
    op.1 ∈ pushAccesses N hash bases initial := by
  induction bases generalizing initial ops with
  | nil =>
    change some [] = some ops at logged
    cases logged
    cases member
  | cons base rest ih =>
    cases executed : LifecycleNumeric.pushPrimitive N hash base initial with
    | none => simp only [pushLog,executed,Option.bind_none] at logged; cases logged
    | some middle =>
      cases tail : pushLog N hash rest middle with
      | none => simp only [pushLog,executed,Option.bind_some,tail,Option.map_none] at logged; cases logged
      | some writes =>
        simp only [pushLog,executed,Option.bind_some,tail,Option.map_some] at logged
        cases logged
        simp only [pushAccesses,executed,List.mem_append]
        rcases List.mem_append.mp member with first | later
        · exact Or.inl (NumericCommutation.update_touched N hash base initial op first)
        · exact Or.inr (ih middle writes tail later)

/-- The entire generated log is proved equal to actual successful execution,
using each real single operation. It is not an assumed compiler certificate. -/
theorem push_realized (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (bases : List Solidity.Storage.Loc) (initial final : WordStore)
    (success : pushMany N hash bases initial = some final) :
    ∃ ops, pushLog N hash bases initial = some ops ∧
      final = ops.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial := by
  induction bases generalizing initial with
  | nil =>
    change some initial = some final at success
    cases success
    exact ⟨[],rfl,rfl⟩
  | cons base rest ih =>
    cases executed : LifecycleNumeric.pushPrimitive N hash base initial with
    | none => simp only [pushMany,executed,Option.bind_none] at success; cases success
    | some middle =>
      have tail : pushMany N hash rest middle = some final := by
        simpa only [pushMany,executed,Option.bind_some] using success
      obtain ⟨ops,logged,realized⟩ := ih middle tail
      refine ⟨NumericCommutation.pushUpdates N hash base initial ++ ops,?_,?_⟩
      · simp only [pushLog,executed,Option.bind_some,logged,Option.map_some]
      · rw [List.foldl_append,← NumericCommutation.push_realized N hash base initial middle executed]
        exact realized

/-- Full finite schedule Transport follows from the actual generated touches,
not assumed per-stage preservation or a fixed initial header/index sequence. -/
theorem push_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (bases : List Solidity.Storage.Loc)
    (store : Store) (initial final : WordStore) (before : Transport N hash locations store initial)
    (success : pushMany N hash bases initial = some final)
    (covered : ∀ l ∈ pushAccesses N hash bases initial, l ∈ locations) :
    ∃ ops, pushLog N hash bases initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final := by
  obtain ⟨ops,logged,realized⟩ := push_realized N hash bases initial final success
  refine ⟨ops,logged,?_⟩
  rw [realized]
  apply transport_sequence run before
  intro op member
  exact covered op.1 (push_log_touched N hash bases initial ops logged op member)

theorem push_frame (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (bases : List Solidity.Storage.Loc) (initial final : WordStore)
    (success : pushMany N hash bases initial = some final) (address : Nat)
    (outside : ∀ l ∈ pushAccesses N hash bases initial, address ≠ l.word N hash) :
    final address = initial address := by
  obtain ⟨ops,logged,realized⟩ := push_realized N hash bases initial final success
  rw [realized]
  apply sequence_outside_frame
  intro op member
  exact outside op.1 (push_log_touched N hash bases initial ops logged op member)


def popMany (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List Solidity.Storage.Loc → WordStore → Option WordStore
  | [], initial => some initial
  | base :: rest, initial => (PrimitivePop.execute N hash base initial).bind (popMany N hash rest)

/-- Includes accesses through the FIRST failure, then stops. The failed
operation's actual branch reads only its header, not a fictitious reset. -/
def popAccesses (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List Solidity.Storage.Loc → WordStore → List Solidity.Storage.Loc
  | [], _ => []
  | base :: rest, initial => NumericCommutation.popTouches N hash base initial ++
      match PrimitivePop.execute N hash base initial with
      | none => []
      | some middle => popAccesses N hash rest middle

/-- Successful generated update log follows ACTUAL successive machine stores.
It is a certificate over the owner's Loc×Word interface, not an evaluator used
to define the independent graph behavior. A failed schedule has no final log. -/
def popLog (N : Nat) (hash : Solidity.Storage.Pre → Nat) :
    List Solidity.Storage.Loc → WordStore → Option (List (Solidity.Storage.Loc × Semantics.Word))
  | [], _ => some []
  | base :: rest, initial => (PrimitivePop.execute N hash base initial).bind (fun middle =>
      (popLog N hash rest middle).map (fun tail => NumericCommutation.popUpdates N hash base initial ++ tail))

theorem pop_append (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore) :
    popMany N hash (front ++ back) initial = (popMany N hash front initial).bind (popMany N hash back) := by
  induction front generalizing initial with
  | nil => rfl
  | cons base rest ih =>
    simp only [List.cons_append,popMany,Option.bind_assoc]
    congr 1
    funext middle
    exact ih middle

/-- An actual failed prefix prevents executing the suffix. This does not say
that the successful prefix writes never happened in a transactional world. -/
theorem pop_failed_prefix (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial : WordStore)
    (failed : popMany N hash front initial = none) : popMany N hash (front ++ back) initial = none := by
  rw [pop_append,failed]
  rfl

theorem pop_log_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (bases : List Solidity.Storage.Loc) (initial : WordStore)
    (ops : List (Solidity.Storage.Loc × Semantics.Word)) (logged : popLog N hash bases initial = some ops)
    (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ ops) :
    op.1 ∈ popAccesses N hash bases initial := by
  induction bases generalizing initial ops with
  | nil =>
    change some [] = some ops at logged
    cases logged
    cases member
  | cons base rest ih =>
    cases executed : PrimitivePop.execute N hash base initial with
    | none => simp only [popLog,executed,Option.bind_none] at logged; cases logged
    | some middle =>
      cases tail : popLog N hash rest middle with
      | none => simp only [popLog,executed,Option.bind_some,tail,Option.map_none] at logged; cases logged
      | some writes =>
        simp only [popLog,executed,Option.bind_some,tail,Option.map_some] at logged
        cases logged
        simp only [popAccesses,executed,List.mem_append]
        rcases List.mem_append.mp member with first | later
        · exact Or.inl (NumericCommutation.pop_update_touched N hash base initial op first)
        · exact Or.inr (ih middle writes tail later)

/-- The entire generated log is proved equal to actual successful execution,
using each real single operation. It is not an assumed compiler certificate. -/
theorem pop_realized (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (bases : List Solidity.Storage.Loc) (initial final : WordStore)
    (success : popMany N hash bases initial = some final) :
    ∃ ops, popLog N hash bases initial = some ops ∧
      final = ops.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial := by
  induction bases generalizing initial with
  | nil =>
    change some initial = some final at success
    cases success
    exact ⟨[],rfl,rfl⟩
  | cons base rest ih =>
    cases executed : PrimitivePop.execute N hash base initial with
    | none => simp only [popMany,executed,Option.bind_none] at success; cases success
    | some middle =>
      have tail : popMany N hash rest middle = some final := by
        simpa only [popMany,executed,Option.bind_some] using success
      obtain ⟨ops,logged,realized⟩ := ih middle tail
      refine ⟨NumericCommutation.popUpdates N hash base initial ++ ops,?_,?_⟩
      · simp only [popLog,executed,Option.bind_some,logged,Option.map_some]
      · rw [List.foldl_append,← NumericCommutation.pop_realized N hash base initial middle executed]
        exact realized

/-- Full finite schedule Transport follows from the actual generated touches,
not assumed per-stage preservation or a fixed initial header/index sequence. -/
theorem pop_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (bases : List Solidity.Storage.Loc)
    (store : Store) (initial final : WordStore) (before : Transport N hash locations store initial)
    (success : popMany N hash bases initial = some final)
    (covered : ∀ l ∈ popAccesses N hash bases initial, l ∈ locations) :
    ∃ ops, popLog N hash bases initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final := by
  obtain ⟨ops,logged,realized⟩ := pop_realized N hash bases initial final success
  refine ⟨ops,logged,?_⟩
  rw [realized]
  apply transport_sequence run before
  intro op member
  exact covered op.1 (pop_log_touched N hash bases initial ops logged op member)

theorem pop_frame (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (bases : List Solidity.Storage.Loc) (initial final : WordStore)
    (success : popMany N hash bases initial = some final) (address : Nat)
    (outside : ∀ l ∈ popAccesses N hash bases initial, address ≠ l.word N hash) :
    final address = initial address := by
  obtain ⟨ops,logged,realized⟩ := pop_realized N hash bases initial final success
  rw [realized]
  apply sequence_outside_frame
  intro op member
  exact outside op.1 (pop_log_touched N hash bases initial ops logged op member)

/-- Independent repeated graph operations use existing intrinsic Value and
operationPush. Count is a runtime invocation count, never an admitted-source cap. -/
def graphPushes {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} :
    Nat → Value G (.array E) → Option (Value G (.array E))
  | 0, old => some old
  | count + 1, old => (operationPush old).bind (graphPushes count)

/-- Repeated ACTUAL primitive pushes produce the independent graph result,
full selected post-owner representation and actual numeric Transport. The bound
is exactly the owner's existing terminal header range, not a source admission
bound; numeric schedule/trace laws above have no such premise. No intermediate
representation or desired preservation is assumed. -/
theorem repeated_push_represented {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (count : Nat) (old : Value G (.array (.prim p))) (indices : List Index)
    (base : Solidity.Storage.Loc) (store : Store) (initial final : WordStore)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (transport : Transport N hash locations store initial)
    (success : pushMany N hash (List.replicate count base) initial = some final)
    (covered : ∀ l ∈ pushAccesses N hash (List.replicate count base) initial, l ∈ locations)
    (headerRange : old.length.val + count ≤ lmax) :
    ∃ result ops, graphPushes count old = some result ∧
      pushLog N hash (List.replicate count base) initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final ∧
      Represented result (PrimitivePop.queries indices) base
        (ops.foldl (fun w op => Representation.write w op.1 op.2) store) := by
  induction count generalizing old store initial with
  | zero =>
    change some initial = some final at success
    cases success
    exact ⟨old,[],rfl,rfl,transport,before⟩
  | succ count ih =>
    cases executed : LifecycleNumeric.pushPrimitive N hash base initial with
    | none => simp only [List.replicate_succ,pushMany,executed,Option.bind_none] at success; cases success
    | some middle =>
      have headerMember : base ∈ NumericCommutation.pushTouches N hash base initial := by
        dsimp only [NumericCommutation.pushTouches]
        split <;> exact List.mem_cons_self
      have firstCovered : ∀ l ∈ NumericCommutation.pushTouches N hash base initial, l ∈ locations := by
        intro l member
        apply covered l
        simp only [List.replicate_succ,pushAccesses,executed,List.mem_append]
        exact Or.inl member
      have headerRep : Represented old [.length .nil] base store := by
        intro q member
        simp only [List.mem_singleton] at member
        subst q
        exact before (.length .nil) List.mem_cons_self
      have graphSuccess : ∃ next, operationPush old = some next := by
        cases pushed : operationPush old with
        | some next => exact ⟨next,rfl⟩
        | none =>
          have failed := (LifecycleNumeric.pushPrimitive_failure_matches old base store initial hash locations
            headerRep transport (firstCovered base headerMember)).mpr pushed
          rw [executed] at failed
          cases failed
      obtain ⟨next,pushed⟩ := graphSuccess
      have lengths := operationPush_header old next pushed
      have room : old.length.val + 1 < 2 ^ 256 := by have bound := next.length.isLt; omega
      have lengthKnown := LifecycleNumeric.headerLength_known hash base initial old.length
        (LifecycleNumeric.array_header_numeric old base store initial hash locations headerRep transport
          (firstCovered base headerMember))
      have words : lengthWord (old.length.val + 1) room = lengthWord next.length.val next.length.isLt := by
        apply Subtype.ext
        exact congrArg Int.ofNat lengths.1.symm
      have fold_eq : (NumericCommutation.pushUpdates N hash base initial).foldl
          (fun w op => Representation.write w op.1 op.2) store =
          Representation.write (Representation.write store (.data base old.length.val) ClearDemands.zero)
            base (lengthWord next.length.val next.length.isLt) := by
        simp only [NumericCommutation.pushUpdates,lengthKnown,dif_pos room,List.foldl_cons,List.foldl_nil,words]
      have nextRep : Represented next (PrimitivePop.queries indices) base
          ((NumericCommutation.pushUpdates N hash base initial).foldl
            (fun w op => Representation.write w op.1 op.2) store) := by
        rw [fold_eq]
        exact (PushTransport.represented_iff old next pushed indices base store before).mpr (by omega)
      have nextTransport := NumericCommutation.push_transport run base store initial middle transport executed firstCovered
      have tailSuccess : pushMany N hash (List.replicate count base) middle = some final := by
        simpa only [List.replicate_succ,pushMany,executed,Option.bind_some] using success
      have tailCovered : ∀ l ∈ pushAccesses N hash (List.replicate count base) middle, l ∈ locations := by
        intro l member
        apply covered l
        simp only [List.replicate_succ,pushAccesses,executed,List.mem_append]
        exact Or.inr member
      obtain ⟨result,ops,graphResult,logged,finalTransport,finalRep⟩ :=
        ih next _ middle nextRep nextTransport tailSuccess tailCovered (by omega)
      refine ⟨result,NumericCommutation.pushUpdates N hash base initial ++ ops,?_,?_,?_,?_⟩
      · simp only [graphPushes,pushed,Option.bind_some,graphResult]
      · simp only [List.replicate_succ,pushLog,executed,Option.bind_some,logged,Option.map_some]
      · simpa only [List.foldl_append] using finalTransport
      · simpa only [List.foldl_append] using finalRep

def graphPops {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} :
    Nat → Value G (.array E) → Option (Value G (.array E))
  | 0, old => some old
  | count + 1, old => (recursivePop old).bind (graphPops count)

/-- Repeated actual pops derive every intermediate owner relation from the
OLD one. No further header-range premise is needed: pop decreases length and
keeps extent, so the old owner's bounds already suffice. -/
theorem repeated_pop_represented {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (count : Nat) (old : Value G (.array (.prim p))) (indices : List Index)
    (base : Solidity.Storage.Loc) (store : Store) (initial final : WordStore)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (transport : Transport N hash locations store initial)
    (success : popMany N hash (List.replicate count base) initial = some final)
    (covered : ∀ l ∈ popAccesses N hash (List.replicate count base) initial, l ∈ locations) :
    ∃ result ops, graphPops count old = some result ∧
      popLog N hash (List.replicate count base) initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final ∧
      Represented result (PrimitivePop.queries indices) base
        (ops.foldl (fun w op => Representation.write w op.1 op.2) store) := by
  induction count generalizing old store initial with
  | zero =>
    change some initial = some final at success
    cases success
    exact ⟨old,[],rfl,rfl,transport,before⟩
  | succ count ih =>
    cases executed : PrimitivePop.execute N hash base initial with
    | none => simp only [List.replicate_succ,popMany,executed,Option.bind_none] at success; cases success
    | some middle =>
      have headerMember : base ∈ NumericCommutation.popTouches N hash base initial := by
        dsimp only [NumericCommutation.popTouches]
        split <;> exact List.mem_cons_self
      have firstCovered : ∀ l ∈ NumericCommutation.popTouches N hash base initial, l ∈ locations := by
        intro l member
        apply covered l
        simp only [List.replicate_succ,popAccesses,executed,List.mem_append]
        exact Or.inl member
      have headerRep : Represented old [.length .nil] base store := by
        intro q member
        simp only [List.mem_singleton] at member
        subst q
        exact before (.length .nil) List.mem_cons_self
      have lengthKnown := LifecycleNumeric.headerLength_known hash base initial old.length
        (LifecycleNumeric.array_header_numeric old base store initial hash locations headerRep transport
          (firstCovered base headerMember))
      have live : 0 < old.length.val := by
        by_cases live : 0 < old.length.val
        · exact live
        · have failed : PrimitivePop.execute N hash base initial = none := by
            simp only [PrimitivePop.execute,lengthKnown,dif_neg live]
          rw [executed] at failed
          cases failed
      have graphSuccess : ∃ next, recursivePop old = some next := by
        cases popped : recursivePop old with
        | some next => exact ⟨next,rfl⟩
        | none => have empty := (recursivePop_failure old).mp popped; omega
      obtain ⟨next,popped⟩ := graphSuccess
      have lengths := recursivePop_header old next popped
      have words : lengthWord (old.length.val - 1) (by have bound := old.length.isLt; omega) =
          lengthWord next.length.val next.length.isLt := by
        apply Subtype.ext
        apply congrArg Int.ofNat
        omega
      have fold_eq : (NumericCommutation.popUpdates N hash base initial).foldl
          (fun w op => Representation.write w op.1 op.2) store =
          Representation.write (Representation.write store (.data base (old.length.val - 1)) ClearDemands.zero)
            base (lengthWord next.length.val next.length.isLt) := by
        simp only [NumericCommutation.popUpdates,lengthKnown,if_pos live,List.foldl_cons,List.foldl_nil,words]
      have nextRep : Represented next (PrimitivePop.queries indices) base
          ((NumericCommutation.popUpdates N hash base initial).foldl
            (fun w op => Representation.write w op.1 op.2) store) := by
        rw [fold_eq]
        exact PrimitivePop.represented old next popped indices base store before
      have nextTransport := NumericCommutation.pop_transport run base store initial middle transport executed firstCovered
      have tailSuccess : popMany N hash (List.replicate count base) middle = some final := by
        simpa only [List.replicate_succ,popMany,executed,Option.bind_some] using success
      have tailCovered : ∀ l ∈ popAccesses N hash (List.replicate count base) middle, l ∈ locations := by
        intro l member
        apply covered l
        simp only [List.replicate_succ,popAccesses,executed,List.mem_append]
        exact Or.inr member
      obtain ⟨result,ops,graphResult,logged,finalTransport,finalRep⟩ :=
        ih next _ middle nextRep nextTransport tailSuccess tailCovered
      refine ⟨result,NumericCommutation.popUpdates N hash base initial ++ ops,?_,?_,?_,?_⟩
      · simp only [graphPops,popped,Option.bind_some,graphResult]
      · simp only [List.replicate_succ,popLog,executed,Option.bind_some,logged,Option.map_some]
      · simpa only [List.foldl_append] using finalTransport
      · simpa only [List.foldl_append] using finalRep

/-- Trace restart at an ACTUAL successful prefix, with no unvisited
suffix accesses included before the prefix completes. -/
theorem push_accesses_append (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial middle : WordStore)
    (success : pushMany N hash front initial = some middle) :
    pushAccesses N hash (front ++ back) initial =
      pushAccesses N hash front initial ++ pushAccesses N hash back middle := by
  induction front generalizing initial with
  | nil =>
    change some initial = some middle at success
    cases success
    rfl
  | cons base rest ih =>
    cases executed : LifecycleNumeric.pushPrimitive N hash base initial with
    | none => simp only [pushMany,executed,Option.bind_none] at success; cases success
    | some next =>
      have tail : pushMany N hash rest next = some middle := by
        simpa only [pushMany,executed,Option.bind_some] using success
      simp only [List.cons_append,pushAccesses,executed,ih next tail,List.append_assoc]

/-- Trace restart at an ACTUAL successful prefix, with no unvisited
suffix accesses included before the prefix completes. -/
theorem pop_accesses_append (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List Solidity.Storage.Loc) (initial middle : WordStore)
    (success : popMany N hash front initial = some middle) :
    popAccesses N hash (front ++ back) initial =
      popAccesses N hash front initial ++ popAccesses N hash back middle := by
  induction front generalizing initial with
  | nil =>
    change some initial = some middle at success
    cases success
    rfl
  | cons base rest ih =>
    cases executed : PrimitivePop.execute N hash base initial with
    | none => simp only [popMany,executed,Option.bind_none] at success; cases success
    | some next =>
      have tail : popMany N hash rest next = some middle := by
        simpa only [popMany,executed,Option.bind_some] using success
      simp only [List.cons_append,popAccesses,executed,ih next tail,List.append_assoc]

/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pushMany' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushMany
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pushAccesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushAccesses
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pushLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushLog
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.push_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms push_append
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.push_failed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_failed_prefix
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.push_log_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_log_touched
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.push_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_realized
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.push_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_transport
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.push_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms push_frame
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.popMany' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popMany
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.popAccesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popAccesses
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.popLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popLog
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pop_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pop_append
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pop_failed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_failed_prefix
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pop_log_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_log_touched
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pop_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pop_realized
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pop_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_transport
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pop_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pop_frame
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.graphPushes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graphPushes
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.repeated_push_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms repeated_push_represented
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.graphPops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graphPops
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.repeated_pop_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms repeated_pop_represented
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.push_accesses_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_accesses_append
/-- info: 'Solidity.Backend.StorageOps.LifecycleSchedules.pop_accesses_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_accesses_append

end Solidity.Backend.StorageOps.LifecycleSchedules

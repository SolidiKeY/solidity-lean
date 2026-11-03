import Solidity.Backend.StorageOps.MixedLifecycle

/-! Generic finite alternating invocation blocks over existing runtime argument
lists. No operation tags/constructors, source AST/IR, value/state layer or source
evaluator is introduced. Each block calls the existing concrete operation family
on the actual preceding store; input lists are finite without an admission cap.
An empty argument block still changes the next family. Failure is Option only. -/
namespace Solidity.Backend.StorageOps.AlternatingLifecycle
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open LifecycleSchedules

mutual
def pushBlocks (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List (List Solidity.Storage.Loc) → WordStore → Option WordStore
  | [], initial => some initial
  | args :: rest, initial => (pushMany N hash args initial).bind (popBlocks N hash rest)
def popBlocks (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List (List Solidity.Storage.Loc) → WordStore → Option WordStore
  | [], initial => some initial
  | args :: rest, initial => (popMany N hash args initial).bind (pushBlocks N hash rest)
end

mutual
def pushBlockAccesses (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List (List Solidity.Storage.Loc) → WordStore → List Solidity.Storage.Loc
  | [], _ => []
  | args :: rest, initial => pushAccesses N hash args initial ++
      match pushMany N hash args initial with
      | none => []
      | some middle => popBlockAccesses N hash rest middle
def popBlockAccesses (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List (List Solidity.Storage.Loc) → WordStore → List Solidity.Storage.Loc
  | [], _ => []
  | args :: rest, initial => popAccesses N hash args initial ++
      match popMany N hash args initial with
      | none => []
      | some middle => pushBlockAccesses N hash rest middle
end

mutual
def pushBlockLog (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List (List Solidity.Storage.Loc) → WordStore → Option (List (Solidity.Storage.Loc × Semantics.Word))
  | [], _ => some []
  | args :: rest, initial => (pushMany N hash args initial).bind (fun middle =>
      (pushLog N hash args initial).bind (fun left => (popBlockLog N hash rest middle).map (fun right => left ++ right)))
def popBlockLog (N : Nat) (hash : Solidity.Storage.Pre → Nat) : List (List Solidity.Storage.Loc) → WordStore → Option (List (Solidity.Storage.Loc × Semantics.Word))
  | [], _ => some []
  | args :: rest, initial => (popMany N hash args initial).bind (fun middle =>
      (popLog N hash args initial).bind (fun left => (pushBlockLog N hash rest middle).map (fun right => left ++ right)))
end

private theorem realized_both (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (blocks : List (List Solidity.Storage.Loc)) :
    (∀ initial final, pushBlocks N hash blocks initial = some final →
      ∃ ops, pushBlockLog N hash blocks initial = some ops ∧
        final = ops.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) ∧
    (∀ initial final, popBlocks N hash blocks initial = some final →
      ∃ ops, popBlockLog N hash blocks initial = some ops ∧
        final = ops.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial) := by
  induction blocks with
  | nil =>
    constructor <;> (intro initial final success; change some initial = some final at success; cases success; exact ⟨[],rfl,rfl⟩)
  | cons args rest ih =>
    constructor
    · intro initial final success
      cases first : pushMany N hash args initial with
      | none => simp only [pushBlocks,first,Option.bind_none] at success; cases success
      | some middle =>
        have tail : popBlocks N hash rest middle = some final := by simpa only [pushBlocks,first,Option.bind_some] using success
        obtain ⟨left,leftLog,leftRealized⟩ := push_realized N hash args initial middle first
        obtain ⟨right,rightLog,rightRealized⟩ := ih.2 middle final tail
        refine ⟨left ++ right,?_,?_⟩
        · simp only [pushBlockLog,first,leftLog,rightLog,Option.bind_some,Option.map_some]
        · rw [List.foldl_append,← leftRealized]
          exact rightRealized
    · intro initial final success
      cases first : popMany N hash args initial with
      | none => simp only [popBlocks,first,Option.bind_none] at success; cases success
      | some middle =>
        have tail : pushBlocks N hash rest middle = some final := by simpa only [popBlocks,first,Option.bind_some] using success
        obtain ⟨left,leftLog,leftRealized⟩ := pop_realized N hash args initial middle first
        obtain ⟨right,rightLog,rightRealized⟩ := ih.1 middle final tail
        refine ⟨left ++ right,?_,?_⟩
        · simp only [popBlockLog,first,leftLog,rightLog,Option.bind_some,Option.map_some]
        · rw [List.foldl_append,← leftRealized]
          exact rightRealized

theorem push_blocks_realized (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (blocks : List (List Solidity.Storage.Loc)) (initial final : WordStore)
    (success : pushBlocks N hash blocks initial = some final) :
    ∃ ops, pushBlockLog N hash blocks initial = some ops ∧
      final = ops.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial :=
  (realized_both N hash blocks).1 initial final success

theorem pop_blocks_realized (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (blocks : List (List Solidity.Storage.Loc)) (initial final : WordStore)
    (success : popBlocks N hash blocks initial = some final) :
    ∃ ops, popBlockLog N hash blocks initial = some ops ∧
      final = ops.foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial :=
  (realized_both N hash blocks).2 initial final success

private theorem touched_both (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (blocks : List (List Solidity.Storage.Loc)) :
    (∀ initial ops, pushBlockLog N hash blocks initial = some ops →
      ∀ op ∈ ops, op.1 ∈ pushBlockAccesses N hash blocks initial) ∧
    (∀ initial ops, popBlockLog N hash blocks initial = some ops →
      ∀ op ∈ ops, op.1 ∈ popBlockAccesses N hash blocks initial) := by
  induction blocks with
  | nil =>
    constructor <;> (intro initial ops logged op member; change some [] = some ops at logged; cases logged; cases member)
  | cons args rest ih =>
    constructor
    · intro initial ops logged op member
      cases first : pushMany N hash args initial with
      | none => simp only [pushBlockLog,first,Option.bind_none] at logged; cases logged
      | some middle =>
        obtain ⟨left,leftLog,_⟩ := push_realized N hash args initial middle first
        cases rightLog : popBlockLog N hash rest middle with
        | none => simp only [pushBlockLog,first,leftLog,rightLog,Option.bind_some,Option.map_none] at logged; cases logged
        | some right =>
          simp only [pushBlockLog,first,leftLog,rightLog,Option.bind_some,Option.map_some] at logged
          cases logged
          simp only [pushBlockAccesses,first,List.mem_append]
          rcases List.mem_append.mp member with earlier | later
          · exact Or.inl (push_log_touched N hash args initial left leftLog op earlier)
          · exact Or.inr (ih.2 middle right rightLog op later)
    · intro initial ops logged op member
      cases first : popMany N hash args initial with
      | none => simp only [popBlockLog,first,Option.bind_none] at logged; cases logged
      | some middle =>
        obtain ⟨left,leftLog,_⟩ := pop_realized N hash args initial middle first
        cases rightLog : pushBlockLog N hash rest middle with
        | none => simp only [popBlockLog,first,leftLog,rightLog,Option.bind_some,Option.map_none] at logged; cases logged
        | some right =>
          simp only [popBlockLog,first,leftLog,rightLog,Option.bind_some,Option.map_some] at logged
          cases logged
          simp only [popBlockAccesses,first,List.mem_append]
          rcases List.mem_append.mp member with earlier | later
          · exact Or.inl (pop_log_touched N hash args initial left leftLog op earlier)
          · exact Or.inr (ih.1 middle right rightLog op later)

theorem push_blocks_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (blocks : List (List Solidity.Storage.Loc)) (initial : WordStore)
    (ops : List (Solidity.Storage.Loc × Semantics.Word)) (logged : pushBlockLog N hash blocks initial = some ops)
    (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ ops) :
    op.1 ∈ pushBlockAccesses N hash blocks initial :=
  (touched_both N hash blocks).1 initial ops logged op member

theorem push_blocks_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (blocks : List (List Solidity.Storage.Loc))
    (store : Store) (initial final : WordStore) (before : Transport N hash locations store initial)
    (success : pushBlocks N hash blocks initial = some final)
    (covered : ∀ l ∈ pushBlockAccesses N hash blocks initial, l ∈ locations) :
    ∃ ops, pushBlockLog N hash blocks initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final := by
  obtain ⟨ops,logged,realized⟩ := push_blocks_realized N hash blocks initial final success
  refine ⟨ops,logged,?_⟩
  rw [realized]
  apply transport_sequence run before
  intro op member
  exact covered op.1 (push_blocks_touched N hash blocks initial ops logged op member)

theorem push_blocks_frame (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (blocks : List (List Solidity.Storage.Loc)) (initial final : WordStore)
    (success : pushBlocks N hash blocks initial = some final) (address : Nat)
    (outside : ∀ l ∈ pushBlockAccesses N hash blocks initial, address ≠ l.word N hash) :
    final address = initial address := by
  obtain ⟨ops,logged,realized⟩ := push_blocks_realized N hash blocks initial final success
  rw [realized]
  apply sequence_outside_frame
  intro op member
  exact outside op.1 (push_blocks_touched N hash blocks initial ops logged op member)

theorem pop_blocks_touched (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (blocks : List (List Solidity.Storage.Loc)) (initial : WordStore)
    (ops : List (Solidity.Storage.Loc × Semantics.Word)) (logged : popBlockLog N hash blocks initial = some ops)
    (op : Solidity.Storage.Loc × Semantics.Word) (member : op ∈ ops) :
    op.1 ∈ popBlockAccesses N hash blocks initial :=
  (touched_both N hash blocks).2 initial ops logged op member

theorem pop_blocks_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (blocks : List (List Solidity.Storage.Loc))
    (store : Store) (initial final : WordStore) (before : Transport N hash locations store initial)
    (success : popBlocks N hash blocks initial = some final)
    (covered : ∀ l ∈ popBlockAccesses N hash blocks initial, l ∈ locations) :
    ∃ ops, popBlockLog N hash blocks initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final := by
  obtain ⟨ops,logged,realized⟩ := pop_blocks_realized N hash blocks initial final success
  refine ⟨ops,logged,?_⟩
  rw [realized]
  apply transport_sequence run before
  intro op member
  exact covered op.1 (pop_blocks_touched N hash blocks initial ops logged op member)

theorem pop_blocks_frame (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (blocks : List (List Solidity.Storage.Loc)) (initial final : WordStore)
    (success : popBlocks N hash blocks initial = some final) (address : Nat)
    (outside : ∀ l ∈ popBlockAccesses N hash blocks initial, address ≠ l.word N hash) :
    final address = initial address := by
  obtain ⟨ops,logged,realized⟩ := pop_blocks_realized N hash blocks initial final success
  rw [realized]
  apply sequence_outside_frame
  intro op member
  exact outside op.1 (pop_blocks_touched N hash blocks initial ops logged op member)

private theorem append_both (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front : List (List Solidity.Storage.Loc)) :
    (∀ back initial, pushBlocks N hash (front ++ back) initial =
      (pushBlocks N hash front initial).bind (fun middle =>
        if front.length % 2 = 0 then pushBlocks N hash back middle else popBlocks N hash back middle)) ∧
    (∀ back initial, popBlocks N hash (front ++ back) initial =
      (popBlocks N hash front initial).bind (fun middle =>
        if front.length % 2 = 0 then popBlocks N hash back middle else pushBlocks N hash back middle)) := by
  induction front with
  | nil => constructor <;> (intro back initial; rfl)
  | cons args rest ih =>
    constructor
    · intro back initial
      simp only [List.cons_append,pushBlocks,List.length_cons,Option.bind_assoc]
      apply congrArg (Option.bind (pushMany N hash args initial))
      funext middle
      rw [ih.2 back middle]
      apply congrArg (Option.bind (popBlocks N hash rest middle))
      funext final
      have small : rest.length % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases even : rest.length % 2 = 0
      · have odd : (rest.length + 1) % 2 ≠ 0 := by omega
        simp only [if_pos even,if_neg odd]
      · have nextEven : (rest.length + 1) % 2 = 0 := by omega
        simp only [if_neg even,if_pos nextEven]
    · intro back initial
      simp only [List.cons_append,popBlocks,List.length_cons,Option.bind_assoc]
      apply congrArg (Option.bind (popMany N hash args initial))
      funext middle
      rw [ih.1 back middle]
      apply congrArg (Option.bind (pushBlocks N hash rest middle))
      funext final
      have small : rest.length % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases even : rest.length % 2 = 0
      · have odd : (rest.length + 1) % 2 ≠ 0 := by omega
        simp only [if_pos even,if_neg odd]
      · have nextEven : (rest.length + 1) % 2 = 0 := by omega
        simp only [if_neg even,if_pos nextEven]

/-- Restart uses prefix BLOCK parity; empty blocks still flip the family. -/
theorem push_blocks_append (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List (List Solidity.Storage.Loc)) (initial : WordStore) :
    pushBlocks N hash (front ++ back) initial =
      (pushBlocks N hash front initial).bind (fun middle =>
        if front.length % 2 = 0 then pushBlocks N hash back middle else popBlocks N hash back middle) :=
  (append_both N hash front).1 back initial

theorem push_blocks_failed_prefix (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List (List Solidity.Storage.Loc)) (initial : WordStore)
    (failed : pushBlocks N hash front initial = none) : pushBlocks N hash (front ++ back) initial = none := by
  rw [push_blocks_append,failed]
  rfl

/-- Restart uses prefix BLOCK parity; empty blocks still flip the family. -/
theorem pop_blocks_append (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List (List Solidity.Storage.Loc)) (initial : WordStore) :
    popBlocks N hash (front ++ back) initial =
      (popBlocks N hash front initial).bind (fun middle =>
        if front.length % 2 = 0 then popBlocks N hash back middle else pushBlocks N hash back middle) :=
  (append_both N hash front).2 back initial

theorem pop_blocks_failed_prefix (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List (List Solidity.Storage.Loc)) (initial : WordStore)
    (failed : popBlocks N hash front initial = none) : popBlocks N hash (front ++ back) initial = none := by
  rw [pop_blocks_append,failed]
  rfl

private theorem accesses_append_both (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front : List (List Solidity.Storage.Loc)) :
    (∀ back initial middle, pushBlocks N hash front initial = some middle →
      pushBlockAccesses N hash (front ++ back) initial = pushBlockAccesses N hash front initial ++
        (if front.length % 2 = 0 then pushBlockAccesses N hash back middle else popBlockAccesses N hash back middle)) ∧
    (∀ back initial middle, popBlocks N hash front initial = some middle →
      popBlockAccesses N hash (front ++ back) initial = popBlockAccesses N hash front initial ++
        (if front.length % 2 = 0 then popBlockAccesses N hash back middle else pushBlockAccesses N hash back middle)) := by
  induction front with
  | nil =>
    constructor <;> (intro back initial middle success; change some initial = some middle at success; cases success; rfl)
  | cons args rest ih =>
    constructor
    · intro back initial middle success
      cases first : pushMany N hash args initial with
      | none => simp only [pushBlocks,first,Option.bind_none] at success; cases success
      | some next =>
        have tail : popBlocks N hash rest next = some middle := by simpa only [pushBlocks,first,Option.bind_some] using success
        simp only [List.cons_append,pushBlockAccesses,first,List.length_cons]
        rw [ih.2 back next middle tail]
        simp only [List.append_assoc]
        have small : rest.length % 2 < 2 := Nat.mod_lt _ (by decide)
        by_cases even : rest.length % 2 = 0
        · have odd : (rest.length + 1) % 2 ≠ 0 := by omega
          simp only [if_pos even,if_neg odd]
        · have nextEven : (rest.length + 1) % 2 = 0 := by omega
          simp only [if_neg even,if_pos nextEven]
    · intro back initial middle success
      cases first : popMany N hash args initial with
      | none => simp only [popBlocks,first,Option.bind_none] at success; cases success
      | some next =>
        have tail : pushBlocks N hash rest next = some middle := by simpa only [popBlocks,first,Option.bind_some] using success
        simp only [List.cons_append,popBlockAccesses,first,List.length_cons]
        rw [ih.1 back next middle tail]
        simp only [List.append_assoc]
        have small : rest.length % 2 < 2 := Nat.mod_lt _ (by decide)
        by_cases even : rest.length % 2 = 0
        · have odd : (rest.length + 1) % 2 ≠ 0 := by omega
          simp only [if_pos even,if_neg odd]
        · have nextEven : (rest.length + 1) % 2 = 0 := by omega
          simp only [if_neg even,if_pos nextEven]

theorem push_accesses_append (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List (List Solidity.Storage.Loc)) (initial middle : WordStore)
    (success : pushBlocks N hash front initial = some middle) :
    pushBlockAccesses N hash (front ++ back) initial = pushBlockAccesses N hash front initial ++
      (if front.length % 2 = 0 then pushBlockAccesses N hash back middle else popBlockAccesses N hash back middle) :=
  (accesses_append_both N hash front).1 back initial middle success

theorem pop_accesses_append (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (front back : List (List Solidity.Storage.Loc)) (initial middle : WordStore)
    (success : popBlocks N hash front initial = some middle) :
    popBlockAccesses N hash (front ++ back) initial = popBlockAccesses N hash front initial ++
      (if front.length % 2 = 0 then popBlockAccesses N hash back middle else pushBlockAccesses N hash back middle) :=
  (accesses_append_both N hash front).2 back initial middle success

mutual
/-- Independent graph invocation blocks use the existing intrinsic operations. -/
def graphPushBlocks {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} :
    List Nat → Value G (.array E) → Option (Value G (.array E))
  | [], old => some old
  | count :: rest, old => (graphPushes count old).bind (graphPopBlocks rest)
def graphPopBlocks {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} :
    List Nat → Value G (.array E) → Option (Value G (.array E))
  | [], old => some old
  | count :: rest, old => (graphPops count old).bind (graphPushBlocks rest)
end

mutual
/-- ONLY the PUBLIC owner's original terminal-header coverage at each actual
push peak. This independent graph arithmetic predicate says nothing about desired
representation preservation. Numeric execution never uses it as an admission test. -/
def pushHeaderCoverage {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} : List Nat → Value G (.array E) → Prop
  | [], _ => True
  | count :: rest, old => old.length.val + count ≤ lmax ∧
      match graphPushes count old with
      | none => True
      | some middle => popHeaderCoverage rest middle
def popHeaderCoverage {n : Nat} {G : Schema n} {E : TypeGraph.Ty n} : List Nat → Value G (.array E) → Prop
  | [], _ => True
  | count :: rest, old => match graphPops count old with
      | none => True
      | some middle => pushHeaderCoverage rest middle
end

private theorem represented_both {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (counts : List Nat) :
    (∀ (old : Value G (.array (.prim p))) (indices : List Index) (base : Solidity.Storage.Loc)
      (store : Store) (initial final : WordStore),
      Represented old (PrimitivePop.queries indices) base store → Transport N hash locations store initial →
      pushBlocks N hash (counts.map (fun count => List.replicate count base)) initial = some final →
      (∀ l ∈ pushBlockAccesses N hash (counts.map (fun count => List.replicate count base)) initial, l ∈ locations) →
      pushHeaderCoverage counts old →
      ∃ result ops, graphPushBlocks counts old = some result ∧
        pushBlockLog N hash (counts.map (fun count => List.replicate count base)) initial = some ops ∧
        Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final ∧
        Represented result (PrimitivePop.queries indices) base (ops.foldl (fun w op => Representation.write w op.1 op.2) store)) ∧
    (∀ (old : Value G (.array (.prim p))) (indices : List Index) (base : Solidity.Storage.Loc)
      (store : Store) (initial final : WordStore),
      Represented old (PrimitivePop.queries indices) base store → Transport N hash locations store initial →
      popBlocks N hash (counts.map (fun count => List.replicate count base)) initial = some final →
      (∀ l ∈ popBlockAccesses N hash (counts.map (fun count => List.replicate count base)) initial, l ∈ locations) →
      popHeaderCoverage counts old →
      ∃ result ops, graphPopBlocks counts old = some result ∧
        popBlockLog N hash (counts.map (fun count => List.replicate count base)) initial = some ops ∧
        Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final ∧
        Represented result (PrimitivePop.queries indices) base (ops.foldl (fun w op => Representation.write w op.1 op.2) store)) := by
  induction counts with
  | nil =>
    constructor <;> (
      intro old indices base store initial final before transport success covered bounds
      change some initial = some final at success
      cases success
      exact ⟨old,[],rfl,rfl,transport,before⟩)
  | cons count rest ih =>
    constructor
    · intro old indices base store initial final before transport success covered bounds
      cases first : pushMany N hash (List.replicate count base) initial with
      | none => simp only [List.map_cons,pushBlocks,first,Option.bind_none] at success; cases success
      | some middle =>
        have tail : popBlocks N hash (rest.map (fun count => List.replicate count base)) middle = some final := by
          simpa only [List.map_cons,pushBlocks,first,Option.bind_some] using success
        have firstCovered : ∀ l ∈ pushAccesses N hash (List.replicate count base) initial, l ∈ locations := by
          intro l member
          apply covered l
          simp only [List.map_cons,pushBlockAccesses,first,List.mem_append]
          exact Or.inl member
        have tailCovered : ∀ l ∈ popBlockAccesses N hash (rest.map (fun count => List.replicate count base)) middle, l ∈ locations := by
          intro l member
          apply covered l
          simp only [List.map_cons,pushBlockAccesses,first,List.mem_append]
          exact Or.inr member
        obtain ⟨child,left,graphFirst,leftLog,leftTransport,leftRep⟩ :=
          repeated_push_represented run count old indices base store initial middle before transport first firstCovered bounds.1
        have tailBounds : popHeaderCoverage rest child := by
          simpa only [graphFirst] using bounds.2
        obtain ⟨result,right,graphTail,rightLog,rightTransport,rightRep⟩ :=
          ih.2 child indices base _ middle final leftRep leftTransport tail tailCovered tailBounds
        refine ⟨result,left ++ right,?_,?_,?_,?_⟩
        · simp only [graphPushBlocks,graphFirst,Option.bind_some,graphTail]
        · simp only [List.map_cons,pushBlockLog,first,leftLog,rightLog,Option.bind_some,Option.map_some]
        · simpa only [List.foldl_append] using rightTransport
        · simpa only [List.foldl_append] using rightRep
    · intro old indices base store initial final before transport success covered bounds
      cases first : popMany N hash (List.replicate count base) initial with
      | none => simp only [List.map_cons,popBlocks,first,Option.bind_none] at success; cases success
      | some middle =>
        have tail : pushBlocks N hash (rest.map (fun count => List.replicate count base)) middle = some final := by
          simpa only [List.map_cons,popBlocks,first,Option.bind_some] using success
        have firstCovered : ∀ l ∈ popAccesses N hash (List.replicate count base) initial, l ∈ locations := by
          intro l member
          apply covered l
          simp only [List.map_cons,popBlockAccesses,first,List.mem_append]
          exact Or.inl member
        have tailCovered : ∀ l ∈ pushBlockAccesses N hash (rest.map (fun count => List.replicate count base)) middle, l ∈ locations := by
          intro l member
          apply covered l
          simp only [List.map_cons,popBlockAccesses,first,List.mem_append]
          exact Or.inr member
        obtain ⟨child,left,graphFirst,leftLog,leftTransport,leftRep⟩ :=
          repeated_pop_represented run count old indices base store initial middle before transport first firstCovered
        have tailBounds : pushHeaderCoverage rest child := by
          simpa only [popHeaderCoverage,graphFirst] using bounds
        obtain ⟨result,right,graphTail,rightLog,rightTransport,rightRep⟩ :=
          ih.1 child indices base _ middle final leftRep leftTransport tail tailCovered tailBounds
        refine ⟨result,left ++ right,?_,?_,?_,?_⟩
        · simp only [graphPopBlocks,graphFirst,Option.bind_some,graphTail]
        · simp only [List.map_cons,popBlockLog,first,leftLog,rightLog,Option.bind_some,Option.map_some]
        · simpa only [List.foldl_append] using rightTransport
        · simpa only [List.foldl_append] using rightRep

/-- Generic arbitrary finite alternation derives every intermediate independent
graph result and selected owner relation. Only old evidence, actual success,
generated per-run coverage and independent original-header coverage are premises. -/
theorem push_blocks_represented {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (counts : List Nat) (old : Value G (.array (.prim p))) (indices : List Index)
    (base : Solidity.Storage.Loc) (store : Store) (initial final : WordStore)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (transport : Transport N hash locations store initial)
    (success : pushBlocks N hash (counts.map (fun count => List.replicate count base)) initial = some final)
    (covered : ∀ l ∈ pushBlockAccesses N hash (counts.map (fun count => List.replicate count base)) initial, l ∈ locations)
    (bounds : pushHeaderCoverage counts old) :
    ∃ result ops, graphPushBlocks counts old = some result ∧
      pushBlockLog N hash (counts.map (fun count => List.replicate count base)) initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final ∧
      Represented result (PrimitivePop.queries indices) base (ops.foldl (fun w op => Representation.write w op.1 op.2) store) :=
  (represented_both run counts).1 old indices base store initial final before transport success covered bounds

/-- Generic arbitrary finite alternation derives every intermediate independent
graph result and selected owner relation. Only old evidence, actual success,
generated per-run coverage and independent original-header coverage are premises. -/
theorem pop_blocks_represented {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (counts : List Nat) (old : Value G (.array (.prim p))) (indices : List Index)
    (base : Solidity.Storage.Loc) (store : Store) (initial final : WordStore)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (transport : Transport N hash locations store initial)
    (success : popBlocks N hash (counts.map (fun count => List.replicate count base)) initial = some final)
    (covered : ∀ l ∈ popBlockAccesses N hash (counts.map (fun count => List.replicate count base)) initial, l ∈ locations)
    (bounds : popHeaderCoverage counts old) :
    ∃ result ops, graphPopBlocks counts old = some result ∧
      popBlockLog N hash (counts.map (fun count => List.replicate count base)) initial = some ops ∧
      Transport N hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) store) final ∧
      Represented result (PrimitivePop.queries indices) base (ops.foldl (fun w op => Representation.write w op.1 op.2) store) :=
  (represented_both run counts).2 old indices base store initial final before transport success covered bounds

/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pushBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushBlocks
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.popBlocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms popBlocks
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pushBlockAccesses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushBlockAccesses
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.popBlockAccesses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms popBlockAccesses
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pushBlockLog' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushBlockLog
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.popBlockLog' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms popBlockLog
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.push_blocks_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_blocks_realized
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pop_blocks_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_blocks_realized
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.push_blocks_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_blocks_touched
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.push_blocks_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_blocks_transport
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.push_blocks_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_blocks_frame
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pop_blocks_touched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_blocks_touched
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pop_blocks_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_blocks_transport
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pop_blocks_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_blocks_frame
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.push_blocks_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_blocks_append
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.push_blocks_failed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_blocks_failed_prefix
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pop_blocks_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_blocks_append
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pop_blocks_failed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_blocks_failed_prefix
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.push_accesses_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_accesses_append
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pop_accesses_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_accesses_append
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.graphPushBlocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graphPushBlocks
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.graphPopBlocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graphPopBlocks
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pushHeaderCoverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pushHeaderCoverage
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.popHeaderCoverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms popHeaderCoverage
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.push_blocks_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_blocks_represented
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycle.pop_blocks_represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_blocks_represented

end Solidity.Backend.StorageOps.AlternatingLifecycle

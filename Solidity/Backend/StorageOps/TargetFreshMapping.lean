import Solidity.Backend.StorageOps.PushFrames
import Solidity.Backend.StorageOps.TargetHeaderPush

/-! Fresh primitive-mapping history and old contexts compose with ACTUAL
guarded target instructions. Defaults derive from checked zero-origin history,
not old failed reads. Existing symbolic-slot/finite-run boundaries are retained. -/
namespace Solidity.Backend.StorageOps.TargetFreshMapping
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Header PART only, for a successful intrinsic push. This does not claim
primitive reset or fresh aggregate initialization from header code alone. -/
theorem run_source_header {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (pushed : operationPush old = some result)
    (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base) (store : Store) (machine : Evm.Machine)
    (before : Represented old [.length .nil] base store)
    (initial : machine.store.cells (TargetOperations.toSlot base fits) = TargetOperations.encodeWord (store base)) :
    Evm.run (TargetHeaderPush.code (TargetOperations.toSlot base fits)) machine =
      .ok { machine with store := Evm.WordStore.write machine.store (TargetOperations.toSlot base fits) (TargetOperations.encodeWord (lengthWord result.length.val result.length.isLt)).val } 0 := by
  have header := TargetHeaderPush.source_header old base fits store machine before initial
  have headers := operationPush_header old result pushed
  have room : machine.store (TargetOperations.toSlot base fits) + 1 < Evm.W := by
    rw [header]; have bound := result.length.isLt; change old.length.val + 1 < 2 ^ 256; omega
  rw [TargetHeaderPush.run_current,if_pos room]
  unfold TargetHeaderPush.incremented
  have encoded : (TargetOperations.encodeWord (lengthWord result.length.val result.length.isLt)).val = result.length.val := rfl
  rw [encoded,header,headers.1]

/-- ACTUAL guarded target execution, selected independent source owner relation,
actual numeric operation/finite transport and ACTUAL successful SLOAD readbacks.
All new defaults come from zero-origin history, not desired postpremises. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {K p : PrimTy}
    (old result : Value G (.array (.mapping K (.prim p))))
    (fresh : old.extent.val = old.length.val) (pushed : operationPush old = some result)
    (keys : List K.Denote) (groups : List (Index × List (Query G (.mapping K (.prim p)))))
    (other : ∀ group ∈ groups, group.1.val ≠ old.length.val) (base : Solidity.Storage.Loc)
    (baseFits : TargetOperations.KeysFit base) (target : Evm.Machine)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations) (history : List (Solidity.Storage.Loc × Semantics.Word))
    (historyCovered : ∀ op ∈ history, op.1 ∈ locations)
    (covered : ∀ q ∈ (.length .nil :: keys.map (FreshMappingHistory.keyQuery old.length)) ++ AggregatePopFrames.contexts groups,
      q.location base ∈ locations)
    (apart : ∀ key ∈ keys, ∀ op ∈ history, (FreshMappingHistory.keyQuery (G := G) (p := p) old.length key).location base ≠ op.1)
    (coverage : old.length.val + 1 ≤ lmax)
    (header : Represented old [.length .nil] base (FreshMappingHistory.symbolic history))
    (contexts : Represented old (AggregatePopFrames.contexts groups) base (FreshMappingHistory.symbolic history))
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (FreshMappingHistory.symbolic history l)) :
    ∃ final, LifecycleNumeric.pushHeader N hash base (FreshMappingHistory.numeric N hash history) = some final ∧
      let word := lengthWord result.length.val result.length.isLt
      let afterStore := write (FreshMappingHistory.symbolic history) base word
      let afterTarget := { target with store := Evm.WordStore.write target.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord word).val }
      Evm.run (TargetHeaderPush.code (TargetOperations.toSlot base baseFits)) target = .ok afterTarget 0 ∧
      Represented result ((.length .nil :: keys.map (FreshMappingHistory.keyQuery old.length)) ++ AggregatePopFrames.contexts groups) base afterStore ∧
      Transport N hash locations afterStore final ∧
      (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (final (l.word N hash))) ∧
      (∀ q ∈ ((.length .nil :: keys.map (FreshMappingHistory.keyQuery (G := G) (p := p) old.length)) ++ AggregatePopFrames.contexts groups),
        ∀ value, q.read result = some value →
        Evm.run (TargetOperations.readCode (TargetOperations.toSlot (q.location base) (TargetOperations.query_keysFit q base baseFits))) afterTarget =
          .ok { afterTarget with stack := .val (TargetOperations.encodeWord value) :: afterTarget.stack } 0) := by
  obtain ⟨final,numericExecuted,owner,transported,_,_⟩ := PushFrames.complete_fresh old result fresh pushed keys groups other base
    run history historyCovered covered apart coverage header contexts
  have headerCovered : base ∈ locations := covered (.length .nil) (List.mem_append.mpr (Or.inl List.mem_cons_self))
  have executed := run_source_header old result pushed base baseFits (FreshMappingHistory.symbolic history) target header (targetInitial base headerCovered)
  have agreement := TargetOperations.write_agreement locations fitting base baseFits (lengthWord result.length.val result.length.isLt)
    (FreshMappingHistory.symbolic history) target targetInitial
  refine ⟨final,numericExecuted,executed,owner,transported,?_,?_⟩
  · intro l member
    exact (agreement l member).trans (congrArg TargetOperations.encodeWord (transported l member).symm)
  · intro q member value observed
    apply TargetOperations.represented_read result _ base baseFits _ _ owner _ q member value observed
    intro query queryMember
    exact agreement (query.location base) (covered query queryMember)

/-- info: 'Solidity.Backend.StorageOps.TargetFreshMapping.run_source_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_source_header
/-- info: 'Solidity.Backend.StorageOps.TargetFreshMapping.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric

end Solidity.Backend.StorageOps.TargetFreshMapping

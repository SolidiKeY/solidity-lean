import Solidity.Backend.StorageOps.TargetPrimitivePush

/-! Evolving primitive pop/push: the ACTUAL pop supplies the intermediate
owner/transport/target agreement consumed by the actual guarded reset. No
intermediate preservation premise, source capacity cap or world rollback claim. -/
namespace Solidity.Backend.StorageOps.TargetPrimitivePopPush
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def code (slot : Evm.Slot) : List Evm.Instr := TargetPrimitivePop.code slot ++ TargetPrimitivePush.code slot
noncomputable def execute (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (numeric : WordStore) : Option WordStore := do
  let middle ← PrimitivePop.execute N hash base numeric
  LifecycleNumeric.pushPrimitive N hash base middle

/-- Successful pop always leaves room for intrinsic push, even outside the
PUBLIC lmax observation interface. This is a source operation law, not a cap. -/
theorem push_exists {n : Nat} {G : Schema n} {p : PrimTy}
    (old middle : Value G (.array (.prim p))) (popped : recursivePop old = some middle) :
    ∃ result, operationPush middle = some result := by
  have lengths := (recursivePop_header old middle popped).1
  have bound := old.length.isLt
  cases pushed : operationPush middle with
  | none =>
    have full := (operationPush_failure middle).mp pushed
    omega
  | some result => exact ⟨result,rfl⟩

/-- All successful/defaulted/failing primitive query outcomes after regrowth:
last live cell is reset, EVERY other retained or out-of-extent read is OLD. -/
theorem element_read {n : Nat} {G : Schema n} {p : PrimTy}
    (old middle result : Value G (.array (.prim p)))
    (popped : recursivePop old = some middle) (pushed : operationPush middle = some result) (i : Index) :
    (PrimitivePop.elementQuery i).read result = if i.val = old.length.val - 1 then some ClearDemands.zero
      else (PrimitivePop.elementQuery i).read old := by
  have lengths := (recursivePop_header old middle popped).1
  rw [PushTransport.element_read middle result pushed i]
  by_cases last : i.val = old.length.val - 1
  · rw [if_pos last,if_pos (by omega)]
  · rw [if_neg last,if_neg (by omega)]
    exact PrimitivePop.other_read old middle popped i last

/-- Empty target failure stops concatenation before either operation writes. -/
theorem run_empty (slot : Evm.Slot) (machine : Evm.Machine) (empty : machine.store slot = 0) :
    Evm.run (code slot) machine = .revert := by
  apply Evm.run_append_revert
  rw [TargetPrimitivePop.run_current,if_pos empty]

/-- ONE evolving numeric/target sequence derives its intermediate state from
OLD evidence. PUBLIC postmetadata bound follows OLD header coverage and pop
length restoration, rather than an added source restriction or post premise. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (old middle result : Value G (.array (.prim p)))
    (popped : recursivePop old = some middle) (pushed : operationPush middle = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
    (store : Store) (machine : Evm.Machine) (numeric : WordStore)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (before : Represented old (PrimitivePop.queries indices) base store) (initial : Transport N hash locations store numeric)
    (targetInitial : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location base ∈ locations)
    (lastCovered : Solidity.Storage.Loc.data base (old.length.val - 1) ∈ locations) :
    let middleWord := lengthWord middle.length.val middle.length.isLt
    let middleChild := Solidity.Storage.Loc.data base (old.length.val - 1)
    let middleStore := Representation.write (Representation.write store middleChild ClearDemands.zero) base middleWord
    let middleTarget := { machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord middleWord).val) (TargetOperations.toSlot middleChild baseFits) 0 }
    let finalWord := lengthWord result.length.val result.length.isLt
    let finalChild := Solidity.Storage.Loc.data base middle.length.val
    let finalStore := Representation.write (Representation.write middleStore finalChild ClearDemands.zero) base finalWord
    let finalTarget := { middleTarget with store := Evm.WordStore.write (Evm.WordStore.write middleTarget.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord finalWord).val) (TargetOperations.toSlot finalChild baseFits) 0 }
    ∃ final, execute N hash base numeric = some final ∧
      Evm.run (code (TargetOperations.toSlot base baseFits)) machine = .ok finalTarget 0 ∧
      Represented result (PrimitivePop.queries indices) base finalStore ∧ Transport N hash locations finalStore final ∧
      (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (final (l.word N hash))) := by
  obtain ⟨middleNumeric,popNumeric,popTarget,middleOwner,middleTransport,middleAgreement⟩ :=
    TargetPrimitivePop.complete_numeric run old middle popped indices base baseFits store machine numeric fitting before initial targetInitial covered lastCovered
  have popHeaders := (recursivePop_header old middle popped).1
  have last : middle.length.val = old.length.val - 1 := by omega
  have middleCovered : Solidity.Storage.Loc.data base middle.length.val ∈ locations := by rw [last]; exact lastCovered
  have middleTargetAgreement : ∀ l (member : l ∈ locations),
      ({ machine with store := Evm.WordStore.write (Evm.WordStore.write machine.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord (lengthWord middle.length.val middle.length.isLt)).val) (TargetOperations.toSlot (.data base (old.length.val - 1)) baseFits) 0 } : Evm.Machine).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord ((Representation.write (Representation.write store (.data base (old.length.val - 1)) ClearDemands.zero) base (lengthWord middle.length.val middle.length.isLt)) l) := by
    intro l member
    exact (middleAgreement l member).trans (congrArg TargetOperations.encodeWord (middleTransport l member))
  obtain ⟨final,pushNumeric,pushTarget,ownerIff,transported,agreement⟩ := TargetPrimitivePush.complete_numeric run middle result pushed indices base baseFits
    _ _ middleNumeric fitting middleOwner middleTransport middleTargetAgreement (covered (.length .nil) List.mem_cons_self) middleCovered
  have oldBound : old.length.val ≤ lmax := by
    have compatibility := (before (.length .nil) List.mem_cons_self).2.1
    cases old
    exact compatibility.1
  refine ⟨final,?_,?_,ownerIff.mpr (by omega),transported,agreement⟩
  · unfold execute
    rw [popNumeric]
    exact pushNumeric
  · unfold code
    rw [Evm.run_append_ok popTarget]
    exact pushTarget


/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePopPush.push_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_exists
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePopPush.element_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms element_read
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePopPush.run_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_empty
/-- info: 'Solidity.Backend.StorageOps.TargetPrimitivePopPush.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric

end Solidity.Backend.StorageOps.TargetPrimitivePopPush

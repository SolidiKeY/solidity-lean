import Solidity.Lowering.StorageOps.SourceTwoArrayDeletes
import Solidity.Backend.StorageOps.TwoClearRepresentation

/-! Captured TWO-delete Source operations compose with the actual PUBLIC graph,
symbolic/numeric stores and target code. ORIGINAL read/retained-word premises
derive all middle and post observations. Ordinary address/AST lowering stays open. -/
namespace Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open SourceArrayDeleteTarget

private theorem data_ne_base (base : Solidity.Storage.Loc) (j : Nat) : Solidity.Storage.Loc.data base j ≠ base := by
 intro same
 have depths := congrArg Solidity.Storage.Loc.depth same
 change base.depth+1 = base.depth at depths
 omega

private theorem after_data {n : Nat} {G : Schema n} {p : PrimTy}
 (value : Value G (.array (.prim p))) (base : Solidity.Storage.Loc) (store : Store) (j : Nat) :
 TargetClearRepresentation.afterStore value base store (.data base j) =
   if j < value.length.val then ClearDemands.zero else store (.data base j) := by
 unfold TargetClearRepresentation.afterStore
 rw [Representation.write_other _ _ _ _ (data_ne_base base j),TargetClearRepresentation.symbolic_data]

private theorem after_other {n : Nat} {G : Schema n} {p : PrimTy}
 (value : Value G (.array (.prim p))) (base observer : Solidity.Storage.Loc) (store : Store)
 (apart : observer ≠ base ∧ ∀ j, j < value.length.val → observer ≠ .data base j) :
 TargetClearRepresentation.afterStore value base store observer = store observer := by
 unfold TargetClearRepresentation.afterStore
 rw [Representation.write_other _ _ _ _ apart.1,TargetClearRepresentation.symbolic_outside store base observer value.length.val apart.2]

theorem complete {n m N L R : Nat} {G : Schema n} {H : Schema m}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}

    {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false)
    (leftPath rightPath : Source.SPath) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (run : FiniteRun N L R hash P locations)
    (left : Value G (.array (.prim .uint))) (right : Value H (.array (.prim .uint)))
    (leftIndices rightIndices : List Index) (leftBase rightBase : Solidity.Storage.Loc)
    (leftFits : TargetOperations.KeysFit leftBase) (rightFits : TargetOperations.KeysFit rightBase)
    (store : Store) (numeric : WordStore) (target : Evm.Machine) (tail : List Evm.Word)
    (leftBefore : Represented left (TargetClearRepresentation.oldQueries left leftIndices) leftBase store)
    (rightBefore : Represented right (TargetClearRepresentation.oldQueries right rightIndices) rightBase store)
    (rightOldFrame : ∀ query ∈ TargetClearRepresentation.oldQueries right rightIndices,
      query.location rightBase ≠ leftBase ∧ ∀ j, j < left.length.val → query.location rightBase ≠ .data leftBase j)
    (leftPostFrame : ∀ query ∈ PrimitivePop.queries (G := G) (p := .uint) leftIndices,
      query.location leftBase ≠ rightBase ∧ ∀ j, j < right.length.val → query.location leftBase ≠ .data rightBase j)
    (initial : Transport N hash locations store numeric)
    (leftCovered : ∀ query ∈ PrimitivePop.queries (G := G) (p := .uint) leftIndices, query.location leftBase ∈ locations)
    (rightCovered : ∀ query ∈ PrimitivePop.queries (G := H) (p := .uint) rightIndices, query.location rightBase ∈ locations)
    (leftVisited : ∀ j, j < left.length.val → Solidity.Storage.Loc.data leftBase j ∈ locations)
    (rightVisited : ∀ j, j < right.length.val → Solidity.Storage.Loc.data rightBase j ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (leftTyped : E.pathTy leftPath = some (.array .storage (.int Source.IntTy.u256) none))
    (rightTyped : E.pathTy rightPath = some (.array .storage (.int Source.IntTy.u256) none))
    (leftOrdinary : E.transientRoot leftPath = false) (rightOrdinary : E.transientRoot rightPath = false)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame leftPath).run (locals,state) = (.ok left.length.val,(locals,state)))
    (rightInput : (Source.readLen (E := E) (Γ := Γ) frame rightPath).run (locals,state) = (.ok right.length.val,(locals,state)))
    (sourceHeaders : rightPath ≠ leftPath)
    (sourceLeftData : ∀ j ∈ List.range' 0 left.length.val, rightPath ≠ leftPath.go (.index j))
    (sourceRightData : ∀ j ∈ List.range' 0 right.length.val, leftPath ≠ rightPath.go (.index j))
    (sourceLeftFrame : ∀ i ∈ leftIndices, leftPath.go (.index i.val) ≠ rightPath ∧
      ∀ j ∈ List.range' 0 right.length.val, leftPath.go (.index i.val) ≠ rightPath.go (.index j))
    (sourceRightFrame : ∀ i ∈ rightIndices, right.length.val ≤ i.val →
      rightPath.go (.index i.val) ≠ leftPath ∧
      ∀ j ∈ List.range' 0 left.length.val, rightPath.go (.index i.val) ≠ leftPath.go (.index j))
    (sourceLeftOld : ∀ i ∈ leftIndices, left.length.val ≤ i.val →
      wordAt frame state.ex (leftPath.go (.index i.val)) = some (TargetOperations.encodeWord (store (.data leftBase i.val))).val)
    (sourceRightOld : ∀ i ∈ rightIndices, right.length.val ≤ i.val →
      wordAt frame state.ex (rightPath.go (.index i.val)) = some (TargetOperations.encodeWord (store (.data rightBase i.val))).val) :
    let finalStore := TwoClearRepresentation.afterStore left right leftBase rightBase store
    let finalNumeric := TwoClearRepresentation.execute N hash leftBase rightBase numeric
    let finalTarget := TargetArrayDeleteSequence.after target tail
      (TargetOperations.toSlot leftBase leftFits) (TargetOperations.toSlot rightBase rightFits)
    let sourceResult := (SourceTwoArrayDeletes.program frame Source.IntTy.u256 Source.IntTy.u256
      leftPath rightPath left.length.val right.length.val).run (locals,state)
    (Evm.run (TargetArrayDeleteSequence.code (TargetOperations.toSlot rightBase rightFits))
      {target with stack := .slot (TargetOperations.toSlot leftBase leftFits) :: tail} = .ok finalTarget 0 ∧
    Represented left.clear (PrimitivePop.queries leftIndices) leftBase finalStore ∧
    Represented right.clear (PrimitivePop.queries rightIndices) rightBase finalStore ∧
    Transport N hash locations finalStore finalNumeric ∧
    (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (finalNumeric (l.word N hash))) ∧
    (∀ query ∈ PrimitivePop.queries (G := G) (p := .uint) leftIndices, ∀ word, query.read left.clear = some word →
      finalNumeric ((query.location leftBase).word N hash) = word) ∧
    (∀ query ∈ PrimitivePop.queries (G := H) (p := .uint) rightIndices, ∀ word, query.read right.clear = some word →
      finalNumeric ((query.location rightBase).word N hash) = word)) ∧
    sourceResult = (.ok (), (locals,{state with ex := state.ex.run (((List.range' 0 left.length.val).map (fun j => SourceScalarDeleteLog.clearOp E frame (leftPath.go (.index j))) ++ [SourceScalarDeleteLog.clearOp E frame leftPath]) ++ ((List.range' 0 right.length.val).map (fun j => SourceScalarDeleteLog.clearOp E frame (rightPath.go (.index j))) ++ [SourceScalarDeleteLog.clearOp E frame rightPath]))})) ∧
    wordAt frame sourceResult.2.2.ex leftPath = some (TargetOperations.encodeWord (finalNumeric (leftBase.word N hash))).val ∧
    wordAt frame sourceResult.2.2.ex rightPath = some (TargetOperations.encodeWord (finalNumeric (rightBase.word N hash))).val ∧
    (∀ i ∈ leftIndices, wordAt frame sourceResult.2.2.ex (leftPath.go (.index i.val)) =
      some (TargetOperations.encodeWord (finalNumeric ((Solidity.Storage.Loc.data leftBase i.val).word N hash))).val) ∧
    (∀ i ∈ rightIndices, wordAt frame sourceResult.2.2.ex (rightPath.go (.index i.val)) =
      some (TargetOperations.encodeWord (finalNumeric ((Solidity.Storage.Loc.data rightBase i.val).word N hash))).val) := by
  dsimp only
  have certificate := TwoClearRepresentation.complete run left right leftIndices rightIndices leftBase rightBase leftFits rightFits
    store numeric target tail leftBefore rightBefore rightOldFrame leftPostFrame initial leftCovered rightCovered leftVisited rightVisited fitting targetInitial
  have sourceRun := SourceTwoArrayDeletes.source_run frame writable Source.IntTy.u256 Source.IntTy.u256
    leftPath rightPath left.length.val right.length.val locals state leftInput rightInput sourceHeaders sourceLeftData
  have sourceZero := SourceTwoArrayDeletes.source_headers frame writable leftPath rightPath left.length.val right.length.val
    locals state leftTyped rightTyped leftOrdinary rightOrdinary leftInput rightInput sourceHeaders sourceLeftData sourceRightData
  have numericLeftZero := certificate.2.1.numeric certificate.2.2.2.1 (.length .nil) List.mem_cons_self
    (leftCovered _ List.mem_cons_self) ClearDemands.zero (by cases left; rfl)
  have numericRightZero := certificate.2.2.1.numeric certificate.2.2.2.1 (.length .nil) List.mem_cons_self
    (rightCovered _ List.mem_cons_self) ClearDemands.zero (by cases right; rfl)
  change TwoClearRepresentation.execute N hash leftBase rightBase numeric (leftBase.word N hash) = ClearDemands.zero at numericLeftZero
  change TwoClearRepresentation.execute N hash leftBase rightBase numeric (rightBase.word N hash) = ClearDemands.zero at numericRightZero
  refine ⟨certificate,sourceRun,?_,?_,?_,?_⟩
  · rw [numericLeftZero]
    exact sourceZero.1
  · rw [numericRightZero]
    exact sourceZero.2
  · intro i member
    have queryMember : PrimitivePop.elementQuery (G := G) (p := .uint) i ∈ PrimitivePop.queries leftIndices :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,member,rfl⟩)
    have covered := leftCovered (PrimitivePop.elementQuery i) queryMember
    rw [PrimitivePop.element_location] at covered
    rw [certificate.2.2.2.1 _ covered]
    have outside := leftPostFrame (PrimitivePop.elementQuery i) queryMember
    rw [PrimitivePop.element_location] at outside
    rw [TwoClearRepresentation.afterStore,after_other right rightBase (.data leftBase i.val) _ outside,after_data]
    have observed := SourceTwoArrayDeletes.source_first_data frame writable leftPath rightPath left.length.val right.length.val i.val locals state
      leftTyped leftOrdinary leftInput rightInput sourceHeaders sourceLeftData (sourceLeftFrame i member).1 (sourceLeftFrame i member).2
    by_cases live : i.val < left.length.val
    · rw [if_pos live] at observed ⊢
      exact observed
    · rw [if_neg live] at observed ⊢
      exact observed.trans (sourceLeftOld i member (by omega))
  · intro i member
    have queryMember : PrimitivePop.elementQuery (G := H) (p := .uint) i ∈ PrimitivePop.queries rightIndices :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,member,rfl⟩)
    have covered := rightCovered (PrimitivePop.elementQuery i) queryMember
    rw [PrimitivePop.element_location] at covered
    rw [certificate.2.2.2.1 _ covered,TwoClearRepresentation.afterStore,after_data]
    have observed := SourceTwoArrayDeletes.source_second_data frame writable leftPath rightPath left.length.val right.length.val i.val locals state
      rightTyped rightOrdinary leftInput rightInput sourceHeaders sourceLeftData (sourceRightFrame i member)
    by_cases live : i.val < right.length.val
    · rw [if_pos live] at observed ⊢
      exact observed
    · rw [if_neg live] at observed ⊢
      have oldMember : PrimitivePop.elementQuery i ∈ TargetClearRepresentation.oldQueries right rightIndices := by
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨member,by simp only [decide_eq_true_eq]; omega⟩,rfl⟩)
      have outside := rightOldFrame (PrimitivePop.elementQuery i) oldMember
      rw [PrimitivePop.element_location] at outside
      rw [after_other left leftBase (.data rightBase i.val) store outside]
      exact observed.trans (sourceRightOld i member (by omega))

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.SourceTwoArrayDeleteNumeric

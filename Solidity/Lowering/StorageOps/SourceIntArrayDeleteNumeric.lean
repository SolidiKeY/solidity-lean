import Solidity.Lowering.StorageOps.SourceIntCopyReadbacks
import Solidity.Backend.StorageOps.TargetClearRepresentation

/-! Actual integer Source array deletion: every existing IntTy, including signed
int256, composes with PUBLIC primitive graph clear and numeric/target execution.
Only OLD selected unvisited words are coupled; visited zero is derived from the
actual Source default. No new compiler/address/world relation is assumed. -/
namespace Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open SourceScalarDeleteLog SourceCopyReadbacks
open SourceArrayDeleteTarget (wordAt)

theorem clear_range_word {E : Source.Env} (frame : Source.Fr) (t : Source.IntTy)
    (state : Source.ExecState E.layout E.lay E.lay) (path : Source.SPath) (count j : Nat)
    (ordinary : E.transientRoot (path.go (.index j)) = false)
    (typed : E.cellTy (path.go (.index j)) = .int t) :
    wordAt frame (state.run ((List.range' 0 count).map (fun i => clearOp E frame (path.go (.index i)))))
      (path.go (.index j)) = if j < count then some 0 else wordAt frame state (path.go (.index j)) := by
  rw [SourceIntCopyReadbacks.clear_words_index frame t state path _ j ordinary typed]
  have membership : j ∈ List.range' 0 count ↔ j < count := by
    rw [List.mem_range']
    constructor
    · rintro ⟨i,inside,same⟩
      simp only [Nat.zero_add,Nat.one_mul] at same
      subst j
      exact inside
    · intro inside
      exact ⟨j,inside,by simp only [Nat.zero_add,Nat.one_mul]⟩
  simp only [membership]

theorem source_array_header {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (t : Source.IntTy) (writable : frame.static = false) (path : Source.SPath) (count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy path = some (.array .storage (.int t) none))
    (ordinary : E.transientRoot path = false)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state))) :
    wordAt frame ((Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int t) none) path).run (locals,state)).2.2.ex path = some 0 := by
  rw [SourceArrayDeleteTarget.source_array_run frame writable _ path count locals state readLength,Source.run_append]
  simp only [Source.ExecState.run]
  exact SourceArrayDeleteTarget.clear_word_same frame _ path ordinary (by
    simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some])

/-- Retained word reads stay retained; these are not fresh source index
expressions or a liveness admission rule. No None-to-zero inference occurs. -/
theorem source_array_data {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (t : Source.IntTy) (writable : frame.static = false) (path : Source.SPath) (count j : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy path = some (.array .storage (.int t) none))
    (ordinary : E.transientRoot path = false)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state))) :
    wordAt frame ((Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int t) none) path).run (locals,state)).2.2.ex (path.go (.index j)) =
      if j < count then some 0 else wordAt frame state.ex (path.go (.index j)) := by
  rw [SourceArrayDeleteTarget.source_array_run frame writable _ path count locals state readLength,Source.run_append]
  simp only [Source.ExecState.run]
  rw [SourceArrayDeleteTarget.clear_word_other frame _ path _ (SourceCopyReadbacks.index_ne_header path j)]
  exact clear_range_word frame t state.ex path count j ordinary (SourceStorageCopy.element_type t path typed j)

/-- Coupling is an OLD input observation only for an unvisited retained word.
Visited output is derived without assuming its desired representation. -/
theorem data_correspondence {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (t : Source.IntTy) (writable : frame.static = false) (path : Source.SPath) (count j : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy path = some (.array .storage (.int t) none))
    (ordinary : E.transientRoot path = false)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state)))
    (target : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (header : target.store slot = count)
    (oldWord : count ≤ j → wordAt frame state.ex (path.go (.index j)) = some (target.store (.data slot j))) :
    wordAt frame ((Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int t) none) path).run (locals,state)).2.2.ex (path.go (.index j)) =
      some ((TargetArrayClear.afterClear target tail slot).store (.data slot j)) := by
  rw [source_array_data frame t writable path count j locals state typed ordinary readLength,
    TargetArrayClear.after_data,header]
  by_cases live : j < count
  · simp only [if_pos live]
  · simp only [if_neg live,oldWord (by omega)]


theorem complete {n N L R : Nat} {p : PrimTy} {G : Schema n}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    {E : Source.Env} {Γ : Source.RCtx}
    (run : FiniteRun N L R hash P locations)
    (frame : Source.Fr) (t : Source.IntTy) (writable : frame.static = false)
    (sourcePath : Source.SPath) (locals : Source.Locals E.layout Γ) (sourceState : Source.St E)
    (typed : E.pathTy sourcePath = some (.array .storage (.int t) none))
    (ordinary : E.transientRoot sourcePath = false)
    (old : Value G (.array (.prim p))) (indices : List Index) (base : Solidity.Storage.Loc)
    (baseFits : TargetOperations.KeysFit base) (store : Store) (numeric : WordStore)
    (target : Evm.Machine) (tail : List Evm.Word)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame sourcePath).run (locals,sourceState) =
      (.ok old.length.val,(locals,sourceState)))
    (before : Represented old (TargetClearRepresentation.oldQueries old indices) base store)
    (initial : Transport N hash locations store numeric)
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location base ∈ locations)
    (visitedCovered : ∀ j, j < old.length.val → Solidity.Storage.Loc.data base j ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (sourceOld : ∀ i ∈ indices, old.length.val ≤ i.val →
      wordAt frame sourceState.ex (sourcePath.go (.index i.val)) =
        some (TargetOperations.encodeWord (store (.data base i.val))).val) :
    let sourceResult := (Source.deleteStor (E := E) (Γ := Γ) frame (old.length.val + 2)
      (.array .storage (.int t) none) sourcePath).run (locals,sourceState)
    let targetResult := TargetArrayClear.afterClear target tail (TargetOperations.toSlot base baseFits)
    sourceResult = (.ok (), (locals,{sourceState with ex := sourceState.ex.run (((List.range' 0 old.length.val).map (fun i => SourceScalarDeleteLog.clearOp E frame (sourcePath.go (.index i)))) ++ [SourceScalarDeleteLog.clearOp E frame sourcePath])})) ∧
    Evm.run TargetArrayClear.code {target with stack := .slot (TargetOperations.toSlot base baseFits) :: tail} = .ok targetResult 0 ∧
    Represented old.clear (PrimitivePop.queries indices) base (TargetClearRepresentation.afterStore old base store) ∧
    Transport N hash locations (TargetClearRepresentation.afterStore old base store) (TargetClearRepresentation.execute N hash base numeric) ∧
    (∀ l (member : l ∈ locations), targetResult.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord ((TargetClearRepresentation.execute N hash base numeric) (l.word N hash))) ∧
    wordAt frame sourceResult.2.2.ex sourcePath =
      some (TargetOperations.encodeWord ((TargetClearRepresentation.execute N hash base numeric) (base.word N hash))).val ∧
    (∀ i ∈ indices, wordAt frame sourceResult.2.2.ex (sourcePath.go (.index i.val)) =
      some (TargetOperations.encodeWord ((TargetClearRepresentation.execute N hash base numeric) ((Solidity.Storage.Loc.data base i.val).word N hash))).val) ∧
    (∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ word, q.read old.clear = some word →
      (TargetClearRepresentation.execute N hash base numeric) ((q.location base).word N hash) = word) := by
  dsimp only
  have headerOwner : Represented old [.length .nil] base store := by
    intro q member
    have same := List.mem_singleton.mp member
    subst q
    exact before _ List.mem_cons_self
  have headerCovered : base ∈ locations := covered (.length .nil) List.mem_cons_self
  have targetHeader := TargetHeaderPush.source_header old base baseFits store target headerOwner (targetInitial base headerCovered)
  have certificate := TargetClearRepresentation.complete run old indices base baseFits store numeric target tail
    before initial covered visitedCovered fitting targetInitial
  have elementCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data base i.val ∈ locations := by
    intro i member
    have atQuery := covered (PrimitivePop.elementQuery i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,member,rfl⟩))
    simpa only [PrimitivePop.element_location] using atQuery
  refine ⟨SourceArrayDeleteTarget.source_array_run frame writable _ sourcePath old.length.val locals sourceState readLength,
    certificate.1,certificate.2.1,certificate.2.2.1,certificate.2.2.2.1,?_,?_,certificate.2.2.2.2⟩
  · have sourceHeader := source_array_header frame t writable sourcePath old.length.val locals sourceState typed ordinary readLength
    have numericHeader := congrArg Fin.val (certificate.2.2.2.1 base headerCovered)
    change (TargetArrayClear.afterClear target tail (TargetOperations.toSlot base baseFits)).store (TargetOperations.toSlot base baseFits) = _ at numericHeader
    rw [← numericHeader,TargetArrayClear.after_header]
    exact sourceHeader
  · intro i member
    have oldWord : old.length.val ≤ i.val → wordAt frame sourceState.ex (sourcePath.go (.index i.val)) =
        some (target.store (.data (TargetOperations.toSlot base baseFits) i.val)) := by
      intro unvisited
      have input := congrArg Fin.val (targetInitial (.data base i.val) (elementCovered i member))
      change target.store (.data (TargetOperations.toSlot base baseFits) i.val) = _ at input
      rw [input]
      exact sourceOld i member unvisited
    have sourceWord := data_correspondence frame t writable sourcePath old.length.val i.val locals sourceState
      typed ordinary readLength target tail (TargetOperations.toSlot base baseFits) targetHeader oldWord
    have output := congrArg Fin.val (certificate.2.2.2.1 (.data base i.val) (elementCovered i member))
    change (TargetArrayClear.afterClear target tail (TargetOperations.toSlot base baseFits)).store
      (.data (TargetOperations.toSlot base baseFits) i.val) = _ at output
    rw [← output]
    exact sourceWord

/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.clear_range_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_range_word
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.source_array_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_array_header
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.source_array_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_array_data
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.data_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms data_correspondence
/-- info: 'Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.SourceIntArrayDeleteNumeric

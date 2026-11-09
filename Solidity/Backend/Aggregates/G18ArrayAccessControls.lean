import Solidity.Backend.Aggregates.G18ArrayAccess
import Solidity.Backend.Aggregates.G18StorageClient
import Solidity.Backend.Aggregates.G18SourceMappingControls

/-! An actual declared Basket.items dynamic array. The negative state has
populated elements but no length cell; it is not an admitted aggregate
representation and does not witness compiler coverage. -/
namespace Solidity.Backend.Aggregates.SourceArray.Controls

abbrev E := StorageClient.env
def arrayPath : Source.SPath := ⟨⟨none,"root"⟩,[.field 0]⟩
def declared : E.pathTy arrayPath = some (.array .storage (.int .u8) none) := rfl
abbrev frame := ScalarMapping.SourceMachine.Controls.frame

def elements : Source.Storage E.layout E.cellTy :=
  ((Source.Storage.empty.write (StorageClient.cell 0) (.int 7 (by decide))).write
    (StorageClient.cell 1) (.int 11 (by decide)))
def live : Source.Storage E.layout E.cellTy :=
  elements.write arrayPath (.int 2 (by decide))

def state (storage : Source.Storage E.layout E.cellTy) : Source.St E :=
  {ex := ⟨⟨fun a => ⟨((a.val+17) % 2^256),3,some 9,storage⟩⟩,
      Source.Transient.empty,[.account ⟨99,by decide⟩ (Source.Account.empty _)]⟩,
   heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,
   events := [], logs := [(⟨13,by decide⟩,[1,2])],
   fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩}
def locals : Source.Locals E.layout [.bool] := .cons (.bool true) .nil

def reference : Source.Val E.layout (.array .storage (.int .u8) none) := .storRef rfl arrayPath

theorem length_observations : (Solidity.Backend.Aggregates.SourceArray.Controls.live.read Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath).bind Solidity.Source.Val.key = some 2 ∧ (Solidity.Backend.Aggregates.SourceArray.Controls.elements.read Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath).bind Solidity.Source.Val.key = some 0 ∧ (Solidity.Backend.Aggregates.SourceArray.Controls.elements.read (Solidity.Backend.Aggregates.StorageClient.cell 1)).bind Solidity.Source.Val.key = some 11 := by
  exact ⟨rfl,rfl,rfl⟩

theorem related_one : Solidity.Backend.Aggregates.IntCellAt .u8 Solidity.Backend.Aggregates.SourceArray.Controls.live Solidity.Backend.Aggregates.StorageClient.target (Solidity.Backend.Aggregates.StorageClient.cell 1) (Solidity.Backend.Aggregates.SourceArray.element_type Solidity.Backend.Aggregates.SourceArray.Controls.E Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath .u8 Solidity.Backend.Aggregates.SourceArray.Controls.declared 1) (Solidity.Backend.Aggregates.StorageClient.selected ⟨1,by decide⟩) := by
  obtain ⟨n,range,read,target⟩ := Solidity.Backend.Aggregates.StorageClient.initial_other
  have observed := congrArg (fun x => x.bind Solidity.Source.Val.key) read
  change some 11 = some n at observed
  have same := Option.some.inj observed
  subst n
  refine ⟨11,range,?_,target⟩
  unfold Solidity.Backend.Aggregates.SourceArray.Controls.live
  rw [Solidity.Source.Storage.write_other _ (by decide +kernel)]
  exact Solidity.Source.Storage.write_read _ _ _

theorem index_one : (Solidity.Source.indexLoc (E := Solidity.Backend.Aggregates.SourceArray.Controls.E) (Γ := [.bool]) Solidity.Backend.Aggregates.SourceArray.Controls.frame Solidity.Backend.Aggregates.SourceArray.Controls.reference 1).run (Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live) = (.ok (.stor (Solidity.Backend.Aggregates.StorageClient.cell 1)),(Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live)) := by
  exact Solidity.Backend.Aggregates.SourceArray.index_success Solidity.Backend.Aggregates.SourceArray.Controls.E [.bool] Solidity.Backend.Aggregates.SourceArray.Controls.frame (Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live) Solidity.Backend.Aggregates.SourceArray.Controls.locals Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath .u8 Solidity.Backend.Aggregates.SourceArray.Controls.declared 2 (by decide) rfl rfl 1 (by decide)

theorem read_one : ((Solidity.Source.indexLoc (E := Solidity.Backend.Aggregates.SourceArray.Controls.E) (Γ := [.bool]) Solidity.Backend.Aggregates.SourceArray.Controls.frame Solidity.Backend.Aggregates.SourceArray.Controls.reference 1) >>= fun (loc : Solidity.Source.Loc Solidity.Backend.Aggregates.SourceArray.Controls.E.layout [.bool] (.int .u8)) => Solidity.Source.readLoc (E := Solidity.Backend.Aggregates.SourceArray.Controls.E) (Γ := [.bool]) (τ := .int .u8) Solidity.Backend.Aggregates.SourceArray.Controls.frame loc).run (Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live) = (.ok (.int 11 (by decide)),(Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live)) ∧ Solidity.Backend.Aggregates.StorageClient.target.find (Solidity.Backend.Aggregates.StorageClient.selected ⟨1,by decide⟩) = some (.prim (Solidity.Lowering.V07.integerValue .u8 11 (by decide))) := by
  obtain ⟨n,range,run,target⟩ := Solidity.Backend.Aggregates.SourceArray.read_element Solidity.Backend.Aggregates.SourceArray.Controls.E [.bool] Solidity.Backend.Aggregates.SourceArray.Controls.frame (Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live) Solidity.Backend.Aggregates.SourceArray.Controls.locals Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath .u8 Solidity.Backend.Aggregates.SourceArray.Controls.declared 2 (by decide) rfl rfl 1 (by decide) _ Solidity.Backend.Aggregates.StorageClient.target (Solidity.Backend.Aggregates.StorageClient.selected ⟨1,by decide⟩) Solidity.Backend.Aggregates.SourceArray.Controls.related_one
  have observed := congrArg (fun o => o.bind (fun | Solidity.SVal.prim v => Solidity.PrimTy.num? v)) target
  have targetObserved : (Solidity.Backend.Aggregates.StorageClient.target.find (Solidity.Backend.Aggregates.StorageClient.selected ⟨1,by decide⟩)).bind (fun | Solidity.SVal.prim v => Solidity.PrimTy.num? v) = some 11 := by
    have full := congrArg (fun xs : List (Option Int) => xs[3]?) Solidity.Backend.Aggregates.StorageClient.ordered_observations.1
    change some ((Solidity.Backend.Aggregates.StorageClient.target.find (Solidity.Backend.Aggregates.StorageClient.selected ⟨1,by decide⟩)).bind (fun | Solidity.SVal.prim v => Solidity.PrimTy.num? v)) = some (some 11) at full
    exact Option.some.inj full
  have recorded := targetObserved.symm.trans observed
  have captured : some 11 = some n := by
    simpa only [Option.bind_some,Solidity.Lowering.V07.integer_observe] using recorded
  have same := Option.some.inj captured
  subst n
  exact ⟨run,target⟩

theorem failure_controls : (Solidity.Source.indexLoc (E := Solidity.Backend.Aggregates.SourceArray.Controls.E) (Γ := [.bool]) Solidity.Backend.Aggregates.SourceArray.Controls.frame Solidity.Backend.Aggregates.SourceArray.Controls.reference 2).run (Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live) = (.error (.revert (Solidity.Source.panicData .index)),(Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live)) ∧ (Solidity.Source.indexLoc (E := Solidity.Backend.Aggregates.SourceArray.Controls.E) (Γ := [.bool]) Solidity.Backend.Aggregates.SourceArray.Controls.frame Solidity.Backend.Aggregates.SourceArray.Controls.reference 0).run (Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.elements) = (.error (.revert (Solidity.Source.panicData .index)),(Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.elements)) ∧ Solidity.Source.panicData .index ≠ [] ∧ Solidity.Source.panicData .index ≠ Solidity.Source.panicData .divZero ∧ Solidity.Source.Halt.revert (Solidity.Source.panicData .index) ≠ Solidity.Source.Halt.timeout := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact Solidity.Backend.Aggregates.SourceArray.index_failure Solidity.Backend.Aggregates.SourceArray.Controls.E [.bool] Solidity.Backend.Aggregates.SourceArray.Controls.frame (Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live) Solidity.Backend.Aggregates.SourceArray.Controls.locals Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath .u8 Solidity.Backend.Aggregates.SourceArray.Controls.declared 2 (by decide) rfl rfl 2 (by decide)
  · exact Solidity.Backend.Aggregates.SourceArray.index_failure Solidity.Backend.Aggregates.SourceArray.Controls.E [.bool] Solidity.Backend.Aggregates.SourceArray.Controls.frame (Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.elements) Solidity.Backend.Aggregates.SourceArray.Controls.locals Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath .u8 Solidity.Backend.Aggregates.SourceArray.Controls.declared 0 (by decide) rfl rfl 0 (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel

def view (storage : Source.Storage E.layout E.cellTy) : List (Option Int) :=
  [(storage.read arrayPath).bind Source.Val.key,
   (storage.read (StorageClient.cell 0)).bind Source.Val.key,
   (storage.read (StorageClient.cell 1)).bind Source.Val.key,
   (StorageClient.target.find (StorageClient.selected ⟨0,by decide⟩)).bind (fun | .prim n => PrimTy.num? n),
   (StorageClient.target.find (StorageClient.selected ⟨1,by decide⟩)).bind (fun | .prim n => PrimTy.num? n)]

theorem ordered : Solidity.Backend.Aggregates.SourceArray.Controls.view Solidity.Backend.Aggregates.SourceArray.Controls.live = [some 2,some 7,some 11,some 7,some 11] ∧ Solidity.Backend.Aggregates.SourceArray.Controls.view Solidity.Backend.Aggregates.SourceArray.Controls.elements = [some 0,some 7,some 11,some 7,some 11] := by
  decide +kernel

theorem wrong_length : (((Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.elements).ex.world.accounts Solidity.Backend.Aggregates.SourceArray.Controls.frame.this).storage.read Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath) ≠ some (cast (congrArg (Solidity.Source.Val Solidity.Backend.Aggregates.SourceArray.Controls.E.layout) (Solidity.Backend.Aggregates.SourceArray.length_type Solidity.Backend.Aggregates.SourceArray.Controls.E Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath .u8 Solidity.Backend.Aggregates.SourceArray.Controls.declared).symm) (Solidity.Source.Val.int 2 (by decide))) := by
  intro wrong
  have observed := congrArg (fun o => o.bind Solidity.Source.Val.key) wrong
  change some 0 = some 2 at observed
  contradiction

theorem wrong_location : (Solidity.Source.indexLoc (E := Solidity.Backend.Aggregates.SourceArray.Controls.E) (Γ := [.bool]) Solidity.Backend.Aggregates.SourceArray.Controls.frame Solidity.Backend.Aggregates.SourceArray.Controls.reference 1).run (Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live) ≠ (.ok (.stor (Solidity.Backend.Aggregates.StorageClient.cell 0)),(Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live)) := by
  intro wrong
  have observed := congrArg Prod.fst (Solidity.Backend.Aggregates.SourceArray.Controls.index_one.symm.trans wrong)
  cases observed

theorem typed_out_of_bounds : Solidity.Backend.Aggregates.SourceArray.Controls.E.cellTy (Solidity.Backend.Aggregates.StorageClient.cell 99) = .int .u8 ∧ (Solidity.Source.indexLoc (E := Solidity.Backend.Aggregates.SourceArray.Controls.E) (Γ := [.bool]) Solidity.Backend.Aggregates.SourceArray.Controls.frame Solidity.Backend.Aggregates.SourceArray.Controls.reference 99).run (Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live) = (.error (.revert (Solidity.Source.panicData .index)),(Solidity.Backend.Aggregates.SourceArray.Controls.locals,Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live)) ∧ (Solidity.Backend.Aggregates.StorageClient.target.find (Solidity.Backend.Aggregates.StorageClient.selected ⟨99,by decide⟩)).isNone = true := by
  refine ⟨?_,?_,?_⟩
  · exact Solidity.Backend.Aggregates.SourceArray.element_type Solidity.Backend.Aggregates.SourceArray.Controls.E Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath .u8 Solidity.Backend.Aggregates.SourceArray.Controls.declared 99
  · exact Solidity.Backend.Aggregates.SourceArray.index_failure Solidity.Backend.Aggregates.SourceArray.Controls.E [.bool] Solidity.Backend.Aggregates.SourceArray.Controls.frame (Solidity.Backend.Aggregates.SourceArray.Controls.state Solidity.Backend.Aggregates.SourceArray.Controls.live) Solidity.Backend.Aggregates.SourceArray.Controls.locals Solidity.Backend.Aggregates.SourceArray.Controls.arrayPath .u8 Solidity.Backend.Aggregates.SourceArray.Controls.declared 2 (by decide) rfl rfl 99 (by decide)
  · decide +kernel

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.length_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms length_observations

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.related_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms related_one

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.index_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms index_one

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.read_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_one

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.failure_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failure_controls

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ordered

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.wrong_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_length

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.wrong_location' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_location

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.typed_out_of_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms typed_out_of_bounds
end Solidity.Backend.Aggregates.SourceArray.Controls


/-! A declared mapping whose values are dynamic storage arrays. These Source-only
clients keep key/index order and actual length checks separate. They establish
no Source/native relation, physical address correspondence, or H249 packet. -/
namespace Solidity.Backend.Aggregates.SourceArray.Controls.Mapped

/-- Consume the mapping-path law before the array-path law. -/
theorem mapping_array_type (E : Source.Env) (p : Source.SPath)
    (typed : E.pathTy p = some (.mapping .bool (.array .storage (.int .u8) none)))
    (b : Bool) : E.pathTy (p.go (.key (ScalarMapping.Controls.keyBytes b))) =
      some (.array .storage (.int .u8) none) := by
  exact mapping_path E p .bool (.array .storage (.int .u8) none) typed
    (ScalarMapping.Controls.keyBytes b)

def declaration : Source.Decl :=
  ⟨.stateVar, "buckets", none, true,
    .stateVar (.mapping (.elem .bool (by decide)) none
      (.array (.elem (.int false 8 Source.IntTy.u8.valid)) .none) none)
      none none none false "buckets" .none⟩
def env : Source.Env := ⟨[declaration]⟩
abbrev E := env
def root : Source.SPath := ⟨⟨none,"buckets"⟩,[]⟩
def arrayPath (b : Bool) : Source.SPath := root.go (.key (ScalarMapping.Controls.keyBytes b))
def cell (b : Bool) (i : Nat) : Source.SPath := (arrayPath b).go (.index i)

theorem array_typed (b : Bool) :
    E.pathTy (arrayPath b) = some (.array .storage (.int .u8) none) :=
  mapping_array_type E root rfl b

theorem element_typed (b : Bool) (i : Nat) : E.cellTy (cell b i) = .int .u8 :=
  SourceArray.element_type E (arrayPath b) .u8 (array_typed b) i

def storage : Source.Storage E.layout E.cellTy :=
  ((((Source.Storage.empty.write (cell true 0) (.int 7 (by decide))).write
    (cell true 1) (.int 11 (by decide))).write
    (cell false 0) (.int 23 (by decide))).write
    (arrayPath true) (.int 2 (by decide))).write
    (arrayPath false) (.int 1 (by decide))

abbrev frame := ScalarMapping.SourceMachine.Controls.frame
def locals : Source.Locals E.layout [.bool] := .cons (.bool true) .nil
def state : Source.St E :=
  {ex := ⟨⟨fun a => ⟨((a.val+17) % 2^256),3,some 9,storage⟩⟩,
      Source.Transient.empty,[.account ⟨99,by decide⟩ (Source.Account.empty _)]⟩,
   heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,
   events := [], logs := [(⟨13,by decide⟩,[1,2])],
   fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩}
def reference (b : Bool) : Source.Val E.layout (.array .storage (.int .u8) none) :=
  .storRef rfl (arrayPath b)

/-- Actual selection and index-panic runs preserve the entire reached state. -/
theorem selected_and_refused :
    (Source.indexLoc (E := E) (Γ := [.bool]) frame (reference true) 1).run (locals,state) = (.ok (.stor (cell true 1)),(locals,state)) ∧
    (Source.indexLoc (E := E) (Γ := [.bool]) frame (reference false) 1).run (locals,state) = (.error (.revert (Source.panicData .index)),(locals,state)) ∧
    (Source.indexLoc (E := E) (Γ := [.bool]) frame (reference true) 99).run (locals,state) = (.error (.revert (Source.panicData .index)),(locals,state)) := by
  refine ⟨?_,?_,?_⟩
  · exact SourceArray.index_success E [.bool] frame state locals (arrayPath true) .u8
      (array_typed true) 2 (by decide) rfl rfl 1 (by decide)
  · exact SourceArray.index_failure E [.bool] frame state locals (arrayPath false) .u8
      (array_typed false) 1 (by decide) rfl rfl 1 (by decide)
  · exact SourceArray.index_failure E [.bool] frame state locals (arrayPath true) .u8
      (array_typed true) 2 (by decide) rfl rfl 99 (by decide)

/-- Static cell typing does not discharge bounds; key/index order matters.
The fixture has live heap/journal/log state and distinct mapping contents. -/
theorem ordered_state_controls :
    E.cellTy (cell true 99) = .int .u8 ∧
    E.pathTy ((root.go (.index 1)).go (.key (ScalarMapping.Controls.keyBytes true))) = none ∧
    arrayPath true ≠ arrayPath false ∧
    [(storage.read (arrayPath true)).bind Source.Val.key,
     (storage.read (arrayPath false)).bind Source.Val.key,
     (storage.read (cell true 1)).bind Source.Val.key,
     (storage.read (cell false 0)).bind Source.Val.key] = [some 2,some 1,some 11,some 23] ∧
    state.heap.next = 1 ∧
    state.ex.journal.length = 1 ∧
    state.logs.length = 1 := by
  refine ⟨element_typed true 99, ?_⟩
  decide +kernel

/-- The selected cell is read through the actual Source location operation. -/
theorem read_one :
    ((Source.indexLoc (E := E) (Γ := [.bool]) frame (reference true) 1) >>= fun loc =>
      Source.readLoc (E := E) (Γ := [.bool]) (τ := .int .u8) frame loc).run (locals,state) = (.ok (.int 11 (by decide)),(locals,state)) := by
  rfl

/-- The real Boolean key helper is sequenced before indexing and reading.
This is a fixed pure index, not arbitrary effectful-index preservation. -/
theorem key_index_read :
    ∀ b : Bool,
    ((Source.keyStep (E := E) (Γ := [.bool]) frame 0 (.val (.bool b))) >>= fun step =>
      ((Source.indexLoc (E := E) (Γ := [.bool]) frame ((.storRef rfl (root.go step)) : Source.Val E.layout (.array .storage (.int .u8) none)) 1) >>= fun loc =>
      Source.readLoc (E := E) (Γ := [.bool]) (τ := .int .u8) frame loc)).run (locals,state) = ((if b then .ok (.int 11 (by decide)) else .error (.revert (Source.panicData .index))),(locals,state)) := by
  intro b
  cases b <;> rfl

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.Mapped.mapping_array_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_array_type

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.Mapped.array_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms array_typed

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.Mapped.element_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms element_typed

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.Mapped.selected_and_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_and_refused

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.Mapped.ordered_state_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_state_controls

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.Mapped.read_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_one

/-- info: 'Solidity.Backend.Aggregates.SourceArray.Controls.Mapped.key_index_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms key_index_read

end Solidity.Backend.Aggregates.SourceArray.Controls.Mapped

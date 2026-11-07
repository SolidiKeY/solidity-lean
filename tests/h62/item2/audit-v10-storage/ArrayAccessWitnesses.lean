import Solidity.Backend.StorageOps.TargetDefaultInit
import Solidity.Backend.StorageOps.TargetArrayWrite
import Solidity.Backend.StorageOps.CopyDemandControls
import Solidity.Backend.StorageOps.ProducerInterfaceControls

/-! Populated live-array access witnesses. Retained cells beyond the current
header are distinct from out-of-extent cells. Existing operation adapters and
symbolic-slot EVM execution are used; Source/physical/world adequacy is open. -/
namespace H62.StorageAudit.ArrayAccessWitnesses
open Solidity Solidity.Backend.StorageOps TypeGraph
open Solidity.Storage.Representation Solidity.Storage.Representation.Graph
abbrev graph := CopyDemandControls.graph
def zero : Index := ⟨0, by decide⟩
def one : Index := ⟨1, by decide⟩
def three : Index := ⟨3, by decide⟩
def old : Value graph (.array (.prim .bool)) :=
  .array ⟨3, by decide⟩ one (by decide) (fun _ => .present (.prim true))
def result : Value graph (.array (.prim .bool)) :=
  (TargetArrayWrite.writeAt old zero false).getD old
def machine : Evm.Machine := {ProducerInterfaceControls.before with
  store := .ofFn fun slot => if slot = .root 0 then 1 else
    if slot = .data (.root 0) 0 then 1 else
    if slot = .data (.root 0) 1 then 1 else 99}
def tail : List Evm.Word := [.val ⟨17, by decide⟩, .slot (.root 9)]

theorem read_joint : zero.val < Evm.W := zero.isLt
theorem write_joint : zero.val < Evm.W := zero.isLt
theorem read_failure_joint : machine.store (.root 0) = old.length.val := rfl
theorem write_failure_joint : machine.store (.root 0) = old.length.val := rfl
theorem success_joint : TargetArrayWrite.writeAt old zero false = some result := rfl

def symbolic : Store := fun _ => lengthWord 1 (by decide)
theorem header_joint : TargetArrayWrite.writeAt old zero false = some result ∧
    Represented old [.length .nil] (.root 0) symbolic := by
  refine ⟨success_joint, ?_⟩
  intro query member
  have same : query = .length .nil := List.mem_singleton.mp member
  subst query
  refine ⟨True.intro, by change 1 ≤ Storage.lmax ∧ 3 ≤ Storage.lmax; decide, ?_⟩
  intro value observed
  cases observed
  rfl

theorem live_read :
    Evm.run TargetArrayRead.code {machine with stack := .val zero :: .slot (.root 0) :: tail} =
      .ok {machine with stack := .val ⟨1, by decide⟩ :: tail} 0 := by
  exact (TargetArrayRead.run_current machine tail (.root 0) zero.val read_joint).trans (by rfl)

theorem live_write :
    Evm.run TargetArrayWrite.code
      {machine with stack := .val zero :: .slot (.root 0) :: .val ⟨0, by decide⟩ :: tail} =
      .ok {machine with stack := tail, store := Evm.WordStore.write machine.store (.data (.root 0) 0) 0} 0 := by
  exact (TargetArrayWrite.run_current machine tail (.root 0) zero.val write_joint ⟨0, by decide⟩).trans (by rfl)

theorem adapter_success : zero.val < old.length.val ∧
    old.save (TargetArrayRead.path zero) (.prim false) = some result :=
  TargetArrayWrite.success old result zero false success_joint

theorem header_frame_actual : Represented result [.length .nil] (.root 0)
    (write symbolic (pathLoc (TargetArrayRead.path (G := graph) (p := .bool) zero) (.root 0)) (PrimTy.toWord (p := .bool) false)) :=
  TargetArrayWrite.header_frame old result zero false header_joint.1 (.root 0) symbolic header_joint.2

theorem retained_raw_and_live :
    Step.get Value.dflt (.index one) old = some (.prim true) ∧
    (TargetArrayRead.path one).readLive Value.dflt old = none ∧
    TargetArrayWrite.writeAt old one false = none ∧
    old.save (TargetArrayRead.path one) (.prim false) ≠ none := by
  exact ⟨rfl, rfl, rfl, by intro impossible; cases impossible⟩

theorem retained_read_reverts : Evm.run TargetArrayRead.code
    {machine with stack := .val one :: .slot (.root 0) :: tail} = .revert := by
  exact (TargetArrayRead.failure_matches old one machine tail (.root 0) read_failure_joint).mpr rfl

theorem retained_write_reverts : Evm.run TargetArrayWrite.code
    {machine with stack := .val one :: .slot (.root 0) :: .val (TargetOperations.encodeWord (PrimTy.toWord (p := .bool) false)) :: tail} = .revert := by
  exact (TargetArrayWrite.failure_matches old one false machine tail (.root 0) write_failure_joint).mpr rfl

theorem outside_extent_reverts : Evm.run TargetArrayRead.code
    {machine with stack := .val three :: .slot (.root 0) :: tail} = .revert ∧
    Evm.run TargetArrayWrite.code {machine with stack := .val three :: .slot (.root 0) :: .val (TargetOperations.encodeWord (PrimTy.toWord (p := .bool) false)) :: tail} = .revert := by
  exact ⟨(TargetArrayRead.failure_matches old three machine tail (.root 0) read_failure_joint).mpr rfl,
    (TargetArrayWrite.failure_matches old three false machine tail (.root 0) write_failure_joint).mpr rfl⟩

theorem after_write_observations :
    let after := {machine with stack := tail, store := Evm.WordStore.write machine.store (.data (.root 0) 0) 0}
    (after.store (.root 0), after.store (.data (.root 0) 0),
      after.store (.data (.root 0) 1), after.store (.root 9), after.stack,
      after.mem 0, after.self, after.caller, after.timestamp) =
    (1, 0, 1, 99, tail, machine.mem 0, machine.self, machine.caller, machine.timestamp) := rfl

theorem reject_all_mismatch : Evm.run [.revert]
    {machine with stack := .val zero :: .slot (.root 0) :: tail} ≠
    Evm.run TargetArrayRead.code {machine with stack := .val zero :: .slot (.root 0) :: tail} := by
  rw [live_read]
  intro equal
  cases equal

def readQueries : List (Query graph (.array (.prim .bool))) := PrimitivePop.queries [zero]
def readStore : Store := fun _ => PrimTy.toWord (p := .bool) true
def numeric : WordStore := fun _ => PrimTy.toWord (p := .bool) true
def hash (_ : Storage.Pre) : Nat := 8
def readLocations : List Storage.Loc := [.root 0, .data (.root 0) 0]

theorem read_before : Represented old readQueries (.root 0) readStore := by
  intro query member
  change query ∈ [.length .nil, PrimitivePop.elementQuery zero] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨True.intro, ?_, ?_⟩
    · change 1 ≤ Storage.lmax ∧ 3 ≤ Storage.lmax
      decide
    · intro value observed
      cases observed
      rfl
  · refine ⟨?_, True.intro, ?_⟩
    · change 0 < Storage.lmax ∧ True
      exact ⟨by decide, True.intro⟩
    intro value observed
    cases observed
    rfl

theorem read_initial : ∀ query ∈ readQueries,
    machine.store.cells (TargetOperations.toSlot (query.location (.root 0))
      (TargetOperations.query_keysFit query (.root 0) True.intro)) =
        TargetOperations.encodeWord (readStore (query.location (.root 0))) := by
  intro query member
  change query ∈ [.length .nil, PrimitivePop.elementQuery zero] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem represented_read_joint :
    (TargetArrayRead.path zero).readLive Value.dflt old = some (.prim true) ∧
    TargetOperations.KeysFit (.root 0) ∧
    Represented old readQueries (.root 0) readStore ∧
    (∀ query ∈ readQueries, machine.store.cells
      (TargetOperations.toSlot (query.location (.root 0))
        (TargetOperations.query_keysFit query (.root 0) True.intro)) =
          TargetOperations.encodeWord (readStore (query.location (.root 0)))) :=
  ⟨rfl, True.intro, read_before, read_initial⟩

theorem complete_read_joint :
    (TargetArrayRead.path zero).readLive Value.dflt old = some (.prim true) ∧
    TargetOperations.KeysFit (.root 0) ∧
    Represented old readQueries (.root 0) readStore ∧
    Transport 16 hash readLocations readStore numeric ∧
    Storage.Loc.data (.root 0) zero.val ∈ readLocations ∧
    (∀ query ∈ readQueries, machine.store.cells
      (TargetOperations.toSlot (query.location (.root 0))
        (TargetOperations.query_keysFit query (.root 0) True.intro)) =
          TargetOperations.encodeWord (readStore (query.location (.root 0)))) := by
  refine ⟨rfl, True.intro, read_before, ?_, List.mem_cons_of_mem _ (List.mem_singleton_self _), read_initial⟩
  intro loc _
  rfl

theorem represented_read_actual : Evm.run TargetArrayRead.code
    {machine with stack := .val zero :: .slot (.root 0) :: tail} =
      .ok {machine with stack := .val (TargetOperations.encodeWord (PrimTy.toWord (p := .bool) true)) :: tail} 0 :=
  TargetArrayRead.represented_read old zero (.prim true) represented_read_joint.1
    (.root 0) represented_read_joint.2.1 readStore machine tail
    represented_read_joint.2.2.1 represented_read_joint.2.2.2

theorem complete_read_actual : Evm.run TargetArrayRead.code
    {machine with stack := .val zero :: .slot (.root 0) :: tail} =
      .ok {machine with stack := .val (TargetOperations.encodeWord (PrimTy.toWord (p := .bool) true)) :: tail} 0 ∧
    numeric ((Storage.Loc.data (.root 0) zero.val).word 16 hash) = PrimTy.toWord (p := .bool) true :=
  TargetArrayRead.complete_read old zero (.prim true) complete_read_joint.1
    (.root 0) complete_read_joint.2.1 readStore machine tail numeric hash readLocations
    complete_read_joint.2.2.1 complete_read_joint.2.2.2.1 complete_read_joint.2.2.2.2.1
    complete_read_joint.2.2.2.2.2

theorem wrong_numeric_refuses :
    ¬ Transport 16 hash readLocations readStore (fun _ => PrimTy.toWord (p := .bool) false) := by
  intro transported
  have wrong := transported (.data (.root 0) 0) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have unequal : PrimTy.toWord (p := .bool) false ≠ PrimTy.toWord (p := .bool) true := by decide
  exact unequal wrong

def wrongChild : Evm.Machine := {machine with
  store := Evm.WordStore.write machine.store (.data (.root 0) 0) 0}

theorem wrong_target_refuses : ¬ (∀ query ∈ readQueries,
    wrongChild.store.cells (TargetOperations.toSlot (query.location (.root 0))
      (TargetOperations.query_keysFit query (.root 0) True.intro)) =
        TargetOperations.encodeWord (readStore (query.location (.root 0)))) := by
  intro initial
  have wrong := initial (PrimitivePop.elementQuery zero)
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have unequal : (⟨0, by decide⟩ : Fin Evm.W) ≠ ⟨1, by decide⟩ := by decide
  exact unequal wrong

def writeLocations : List Storage.Loc := [.root 0, .data (.root 0) 0, .data (.root 0) 1]
def writePreimages : List Storage.Pre := [.data 0]
def frameQueries : List (Query graph (.array (.prim .bool))) := [PrimitivePop.elementQuery one]

theorem write_run : FiniteRun 16 2 1 hash writePreimages writeLocations := by
  constructor
  · intro _; change 8 < 16; decide
  · decide
  · decide
  · decide
  · intro loc member
    simp only [writeLocations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp only [Storage.Loc.Bounded] <;> decide
  · intro loc member
    simp only [writeLocations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide

theorem write_header : Represented old [.length .nil] (.root 0) readStore := by
  intro query member
  have same : query = .length .nil := List.mem_singleton.mp member
  subst query
  exact read_before _ List.mem_cons_self

theorem write_frame : Represented old frameQueries (.root 0) readStore := by
  intro query member
  have same : query = PrimitivePop.elementQuery one := List.mem_singleton.mp member
  subst query
  refine ⟨?_, True.intro, ?_⟩
  · change 1 < Storage.lmax ∧ True
    exact ⟨by decide, True.intro⟩
  · intro value observed
    cases observed
    rfl

theorem write_support : PathSupported (TargetArrayRead.path (G := graph) (p := .bool) zero) := by
  change 0 < Storage.lmax ∧ True
  exact ⟨by decide, True.intro⟩

theorem write_apart : ∀ query ∈ frameQueries,
    query.apart (TargetArrayRead.path (G := graph) (p := .bool) zero) := by
  intro query member
  have same : query = PrimitivePop.elementQuery one := List.mem_singleton.mp member
  subst query
  exact Apart.fork (StepApart.index zero one (by decide)) .nil .nil

theorem write_nonalias : ∀ query ∈ frameQueries,
    query.location (.root 0) ≠ pathLoc (TargetArrayRead.path (G := graph) (p := .bool) zero) (.root 0) := by
  intro query member
  have same : query = PrimitivePop.elementQuery one := List.mem_singleton.mp member
  subst query
  change Storage.Loc.data (.root 0) 1 ≠ .data (.root 0) 0
  decide

theorem write_transport : Transport 16 hash writeLocations readStore numeric := by
  intro loc _
  rfl

theorem write_header_covered : Storage.Loc.root 0 ∈ writeLocations := List.mem_cons_self

theorem write_child_covered :
    pathLoc (TargetArrayRead.path (G := graph) (p := .bool) zero) (.root 0) ∈ writeLocations :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem write_fitting : ∀ loc ∈ writeLocations, TargetOperations.KeysFit loc := by
  intro loc member
  simp only [writeLocations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact True.intro

theorem write_initial : ∀ loc (member : loc ∈ writeLocations),
    machine.store.cells (TargetOperations.toSlot loc (write_fitting loc member)) =
      TargetOperations.encodeWord (readStore loc) := by
  intro loc member
  simp only [writeLocations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem numeric_write_joint :
    FiniteRun 16 2 1 hash writePreimages writeLocations ∧
    TargetArrayWrite.writeAt old zero false = some result ∧
    TargetOperations.KeysFit (.root 0) ∧
    Represented old [.length .nil] (.root 0) readStore ∧
    Represented old frameQueries (.root 0) readStore ∧
    PathSupported (TargetArrayRead.path (G := graph) (p := .bool) zero) ∧
    (∀ query ∈ frameQueries, query.apart (TargetArrayRead.path (G := graph) (p := .bool) zero)) ∧
    (∀ query ∈ frameQueries, query.location (.root 0) ≠
      pathLoc (TargetArrayRead.path (G := graph) (p := .bool) zero) (.root 0)) ∧
    Transport 16 hash writeLocations readStore numeric ∧
    Storage.Loc.root 0 ∈ writeLocations ∧
    pathLoc (TargetArrayRead.path (G := graph) (p := .bool) zero) (.root 0) ∈ writeLocations ∧
    ∃ fitting : ∀ loc ∈ writeLocations, TargetOperations.KeysFit loc,
      ∀ loc (member : loc ∈ writeLocations),
        machine.store.cells (TargetOperations.toSlot loc (fitting loc member)) =
          TargetOperations.encodeWord (readStore loc) :=
  ⟨write_run, success_joint, True.intro, write_header, write_frame, write_support,
    write_apart, write_nonalias, write_transport, write_header_covered, write_child_covered,
    write_fitting, write_initial⟩

def writtenStore : Store := write readStore (.data (.root 0) 0) (PrimTy.toWord (p := .bool) false)
def writtenNumeric : WordStore := writeWord numeric 8 (PrimTy.toWord (p := .bool) false)
def writtenTarget : Evm.Machine := {machine with stack := tail, store := Evm.WordStore.write machine.store (.data (.root 0) 0) 0}

theorem numeric_write_actual :
    Evm.run TargetArrayWrite.code {machine with stack := .val zero :: .slot (.root 0) :: .val (TargetOperations.encodeWord (PrimTy.toWord (p := .bool) false)) :: tail} = .ok writtenTarget 0 ∧
    Represented result (.length .nil :: .word (TargetArrayRead.path zero) :: frameQueries) (.root 0) writtenStore ∧
    Transport 16 hash writeLocations writtenStore writtenNumeric ∧
    (∀ loc (member : loc ∈ writeLocations),
      writtenTarget.store.cells (TargetOperations.toSlot loc (write_fitting loc member)) =
        TargetOperations.encodeWord (writtenStore loc)) := by
  rcases numeric_write_joint with ⟨run, performed, fits, header, before, supported,
    apart, nonalias, initial, headerCovered, childCovered, fitting, targetInitial⟩
  exact TargetArrayWrite.complete_numeric run old result zero false performed frameQueries
    (.root 0) fits readStore numeric machine tail header before supported apart nonalias
    initial headerCovered childCovered fitting targetInitial

theorem numeric_write_observations :
    (writtenNumeric 0, writtenNumeric 8, writtenNumeric 9,
      writtenTarget.store (.root 0), writtenTarget.store (.data (.root 0) 0),
      writtenTarget.store (.data (.root 0) 1), writtenTarget.store (.root 9),
      writtenTarget.stack, writtenTarget.mem 0) =
    (PrimTy.toWord (p := .bool) true, PrimTy.toWord (p := .bool) false,
      PrimTy.toWord (p := .bool) true, 1, 0, 1, 99, tail, machine.mem 0) := rfl

theorem colliding_hash_refuses :
    ¬ FiniteRun 16 2 1 (fun _ => 0) writePreimages writeLocations := by
  intro run
  have alias := run.word_inj (a := .root 0) (b := .data (.root 0) 0)
    write_header_covered write_child_covered rfl
  exact (Storage.Loc.data_ne_self (.root 0) 0) alias.symm

def defaultQueries : List (Query graph (.array (.prim .bool))) :=
  [.length .nil, PrimitivePop.elementQuery zero, PrimitivePop.elementQuery one]
def defaultPermit : CopyPermit graph (.array (.prim .bool)) :=
  CopyPermit.checked (fun _ => true) (by decide)

theorem default_supported : ∀ query ∈ defaultQueries, query.supported := by
  intro query member
  simp only [defaultQueries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact True.intro
  · change 0 < Storage.lmax ∧ True
    exact ⟨by decide, True.intro⟩
  · change 1 < Storage.lmax ∧ True
    exact ⟨by decide, True.intro⟩

theorem default_covered :
    ∀ query ∈ CopyDefaults.demands graph (.array (.prim .bool)) ++ defaultQueries,
      query.location (.root 0) ∈ writeLocations := by
  intro query member
  change query ∈ [.length .nil, .length .nil,
    PrimitivePop.elementQuery zero, PrimitivePop.elementQuery one] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem default_joint : ∃ _permit : CopyPermit graph (.array (.prim .bool)),
    (∀ query ∈ defaultQueries, query.supported) ∧
    TargetOperations.KeysFit (.root 0) ∧
    FiniteRun 16 2 1 hash writePreimages writeLocations ∧
    Transport 16 hash writeLocations readStore numeric ∧
    (∀ query ∈ CopyDefaults.demands graph (.array (.prim .bool)) ++ defaultQueries,
      query.location (.root 0) ∈ writeLocations) ∧
    ∃ fitting : ∀ loc ∈ writeLocations, TargetOperations.KeysFit loc,
      ∀ loc (member : loc ∈ writeLocations),
        machine.store.cells (TargetOperations.toSlot loc (fitting loc member)) =
          TargetOperations.encodeWord (readStore loc) :=
  ⟨defaultPermit, default_supported, True.intro, write_run, write_transport,
    default_covered, write_fitting, write_initial⟩

noncomputable def defaultStore : Store :=
  (CopyDefaults.updates graph (.array (.prim .bool)) (.root 0)).foldl
    (fun store op => write store op.1 op.2) readStore
noncomputable def defaultNumeric : WordStore :=
  CopyDefaults.numericInit (N := 16) graph (.array (.prim .bool)) (.root 0) hash numeric
noncomputable def defaultTarget : Evm.Machine :=
  TargetDefaultInit.afterInit graph (.array (.prim .bool)) (.root 0) True.intro machine

theorem default_complete_actual :
    Evm.run (TargetDefaultInit.code graph (.array (.prim .bool)) defaultPermit (.root 0) True.intro)
      machine = .ok defaultTarget 0 ∧
    Represented (Value.dflt (.array (.prim .bool))) defaultQueries (.root 0) defaultStore ∧
    Transport 16 hash writeLocations defaultStore defaultNumeric ∧
    (∀ loc (member : loc ∈ writeLocations),
      defaultTarget.store.cells (TargetOperations.toSlot loc (write_fitting loc member)) =
        TargetOperations.encodeWord (defaultNumeric (loc.word 16 hash))) ∧
    (∀ query ∈ defaultQueries, ∀ word, query.read (Value.dflt (.array (.prim .bool))) = some word →
      Evm.run (TargetOperations.readCode (TargetOperations.toSlot (query.location (.root 0))
        (TargetOperations.query_keysFit query (.root 0) True.intro))) defaultTarget =
          .ok {defaultTarget with stack := .val (TargetOperations.encodeWord word) :: defaultTarget.stack} 0) := by
  rcases default_joint with ⟨permit, supported, fits, run, initial, covered, fitting, before⟩
  exact TargetDefaultInit.complete graph (.array (.prim .bool)) permit defaultQueries supported
    (.root 0) fits run readStore numeric machine initial covered fitting before

theorem default_observations :
    (defaultQueries.map (fun query => query.read (Value.dflt (.array (.prim .bool)))),
      defaultNumeric 0, defaultNumeric 8, defaultNumeric 9,
      defaultTarget.store (.root 0), defaultTarget.store (.data (.root 0) 0),
      defaultTarget.store (.data (.root 0) 1), defaultTarget.store (.root 9),
      defaultTarget.stack, defaultTarget.mem 0) =
    ([some (PrimTy.toWord (p := .bool) false), none, none],
      PrimTy.toWord (p := .bool) false, PrimTy.toWord (p := .bool) true,
      PrimTy.toWord (p := .bool) true, 0, 1, 1, 99, machine.stack, machine.mem 0) := rfl

theorem default_read_header : Evm.run (TargetOperations.readCode (.root 0)) defaultTarget =
    .ok {defaultTarget with stack := .val (TargetOperations.encodeWord (PrimTy.toWord (p := .bool) false)) :: defaultTarget.stack} 0 :=
  default_complete_actual.2.2.2.2 (.length .nil) List.mem_cons_self
    (PrimTy.toWord (p := .bool) false) rfl

theorem default_noop_mismatch : Evm.run [] machine ≠
    Evm.run (TargetDefaultInit.code graph (.array (.prim .bool)) defaultPermit (.root 0) True.intro) machine := by
  rw [default_complete_actual.1]
  intro equal
  have observed := congrArg (fun output : Evm.Out => match output with
    | .ok next _ => next.store (.root 0)
    | _ => 99) equal
  change (1 : Nat) = 0 at observed
  omega

theorem default_reject_mismatch : Evm.run [.revert] machine ≠
    Evm.run (TargetDefaultInit.code graph (.array (.prim .bool)) defaultPermit (.root 0) True.intro) machine := by
  rw [default_complete_actual.1]
  intro equal
  cases equal

theorem default_owner_joint : ∃ _permit : CopyPermit graph (.array (.prim .bool)),
    ∀ query ∈ defaultQueries, query.supported := ⟨defaultPermit, default_supported⟩

theorem default_transport_joint :
    FiniteRun 16 2 1 hash writePreimages writeLocations ∧
    Transport 16 hash writeLocations readStore numeric ∧
    (∀ query ∈ CopyDefaults.demands graph (.array (.prim .bool)),
      query.location (.root 0) ∈ writeLocations) :=
  ⟨write_run, write_transport, fun query member => default_covered query
    (List.mem_append.mpr (Or.inl member))⟩

theorem default_owner_actual :
    Represented (Value.dflt (.array (.prim .bool))) defaultQueries (.root 0) defaultStore := by
  rcases default_owner_joint with ⟨permit, supported⟩
  exact CopyDefaults.represented graph (.array (.prim .bool)) permit defaultQueries supported (.root 0) readStore

theorem default_transport_actual : Transport 16 hash writeLocations defaultStore defaultNumeric := by
  rcases default_transport_joint with ⟨run, initial, covered⟩
  exact CopyDefaults.numeric_transport graph (.array (.prim .bool)) run (.root 0) readStore numeric initial covered

/-- Reuse the populated default-initialization fixture to witness the base
key premise; this is symbolic-slot coverage, not physical layout adequacy. -/
theorem default_fit_base_joint : TargetOperations.KeysFit (.root 0) := True.intro

/-- Every generated update fits simultaneously, with a nonempty update list. -/
theorem default_updates_joint :
    ∀ op ∈ CopyDefaults.updates graph (.array (.prim .bool)) (.root 0),
      TargetOperations.KeysFit op.1 :=
  TargetDefaultInit.updates_fit graph (.array (.prim .bool)) (.root 0) default_fit_base_joint

/-- Generated defaults really write the existing header; a reject-all or
empty-update replacement cannot satisfy this fixture. -/
theorem default_updates_nonempty :
    CopyDefaults.updates graph (.array (.prim .bool)) (.root 0) ≠ [] := by
  intro impossible
  cases impossible

/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_fit_base_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms default_fit_base_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_updates_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_updates_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_updates_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_updates_nonempty

/-- Input inhabitance only for the no-hypothesis logical read laws. The
existing retained index is populated but outside the live header. -/
theorem logical_read_inputs : Nonempty (Value graph (.array (.prim .bool)) × Index) :=
  ⟨(old, one)⟩

/-- Input inhabitance only for the no-hypothesis primitive-write failure law;
no logical premise bundle or compiler totality is claimed. -/
theorem logical_write_inputs :
    Nonempty (Value graph (.array (.prim .bool)) × Index × Bool) :=
  ⟨(old, one, false)⟩

/-- Exercise the original word law at the existing dirty retained cell; the
raw query can observe true while the live path refuses the same index. -/
theorem retained_word_law :
    ((TargetArrayRead.path one).readLive Value.dflt old).map (fun v => PrimTy.toWord (p := .bool) v.head) =
      if one.val < old.length.val then (PrimitivePop.elementQuery one).read old else none :=
  TargetArrayRead.live_word old one

/-- Reuse the original logical failure equivalence on the retained fixture. -/
theorem retained_none_law :
    (TargetArrayRead.path one).readLive Value.dflt old = none ↔ old.length.val ≤ one.val :=
  TargetArrayRead.live_none_iff old one

/-- Reuse the original primitive save failure equivalence, keeping raw
retained save distinct from the live adapter's refusal. -/
theorem retained_write_failure_law :
    TargetArrayWrite.writeAt old one false = none ↔ old.length.val ≤ one.val :=
  TargetArrayWrite.failure old one false

/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.logical_read_inputs' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms logical_read_inputs
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.logical_write_inputs' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms logical_write_inputs
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.retained_word_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retained_word_law
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.retained_none_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retained_none_law
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.retained_write_failure_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retained_write_failure_law

/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.read_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms read_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms write_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.read_failure_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms read_failure_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_failure_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms write_failure_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.success_joint' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms success_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.header_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.live_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms live_read
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.live_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms live_write
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.adapter_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms adapter_success
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.header_frame_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header_frame_actual
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.retained_raw_and_live' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms retained_raw_and_live
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.retained_read_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retained_read_reverts
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.retained_write_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retained_write_reverts
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.outside_extent_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside_extent_reverts
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.after_write_observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms after_write_observations
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.reject_all_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reject_all_mismatch

/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.read_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_before
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.read_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_initial
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.represented_read_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms represented_read_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.complete_read_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_read_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.represented_read_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms represented_read_actual
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.complete_read_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_read_actual
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.wrong_numeric_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_numeric_refuses
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.wrong_target_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_target_refuses

/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_run' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms write_run
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_header
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_frame
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_support' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms write_support
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_apart' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms write_apart
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_nonalias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_nonalias
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_transport
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_header_covered' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms write_header_covered
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_child_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_child_covered
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_fitting' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms write_fitting
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.write_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_initial
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.numeric_write_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_write_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.numeric_write_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_write_actual
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.numeric_write_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_write_observations
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.colliding_hash_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms colliding_hash_refuses

/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_supported' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms default_supported
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_covered
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_complete_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_complete_actual
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_observations
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_read_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_read_header
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_noop_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_noop_mismatch
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_reject_mismatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_reject_mismatch

/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_owner_joint' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms default_owner_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_transport_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_transport_joint
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_owner_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_owner_actual
/-- info: 'H62.StorageAudit.ArrayAccessWitnesses.default_transport_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms default_transport_actual

end H62.StorageAudit.ArrayAccessWitnesses

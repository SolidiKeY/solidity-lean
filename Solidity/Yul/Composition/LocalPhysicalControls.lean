import Solidity.Yul.Composition.LocalPhysicalMemory
import Solidity.Yul.Composition.PhysicalControls
import Solidity.Yul.LocalBlockLogic

/-! Inhabited joint VY1/VY2 boundary in the SAME actual Source context.
A real heap object backs the unchanged nonword local. Physical actions precede
the raw block; the rollback comparison rebases St, never resumes old EM on raw
locals. Raw-local rollback/function-frame semantics are NOT asserted. -/
namespace Solidity.Yul.Composition.LocalPhysicalControls
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls

def functionTy : Source.STy := .fn true [.bool] [.int Source.IntTy.u8] (some .view)
def ctx : Source.Ctx :=
  {env:=originEnv,scope:=none,locals:=[("flag",.bool),("ptr1",functionTy),
    ("small",.int Source.IntTy.u8),("ptr2",functionTy),("byte",.fixedBytes 1 (by decide)),
    ("memory",.bytes .memory)]}
abbrev X := localExternalTypes ctx

def heap : Source.Heap originEnv.layout :=
  ((Source.Heap.empty (D := originEnv.layout)).alloc ⟨.bytes .memory,.bytes [0xaa,0xbb]⟩).1
def locals : Source.Locals originEnv.layout ctx.tys :=
  .cons (.bool true) (.cons (.externalFn ⟨4660,by decide⟩ [137,171,205,239] rfl)
    (.cons (.int 1 (by decide)) (.cons (.externalFn ⟨22136,by decide⟩ [1,2,3,4] rfl)
      (.cons (.fixedBytes [171] rfl) (.cons (.memRef rfl 0) .nil)))))
def initial : Source.EMState originEnv ctx.tys :=
  (locals,{ownedOriginState.2 with heap:=heap,logs:=[(account,[0x55])]})

theorem initial_MemOK : Source.MemOK originEnv heap.ty initial := by
  refine ⟨⟨⟨Source.HeapOK.alloc Source.HeapOK.empty (.bytes _),Source.HeapTy.Le.refl _⟩,?_⟩,
    Source.HeapShaped.alloc Source.HeapShaped.empty trivial,
    Source.HeapInner.alloc Source.HeapInner.empty trivial⟩
  exact ⟨trivial,trivial,trivial,trivial,trivial,⟨.bytes .memory,rfl,rfl⟩,trivial⟩

def flag : WordCell X := .scalar ⟨.boolean,.here⟩
def first : Member X .externalFunction := .there .here
def second : Member X .externalFunction := .there (.there (.there .here))
def small : WordCell X := .scalar ⟨.unsigned 0,.there (.there .here)⟩
def byte : WordCell X := .scalar ⟨.fixedBytes 0,.there (.there (.there (.there .here)))⟩
def memoryRef : SourceLocalRef ctx := ⟨.there (.there (.there (.there (.there .here))))⟩
def memoryShape : DeclaredSourceTypeD originEnv memoryRef.ty .memory := .basic (.reference .bytesMemory)

def assign (c : Control) (cell : WordCell X) (value : Expr [] X 0 1) : Stmt [] X c 0 :=
  .assign (Fin.cases (.external cell.writeRef) Fin.elim0) value
def maxExpr : Expr [] X 0 1 := .builtin (.pure .not) (Fin.cases (.literal (word 0)) Fin.elim0)
def addExpr : Expr [] X 0 1 := .builtin (.pure .add)
  (Fin.cases (.external small.readRef) (Fin.cases (.literal (word 256)) Fin.elim0))
def dirtyCode (c : Control) : Stmt [] X c 0 :=
  .seq (assign c flag (.literal (word 2)))
    (.seq (assign c (.address first) maxExpr)
      (.seq (assign c (.selector second) maxExpr) (assign c small addExpr)))
def policy (c : Control) : Policy.StmtP .A (dirtyCode c) := (Policy.stmt_iff .A _).mp rfl
def code := dirtyCode ⟨false,false⟩
def firstPhysical := representedSourceStep originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
  packedStepFrame ownedOriginPlan initial ownedOriginResidual
def childPhysical := representedSourceStep originRegistry originTempRegistry PhysicalControls.childRequest firstPhysical.2
  packedStepFrame PhysicalControls.childPlan firstPhysical.1.1.2 firstPhysical.1.2

def joint (fuel : Nat) := representedThenLocal ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
  packedStepFrame ownedOriginPlan initial ownedOriginResidual code (policy _) fuel
def localResult := runLocalBlock ctx code (policy _) 32 (LocalState.ofClean firstPhysical.1.1.2)
theorem local_done : localResult.isSome := by decide +kernel
def completed := localResult.get local_done

theorem joint_complete : (joint 32).2 = .ok (some completed) :=
  congrArg Except.ok (Option.some_get local_done).symm

def snapshot (state : LocalState originEnv ctx.tys) : List Nat :=
  (List.finRange (wordCellCount X)).map (fun i => (localWordCells ctx state.1 (wordCellAt X i)).val)

theorem seven_dirty_words : snapshot completed.state =
    [2,2^256-1,2309737967,257,22136,2^256-1,171*2^248] := by decide +kernel

theorem same_type_locals_distinct :
    localWordCells ctx completed.state.1 (.address first) ≠ localWordCells ctx completed.state.1 (.address second) ∧
    localWordCells ctx completed.state.1 (.selector first) ≠ localWordCells ctx completed.state.1 (.selector second) := by decide +kernel

theorem source_retained : completed.state.2 = firstPhysical.1.1.2.2 :=
  represented_local_source ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan initial ownedOriginResidual code (policy _) 32 joint_complete

theorem nonword_retained : completed.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index :=
  represented_local_nonword ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan initial ownedOriginResidual code (policy _) 32 joint_complete memoryRef memoryShape rfl

theorem physical_checked :
    representedFrameWrite? originRegistry originTempRegistry packedStepFrame false 43 ownedOriginRequest.raw
      boolEncodingInitial initial ownedOriginResidual = some firstPhysical ∧
    Source.MemOK originEnv heap.ty firstPhysical.1.1.2 ∧
    reencodePersistentSlot (representedBanks originRegistry false firstPhysical.2)
      ⟨firstPhysical.1.1.2.2.ex,firstPhysical.1.2⟩ account 43 = some ownedOriginRequest.raw :=
  prepared_persistent_source originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan (Option.some_get owned_origin_prepared).symm rfl initial
    ownedOriginResidual _ initial_MemOK rfl rfl originChecked.separated

/-- Raw words may be numerically canonical or dirty; writeback retags them.
Neither literal clean-state identity nor runClean resumption follows. -/
theorem raw_not_clean : LocalState.clean? completed.state = none := rfl

theorem no_raw_resume (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action completed.state = none := LocalState.runClean_refuses action _ raw_not_clean

def revertedCore := companionRollback (companionEnter ⟨initial.2.ex,ownedOriginResidual⟩ account account 0 [] false)
  (companionCommit (companionEnter ⟨firstPhysical.1.1.2.2.ex,firstPhysical.1.2⟩ account account 0 [] false)
    ⟨childPhysical.1.1.2.2.ex,childPhysical.1.2⟩)
def revertedEncoding := boolEncodingRollback boolEncodingInitial.journal.length childPhysical.2

theorem three_journals_restore :
    revertedCore = ⟨initial.2.ex,ownedOriginResidual⟩ ∧ revertedEncoding = boolEncodingInitial :=
  physical_child_outer_rollback originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan initial ownedOriginResidual PhysicalControls.childRequest PhysicalControls.childPlan rfl []

def restored : Source.EMState originEnv ctx.tys :=
  (childPhysical.1.1.2.1,{childPhysical.1.1.2.2 with ex:=revertedCore.source})
theorem full_source_restored : restored = initial :=
  physical_child_state_rollback originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan initial ownedOriginResidual PhysicalControls.childRequest PhysicalControls.childPlan rfl []

/-- Every horizon transports the full raw result/control across the actual
physical rollback. This rebases St only; raw local rollback is not asserted. -/
theorem rollback_rebase (fuel : Nat) :
    runLocalBlock ctx code (policy _) fuel (LocalValues.ofClean locals,restored.2) =
      (runLocalBlock ctx code (policy _) fuel (LocalValues.ofClean locals,childPhysical.1.1.2.2)).map
        (fun result => ⟨(result.state.1,initial.2),result.flow⟩) := by
  rw [full_source_restored]
  exact local_rebase ctx code (policy _) fuel _ _ _

theorem static_halts (fuel : Nat) :
    (representedThenLocal ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
      {packedStepFrame with static:=true} ownedOriginPlan initial ownedOriginResidual code (policy _) fuel).2 =
      .error (.revert []) :=
  congrArg Prod.snd (represented_local_static ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    {packedStepFrame with static:=true} ownedOriginPlan initial ownedOriginResidual code (policy _) fuel rfl)

/-- Full completed result (raw values, source and control) is stable at every
completed horizon; horizon exhaustion remains distinct from a physical halt. -/
theorem completed_horizon (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : runLocalBlock ctx code (policy _) fuel (LocalState.ofClean firstPhysical.1.1.2) = some result) :
    result = completed :=
  LocalBlockLogic.completed_unique code (policy _) _ done (Option.some_get local_done).symm

def breakCode : Stmt [] X ⟨false,true⟩ 0 := .seq (dirtyCode _) .break_
def continueCode : Stmt [] X ⟨false,true⟩ 0 := .seq (dirtyCode _) .continue_
def leaveCode : Stmt [] X ⟨true,false⟩ 0 := .seq (dirtyCode _) .leave
def breakPolicy : Policy.StmtP .A breakCode := (Policy.stmt_iff .A _).mp rfl
def continuePolicy : Policy.StmtP .A continueCode := (Policy.stmt_iff .A _).mp rfl
def leavePolicy : Policy.StmtP .A leaveCode := (Policy.stmt_iff .A _).mp rfl
def breakRun := runLocalBlock ctx breakCode breakPolicy 32 (LocalState.ofClean firstPhysical.1.1.2)
def continueRun := runLocalBlock ctx continueCode continuePolicy 32 (LocalState.ofClean firstPhysical.1.1.2)
def leaveRun := runLocalBlock ctx leaveCode leavePolicy 32 (LocalState.ofClean firstPhysical.1.1.2)
theorem transfers_complete : breakRun.isSome ∧ continueRun.isSome ∧ leaveRun.isSome := by decide +kernel

theorem break_flow : (breakRun.get transfers_complete.1).flow = .break_ rfl := rfl
theorem continue_flow : (continueRun.get transfers_complete.2.1).flow = .continue_ rfl := rfl
theorem leave_flow : (leaveRun.get transfers_complete.2.2).flow = .leave_ rfl := rfl

def wrongOwnerRun := representedFrameWrite? originRegistry originTempRegistry PhysicalControls.wrongOwner false 43
  ownedOriginRequest.raw boolEncodingInitial initial ownedOriginResidual
def wrongSlotRun := representedFrameWrite? originRegistry originTempRegistry packedStepFrame false 42
  ownedOriginRequest.raw boolEncodingInitial initial ownedOriginResidual
theorem wrong_owner_control : (wrongOwnerRun.map fun out =>
    (out.1.1.2.2.ex.world.accounts account).storage.read (originPath "c")) = some (some (.bool false)) := rfl
theorem wrong_slot_control : (wrongSlotRun.map fun out =>
    (out.1.1.2.2.ex.world.accounts account).storage.read (originPath "c")) = some (some (.bool false)) := rfl

theorem local_full_word : reencodePersistentSlot (representedBanks originRegistry false firstPhysical.2)
    ⟨completed.state.2.ex,firstPhysical.1.2⟩ account 43 = some ownedOriginRequest.raw :=
  local_persistent_word ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial packedStepFrame
    ownedOriginPlan initial ownedOriginResidual code (policy _) 32 joint_complete rfl rfl rfl originChecked.separated

/-- This concrete placement is for the existing actual allocated byte object;
no equality with the native compiler's allocation addresses is assumed. -/
def placement : Placement heap where
  address a := 160+a*64
  shape _ := .bytes 2
  free := ⟨224,by decide⟩
  free_start := by decide
  distinct a b _ _ eq := by omega
  typed a τ data found := by
    by_cases zero : a=0
    · subst a
      have same : (some ⟨.bytes .memory,Source.Data.bytes [0xaa,0xbb]⟩ : Option (Sigma (Source.Data originEnv.layout))) = some ⟨τ,data⟩ := found
      cases Option.some.inj same
      exact .bytes _
    · simp only [Source.Heap.alloc,Source.Heap.empty,heap,Source.Heap.get,zero,if_false] at found
      cases found
  starts a _ := by omega
  ends a present := by
    by_cases zero : a=0
    · subst a
      decide
    · simp only [heap,Source.Heap.alloc,Source.Heap.empty,zero,if_false,Option.isSome_none] at present
      cases present
  separate a b one two different := by
    have onlyZero : ∀ n, (heap.cells n).isSome → n=0 := by
      intro n present
      by_cases zero : n=0
      · exact zero
      · simp only [heap,Source.Heap.alloc,Source.Heap.empty,zero,if_false,Option.isSome_none] at present
        cases present
    exact False.elim (different ((onlyZero a one).trans (onlyZero b two).symm))

def reserved : ByteView := mstore (fun _=>0) 64 placement.free
theorem reserved_valid : ReservedOK reserved placement.free := by
  constructor
  · exact congrArg Fin.val (mload_mstore (fun _=>0) 64 placement.free)
  · intro i
    exact mstore_outside (fun _=>0) 64 (96+i.val) placement.free (by have hi:=i.isLt;omega)

def image : MemoryImage placement (Source.Data.bytes (l := .memory) [0xaa,0xbb]) := .bytes _ (by decide)
def memoryView := image.encode reserved (placement.address 0)
def target := Solidity.Backend.Environment.runData (Solidity.Backend.Environment.materialize 31 [0xbb])
  PhysicalMemoryControls.caller

theorem joint_memory_target :
    completed.state.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0xaa,0xbb]⟩ ∧
    ReservedOK memoryView placement.free ∧
    target = some {(PhysicalMemoryControls.caller) with memory := copyBytes PhysicalMemoryControls.caller.memory memoryView 31 (placement.address 0+33) 1} ∧
    ValidRange (placement.address 0+33) 1 :=
  local_heap_window_target ctx originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
    packedStepFrame ownedOriginPlan initial ownedOriginResidual code (policy _) 32 joint_complete
    placement 0 [0xaa,0xbb] (by decide) rfl reserved reserved_valid 1 1 31 [0xbb] (by decide)
    PhysicalMemoryControls.caller (by decide)

example : target.map (fun s => [s.memory 30,s.memory 31,s.memory 32]) = some [0xee,0xbb,0xee] := by decide +kernel
example : (runLocalBlock ctx code (policy _) 4 (LocalState.ofClean firstPhysical.1.1.2)).isNone = true := by decide +kernel
#print axioms completed_horizon
#print axioms local_full_word
#print axioms joint_memory_target
#print axioms break_flow
#print axioms continue_flow
#print axioms leave_flow
example : snapshot completed.state ≠ [1,2^256-1,2309737967,1,22136,2^256-1,171*2^248] := by decide +kernel
example : completed.flow.isNormal = true := by decide +kernel
example : completed.state.2.logs = [(account,[0x55])] := by rw [source_retained]; rfl
example : (joint 0).2 = .ok none := rfl
#print axioms initial_MemOK
#print axioms seven_dirty_words
#print axioms source_retained
#print axioms physical_checked
#print axioms three_journals_restore
#print axioms rollback_rebase
#print axioms static_halts
end Solidity.Yul.Composition.LocalPhysicalControls

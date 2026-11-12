import Solidity.Yul.Composition.RecursivePhysical

/-! Raw caller-local continuation across actual coupled physical rollback.
The physical action runs on its existing EMState carrier; raw locals are an
explicit unchanged companion, not fed through runClean or a new Source hook.
Supplied VY4 completion bytes do not assert general try/catch dispatch. -/
namespace Solidity.Yul.Composition.RawCatchPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

def callerPrefix : LocalState originEnv ctx.tys := (RecursivePhysical.completed.state.1,initial.2)
/-- Both Source.St values come from the actual represented/journal execution. -/
def afterChild : LocalState originEnv ctx.tys := (callerPrefix.1,childPhysical.1.1.2.2)
def afterRollback : LocalState originEnv ctx.tys := (afterChild.1,restored.2)

theorem actual_prefix :
    runLocalBlock ctx (RecursivePhysical.code true) (RecursivePhysical.policy true) 32
      (LocalState.ofClean initial) = some ⟨callerPrefix,.normal⟩ := by
  have moved := local_rebase ctx (RecursivePhysical.code true) (RecursivePhysical.policy true) 32
    (LocalValues.ofClean locals) LocalPhysicalControls.firstPhysical.1.1.2.2 initial.2
  change _ = _ at moved
  rw [show runLocalBlock ctx (RecursivePhysical.code true) (RecursivePhysical.policy true) 32
      (LocalValues.ofClean locals,LocalPhysicalControls.firstPhysical.1.1.2.2) = some RecursivePhysical.completed from
        (Option.some_get RecursivePhysical.completes).symm] at moved
  exact moved.trans (congrArg some (congrArg (fun flow => (⟨callerPrefix,flow⟩ : LocalBlockOutcome ctx ⟨false,false⟩)) RecursivePhysical.normal_return))

theorem snapshot_state_irrelevant (values : LocalValues originEnv ctx.tys) (a b : Source.St originEnv) :
    snapshot (values,a) = snapshot (values,b) := rfl

theorem raw_prefix_words : snapshot callerPrefix =
    [2,2^256-1,2309737967,1025,22136,2^256-1,171*2^248] := by
  exact (snapshot_state_irrelevant _ initial.2 RecursivePhysical.completed.state.2).trans RecursivePhysical.recursive_words

theorem complete_state_restore : afterRollback = callerPrefix := by
  unfold afterRollback afterChild callerPrefix
  rw [full_source_restored]

theorem raw_child_identity : afterChild.1 = callerPrefix.1 := rfl

theorem coupled_journals :
    revertedCore = ⟨callerPrefix.2.ex,ownedOriginResidual⟩ ∧ revertedEncoding = boolEncodingInitial := three_journals_restore

/-- This consumes existing RAW LocalValues, never LocalValues.ofClean. -/
def catchCode : Stmt [] X ⟨false,false⟩ 0 := assign _ small addExpr
def catchPolicy : Policy.StmtP .A catchCode := (Policy.stmt_iff .A _).mp rfl
def runCatch (fuel : Nat) := runLocalBlock ctx catchCode catchPolicy fuel afterRollback

theorem every_horizon (fuel : Nat) :
    runCatch fuel = (runLocalBlock ctx catchCode catchPolicy fuel afterChild).map
      (fun result => ⟨(result.state.1,callerPrefix.2),result.flow⟩) := by
  unfold runCatch afterRollback
  rw [full_source_restored]
  exact local_rebase ctx catchCode catchPolicy fuel afterChild.1 _ _

theorem completes : (runCatch 32).isSome := by decide +kernel
def completed : LocalBlockOutcome ctx ⟨false,false⟩ := (runCatch 32).get completes

theorem exact_catch_words : snapshot completed.state =
    [2,2^256-1,2309737967,1281,22136,2^256-1,171*2^248] := by decide +kernel

theorem caller_source_retained : completed.state.2 = callerPrefix.2 := by
  have kept := runLocalBlock_world ctx catchCode catchPolicy 32 afterRollback (Option.some_get completes).symm
  exact kept.trans (congrArg Prod.snd complete_state_restore)

theorem nonword_retained : completed.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index := by
  have kept : completed.state.1.get memoryRef.index = afterRollback.1.get memoryRef.index :=
    runLocalBlock_nonword ctx catchCode catchPolicy 32 afterRollback (Option.some_get completes).symm memoryRef memoryShape rfl
  have old : callerPrefix.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index :=
    runLocalBlock_nonword ctx (RecursivePhysical.code true) (RecursivePhysical.policy true) 32
      (LocalState.ofClean initial) actual_prefix memoryRef memoryShape rfl
  exact kept.trans old

theorem writeback_raw (values : LocalValues originEnv ctx.tys) (cells : WordCells X) :
    LocalValues.clean? ctx.tys (writebackLocalWords ctx values cells) = none := rfl

theorem catch_raw (values : LocalState originEnv ctx.tys) (fuel : Nat)
    (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : runLocalBlock ctx catchCode catchPolicy fuel values = some result) :
    LocalState.clean? result.state = none := by
  unfold runLocalBlock at done
  cases actual : WordAdapter.run catchCode catchPolicy fuel ⟨Fin.elim0,localWordCells ctx values.1⟩ with
  | none => rw [actual] at done; cases done
  | some raw =>
      rw [actual] at done
      cases done
      change (LocalValues.clean? ctx.tys (writebackLocalWords ctx values.1 raw.state.cells)).map _ = none
      rw [writeback_raw]
      rfl

theorem raw_not_clean : LocalState.clean? completed.state = none :=
  catch_raw afterRollback 32 completed (Option.some_get completes).symm

theorem no_clean_resume (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action completed.state = none := LocalState.runClean_refuses action _ raw_not_clean

theorem completed_unique (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : runCatch fuel = some result) : result=completed :=
  runLocalBlock_unique ctx catchCode catchPolicy _ done (Option.some_get completes).symm

/-- Actual VY4 rollback retains the caller's nonempty log callerPrefix and exact
failure bytes. Its Effects does not carry VY2 complement/owned-byte journals. -/
def entry := physicalExecution initial [⟨account,⟨0,by decide⟩,#v[],[0x55]⟩] [0xfa]
def reverted (data : List UInt8) := Solidity.Yul.World.complete entry account account 0 [] false
  [ownedOriginPlan.packed.sourceOp,PhysicalControls.childPlan.packed.sourceOp] [⟨account,⟨0,by decide⟩,#v[],[0x66]⟩] (.revert data)

theorem exact_failure (data : List UInt8) : reverted data = ⟨initial.2.ex,[⟨account,⟨0,by decide⟩,#v[],[0x55]⟩],data⟩ :=
  Solidity.Yul.World.complete_revert entry account account 0 [] false _ _ data

theorem heap_alias : completed.state.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0xaa,0xbb]⟩ := by
  rw [caller_source_retained]
  rfl

def failureCopy (data : List UInt8) := completeAndCopy entry account account 0 [] false
  [ownedOriginPlan.packed.sourceOp,PhysicalControls.childPlan.packed.sourceOp] [⟨account,⟨0,by decide⟩,#v[],[0x66]⟩] (.revert data) 0 data.length 31 PhysicalMemoryControls.caller

theorem failure_window : (failureCopy [0xde,0xad]).map (fun out =>
    (out.1.returndata,[out.2.memory 30,out.2.memory 31,out.2.memory 32,out.2.memory 33])) =
      some ([0xde,0xad],[0xee,0xde,0xad,0xee]) := by decide +kernel

theorem empty_failure : (failureCopy []).map (fun out =>
    (out.1.returndata,[out.2.memory 30,out.2.memory 31,out.2.memory 32])) =
      some ([],[0xee,0xee,0xee]) := by decide +kernel

theorem missing_bytes_refused : completeAndCopy entry account account 0 [] false [] [] (.revert [])
    0 1 31 PhysicalMemoryControls.caller = none := rfl

theorem wrong_rollback_control : reencodePersistentSlot
    (representedBanks originRegistry false childPhysical.2) ⟨afterChild.2.ex,childPhysical.1.2⟩ account 43 =
      some PhysicalControls.childRequest.raw := by decide +kernel

theorem restored_word : reencodePersistentSlot (representedBanks originRegistry false revertedEncoding)
    ⟨completed.state.2.ex,revertedCore.residual⟩ account 43 = some (word 0) := by
  rw [caller_source_retained]
  decide +kernel

theorem wrong_owner_control : (wrongOwnerRun.map fun out =>
    (out.1.1.2.2.ex.world.accounts account).storage.read (originPath "c")) = some (some (.bool false)) :=
  LocalPhysicalControls.wrong_owner_control

theorem wrong_slot_control : (wrongSlotRun.map fun out =>
    (out.1.1.2.2.ex.world.accounts account).storage.read (originPath "c")) = some (some (.bool false)) :=
  LocalPhysicalControls.wrong_slot_control

theorem zero_horizon : runCatch 0 = none := rfl
#print axioms actual_prefix
#print axioms every_horizon
#print axioms exact_catch_words
#print axioms coupled_journals
#print axioms exact_failure
#print axioms failure_window
#print axioms restored_word
end Solidity.Yul.Composition.RawCatchPhysical

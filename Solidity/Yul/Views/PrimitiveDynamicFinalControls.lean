import Solidity.Yul.Views.PrimitiveDynamicWriteControls
import Solidity.Yul.Views.GenericFlow.FollowingLaws

namespace Solidity.Yul.Views.Controls

def pcBoolArray : Source.STy := .array .storage .bool none
def pcAliases : Source.EMState pcEnv [pcBoolArray,pcBoolArray] :=
  ⟨.cons pcB.reference (.cons pcB.reference .nil),pcSignedWrite.step.1.2.2⟩

theorem pc_alias_length : (Source.readLen (E := pcEnv) packedStepFrame (pcPath "bs")).run pcAliases = (.ok 3,pcAliases) := by
  have member := pcLayout.primitive_root_member pcFixed pcSignedWrite.nextRaw (pcB.registration account) (pcLayout.scalarFamilyHeader_member pcBEntry)
  have view := pcSignedWrite.view rfl (pcB.registration account) member
  have cell := pcB.view_length_cell account _ pcSignedWrite.nextRaw view
  have read := pcB.readLen packedStepFrame pcAliases (pcSignedWrite.nextRaw 3) rfl cell
  rw [pcsignedwrite_next] at read
  exact read

theorem pc_alias_value :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .bool) ⟨pcName "bs",[.index 0]⟩)).run pcAliases = (.ok (.bool true),pcAliases) := by
  have member : pcB.element pcFixed account 0 ∈ pcSignedWrite.next := by
    change _ ∈ pcLayout.primitiveSnapshot pcFixed pcSignedWrite.nextRaw
    rw [pcsignedwrite_next]
    exact pcLayout.primitive_scalar_subset pcFixed pcSignedWriteRaw _ (pcLayout.scalarFamily_element_member pcFixed pcSignedWriteRaw pcBEntry 0 (by decide))
  have view := pcSignedWrite.view rfl (pcB.element pcFixed account 0) member
  have bank := pcLayout.primitive_bank_agreement pcFixed pcSignedWrite.nextRaw _ member
  rw [pcsignedwrite_next] at view
  exact pcB.read_decoded packedStepFrame pcAliases pcFixed 0 pcSignedWriteRaw (.bool true) rfl bank view

theorem pc_two_real_aliases :
    (do let loc ← Source.indexLoc (E := pcEnv) packedStepFrame (pcAliases.1.get .here) 0
        Source.readLoc packedStepFrame loc).run pcAliases = (.ok (.bool true),pcAliases) ∧
    (do let loc ← Source.indexLoc (E := pcEnv) packedStepFrame (pcAliases.1.get (.there .here)) 0
        Source.readLoc packedStepFrame loc).run pcAliases = (.ok (.bool true),pcAliases) := by
  have first : (Source.indexLoc (E := pcEnv) packedStepFrame (pcAliases.1.get .here) 0).run pcAliases =
      (.ok (.stor ⟨pcName "bs",[.index 0]⟩),pcAliases) := pcB.indexLoc packedStepFrame pcAliases 3 pc_alias_length 0
  have second : (Source.indexLoc (E := pcEnv) packedStepFrame (pcAliases.1.get (.there .here)) 0).run pcAliases =
      (.ok (.stor ⟨pcName "bs",[.index 0]⟩),pcAliases) := pcB.indexLoc packedStepFrame pcAliases 3 pc_alias_length 0
  constructor
  · rw [Source.Hoare.run_bind,first]; exact pc_alias_value
  · rw [Source.Hoare.run_bind,second]; exact pc_alias_value

theorem pc_alias_bounds_error : (Source.indexLoc (E := pcEnv) packedStepFrame (pcAliases.1.get .here) 3).run pcAliases =
    (.error (.revert (Source.panicData .index)),pcAliases) := pcB.indexLoc packedStepFrame pcAliases 3 pc_alias_length 3

theorem pc_alias_MemOK : Source.MemOK pcEnv pcState.2.heap.ty pcAliases := by
  have h := pc_written_MemOK
  exact ⟨⟨h.1.1,⟨rfl,rfl,trivial⟩⟩,h.2⟩

/-- Failed canonical preparation retains the successful combined prefix.
The external dirtyGrow succeeds; None is NOT execution/refusal/no-op. -/
theorem pc_dirty_decode_false : (finiteAccountWrite? (T := pcEnv.lay) account
    (pcLayout.primitiveSnapshot pcFixed (saveSlot pcSignedWriteRaw 3 4)) (saveSlot pcSignedWriteRaw 3 4)).isSome = false := by decide

theorem pc_dirty_decode_none : finiteAccountWrite? (T := pcEnv.lay) account
    (pcLayout.primitiveSnapshot pcFixed (saveSlot pcSignedWriteRaw 3 4)) (saveSlot pcSignedWriteRaw 3 4) = none := by
  cases found : finiteAccountWrite? (T := pcEnv.lay) account (pcLayout.primitiveSnapshot pcFixed (saveSlot pcSignedWriteRaw 3 4)) (saveSlot pcSignedWriteRaw 3 4) with
  | none => rfl
  | some op => have bad := pc_dirty_decode_false; rw [found] at bad; cases bad

theorem pc_dirty_following_none : pcSignedWrite.following? rfl 3 4 = none := by
  have bad : finiteAccountWrite? (T := pcEnv.lay) account (pcLayout.primitiveSnapshot pcFixed (saveSlot pcSignedWrite.nextRaw 3 4)) (saveSlot pcSignedWrite.nextRaw 3 4) = none := by
    rw [pcsignedwrite_next]
    exact pc_dirty_decode_none
  unfold PrimitiveOwnershipPlan.following?
  exact GenericFlow.Following.none_of_write_none _ bad

theorem pc_dirty_fresh_none : preparePrimitiveOwnership? packedStepFrame pcLayout pcFixed 3 4 pcSignedWrite.step.1.2 pcSignedWrite.step.2 = none :=
  (pcSignedWrite.following_fresh rfl 3 4).symm.trans pc_dirty_following_none

theorem pc_unsupported_exact_prefix : runPrimitiveOwnership? packedStepFrame pcLayout pcFixed [(3,4)] pcSignedWrite.step.1.2 pcSignedWrite.step.2 =
    (none,pcSignedWrite.step.1.2,pcSignedWrite.step.2) := runPrimitiveOwnership?_unsupported _ _ _ _ _ _ _ _ pc_dirty_fresh_none

theorem pc_duplicate_inventory : packedSeparationCheck (pcLayout.registrations ++ pcLayout.registrations) = false := by decide

def pcMissing : StorageDeclarations pcEnv [(pcName "ss",.array .storage (.int pcI16) none)] := .cons (.signedArray pcI16 rfl) .nil

theorem pc_missing_metadata : (prepareComputedStorage pcMissing "PC" account).toOption.isSome = false := by decide

def pcWrong : StorageDeclarations pcEnv [(pcName "ss",.array .storage (.int pcI16) none),(pcName "us",.array .storage (.int .u256) none),
    (pcName "ws",.array .storage (.int .u256) none),(pcName "bs",.array .storage .bool none),(pcName "ys",.array .storage pcBytes.ty none),
    (pcName "zs",.array .storage pcAddress.ty none),(pcName "marker",.int .u256)] :=
  .cons (.signedArray pcI16 rfl) (.cons .uintArray (.cons .uintArray (.cons (.scalarArray .bool)
    (.cons (.scalarArray pcBytes) (.cons (.scalarArray pcAddress) (.cons (.fixed (.scalar (.int .u256) rfl)) .nil))))))

theorem pc_wrong_metadata : (prepareComputedStorage pcWrong "PC" account).toOption.isSome = false := by decide

theorem pcNoopReady : (preparePrimitiveOwnership? packedStepFrame pcLayout pcFixed 6 0 pcState pcResidual).isSome := by decide
@[irreducible]
def pcNoop : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 6 0 pcState pcResidual :=
  (preparePrimitiveOwnership? packedStepFrame pcLayout pcFixed 6 0 pcState pcResidual).get pcNoopReady

theorem pc_noop_raw : pcNoop.raw = pcRaw := pcNoop.raw_from_encoding pcRaw pc_initial_view pc_initial_encoding

theorem pc_noop_whole_store : (pcNoop.after.source.world.accounts account).storage = (pcState.2.ex.world.accounts account).storage := by
  apply pcNoop.same_word_store rfl
  exact (congrFun pc_noop_raw 6).trans (show pcRaw 6 = 0 from rfl)

def pcExplicitStorage : Source.Storage pcEnv.layout (pcEnv.lay account) :=
  (pcState.2.ex.world.accounts account).storage.write (pcPath "marker") (uintValueOfWord pcEnv.layout 0)

theorem pc_explicit_view : finiteView pcLayout.registrations pcExplicitStorage pcRaw := by
  intro c member
  change c ∈ [_,_,_,_,_,_,_] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem pc_explicit_whole_identity : pcLayout.primitiveSnapshotWriteback pcFixed pcRaw pcExplicitStorage =
    some (pcExplicitStorage,packedMask (pcLayout.primitiveSnapshot pcFixed pcRaw) pcRaw) :=
  pcLayout.primitive_unchanged pcFixed pcRaw pcExplicitStorage (by decide) pc_explicit_view

theorem pc_admin_distinction : (pcState.2.ex.world.accounts account).storage.cell (pcPath "marker") = none ∧
    pcExplicitStorage.cell (pcPath "marker") = some (uintValueOfWord pcEnv.layout 0) := ⟨rfl,rfl⟩

end Solidity.Yul.Views.Controls

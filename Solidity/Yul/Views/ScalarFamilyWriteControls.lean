import Solidity.Yul.Views.ScalarFamilyAliasControls

namespace Solidity.Yul.Views.Controls

def sfBoolWriteWord : Roadmap.Word := (sfX.element sfFixed account 33).field.saveWord sfWord1 ⟨0,by decide⟩
def sfBytesWriteWord : Roadmap.Word := (sfY.element sfFixed account 0).field.saveWord sfWordBytes ⟨0xa1b2c3,by decide⟩
def sfAddressWriteWord : Roadmap.Word := (sfZ.element sfFixed account 0).field.saveWord sfAddr0 ⟨2^160-1,by decide⟩

def sfBoolRaw := saveSlot sfMixedRaw 1001 sfBoolWriteWord
theorem sfboolwrite_ready : (sfZFill.following? rfl 1001 sfBoolWriteWord).isSome := by
  apply sfZFill.following_ready rfl
  · rw [sfzfill_next]; decide
  · rw [sfzfill_next]; decide
@[irreducible]
def sfBoolWrite : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 1001 sfBoolWriteWord sfZFill.step.1.2 sfZFill.step.2 :=
  (sfZFill.following? rfl 1001 sfBoolWriteWord).get sfboolwrite_ready

theorem sfboolwrite_next : sfBoolWrite.nextRaw = sfBoolRaw :=
  (congrArg (fun m => saveSlot m 1001 sfBoolWriteWord) (sfZFill.following_raw sfBoolWrite rfl)).trans (congrArg (fun m => saveSlot m 1001 sfBoolWriteWord) sfzfill_next)

theorem sfboolwrite_whole_map : finiteEncode sfBoolWrite.next (sfBoolWrite.step.1.2.2.ex.world.accounts account).storage
    (fun q => sfBoolWrite.step.2.cells (complementKey false account q)) = some sfBoolRaw :=
  (sfBoolWrite.reencode rfl).trans (congrArg some sfboolwrite_next)

def sfBytesRaw := saveSlot sfBoolRaw 2000 sfBytesWriteWord
theorem sfbyteswrite_ready : (sfBoolWrite.following? rfl 2000 sfBytesWriteWord).isSome := by
  apply sfBoolWrite.following_ready rfl
  · rw [sfboolwrite_next]; decide
  · rw [sfboolwrite_next]; decide
@[irreducible]
def sfBytesWrite : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 2000 sfBytesWriteWord sfBoolWrite.step.1.2 sfBoolWrite.step.2 :=
  (sfBoolWrite.following? rfl 2000 sfBytesWriteWord).get sfbyteswrite_ready

theorem sfbyteswrite_next : sfBytesWrite.nextRaw = sfBytesRaw :=
  (congrArg (fun m => saveSlot m 2000 sfBytesWriteWord) (sfBoolWrite.following_raw sfBytesWrite rfl)).trans (congrArg (fun m => saveSlot m 2000 sfBytesWriteWord) sfboolwrite_next)

theorem sfbyteswrite_whole_map : finiteEncode sfBytesWrite.next (sfBytesWrite.step.1.2.2.ex.world.accounts account).storage
    (fun q => sfBytesWrite.step.2.cells (complementKey false account q)) = some sfBytesRaw :=
  (sfBytesWrite.reencode rfl).trans (congrArg some sfbyteswrite_next)

def sfFinalRaw := saveSlot sfBytesRaw 3000 sfAddressWriteWord
theorem sfaddresswrite_ready : (sfBytesWrite.following? rfl 3000 sfAddressWriteWord).isSome := by
  apply sfBytesWrite.following_ready rfl
  · rw [sfbyteswrite_next]; decide
  · rw [sfbyteswrite_next]; decide
@[irreducible]
def sfAddressWrite : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 3000 sfAddressWriteWord sfBytesWrite.step.1.2 sfBytesWrite.step.2 :=
  (sfBytesWrite.following? rfl 3000 sfAddressWriteWord).get sfaddresswrite_ready

theorem sfaddresswrite_next : sfAddressWrite.nextRaw = sfFinalRaw :=
  (congrArg (fun m => saveSlot m 3000 sfAddressWriteWord) (sfBytesWrite.following_raw sfAddressWrite rfl)).trans (congrArg (fun m => saveSlot m 3000 sfAddressWriteWord) sfbyteswrite_next)

theorem sfaddresswrite_whole_map : finiteEncode sfAddressWrite.next (sfAddressWrite.step.1.2.2.ex.world.accounts account).storage
    (fun q => sfAddressWrite.step.2.cells (complementKey false account q)) = some sfFinalRaw :=
  (sfAddressWrite.reencode rfl).trans (congrArg some sfaddresswrite_next)
theorem sf_written_read (entry : {entry // entry ∈ sfLayout.scalarFamilyTrace}) (i : Nat)
    (bound : i < (sfFinalRaw ((sfLayout.scalarFamilyHeader entry).registration account).slot).val)
    (v : Source.Val sfEnv.layout (sfEnv.cellTy ((sfLayout.scalarFamilyHeader entry).elementPath i)))
    (decoded : ((sfLayout.scalarFamilyHeader entry).element sfFixed account i).codec.decode
      (((sfLayout.scalarFamilyHeader entry).element sfFixed account i).field.findWord
      (sfFinalRaw ((sfLayout.scalarFamilyHeader entry).element sfFixed account i).slot)) = some v) :
    (Source.readLoc packedStepFrame (Source.Loc.stor (τ := entry.val.2.1.ty)
      ((sfLayout.scalarFamilyHeader entry).elementPath i))).run sfAddressWrite.step.1.2 =
      (.ok (((sfLayout.scalarFamilyHeader entry).element_type i) ▸ v),sfAddressWrite.step.1.2) := by
  let h := sfLayout.scalarFamilyHeader entry
  have member : h.element sfFixed account i ∈ sfAddressWrite.next := by
    change _ ∈ sfLayout.scalarFamilySnapshot sfFixed sfAddressWrite.nextRaw
    rw [sfaddresswrite_next]
    exact sfLayout.scalarFamily_element_member sfFixed sfFinalRaw entry i bound
  have view := sfAddressWrite.view rfl (h.element sfFixed account i) member
  have bank := sfLayout.scalarFamily_bank_agreement sfFixed sfAddressWrite.nextRaw _ member
  rw [sfaddresswrite_next] at view
  exact h.read_decoded packedStepFrame sfAddressWrite.step.1.2 sfFixed i sfFinalRaw v decoded bank view

theorem sf_actual_bool_changed :
    (Source.readLoc (E := sfEnv) packedStepFrame (Source.Loc.stor (τ := .bool) ⟨sfName "xs",[.index 33]⟩)).run sfAddressWrite.step.1.2 =
      (.ok (.bool false),sfAddressWrite.step.1.2) := sf_written_read sfXEntry 33 (by decide) (.bool false) rfl

theorem sf_actual_bytes_changed :
    (Source.readLoc (E := sfEnv) packedStepFrame (Source.Loc.stor (τ := sfBytes.ty) ⟨sfName "ys",[.index 0]⟩)).run sfAddressWrite.step.1.2 =
      (.ok (.fixedBytes [0xa1,0xb2,0xc3] rfl),sfAddressWrite.step.1.2) := sf_written_read sfYEntry 0 (by decide) (.fixedBytes [0xa1,0xb2,0xc3] rfl) rfl

theorem sf_actual_address_changed :
    (Source.readLoc (E := sfEnv) packedStepFrame (Source.Loc.stor (τ := .address false) ⟨sfName "zs",[.index 0]⟩)).run sfAddressWrite.step.1.2 =
      (.ok (.address ⟨2^160-1,by decide⟩),sfAddressWrite.step.1.2) := sf_written_read sfZEntry 0 (by decide) (.address ⟨2^160-1,by decide⟩) rfl

theorem sf_written_every_H (H : Source.HeapTy) (ok : Source.MemOK sfEnv H sfState) : Source.MemOK sfEnv H sfAddressWrite.step.1.2 :=
  sfAddressWrite.MemOK H (sfBytesWrite.MemOK H (sfBoolWrite.MemOK H (sfZFill.MemOK H (sfYFill.MemOK H (sf_every_H H ok)))))

theorem sf_written_MemOK : Source.MemOK sfEnv sfState.2.heap.ty sfAddressWrite.step.1.2 := sf_written_every_H _ sf_initial_MemOK

theorem sf_persistent_endTx : finiteEncode sfAddressWrite.next ((companionEndTx sfAddressWrite.after).source.world.accounts account).storage
    (fun q => (companionEndTx sfAddressWrite.after).residual.cells (complementKey false account q)) = some sfFinalRaw :=
  (sfAddressWrite.endTx_reencode rfl).trans (congrArg some sfaddresswrite_next)

theorem sf_final_bool_padding : packedMask sfAddressWrite.next sfFinalRaw 1001 = ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc00020000,by decide⟩ := by
  change packedMask (sfLayout.scalarFamilySnapshot sfFixed sfAddressWrite.nextRaw) sfFinalRaw 1001 = _
  rw [sfaddresswrite_next]
  have owns : ∀ i : Fin 32, packedOwnsByte (sfLayout.scalarFamilySnapshot sfFixed sfFinalRaw) 1001 i = decide (i.val < 2) := by decide
  change complementWord (packedOwnsByte (sfLayout.scalarFamilySnapshot sfFixed sfFinalRaw) 1001) (sfFinalRaw 1001) = _
  rw [funext owns]
  rfl

theorem sf_final_bytes_padding : packedMask sfAddressWrite.next sfFinalRaw 2000 = ⟨0xaabb000000000000000000000000000000000000000000000000000000000000,by decide⟩ := by
  change packedMask (sfLayout.scalarFamilySnapshot sfFixed sfAddressWrite.nextRaw) sfFinalRaw 2000 = _
  rw [sfaddresswrite_next]
  have owns : ∀ i : Fin 32, packedOwnsByte (sfLayout.scalarFamilySnapshot sfFixed sfFinalRaw) 2000 i = decide (i.val < 30) := by decide
  change complementWord (packedOwnsByte (sfLayout.scalarFamilySnapshot sfFixed sfFinalRaw) 2000) (sfFinalRaw 2000) = _
  rw [funext owns]
  rfl

theorem sf_final_address_padding : packedMask sfAddressWrite.next sfFinalRaw 3000 = ⟨0xaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000000000,by decide⟩ := by
  change packedMask (sfLayout.scalarFamilySnapshot sfFixed sfAddressWrite.nextRaw) sfFinalRaw 3000 = _
  rw [sfaddresswrite_next]
  have owns : ∀ i : Fin 32, packedOwnsByte (sfLayout.scalarFamilySnapshot sfFixed sfFinalRaw) 3000 i = decide (i.val < 20) := by decide
  change complementWord (packedOwnsByte (sfLayout.scalarFamilySnapshot sfFixed sfFinalRaw) 3000) (sfFinalRaw 3000) = _
  rw [funext owns]
  rfl

def sfExplicitStorage : Source.Storage sfEnv.layout (sfEnv.lay account) :=
  (sfState.2.ex.world.accounts account).storage.write (sfPath "xs") (sfX.lengthValue 0)

theorem sf_explicit_view : finiteView sfLayout.registrations sfExplicitStorage sfRaw := by
  intro c member
  change c ∈ [_,_,_,_] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem sf_explicit_unchanged_whole_store : sfLayout.scalarFamilySnapshotWriteback sfFixed sfRaw sfExplicitStorage =
    some (sfExplicitStorage,packedMask (sfLayout.scalarFamilySnapshot sfFixed sfRaw) sfRaw) :=
  sfLayout.scalarFamily_unchanged sfFixed sfRaw sfExplicitStorage (by decide) sf_explicit_view

theorem sf_distinct_administrative_defaults :
    (sfState.2.ex.world.accounts account).storage.cell (sfPath "xs") = none ∧
    sfExplicitStorage.cell (sfPath "xs") = some (sfX.lengthValue 0) := ⟨rfl,rfl⟩

def sfWrittenAliases : Source.EMState sfEnv [sfArray,sfArray] :=
  ⟨.cons sfX.reference (.cons sfX.reference .nil),sfAddressWrite.step.1.2.2⟩

theorem sf_written_alias_length : (Source.readLen (E := sfEnv) packedStepFrame (sfPath "xs")).run sfWrittenAliases = (.ok 34,sfWrittenAliases) := by
  have member := sfLayout.scalarFamily_root_member sfFixed sfAddressWrite.nextRaw (sfX.registration account) (sfLayout.scalarFamilyHeader_member sfXEntry)
  have view := sfAddressWrite.view rfl (sfX.registration account) member
  have cell := sfX.view_length_cell account _ sfAddressWrite.nextRaw view
  have read := sfX.readLen packedStepFrame sfWrittenAliases (sfAddressWrite.nextRaw 0) rfl cell
  rw [sfaddresswrite_next] at read
  exact read

theorem sf_written_alias_value :
    (Source.readLoc (E := sfEnv) packedStepFrame (Source.Loc.stor (τ := .bool) ⟨sfName "xs",[.index 33]⟩)).run sfWrittenAliases =
    (.ok (.bool false),sfWrittenAliases) := by
  have member : sfX.element sfFixed account 33 ∈ sfAddressWrite.next := by
    change _ ∈ sfLayout.scalarFamilySnapshot sfFixed sfAddressWrite.nextRaw
    rw [sfaddresswrite_next]
    exact sfLayout.scalarFamily_element_member sfFixed sfFinalRaw sfXEntry 33 (by decide)
  have view := sfAddressWrite.view rfl (sfX.element sfFixed account 33) member
  have bank := sfLayout.scalarFamily_bank_agreement sfFixed sfAddressWrite.nextRaw _ member
  rw [sfaddresswrite_next] at view
  exact sfX.read_decoded packedStepFrame sfWrittenAliases sfFixed 33 sfFinalRaw (.bool false) rfl bank view

theorem sf_both_aliases_observe_change :
    (do let loc ← Source.indexLoc (E := sfEnv) packedStepFrame (sfWrittenAliases.1.get .here) 33
        Source.readLoc packedStepFrame loc).run sfWrittenAliases = (.ok (.bool false),sfWrittenAliases) ∧
    (do let loc ← Source.indexLoc (E := sfEnv) packedStepFrame (sfWrittenAliases.1.get (.there .here)) 33
        Source.readLoc packedStepFrame loc).run sfWrittenAliases = (.ok (.bool false),sfWrittenAliases) := by
  have first : (Source.indexLoc (E := sfEnv) packedStepFrame (sfWrittenAliases.1.get .here) 33).run sfWrittenAliases =
      (.ok (.stor ⟨sfName "xs",[.index 33]⟩),sfWrittenAliases) := sfX.indexLoc packedStepFrame sfWrittenAliases 34 sf_written_alias_length 33
  have second : (Source.indexLoc (E := sfEnv) packedStepFrame (sfWrittenAliases.1.get (.there .here)) 33).run sfWrittenAliases =
      (.ok (.stor ⟨sfName "xs",[.index 33]⟩),sfWrittenAliases) := sfX.indexLoc packedStepFrame sfWrittenAliases 34 sf_written_alias_length 33
  constructor
  · rw [Source.Hoare.run_bind,first]; exact sf_written_alias_value
  · rw [Source.Hoare.run_bind,second]; exact sf_written_alias_value

end Solidity.Yul.Views.Controls

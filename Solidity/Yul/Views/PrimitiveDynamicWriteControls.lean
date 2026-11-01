import Solidity.Yul.Views.PrimitiveDynamicFrameControls

namespace Solidity.Yul.Views.Controls

def pcBoolWriteWord : Roadmap.Word := (pcB.element pcFixed account 0).field.saveWord pcB0 ⟨1,by decide⟩
def pcSignedWriteWord : Roadmap.Word := (pcS.element pcFixed account 0).field.saveWord pcS0 ⟨32768,by decide⟩

def pcBoolZeroRaw := saveSlot pcRegrowRaw 3 0
theorem pcboolzero_ready : (pcRegrow.following? rfl 3 0).isSome := by
  apply pcRegrow.following_ready rfl
  · rw [pcregrow_next]; decide
  · rw [pcregrow_next]; decide
@[irreducible]
def pcBoolZero : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 3 0 pcRegrow.step.1.2 pcRegrow.step.2 :=
  (pcRegrow.following? rfl 3 0).get pcboolzero_ready

theorem pcboolzero_next : pcBoolZero.nextRaw = pcBoolZeroRaw :=
  (congrArg (fun m => saveSlot m 3 0) (pcRegrow.following_raw pcBoolZero rfl)).trans (congrArg (fun m => saveSlot m 3 0) pcregrow_next)

theorem pcboolzero_map : finiteEncode pcBoolZero.next (pcBoolZero.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcBoolZero.step.2.cells (complementKey false account q)) = some pcBoolZeroRaw :=
  (pcBoolZero.reencode rfl).trans (congrArg some pcboolzero_next)

def pcBoolRegrowRaw := saveSlot pcBoolZeroRaw 3 3
theorem pcboolregrow_ready : (pcBoolZero.following? rfl 3 3).isSome := by
  apply pcBoolZero.following_ready rfl
  · rw [pcboolzero_next]; decide
  · rw [pcboolzero_next]; decide
@[irreducible]
def pcBoolRegrow : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 3 3 pcBoolZero.step.1.2 pcBoolZero.step.2 :=
  (pcBoolZero.following? rfl 3 3).get pcboolregrow_ready

theorem pcboolregrow_next : pcBoolRegrow.nextRaw = pcBoolRegrowRaw :=
  (congrArg (fun m => saveSlot m 3 3) (pcBoolZero.following_raw pcBoolRegrow rfl)).trans (congrArg (fun m => saveSlot m 3 3) pcboolzero_next)

theorem pcboolregrow_map : finiteEncode pcBoolRegrow.next (pcBoolRegrow.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcBoolRegrow.step.2.cells (complementKey false account q)) = some pcBoolRegrowRaw :=
  (pcBoolRegrow.reencode rfl).trans (congrArg some pcboolregrow_next)

def pcBoolWriteRaw := saveSlot pcBoolRegrowRaw 4000 pcBoolWriteWord
theorem pcboolwrite_ready : (pcBoolRegrow.following? rfl 4000 pcBoolWriteWord).isSome := by
  apply pcBoolRegrow.following_ready rfl
  · rw [pcboolregrow_next]; decide
  · rw [pcboolregrow_next]; decide
@[irreducible]
def pcBoolWrite : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 4000 pcBoolWriteWord pcBoolRegrow.step.1.2 pcBoolRegrow.step.2 :=
  (pcBoolRegrow.following? rfl 4000 pcBoolWriteWord).get pcboolwrite_ready

theorem pcboolwrite_next : pcBoolWrite.nextRaw = pcBoolWriteRaw :=
  (congrArg (fun m => saveSlot m 4000 pcBoolWriteWord) (pcBoolRegrow.following_raw pcBoolWrite rfl)).trans (congrArg (fun m => saveSlot m 4000 pcBoolWriteWord) pcboolregrow_next)

theorem pcboolwrite_map : finiteEncode pcBoolWrite.next (pcBoolWrite.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcBoolWrite.step.2.cells (complementKey false account q)) = some pcBoolWriteRaw :=
  (pcBoolWrite.reencode rfl).trans (congrArg some pcboolwrite_next)

def pcSignedWriteRaw := saveSlot pcBoolWriteRaw 1000 pcSignedWriteWord
theorem pcsignedwrite_ready : (pcBoolWrite.following? rfl 1000 pcSignedWriteWord).isSome := by
  apply pcBoolWrite.following_ready rfl
  · rw [pcboolwrite_next]; decide
  · rw [pcboolwrite_next]; decide
@[irreducible]
def pcSignedWrite : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 1000 pcSignedWriteWord pcBoolWrite.step.1.2 pcBoolWrite.step.2 :=
  (pcBoolWrite.following? rfl 1000 pcSignedWriteWord).get pcsignedwrite_ready

theorem pcsignedwrite_next : pcSignedWrite.nextRaw = pcSignedWriteRaw :=
  (congrArg (fun m => saveSlot m 1000 pcSignedWriteWord) (pcBoolWrite.following_raw pcSignedWrite rfl)).trans (congrArg (fun m => saveSlot m 1000 pcSignedWriteWord) pcboolwrite_next)

theorem pcsignedwrite_map : finiteEncode pcSignedWrite.next (pcSignedWrite.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcSignedWrite.step.2.cells (complementKey false account q)) = some pcSignedWriteRaw :=
  (pcSignedWrite.reencode rfl).trans (congrArg some pcsignedwrite_next)
theorem pc_written_integer_read (entry : {entry // entry ∈ pcLayout.integerTrace}) (i : Nat)
    (bound : i < (pcSignedWriteRaw ((pcLayout.integerHeader entry).registration account).slot).val) :
    (Source.readLoc packedStepFrame (Source.Loc.stor (τ := .int entry.val.2.1)
      ((pcLayout.integerHeader entry).elementPath i))).run pcSignedWrite.step.1.2 =
      (.ok (((pcLayout.integerHeader entry).element_type i) ▸
        (pcLayout.integerHeader entry).elementValue pcFixed account i (pcSignedWriteRaw ((pcLayout.integerHeader entry).element pcFixed account i).slot)),pcSignedWrite.step.1.2) := by
  let h := pcLayout.integerHeader entry
  have member : h.element pcFixed account i ∈ pcSignedWrite.next := by
    change _ ∈ pcLayout.primitiveSnapshot pcFixed pcSignedWrite.nextRaw
    rw [pcsignedwrite_next]
    exact pcLayout.primitive_integer_subset pcFixed pcSignedWriteRaw _ (pcLayout.integer_element_member pcFixed pcSignedWriteRaw entry i bound)
  have view := pcSignedWrite.view rfl (h.element pcFixed account i) member
  have bank := pcLayout.primitive_bank_agreement pcFixed pcSignedWrite.nextRaw _ member
  rw [pcsignedwrite_next] at view
  exact h.read_element packedStepFrame pcSignedWrite.step.1.2 pcFixed i pcSignedWriteRaw bank view

theorem pc_written_scalar_read (entry : {entry // entry ∈ pcLayout.scalarFamilyTrace}) (i : Nat)
    (bound : i < (pcSignedWriteRaw ((pcLayout.scalarFamilyHeader entry).registration account).slot).val)
    (v : Source.Val pcEnv.layout (pcEnv.cellTy ((pcLayout.scalarFamilyHeader entry).elementPath i)))
    (decoded : ((pcLayout.scalarFamilyHeader entry).element pcFixed account i).codec.decode
      (((pcLayout.scalarFamilyHeader entry).element pcFixed account i).field.findWord
      (pcSignedWriteRaw ((pcLayout.scalarFamilyHeader entry).element pcFixed account i).slot)) = some v) :
    (Source.readLoc packedStepFrame (Source.Loc.stor (τ := entry.val.2.1.ty)
      ((pcLayout.scalarFamilyHeader entry).elementPath i))).run pcSignedWrite.step.1.2 =
      (.ok (((pcLayout.scalarFamilyHeader entry).element_type i) ▸ v),pcSignedWrite.step.1.2) := by
  let h := pcLayout.scalarFamilyHeader entry
  have member : h.element pcFixed account i ∈ pcSignedWrite.next := by
    change _ ∈ pcLayout.primitiveSnapshot pcFixed pcSignedWrite.nextRaw
    rw [pcsignedwrite_next]
    exact pcLayout.primitive_scalar_subset pcFixed pcSignedWriteRaw _ (pcLayout.scalarFamily_element_member pcFixed pcSignedWriteRaw entry i bound)
  have view := pcSignedWrite.view rfl (h.element pcFixed account i) member
  have bank := pcLayout.primitive_bank_agreement pcFixed pcSignedWrite.nextRaw _ member
  rw [pcsignedwrite_next] at view
  exact h.read_decoded packedStepFrame pcSignedWrite.step.1.2 pcFixed i pcSignedWriteRaw v decoded bank view

theorem pc_integer_changed :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .int pcI16) ⟨pcName "ss",[.index 0]⟩)).run pcSignedWrite.step.1.2 =
      (.ok (.int (-32768) (by decide)),pcSignedWrite.step.1.2) := pc_written_integer_read pcSEntry 0 (by decide)

theorem pc_scalar_survives_integer_write :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .bool) ⟨pcName "bs",[.index 0]⟩)).run pcSignedWrite.step.1.2 =
      (.ok (.bool true),pcSignedWrite.step.1.2) := pc_written_scalar_read pcBEntry 0 (by decide) (.bool true) rfl

theorem pc_unsigned_survives_cross_writes :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .int pcU24) ⟨pcName "us",[.index 10]⟩)).run pcSignedWrite.step.1.2 =
      (.ok (.int 77 (by decide)),pcSignedWrite.step.1.2) := pc_written_integer_read pcUEntry 10 (by decide)

theorem pc_word_survives_cross_writes :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .int .u256) ⟨pcName "ws",[.index 0]⟩)).run pcSignedWrite.step.1.2 =
      (.ok (.int 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (by decide)),pcSignedWrite.step.1.2) := pc_written_integer_read pcWEntry 0 (by decide)

theorem pc_bytes_survives_cross_writes :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := pcBytes.ty) ⟨pcName "ys",[.index 0]⟩)).run pcSignedWrite.step.1.2 =
      (.ok (.fixedBytes [1,2,3] rfl),pcSignedWrite.step.1.2) := pc_written_scalar_read pcYEntry 0 (by decide) (.fixedBytes [1,2,3] rfl) rfl

theorem pc_address_survives_cross_writes :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .address false) ⟨pcName "zs",[.index 0]⟩)).run pcSignedWrite.step.1.2 =
      (.ok (.address ⟨0x1234,by decide⟩),pcSignedWrite.step.1.2) := pc_written_scalar_read pcZEntry 0 (by decide) (.address ⟨0x1234,by decide⟩) rfl

theorem pc_written_every_H (H : Source.HeapTy) (ok : Source.MemOK pcEnv H pcState) : Source.MemOK pcEnv H pcSignedWrite.step.1.2 :=
  pcSignedWrite.MemOK H (pcBoolWrite.MemOK H (pcBoolRegrow.MemOK H (pcBoolZero.MemOK H (pc_every_H H ok))))

theorem pc_written_MemOK : Source.MemOK pcEnv pcState.2.heap.ty pcSignedWrite.step.1.2 := pc_written_every_H _ pc_initial_MemOK

theorem pc_final_endTx : finiteEncode pcSignedWrite.next ((companionEndTx pcSignedWrite.after).source.world.accounts account).storage
    (fun q => (companionEndTx pcSignedWrite.after).residual.cells (complementKey false account q)) = some pcSignedWriteRaw :=
  (pcSignedWrite.endTx_reencode rfl).trans (congrArg some pcsignedwrite_next)

end Solidity.Yul.Views.Controls

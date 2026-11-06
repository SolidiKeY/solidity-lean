import Solidity.Yul.Views.PrimitiveDynamicFinalControls
import Solidity.Yul.Views.PrimitiveOwnershipResidual

namespace Solidity.Yul.Views.Controls

theorem pc_signed_residual_byte : lowByte (pcSignedWrite.step.2.cells (complementKey false account 1001)) ⟨4,by decide⟩ = 204 := by
  have unowned : packedOwnsByte pcSignedWrite.next 1001 ⟨4,by decide⟩ = false := by
    change packedOwnsByte (pcLayout.primitiveSnapshot pcFixed pcSignedWrite.nextRaw) _ _ = false
    rw [pcsignedwrite_next]
    decide
  have byte := pcSignedWrite.residual_byte rfl 1001 ⟨4,by decide⟩ unowned
  rw [pcsignedwrite_next] at byte
  exact byte

theorem pc_unsigned_residual_byte : lowByte (pcSignedWrite.step.2.cells (complementKey false account 2000)) ⟨30,by decide⟩ = 205 := by
  have unowned : packedOwnsByte pcSignedWrite.next 2000 ⟨30,by decide⟩ = false := by
    change packedOwnsByte (pcLayout.primitiveSnapshot pcFixed pcSignedWrite.nextRaw) _ _ = false
    rw [pcsignedwrite_next]
    decide
  have byte := pcSignedWrite.residual_byte rfl 2000 ⟨30,by decide⟩ unowned
  rw [pcsignedwrite_next] at byte
  exact byte

theorem pc_bool_dirty_residual_byte : lowByte (pcSignedWrite.step.2.cells (complementKey false account 4000)) ⟨3,by decide⟩ = 2 := by
  have unowned : packedOwnsByte pcSignedWrite.next 4000 ⟨3,by decide⟩ = false := by
    change packedOwnsByte (pcLayout.primitiveSnapshot pcFixed pcSignedWrite.nextRaw) _ _ = false
    rw [pcsignedwrite_next]
    decide
  have byte := pcSignedWrite.residual_byte rfl 4000 ⟨3,by decide⟩ unowned
  rw [pcsignedwrite_next] at byte
  exact byte

theorem pc_bytes_residual_byte : lowByte (pcSignedWrite.step.2.cells (complementKey false account 5000)) ⟨9,by decide⟩ = 244 := by
  have unowned : packedOwnsByte pcSignedWrite.next 5000 ⟨9,by decide⟩ = false := by
    change packedOwnsByte (pcLayout.primitiveSnapshot pcFixed pcSignedWrite.nextRaw) _ _ = false
    rw [pcsignedwrite_next]
    decide
  have byte := pcSignedWrite.residual_byte rfl 5000 ⟨9,by decide⟩ unowned
  rw [pcsignedwrite_next] at byte
  exact byte

theorem pc_address_residual_byte : lowByte (pcSignedWrite.step.2.cells (complementKey false account 6000)) ⟨20,by decide⟩ = 170 := by
  have unowned : packedOwnsByte pcSignedWrite.next 6000 ⟨20,by decide⟩ = false := by
    change packedOwnsByte (pcLayout.primitiveSnapshot pcFixed pcSignedWrite.nextRaw) _ _ = false
    rw [pcsignedwrite_next]
    decide
  have byte := pcSignedWrite.residual_byte rfl 6000 ⟨20,by decide⟩ unowned
  rw [pcsignedwrite_next] at byte
  exact byte

theorem pc_other_account_whole : pcSignedWrite.after.source.world.accounts (⟨2,by decide⟩) = pcState.2.ex.world.accounts (⟨2,by decide⟩) :=
  (pcSignedWrite.account_other (⟨2,by decide⟩) (by decide)).trans ((pcBoolWrite.account_other (⟨2,by decide⟩) (by decide)).trans ((pcBoolRegrow.account_other (⟨2,by decide⟩) (by decide)).trans ((pcBoolZero.account_other (⟨2,by decide⟩) (by decide)).trans ((pcRegrow.account_other (⟨2,by decide⟩) (by decide)).trans ((pcZero.account_other (⟨2,by decide⟩) (by decide)).trans ((pcShrink.account_other (⟨2,by decide⟩) (by decide)).trans ((pcAddressPlan.account_other (⟨2,by decide⟩) (by decide)).trans ((pcBytesPlan.account_other (⟨2,by decide⟩) (by decide)).trans ((pcBool.account_other (⟨2,by decide⟩) (by decide)).trans ((pcWord.account_other (⟨2,by decide⟩) (by decide)).trans ((pcUnsigned.account_other (⟨2,by decide⟩) (by decide)).trans ((pcSigned.account_other (⟨2,by decide⟩) (by decide))))))))))))))

theorem pc_other_bank (q : Roadmap.Word) : pcSignedWrite.step.2.cells (complementKey true account q) = pcResidual.cells (complementKey true account q) :=
  (pcSignedWrite.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcBoolWrite.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcBoolRegrow.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcBoolZero.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcRegrow.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcZero.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcShrink.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcAddressPlan.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcBytesPlan.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcBool.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcWord.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcUnsigned.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide))).trans ((pcSigned.other_key (complementKey true account q) (Or.inl (by change true ≠ false; decide)))))))))))))))

theorem pc_endTx_residual_transient (a : Roadmap.Address) (q : Roadmap.Word) :
    (companionEndTx pcSignedWrite.after).residual.cells (complementKey true a q) = 0 := rfl

theorem pc_noop_original_none : (pcNoop.after.source.world.accounts account).storage.cell (pcPath "marker") = none := by
  rw [pc_noop_whole_store]
  rfl

/-- Separate component checks can BOTH pass while the actual union overlaps.
This synthetic Fixed is deliberately NOT the real Keccak fixture. -/
def pcCollisionFixed : Roadmap.Evm.Fixed where
  keccak _ := 1000
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0

def pcCollisionRaw := saveSlot (saveSlot pcRaw 0 1) 3 1

theorem pc_collision_integer_component_passes : packedSeparationCheck (pcLayout.integerSnapshot pcCollisionFixed pcCollisionRaw) = true := by decide

theorem pc_collision_scalar_component_passes : packedSeparationCheck (pcLayout.scalarFamilySnapshot pcCollisionFixed pcCollisionRaw) = true := by decide

theorem pc_collision_union_rejects : packedSeparationCheck (pcLayout.primitiveSnapshot pcCollisionFixed pcCollisionRaw) = false := by decide

end Solidity.Yul.Views.Controls

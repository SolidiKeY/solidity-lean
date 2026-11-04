import Solidity.Yul.Views.ActualBankedScalar
import Solidity.Yul.Views.ActualScalarSafetyControls

/-! Same-slot persistent/transient actual typed writes use distinct raw maps.
Later refusal preserves exactly the first source/map prefix. Frame static flags
are operation inputs; no runtime frame-mode transition is asserted. -/
namespace Solidity.Yul.Views.Controls

def abPersistent : FiniteCellWrites.Request rootEnv account :=
  ⟨(rootRegistry account)[0]'(by decide),Source.intWrap rootU8 7⟩
def abTransient : FiniteCellWrites.Request rootEnv account := ⟨atCell,Source.intWrap unsigned16 0x1234⟩
def abMaps : SlotView × SlotView := (fun _=>0,atRaw)
def abRun := actualBankedScalarPair TransientSlotControls.frame false abPersistent abTransient abMaps TransientSlotControls.state

theorem ab_same_coordinate : abPersistent.1.slot=abTransient.1.slot := rfl

theorem ab_both_raw : abRun.2.1 0=7 ∧ abRun.2.2 0=0xbeef1234 := ⟨rfl,rfl⟩

theorem ab_both_source : (abRun.1.2.2.ex.world.accounts account).storage.read abPersistent.1.path=
    some (Source.intWrap rootU8 7) ∧ (abRun.1.2.2.ex.transient.cells account).read atCell.path=
    some (Source.intWrap unsigned16 0x1234) := ⟨rfl,rfl⟩

def abLate := actualBankedScalarPair TransientSlotControls.frame true abPersistent abTransient abMaps TransientSlotControls.state

theorem ab_late_refusal : abLate.1.1=.error (.revert []) ∧ abLate.2.1 0=7 ∧ abLate.2.2 0=0xbeef0000 :=
  ⟨rfl,rfl,rfl⟩

theorem ab_late_source_prefix : (abLate.1.2.2.ex.world.accounts account).storage.read abPersistent.1.path=
    some (Source.intWrap rootU8 7) ∧ (abLate.1.2.2.ex.transient.cells account).read atCell.path=
    some (Source.intWrap unsigned16 0) := ⟨rfl,rfl⟩

theorem ab_first_refusal :
    actualBankedScalarPair {TransientSlotControls.frame with static:=true} false abPersistent abTransient
      abMaps TransientSlotControls.state=((.error (.revert []),TransientSlotControls.state),abMaps) := rfl

theorem ab_safe : Source.MemOK rootEnv TransientSlotControls.state.2.heap.ty abRun.1.2 :=
  actualBankedScalarPair_MemOK TransientSlotControls.frame false abPersistent abTransient abMaps TransientSlotControls.state _ safety_transient_initial

theorem ab_late_safe : Source.MemOK rootEnv TransientSlotControls.state.2.heap.ty abLate.1.2 :=
  actualBankedScalarPair_MemOK TransientSlotControls.frame true abPersistent abTransient abMaps TransientSlotControls.state _ safety_transient_initial

theorem ab_wrong_shared_raw : abRun.2.1 0≠abRun.2.2 0 := by decide
end Solidity.Yul.Views.Controls

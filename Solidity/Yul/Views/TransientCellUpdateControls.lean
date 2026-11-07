import Solidity.Yul.Views.TransientCellUpdate
import Solidity.Yul.Views.TransientSlotControls

/-! Actual declared transient uint16 after nontrivial persistent/transient
prefixes. Typed writes retain padding and unknown slot99, with real static
refusal, rollback and transaction reset. No transient aggregates are admitted. -/
namespace Solidity.Yul.Views.Controls
open TransientSlotControls

def tcuPath := (rootTempRegistry account).head (by
  intro empty
  have count := congrArg List.length empty
  change 1=0 at count
  contradiction)
theorem tcu_member : tcuPath ∈ rootTempRegistry account := by
  change tcuPath ∈ tcuPath::[]
  exact List.mem_cons_self

def tcuValue : Source.Val rootEnv.layout (rootEnv.cellTy tcuPath.path) := Source.intWrap unsigned16 7
def tcuRaw : SlotView := fun slot => if slot=0 then rawB else if slot=99 then rawMax else 0xbeef0000
def tcuRun := (Source.setCell frame tcuPath.path (some tcuValue)).run child.1.2

theorem tcu_before : finiteView (rootTempRegistry account) (child.1.2.2.ex.transient.cells account) tcuRaw := by
  intro c member
  change c ∈ [tcuPath] at member
  have same := List.mem_singleton.mp member
  subst c
  unfold scalarPathView
  decide

theorem tcu_reencode : finiteEncode (rootTempRegistry account) (tcuRun.2.2.ex.transient.cells account)
    (packedMask (rootTempRegistry account) tcuRaw)=some (PackedCellUpdate.raw tcuPath tcuValue tcuRaw) :=
  TransientCellUpdate.reencode frame child.1.2 _ tcuPath tcu_member rootTempChecked.separated tcuRaw tcu_before tcuValue rfl rfl

theorem tcu_padding : PackedCellUpdate.raw tcuPath tcuValue tcuRaw 0=0xb6b60007 := by decide

theorem tcu_unknown : PackedCellUpdate.raw tcuPath tcuValue tcuRaw 99=rawMax := by
  unfold PackedCellUpdate.raw
  rw [patchScalarSlot,find_saveSlot_other]
  · rfl
  · decide

theorem tcu_persistent : tcuRun.2.2.ex.world=child.1.2.2.ex.world :=
  TransientCellUpdate.persistent frame child.1.2 tcuPath tcuValue rfl rfl

theorem tcu_read : (Source.readLoc frame (.stor (τ:=.int unsigned16) (rootPath "temp"))).run tcuRun.2=
    (.ok (Source.intWrap unsigned16 7),tcuRun.2) := rfl

theorem tcu_other_account : tcuRun.2.2.ex.transient.cells (2:Roadmap.Address)=
    child.1.2.2.ex.transient.cells (2:Roadmap.Address) := rfl

theorem tcu_static : (Source.setCell {frame with static:=true} tcuPath.path (some tcuValue)).run child.1.2=
    (.error (.revert []),child.1.2) := TransientCellUpdate.static _ _ _ _ rfl rfl

theorem tcu_rollback : companionRollback (companionEnter childCore frame.this frame.sender frame.value frame.cd frame.static)
    ⟨tcuRun.2.2.ex,child.2⟩=childCore :=
  TransientCellUpdate.rollback frame child.1.2 tcuPath tcuValue child.2 rfl rfl

theorem tcu_reset : (companionEndTx (⟨tcuRun.2.2.ex,child.2⟩ : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership)).source.transient=
    Source.Transient.empty ∧
    (companionEndTx (⟨tcuRun.2.2.ex,child.2⟩ : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership)).residual.cells
      (complementKey true account 99)=0 :=
  ⟨rfl,residualEndTx_transient _ _ rfl⟩
end Solidity.Yul.Views.Controls

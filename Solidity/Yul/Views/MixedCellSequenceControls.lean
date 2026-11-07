import Solidity.Yul.Views.MixedCellSequence
import Solidity.Yul.Views.TransientCellUpdateControls

/-! One actual Source bind writes both banks at slot0 after a nontrivial prefix.
Late static refusal preserves the persistent prefix and old transient payload. -/
namespace Solidity.Yul.Views.Controls
open TransientSlotControls

def mcsPaths := selectedSlotPaths (rootRegistry account) 0
def mcsPath := (rootRegistry account).head (by
  intro empty
  have count := congrArg List.length empty
  change 10=0 at count
  contradiction)
def mcsValue : Source.Val rootEnv.layout (rootEnv.cellTy mcsPath.path) := Source.intWrap rootU8 2
def mcsRaw : SlotView := fun _ => 777

theorem mcs_member : mcsPath ∈ mcsPaths := by
  change mcsPath ∈ mcsPath::_
  exact List.mem_cons_self

theorem mcs_view : finiteView mcsPaths (child.1.2.2.ex.world.accounts account).storage mcsRaw := by
  intro c member
  change c ∈ [mcsPath,_] at member
  rcases List.mem_cons.mp member with same | later
  · subst c; unfold scalarPathView; decide
  · have same := List.mem_singleton.mp later
    subst c; unfold scalarPathView; decide

def mcsRun := (MixedCellSequence.program frame mcsPath tcuPath mcsValue tcuValue false false).run child.1.2
def mcsHalt := (MixedCellSequence.program frame mcsPath tcuPath mcsValue tcuValue false true).run child.1.2

theorem mcs_both_maps :
    finiteEncode mcsPaths (mcsRun.2.2.ex.world.accounts account).storage (packedMask mcsPaths mcsRaw)=
      some (PackedCellUpdate.raw mcsPath mcsValue mcsRaw) ∧
    finiteEncode (rootTempRegistry account) (mcsRun.2.2.ex.transient.cells account) (packedMask (rootTempRegistry account) tcuRaw)=
      some (PackedCellUpdate.raw tcuPath tcuValue tcuRaw) :=
  MixedCellSequence.agreement frame child.1.2 mcsPaths _ mcsPath tcuPath mcsValue tcuValue mcs_member tcu_member
    (selectedSlotPaths_separated _ _ root_separation) rootTempChecked.separated mcsRaw tcuRaw mcs_view tcu_before rfl rfl

theorem mcs_same_slot : mcsPath.slot=tcuPath.slot ∧ mcsPath.slot=0 := ⟨rfl,rfl⟩

theorem mcs_raw_words : PackedCellUpdate.raw mcsPath mcsValue mcsRaw 0=770 ∧
    PackedCellUpdate.raw tcuPath tcuValue tcuRaw 0=0xb6b60007 := ⟨by decide,tcu_padding⟩

theorem mcs_reads :
    (Source.readLoc frame (.stor (τ:=.int rootU8) (rootPath "a"))).run mcsRun.2=(.ok (Source.intWrap rootU8 2),mcsRun.2) ∧
    (Source.readLoc frame (.stor (τ:=.int unsigned16) (rootPath "temp"))).run mcsRun.2=(.ok (Source.intWrap unsigned16 7),mcsRun.2) :=
  ⟨rfl,rfl⟩

theorem mcs_late_prefix : mcsHalt.1=.error (.revert []) ∧
    (Source.readLoc frame (.stor (τ:=.int rootU8) (rootPath "a"))).run mcsHalt.2=(.ok (Source.intWrap rootU8 2),mcsHalt.2) ∧
    (Source.readLoc frame (.stor (τ:=.int unsigned16) (rootPath "temp"))).run mcsHalt.2=(.ok (Source.intWrap unsigned16 0xabcd),mcsHalt.2) :=
  ⟨rfl,rfl,rfl⟩

theorem mcs_first_static : (MixedCellSequence.program frame mcsPath tcuPath mcsValue tcuValue true false).run child.1.2=
    (.error (.revert []),child.1.2) := MixedCellSequence.first_static _ _ _ _ _ _ rfl false
theorem mcs_reset :
    (Source.readLoc frame (.stor (τ:=.int rootU8) (rootPath "a"))).run
      (mcsRun.2.1,{mcsRun.2.2 with ex:=mcsRun.2.2.ex.endTx})=
      (.ok (Source.intWrap rootU8 2),(mcsRun.2.1,{mcsRun.2.2 with ex:=mcsRun.2.2.ex.endTx})) ∧
    (mcsRun.2.2.ex.endTx.transient.cells account).read (rootPath "temp")=some (Source.intWrap unsigned16 0) ∧
    mcsRun.2.2.ex.endTx.journal=[] := ⟨rfl,rfl,rfl⟩
end Solidity.Yul.Views.Controls

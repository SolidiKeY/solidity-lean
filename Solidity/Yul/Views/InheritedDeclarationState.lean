import Solidity.Yul.Views.InheritedDeclarationControls

namespace Solidity.Yul.Views.Controls

def diamondRaw0 : Roadmap.Word := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff11,by decide⟩
def diamondRaw1 : Roadmap.Word := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa01,by decide⟩
def diamondRaw2 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222201,by decide⟩
def diamondRaw3 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222301,by decide⟩
def diamondRaw4 : Roadmap.Word := ⟨0xee00000000000000000000000000000000000000000000000000000000009876,by decide⟩
def diamondRaw5 : Roadmap.Word := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc3456,by decide⟩
def diamondRaw6 : Roadmap.Word := ⟨0x0000000000000000000000000000000000000000000000000000000000000037,by decide⟩
/-- Residual seed: owned bytes are masked out, so initial logical defaults
replace them; unowned bytes in observed slots0–7 match the independent constructor snapshot.
Slots8+ are arbitrary kernel residual0xee, not fresh EVM constructor zeros. -/
def diamondInitialRaw (q : Roadmap.Word) : Roadmap.Word :=
  if q = 0 then diamondRaw0 else if q = 1 then diamondRaw1 else if q = 2 then diamondRaw2 else if q = 3 then diamondRaw3 else if q = 4 then diamondRaw4 else if q = 5 then diamondRaw5 else if q = 6 then diamondRaw6 else if q = 7 then 999 else ⟨0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,by decide⟩
def diamondInitialStore : Source.Storage diamondEnv.layout (diamondEnv.lay account) :=
  Source.Storage.empty.write (diamondPath "marker") (.int 55 (by decide))
def diamondResidual := initialPackedComplement diamondRegistry diamondTempRegistry (fun k => if k.transient then 0 else diamondInitialRaw k.slot)
def diamondState : Source.EMState diamondEnv [] :=
  ⟨.nil,⟨⟨⟨fun a => if a = account then
    {Source.Account.empty (D := diamondEnv.layout) (diamondEnv.lay account) with storage := diamondInitialStore}
    else Source.Account.empty (D := diamondEnv.layout) (diamondEnv.lay a)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩

theorem diamond_initial_MemOK : Source.MemOK diamondEnv diamondState.2.heap.ty diamondState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem diamond_ready0 : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 0 diamondRaw0).isSome := by decide
def diamondPlan0 := (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 0 diamondRaw0).get diamond_ready0
def diamondFrame0 := packedSourceStep packedStepFrame diamondPlan0 diamondState diamondResidual

theorem diamond_ready1 : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 1 diamondRaw1).isSome := by decide
def diamondPlan1 := (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 1 diamondRaw1).get diamond_ready1
def diamondFrame1 := packedSourceStep packedStepFrame diamondPlan1 diamondFrame0.1.2 diamondFrame0.2

theorem diamond_ready2 : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 2 diamondRaw2).isSome := by decide
def diamondPlan2 := (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 2 diamondRaw2).get diamond_ready2
def diamondFrame2 := packedSourceStep packedStepFrame diamondPlan2 diamondFrame1.1.2 diamondFrame1.2

theorem diamond_ready3 : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 3 diamondRaw3).isSome := by decide
def diamondPlan3 := (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 3 diamondRaw3).get diamond_ready3
def diamondFrame3 := packedSourceStep packedStepFrame diamondPlan3 diamondFrame2.1.2 diamondFrame2.2

theorem diamond_ready4 : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 4 diamondRaw4).isSome := by decide
def diamondPlan4 := (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 4 diamondRaw4).get diamond_ready4
def diamondFrame4 := packedSourceStep packedStepFrame diamondPlan4 diamondFrame3.1.2 diamondFrame3.2

theorem diamond_ready5 : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 5 diamondRaw5).isSome := by decide
def diamondPlan5 := (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 5 diamondRaw5).get diamond_ready5
def diamondFrame5 := packedSourceStep packedStepFrame diamondPlan5 diamondFrame4.1.2 diamondFrame4.2

theorem diamond_ready6 : (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 6 diamondRaw6).isSome := by decide
def diamondPlan6 := (preparePackedFrame (ps := diamondRegistry) (ts := diamondTempRegistry) packedStepFrame false 6 diamondRaw6).get diamond_ready6
def diamondFrame6 := packedSourceStep packedStepFrame diamondPlan6 diamondFrame5.1.2 diamondFrame5.2

def diamondItemPath (i j : Nat) : Source.SPath := ⟨diamondName "items",[.index i,.field j]⟩

theorem diamond_max248_value : (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff : Nat) = 2^248-1 := by decide

theorem diamond_actual_selected_reads :
    (diamondFrame6.1.2.2.ex.world.accounts account).storage.read (diamondPath "a") = some (.int 17 (by decide)) ∧
    (diamondFrame6.1.2.2.ex.world.accounts account).storage.read (diamondPath "b") = some (.int 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (by decide)) ∧
    (diamondFrame6.1.2.2.ex.world.accounts account).storage.read (diamondPath "c") = some (.bool true) ∧
    (diamondFrame6.1.2.2.ex.world.accounts account).storage.read (diamondItemPath 1 1) = some (.int 0x2223 (by decide)) ∧
    (diamondFrame6.1.2.2.ex.world.accounts account).storage.read (diamondPath "e") = some (.int 0x9876 (by decide)) ∧
    (diamondFrame6.1.2.2.ex.world.accounts account).storage.read (diamondPath "f") = some (.int 0x3456 (by decide)) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem diamond_every_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK diamondEnv H diamondState) : Source.MemOK diamondEnv H diamondFrame6.1.2 :=
  (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ ok)))))))

theorem diamond_written_MemOK : Source.MemOK diamondEnv diamondState.2.heap.ty diamondFrame6.1.2 := diamond_every_H_MemOK _ diamond_initial_MemOK

end Solidity.Yul.Views.Controls

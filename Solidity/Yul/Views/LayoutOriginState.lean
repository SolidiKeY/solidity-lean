import Solidity.Yul.Views.LayoutOriginControls

namespace Solidity.Yul.Views.Controls

def originRaw0 : Roadmap.Word := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff11,by decide⟩
def originRaw1 : Roadmap.Word := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa01,by decide⟩
def originRaw2 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222201,by decide⟩
def originRaw3 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222301,by decide⟩
def originRaw4 : Roadmap.Word := ⟨0xee00000000000000000000000000000000000000000000000000000000009876,by decide⟩
def originRaw5 : Roadmap.Word := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc3456,by decide⟩
def originRaw6 : Roadmap.Word := ⟨0x0000000000000000000000000000000000000000000000000000000000000037,by decide⟩
/-- Residual seed: owned bytes are masked out, so initial logical defaults
replace them; unowned bytes in observed slots42–49 match the independent constructor snapshot.
Slots outside42–49 are arbitrary kernel residual0xee, not fresh EVM constructor zeros. -/
def originInitialRaw (q : Roadmap.Word) : Roadmap.Word :=
  if q = 42 then originRaw0 else if q = 43 then originRaw1 else if q = 44 then originRaw2 else if q = 45 then originRaw3 else if q = 46 then originRaw4 else if q = 47 then originRaw5 else if q = 48 then originRaw6 else if q = 49 then 999 else ⟨0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,by decide⟩
def originInitialStore : Source.Storage originEnv.layout (originEnv.lay account) :=
  Source.Storage.empty.write (originPath "marker") (.int 55 (by decide))
def originResidual := initialPackedComplement originRegistry originTempRegistry (fun k => if k.transient then 0 else originInitialRaw k.slot)
def originState : Source.EMState originEnv [] :=
  ⟨.nil,⟨⟨⟨fun a => if a = account then
    {Source.Account.empty (D := originEnv.layout) (originEnv.lay account) with storage := originInitialStore}
    else Source.Account.empty (D := originEnv.layout) (originEnv.lay a)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩

theorem origin_initial_MemOK : Source.MemOK originEnv originState.2.heap.ty originState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem origin_ready0 : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 42 originRaw0).isSome := by decide
def originPlan0 := (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 42 originRaw0).get origin_ready0
def originFrame0 := packedSourceStep packedStepFrame originPlan0 originState originResidual

theorem origin_ready1 : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 43 originRaw1).isSome := by decide
def originPlan1 := (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 43 originRaw1).get origin_ready1
def originFrame1 := packedSourceStep packedStepFrame originPlan1 originFrame0.1.2 originFrame0.2

theorem origin_ready2 : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 44 originRaw2).isSome := by decide
def originPlan2 := (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 44 originRaw2).get origin_ready2
def originFrame2 := packedSourceStep packedStepFrame originPlan2 originFrame1.1.2 originFrame1.2

theorem origin_ready3 : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 45 originRaw3).isSome := by decide
def originPlan3 := (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 45 originRaw3).get origin_ready3
def originFrame3 := packedSourceStep packedStepFrame originPlan3 originFrame2.1.2 originFrame2.2

theorem origin_ready4 : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 46 originRaw4).isSome := by decide
def originPlan4 := (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 46 originRaw4).get origin_ready4
def originFrame4 := packedSourceStep packedStepFrame originPlan4 originFrame3.1.2 originFrame3.2

theorem origin_ready5 : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 47 originRaw5).isSome := by decide
def originPlan5 := (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 47 originRaw5).get origin_ready5
def originFrame5 := packedSourceStep packedStepFrame originPlan5 originFrame4.1.2 originFrame4.2

theorem origin_ready6 : (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 48 originRaw6).isSome := by decide
def originPlan6 := (preparePackedFrame (ps := originRegistry) (ts := originTempRegistry) packedStepFrame false 48 originRaw6).get origin_ready6
def originFrame6 := packedSourceStep packedStepFrame originPlan6 originFrame5.1.2 originFrame5.2

def originItemPath (i j : Nat) : Source.SPath := ⟨originName "items",[.index i,.field j]⟩

theorem origin_max248_value : (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff : Nat) = 2^248-1 := by decide

theorem origin_actual_selected_reads :
    (originFrame6.1.2.2.ex.world.accounts account).storage.read (originPath "a") = some (.int 17 (by decide)) ∧
    (originFrame6.1.2.2.ex.world.accounts account).storage.read (originPath "b") = some (.int 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (by decide)) ∧
    (originFrame6.1.2.2.ex.world.accounts account).storage.read (originPath "c") = some (.bool true) ∧
    (originFrame6.1.2.2.ex.world.accounts account).storage.read (originItemPath 1 1) = some (.int 0x2223 (by decide)) ∧
    (originFrame6.1.2.2.ex.world.accounts account).storage.read (originPath "e") = some (.int 0x9876 (by decide)) ∧
    (originFrame6.1.2.2.ex.world.accounts account).storage.read (originPath "f") = some (.int 0x3456 (by decide)) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem origin_every_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK originEnv H originState) : Source.MemOK originEnv H originFrame6.1.2 :=
  (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ ok)))))))

theorem origin_written_MemOK : Source.MemOK originEnv originState.2.heap.ty originFrame6.1.2 := origin_every_H_MemOK _ origin_initial_MemOK

end Solidity.Yul.Views.Controls

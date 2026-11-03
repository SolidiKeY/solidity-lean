import Solidity.Yul.Views.RootDeclarationControls

namespace Solidity.Yul.Views.Controls

def rootRaw0 : Roadmap.Word := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff11,by decide⟩
def rootRaw1 : Roadmap.Word := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa01,by decide⟩
def rootRaw2 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222201,by decide⟩
def rootRaw3 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222301,by decide⟩
def rootRaw4 : Roadmap.Word := ⟨0xee00000000000000000000000000000000000000000000000000000000009876,by decide⟩
def rootRaw5 : Roadmap.Word := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc3456,by decide⟩
def rootRaw6 : Roadmap.Word := ⟨0x0000000000000000000000000000000000000000000000000000000000000037,by decide⟩
/-- Residual seed: owned bytes are masked out, so initial logical defaults
replace them; unowned bytes match the independent constructor snapshot. -/
def rootInitialRaw (q : Roadmap.Word) : Roadmap.Word :=
  if q = 0 then rootRaw0 else if q = 1 then rootRaw1 else if q = 2 then rootRaw2 else if q = 3 then rootRaw3 else if q = 4 then rootRaw4 else if q = 5 then rootRaw5 else if q = 6 then rootRaw6 else if q = 7 then 999 else ⟨0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,by decide⟩
def rootInitialStore : Source.Storage rootEnv.layout (rootEnv.lay account) :=
  Source.Storage.empty.write (rootPath "marker") (.int 55 (by decide))
def rootResidual := initialPackedComplement rootRegistry rootTempRegistry (fun k => if k.transient then 0 else rootInitialRaw k.slot)
def rootState : Source.EMState rootEnv [] :=
  ⟨.nil,⟨⟨⟨fun a => if a = account then
    {Source.Account.empty (D := rootEnv.layout) (rootEnv.lay account) with storage := rootInitialStore}
    else Source.Account.empty (D := rootEnv.layout) (rootEnv.lay a)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩

theorem root_initial_MemOK : Source.MemOK rootEnv rootState.2.heap.ty rootState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem root_ready0 : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 0 rootRaw0).isSome := by decide
def rootPlan0 := (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 0 rootRaw0).get root_ready0
def rootFrame0 := packedSourceStep packedStepFrame rootPlan0 rootState rootResidual

theorem root_ready1 : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 1 rootRaw1).isSome := by decide
def rootPlan1 := (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 1 rootRaw1).get root_ready1
def rootFrame1 := packedSourceStep packedStepFrame rootPlan1 rootFrame0.1.2 rootFrame0.2

theorem root_ready2 : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 2 rootRaw2).isSome := by decide
def rootPlan2 := (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 2 rootRaw2).get root_ready2
def rootFrame2 := packedSourceStep packedStepFrame rootPlan2 rootFrame1.1.2 rootFrame1.2

theorem root_ready3 : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 3 rootRaw3).isSome := by decide
def rootPlan3 := (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 3 rootRaw3).get root_ready3
def rootFrame3 := packedSourceStep packedStepFrame rootPlan3 rootFrame2.1.2 rootFrame2.2

theorem root_ready4 : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 4 rootRaw4).isSome := by decide
def rootPlan4 := (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 4 rootRaw4).get root_ready4
def rootFrame4 := packedSourceStep packedStepFrame rootPlan4 rootFrame3.1.2 rootFrame3.2

theorem root_ready5 : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 5 rootRaw5).isSome := by decide
def rootPlan5 := (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 5 rootRaw5).get root_ready5
def rootFrame5 := packedSourceStep packedStepFrame rootPlan5 rootFrame4.1.2 rootFrame4.2

theorem root_ready6 : (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 6 rootRaw6).isSome := by decide
def rootPlan6 := (preparePackedFrame (ps := rootRegistry) (ts := rootTempRegistry) packedStepFrame false 6 rootRaw6).get root_ready6
def rootFrame6 := packedSourceStep packedStepFrame rootPlan6 rootFrame5.1.2 rootFrame5.2

def rootItemPath (i j : Nat) : Source.SPath := ⟨rootName "items",[.index i,.field j]⟩

theorem root_max248_value : (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff : Nat) = 2^248-1 := by decide

theorem root_actual_selected_reads :
    (rootFrame6.1.2.2.ex.world.accounts account).storage.read (rootPath "a") = some (.int 17 (by decide)) ∧
    (rootFrame6.1.2.2.ex.world.accounts account).storage.read (rootPath "b") = some (.int 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (by decide)) ∧
    (rootFrame6.1.2.2.ex.world.accounts account).storage.read (rootPath "c") = some (.bool true) ∧
    (rootFrame6.1.2.2.ex.world.accounts account).storage.read (rootItemPath 1 1) = some (.int 0x2223 (by decide)) ∧
    (rootFrame6.1.2.2.ex.world.accounts account).storage.read (rootPath "e") = some (.int 0x9876 (by decide)) ∧
    (rootFrame6.1.2.2.ex.world.accounts account).storage.read (rootPath "f") = some (.int 0x3456 (by decide)) := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem root_every_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK rootEnv H rootState) : Source.MemOK rootEnv H rootFrame6.1.2 :=
  (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ ok)))))))

theorem root_written_MemOK : Source.MemOK rootEnv rootState.2.heap.ty rootFrame6.1.2 := root_every_H_MemOK _ root_initial_MemOK

end Solidity.Yul.Views.Controls

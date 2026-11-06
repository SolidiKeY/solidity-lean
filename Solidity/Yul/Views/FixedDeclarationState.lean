import Solidity.Yul.Views.FixedDeclarationControls

namespace Solidity.Yul.Views.Controls

def recursiveRaw8 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222201,by decide⟩
def recursiveRaw9 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222301,by decide⟩
def recursiveRaw10 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222401,by decide⟩
def recursiveRaw11 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb222501,by decide⟩
def recursiveRaw12 : Roadmap.Word := ⟨0x0000000000000000000000000000000200000000000000000000000000000001,by decide⟩
def recursiveRaw13 : Roadmap.Word := ⟨0xdddddddddddddddddddddddddddddddd00000000000000000000000000000003,by decide⟩
def recursiveInitialRaw (q : Roadmap.Word) : Roadmap.Word := if q = 14 then 55 else ⟨0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,by decide⟩
def recursiveResidual := initialPackedComplement recursiveRegistry recursiveRegistry (fun k => recursiveInitialRaw k.slot)
def recursiveState : Source.EMState recursiveDeclEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := recursiveDeclEnv.layout) (recursiveDeclEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩

theorem recursive_initial_MemOK : Source.MemOK recursiveDeclEnv recursiveState.2.heap.ty recursiveState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem recursive_ready8 : (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 8 recursiveRaw8).isSome := by decide
def recursivePlan8 := (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 8 recursiveRaw8).get recursive_ready8
def recursiveFrame8 := packedSourceStep packedStepFrame recursivePlan8 recursiveState recursiveResidual

theorem recursive_ready9 : (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 9 recursiveRaw9).isSome := by decide
def recursivePlan9 := (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 9 recursiveRaw9).get recursive_ready9
def recursiveFrame9 := packedSourceStep packedStepFrame recursivePlan9 recursiveFrame8.1.2 recursiveFrame8.2

theorem recursive_ready10 : (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 10 recursiveRaw10).isSome := by decide
def recursivePlan10 := (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 10 recursiveRaw10).get recursive_ready10
def recursiveFrame10 := packedSourceStep packedStepFrame recursivePlan10 recursiveFrame9.1.2 recursiveFrame9.2

theorem recursive_ready11 : (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 11 recursiveRaw11).isSome := by decide
def recursivePlan11 := (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 11 recursiveRaw11).get recursive_ready11
def recursiveFrame11 := packedSourceStep packedStepFrame recursivePlan11 recursiveFrame10.1.2 recursiveFrame10.2

theorem recursive_ready12 : (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 12 recursiveRaw12).isSome := by decide
def recursivePlan12 := (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 12 recursiveRaw12).get recursive_ready12
def recursiveFrame12 := packedSourceStep packedStepFrame recursivePlan12 recursiveFrame11.1.2 recursiveFrame11.2

theorem recursive_ready13 : (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 13 recursiveRaw13).isSome := by decide
def recursivePlan13 := (preparePackedFrame (ps := recursiveRegistry) (ts := recursiveRegistry)
    packedStepFrame false 13 recursiveRaw13).get recursive_ready13
def recursiveFrame13 := packedSourceStep packedStepFrame recursivePlan13 recursiveFrame12.1.2 recursiveFrame12.2

theorem recursive_actual_reads :
    (recursiveFrame13.1.2.2.ex.world.accounts account).storage.read (recursiveGridPath 0 0 0) = some (.bool true) ∧
    (recursiveFrame13.1.2.2.ex.world.accounts account).storage.read (recursiveGridPath 1 1 1) = some (.int 0x2225 (by decide)) ∧
    (recursiveFrame13.1.2.2.ex.world.accounts account).storage.read (recursiveValuePath 0) = some (.int 1 (by decide)) ∧
    (recursiveFrame13.1.2.2.ex.world.accounts account).storage.read (recursiveValuePath 2) = some (.int 3 (by decide)) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem recursive_every_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK recursiveDeclEnv H recursiveState) :
    Source.MemOK recursiveDeclEnv H recursiveFrame13.1.2 :=
  (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ ok))))))

theorem recursive_written_MemOK : Source.MemOK recursiveDeclEnv recursiveState.2.heap.ty recursiveFrame13.1.2 :=
  recursive_every_H_MemOK _ recursive_initial_MemOK

end Solidity.Yul.Views.Controls

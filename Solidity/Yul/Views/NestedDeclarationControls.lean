import Solidity.Yul.Views.NestedDeclarationSource
import Solidity.Yul.Views.DeclarationBoundaryControls

namespace Solidity.Yul.Views.Controls

def nestedDeclCert := (prepareNestedDeclaration declBoundary account).toOption.get (by decide)
def nestedDeclRegistry (a : Roadmap.Address) : List (ScalarPath declBoundaryEnv.layout (declBoundaryEnv.lay a)) := nestedDeclCert.registrations

theorem nested_decl_coordinates (a : Roadmap.Address) :
    (nestedDeclRegistry a).map (fun c => (c.slot.val,c.field.offset,c.field.width)) =
      [(4,0,3),(4,3,3),(4,6,3),(4,9,3),(4,12,3),(4,15,3),(4,18,3),(4,21,3),(4,24,3),(4,27,3),
       (5,0,3),(5,3,3),(6,0,1),(6,1,2),(6,3,3),(6,6,20)] := rfl

theorem nested_decl_separated (a : Roadmap.Address) : finiteSeparated (nestedDeclRegistry a) := nestedDeclCert.separated

theorem nested_decl_paths (a : Roadmap.Address) :
    (nestedDeclRegistry a).map ScalarPath.path =
      (List.range' 0 12).map (nestedArrayPath declBoundaryRoot) ++
      (List.range' 0 4).map (nestedStructPath declBoundaryRoot) := nestedDeclCert.paths

def nestedRaw4 : Roadmap.Word := ⟨0xcccc00000a000009000008000007000006000005000004000003000002000001,by decide⟩
def nestedRaw5 : Roadmap.Word := ⟨0xdddddddddddddddddddddddddddddddddddddddddddddddddddd00000c00000b,by decide⟩
def nestedRaw6 : Roadmap.Word := ⟨0xbbbbbbbbbbbb0000000000000000000000000000000000000042123456222201,by decide⟩

def nestedInitialRaw (q : Roadmap.Word) : Roadmap.Word := if q = 7 then 55 else ⟨0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,by decide⟩
def nestedDeclResidual := initialPackedComplement nestedDeclRegistry nestedDeclRegistry (fun k => nestedInitialRaw k.slot)
def nestedDeclState : Source.EMState declBoundaryEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := declBoundaryEnv.layout) (declBoundaryEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩

theorem nested_decl_initial_MemOK : Source.MemOK declBoundaryEnv nestedDeclState.2.heap.ty nestedDeclState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem nested_slot4_ready : (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry)
    packedStepFrame false 4 nestedRaw4).isSome := by decide

theorem nested_slot5_ready : (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry)
    packedStepFrame false 5 nestedRaw5).isSome := by decide

theorem nested_slot6_ready : (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry)
    packedStepFrame false 6 nestedRaw6).isSome := by decide

def nestedPlan4 := (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry) packedStepFrame false 4 nestedRaw4).get nested_slot4_ready
def nestedPlan5 := (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry) packedStepFrame false 5 nestedRaw5).get nested_slot5_ready
def nestedPlan6 := (preparePackedFrame (ps := nestedDeclRegistry) (ts := nestedDeclRegistry) packedStepFrame false 6 nestedRaw6).get nested_slot6_ready

def nestedFrame4 := packedSourceStep packedStepFrame nestedPlan4 nestedDeclState nestedDeclResidual
def nestedFrame5 := packedSourceStep packedStepFrame nestedPlan5 nestedFrame4.1.2 nestedFrame4.2
def nestedFrame6 := packedSourceStep packedStepFrame nestedPlan6 nestedFrame5.1.2 nestedFrame5.2

theorem nested_decl_source_reads :
    (nestedFrame6.1.2.2.ex.world.accounts account).storage.read (nestedArrayPath declBoundaryRoot 0) = some (.int 1 (by decide)) ∧
    (nestedFrame6.1.2.2.ex.world.accounts account).storage.read (nestedArrayPath declBoundaryRoot 9) = some (.int 10 (by decide)) ∧
    (nestedFrame6.1.2.2.ex.world.accounts account).storage.read (nestedArrayPath declBoundaryRoot 10) = some (.int 11 (by decide)) ∧
    (nestedFrame6.1.2.2.ex.world.accounts account).storage.read (nestedArrayPath declBoundaryRoot 11) = some (.int 12 (by decide)) ∧
    (nestedFrame6.1.2.2.ex.world.accounts account).storage.read (nestedStructPath declBoundaryRoot 0) = some (.bool true) ∧
    (nestedFrame6.1.2.2.ex.world.accounts account).storage.read (nestedStructPath declBoundaryRoot 1) = some (.int 0x2222 (by decide)) ∧
    (nestedFrame6.1.2.2.ex.world.accounts account).storage.read (nestedStructPath declBoundaryRoot 2) = some (.fixedBytes [0x12,0x34,0x56] rfl) ∧
    (nestedFrame6.1.2.2.ex.world.accounts account).storage.read (nestedStructPath declBoundaryRoot 3) = some (.address 0x42) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem nested_decl_every_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK declBoundaryEnv H nestedDeclState) :
    Source.MemOK declBoundaryEnv H nestedFrame6.1.2 :=
  packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ (packedSourceStep_MemOK H _ _ _ _ ok))

theorem nested_decl_written_MemOK : Source.MemOK declBoundaryEnv nestedDeclState.2.heap.ty nestedFrame6.1.2 :=
  nested_decl_every_H_MemOK _ nested_decl_initial_MemOK

end Solidity.Yul.Views.Controls

import Solidity.Yul.Views.DeclarationSeparation
import Solidity.Yul.Views.PackedResidualTypedSourceControls

namespace Solidity.Yul.Views.Controls

def declPackingEnv : Source.Env := ⟨[
  ⟨.struct,"PackedDecl",none,true,.struct "PackedDecl" (.structMember (.elem .bool) "flag")
    (.cons (.structMember (.elem (.int false 16 (by decide))) "small")
    (.cons (.structMember (.elem (.fixedBytes 3 (by decide))) "data")
    (.cons (.structMember (.elem .address) "who")
    (.cons (.structMember (.elem (.int false 256 (by decide))) "wide")
    (.cons (.structMember (.elem (.int false 8 (by decide))) "one")
    (.cons (.structMember (.elem (.fixedBytes 31 (by decide))) "full")
    (.cons (.structMember (.elem (.int false 16 (by decide))) "after") .nil)))))))⟩,
  ⟨.stateVar,"state",none,true,.stateVar (.userType ⟨"PackedDecl",[]⟩) none none none false "state" .none⟩]⟩
def declPackingRoot : Source.DeclName := ⟨none,"state"⟩
def declPackingCert (a : Roadmap.Address) :=
  (preparePackedDeclaration declPackingEnv declPackingRoot a 0).toOption.get (by rfl)
def declPackingRegistry (a : Roadmap.Address) := (declPackingCert a).registrations

theorem decl_packing_coordinates (a : Roadmap.Address) :
    (declPackingRegistry a).map (fun c => (c.slot.val,c.field.offset,c.field.width)) =
      [(0,0,1),(0,1,2),(0,3,3),(0,6,20),(1,0,32),(2,0,1),(2,1,31),(3,0,2)] := rfl

theorem decl_packing_separated (a : Roadmap.Address) : finiteSeparated (declPackingRegistry a) := (declPackingCert a).separated

theorem decl_packing_end (a : Roadmap.Address) : (declPackingCert a).endByte = 98 ∧ (declPackingCert a).nextSlot = 4 := ⟨rfl,by change (98+31)/32*32/32 = 4; decide⟩

theorem decl_packing_skipped_padding (a : Roadmap.Address) :
    ¬ ∃ c ∈ declPackingRegistry a, declarationStart c ≤ 26 ∧ 26 < declarationEnd c := by
  intro ⟨c,member,lo,hi⟩
  have positions := List.mem_map_of_mem (f := fun c : ScalarPath declPackingEnv.layout (declPackingEnv.lay a) =>
    (c.slot.val,c.field.offset,c.field.width)) member
  rw [decl_packing_coordinates] at positions
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at positions
  simp only [declarationEnd,declarationStart] at lo hi
  omega

theorem decl_missing_root : (preparePackedDeclaration declPackingEnv ⟨none,"missing"⟩ account 0).toOption = none := by rfl

theorem decl_wrong_member_cell : packDeclarationFields declPackingEnv declPackingRoot account 0 [("wrong",.int .u256)] 0 = .error .cellMismatch := by rfl

theorem decl_reference_unsupported : declarationScalar? declPackingEnv.layout (.bytes .storage) = none := rfl

theorem decl_slot_overflow : (packDeclarationFields declPackingEnv declPackingRoot account 0 [("flag",.bool)] ((2^256)*32)).toOption = none := by rfl

def declPackingState : Source.EMState declPackingEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := declPackingEnv.layout) (declPackingEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩
def declPackingResidual := initialPackedComplement declPackingRegistry declPackingRegistry (fun _ => packedZeroRaw)

theorem decl_plan_ready : (preparePackedFrame (ps := declPackingRegistry) (ts := declPackingRegistry)
    packedStepFrame false 0 packedRawA).isSome := by decide

def declPackingPlan := (preparePackedFrame (ps := declPackingRegistry) (ts := declPackingRegistry)
    packedStepFrame false 0 packedRawA).get decl_plan_ready

def declPackingRun := packedSourceStep packedStepFrame declPackingPlan declPackingState declPackingResidual

theorem decl_source_fields :
    ((declPackingRun.1.2.2.ex.world.accounts account).storage).cell (declarationFieldPath declPackingRoot 0) = some (.bool true) ∧
    ((declPackingRun.1.2.2.ex.world.accounts account).storage).cell (declarationFieldPath declPackingRoot 1) = some (.int 0x1234 (by decide)) ∧
    ((declPackingRun.1.2.2.ex.world.accounts account).storage).cell (declarationFieldPath declPackingRoot 2) = some (.fixedBytes [0xff,0,0xaa] rfl) ∧
    ((declPackingRun.1.2.2.ex.world.accounts account).storage).cell (declarationFieldPath declPackingRoot 3) = some (.address ⟨0x1234567890123456789012345678901234567890,by decide⟩) := ⟨rfl,rfl,rfl,rfl⟩

theorem decl_source_MemOK (H : Source.HeapTy) (ok : Source.MemOK declPackingEnv H declPackingState) :
    Source.MemOK declPackingEnv H declPackingRun.1.2 := packedSourceStep_MemOK H _ _ _ _ ok

theorem decl_initial_MemOK : Source.MemOK declPackingEnv declPackingState.2.heap.ty declPackingState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem decl_written_inhabited_MemOK : Source.MemOK declPackingEnv declPackingState.2.heap.ty declPackingRun.1.2 :=
  decl_source_MemOK _ decl_initial_MemOK

theorem decl_source_full_raw : reencodePersistentSlot declPackingRegistry ⟨declPackingRun.1.2.2.ex,declPackingRun.2⟩ account 0 = some packedRawA := by
  exact packedFrameWrite_persistent_reencode packedStepFrame 0 packedRawA declPackingState declPackingResidual declPackingRun
    (by
      unfold packedFrameWrite?
      rw [show preparePackedFrame (ps := declPackingRegistry) (ts := declPackingRegistry) packedStepFrame false 0 packedRawA = some declPackingPlan from Option.get_mem decl_plan_ready]
      rfl) rfl (decl_packing_separated account)

end Solidity.Yul.Views.Controls

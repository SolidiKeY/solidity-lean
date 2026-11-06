import Solidity.Yul.Views.OwnedBoolControls

namespace Solidity.Yul.Views.Controls

def ownedOriginState : Source.EMState originEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D:=originEnv.layout) (originEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩
def ownedOriginResidual := initialPackedComplement originRegistry originTempRegistry (fun _ => 0)
def ownedOriginRequest : PackedSlotRequest := ⟨false,account,43,⟨0xab000002,by decide⟩⟩
def ownedOriginPrepared := prepareRepresentedSlot originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
theorem owned_origin_prepared : ownedOriginPrepared.isSome := by decide
def ownedOriginPlan := ownedOriginPrepared.get owned_origin_prepared
def ownedOriginRun := representedSourceStep originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial
  packedStepFrame ownedOriginPlan ownedOriginState ownedOriginResidual

theorem owned_origin_actual_path_read :
    (ownedOriginRun.1.1.2.2.ex.world.accounts account).storage.read (originPath "c")=some (.bool true) := rfl

theorem owned_origin_actual_fullword :
    reencodePersistentSlot (representedBanks originRegistry false ownedOriginRun.2)
      ⟨ownedOriginRun.1.1.2.2.ex,ownedOriginRun.1.2⟩ account 43=some ownedOriginRequest.raw :=
  represented_step_persistent_at_request packedStepFrame ownedOriginPlan ownedOriginState ownedOriginResidual rfl rfl originChecked.separated

theorem owned_origin_other_actual_path :
    (ownedOriginRun.1.1.2.2.ex.world.accounts account).storage.cell (originPath "a")=none ∧
    (ownedOriginRun.1.1.2.2.ex.world.accounts account).storage.cell (originPath "items")=none := ⟨rfl,rfl⟩

theorem owned_origin_current_frame : representedFrameWrite? originRegistry originTempRegistry packedStepFrame false 43
    ownedOriginRequest.raw boolEncodingInitial ownedOriginState ownedOriginResidual=some ownedOriginRun := by
  change (ownedOriginPrepared.map fun p => representedSourceStep originRegistry originTempRegistry ownedOriginRequest boolEncodingInitial packedStepFrame p ownedOriginState ownedOriginResidual)=some ownedOriginRun
  rw [← Option.some_get owned_origin_prepared,Option.map_some]
  rfl

theorem owned_origin_initial_MemOK : Source.MemOK originEnv ownedOriginState.2.heap.ty ownedOriginState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem owned_origin_output_MemOK : Source.MemOK originEnv ownedOriginState.2.heap.ty ownedOriginRun.1.1.2 :=
  representedSourceStep_MemOK _ _ _ _ _ owned_origin_initial_MemOK

/-- Unwritten and explicitly-default original cells remain administratively
distinct under pure unchanged-view preparation. -/
def dirtyBoolExplicitStore := dirtyBoolEmptyStore.write finiteFlag (.bool false)
theorem dirty_bool_explicit_view : finiteView (representedRegistry (packedTypedRegistry account) false account boolEncodingInitial)
    dirtyBoolExplicitStore (fun _ => 0) := by
  intro c member
  simp only [representedRegistry,packedTypedRegistry,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem dirty_bool_explicit_admin :
    representedStoreWriteback (packedTypedRegistry account) false account (fun _ => 0) boolEncodingInitial dirtyBoolExplicitStore=
    some ((dirtyBoolExplicitStore,packedMask (packedTypedRegistry account) (fun _ => 0)),boolEncodingInitial) :=
  representedStoreWriteback_unchanged _ _ _ _ _ _ dirty_bool_explicit_view

theorem dirty_bool_admin_distinct : dirtyBoolEmptyStore.cell finiteFlag=none ∧
    dirtyBoolExplicitStore.cell finiteFlag=some (.bool false) := ⟨rfl,rfl⟩

end Solidity.Yul.Views.Controls

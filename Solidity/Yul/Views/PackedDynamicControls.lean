import Solidity.Yul.Views.PackedOwnershipBatch

namespace Solidity.Yul.Views.Controls

def pdU16 : Source.IntTy := ⟨false,16,by decide⟩
def pdU24 : Source.IntTy := ⟨false,24,by decide⟩
def pdName (s : String) : Source.DeclName := ⟨some "PD",s⟩
def pdPath (s : String) : Source.SPath := ⟨pdName s,[]⟩
def pdSyn16 : Source.Syn .typeName := .elem (.int false 16 (by decide))
def pdSyn24 : Source.Syn .typeName := .elem (.int false 24 (by decide))
def pdEnv : Source.Env := ⟨[
  ⟨.contract,"PD",none,true,.contract false "PD" .none .nil .nil⟩,
  ⟨.stateVar,"xs",some "PD",false,.stateVar (.array pdSyn16 .none) none none none false "xs" .none⟩,
  ⟨.stateVar,"marker",some "PD",false,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩,
  ⟨.stateVar,"ys",some "PD",false,.stateVar (.array pdSyn24 .none) none none none false "ys" .none⟩]⟩

def pdTypes := [(pdName "xs",Source.STy.array .storage (.int pdU16) none),
  (pdName "marker",.int .u256),(pdName "ys",.array .storage (.int pdU24) none)]
def pdDeclarations : StorageDeclarations pdEnv pdTypes :=
  .cons (.packedUnsignedArray pdU16 rfl (by decide))
    (.cons (.fixed (.scalar (.int .u256) rfl)) (.cons (.packedUnsignedArray pdU24 rfl (by decide)) .nil))
theorem pd_layout_ready : (prepareComputedStorage pdDeclarations "PD" account).toOption.isSome := by decide
def pdLayout := (prepareComputedStorage pdDeclarations "PD" account).toOption.get pd_layout_ready

theorem pd_header_coordinates : pdLayout.registrations.map (fun c => (c.path,c.slot.val,c.field.offset,c.field.width)) =
    [(pdPath "xs",0,0,32),(pdPath "marker",1,0,32),(pdPath "ys",2,0,32)] := rfl

def pdXEntry : {entry // entry ∈ pdLayout.unsignedTrace} := ⟨(pdName "xs",pdU16,0),by decide⟩
def pdYEntry : {entry // entry ∈ pdLayout.unsignedTrace} := ⟨(pdName "ys",pdU24,64),by decide⟩
def pdX := pdLayout.unsignedHeader pdXEntry
def pdY := pdLayout.unsignedHeader pdYEntry

theorem pd_legacy_trace_unchanged : pdLayout.headerTrace = [] ∧ pdLayout.header? (pdName "xs") = none := ⟨rfl,rfl⟩

def pdFixed : Roadmap.Evm.Fixed where
  keccak b := if b = layoutPreimageBytes (.data 0) then 1000 else 2000
  keccak_lt _ := by split <;> decide
  precompile _ _ := none
  precompileGas _ _ := 0

theorem pd_u16_coordinates : [0,15,16,17].map (fun i => ((pdX.element pdFixed account i).slot.val,(pdX.element pdFixed account i).field.offset)) =
    [(1000,0),(1000,30),(1001,0),(1001,2)] := rfl

theorem pd_u24_coordinates : [0,9,10].map (fun i => ((pdY.element pdFixed account i).slot.val,(pdY.element pdFixed account i).field.offset)) =
    [(2000,0),(2000,27),(2001,0)] := rfl

theorem pd_u24_padding : (pdY.element pdFixed account 9).field.offset + (pdY.element pdFixed account 9).field.width = 30 := rfl

def pdWord0 : Roadmap.Word := ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,by decide⟩
def pdWord1 : Roadmap.Word := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc004d,by decide⟩
def pdWord24 : Roadmap.Word := ⟨0xaabbffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,by decide⟩
def pdRaw : SlotView := fun q => if q = 0 ∨ q = 1 ∨ q = 2 then 0 else if q = 1000 then pdWord0 else if q = 1001 then pdWord1 else if q = 2000 then pdWord24 else 77

def pdState : Source.EMState pdEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := pdEnv.layout) (pdEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩
def pdResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask pdLayout.registrations pdRaw k.slot,[]⟩

theorem pd_initial_view : finiteView pdLayout.registrations (pdState.2.ex.world.accounts account).storage pdRaw := by
  intro c member
  change c ∈ [_,_,_] at member
  rcases List.mem_cons.mp member with same | member
  · subst c; rfl
  · rcases List.mem_cons.mp member with same | member
    · subst c; rfl
    · have same := List.mem_singleton.mp member
      subst c; rfl

theorem pd_empty_inventory : pdLayout.unsignedSnapshot pdFixed pdRaw = pdLayout.registrations := rfl

theorem pd_initial_encoding : finiteEncode (pdLayout.unsignedSnapshot pdFixed pdRaw)
    (pdState.2.ex.world.accounts account).storage (fun q => pdResidual.cells (complementKey false account q)) = some pdRaw := by
  rw [pd_empty_inventory]
  exact finiteEncode_fromComplement _ _ _ pdLayout.separated pd_initial_view

theorem pd_fill_decoded : (finiteAccountWrite? (T := pdEnv.lay) account
    (pdLayout.unsignedSnapshot pdFixed (saveSlot pdRaw 0 17)) (saveSlot pdRaw 0 17)).isSome := by decide

theorem pd_fill_separated : packedSeparationCheck (pdLayout.unsignedSnapshot pdFixed (saveSlot pdRaw 0 17)) = true := by decide

def pdFillOp : Source.Op pdEnv.layout pdEnv.lay pdEnv.lay :=
  (finiteAccountWrite? account (pdLayout.unsignedSnapshot pdFixed (saveSlot pdRaw 0 17)) (saveSlot pdRaw 0 17)).get pd_fill_decoded

@[irreducible]
def pdFill : PackedOwnershipPlan packedStepFrame pdLayout pdFixed 0 17 pdState pdResidual :=
  ⟨pdLayout.unsignedSnapshot pdFixed pdRaw,
   pdLayout.unsignedSourceInventory_view packedStepFrame pdFixed pdState pdRaw pd_initial_view,
   pdRaw,pd_initial_encoding,(by rw [pd_empty_inventory]; exact (packedSeparationCheck_iff _).mpr pdLayout.separated),
   pd_fill_separated,pdFillOp,Option.get_mem pd_fill_decoded⟩

theorem pd_fill_raw : pdFill.raw = pdRaw := by unfold pdFill; rfl

theorem pd_fill_map : finiteEncode pdFill.next (pdFill.step.1.2.2.ex.world.accounts account).storage
    (fun q => pdFill.step.2.cells (complementKey false account q)) = some (saveSlot pdRaw 0 17) :=
  (pdFill.reencode rfl).trans (congrArg some (congrArg (fun m => saveSlot m 0 17) pd_fill_raw))

end Solidity.Yul.Views.Controls

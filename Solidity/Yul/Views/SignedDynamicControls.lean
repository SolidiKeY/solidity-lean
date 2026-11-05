import Solidity.Yul.Views.IntOwnershipBatch

namespace Solidity.Yul.Views.Controls

def sdI16 : Source.IntTy := ⟨true,16,by decide⟩
def sdI24 : Source.IntTy := ⟨true,24,by decide⟩
def sdName (s : String) : Source.DeclName := ⟨some "SD",s⟩
def sdPath (s : String) : Source.SPath := ⟨sdName s,[]⟩
def sdSyn16 : Source.Syn .typeName := .elem (.int true 16 (by decide))
def sdSyn24 : Source.Syn .typeName := .elem (.int true 24 (by decide))
def sdEnv : Source.Env := ⟨[
  ⟨.contract,"SD",none,true,.contract false "SD" .none .nil .nil⟩,
  ⟨.stateVar,"xs",some "SD",false,.stateVar (.array sdSyn16 .none) none none none false "xs" .none⟩,
  ⟨.stateVar,"marker",some "SD",false,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩,
  ⟨.stateVar,"ys",some "SD",false,.stateVar (.array sdSyn24 .none) none none none false "ys" .none⟩]⟩

def sdTypes := [(sdName "xs",Source.STy.array .storage (.int sdI16) none),
  (sdName "marker",.int .u256),(sdName "ys",.array .storage (.int sdI24) none)]
def sdDeclarations : StorageDeclarations sdEnv sdTypes :=
  .cons (.signedArray sdI16 rfl)
    (.cons (.fixed (.scalar (.int .u256) rfl)) (.cons (.signedArray sdI24 rfl) .nil))
theorem sd_layout_ready : (prepareComputedStorage sdDeclarations "SD" account).toOption.isSome := by decide
def sdLayout := (prepareComputedStorage sdDeclarations "SD" account).toOption.get sd_layout_ready

theorem sd_header_coordinates : sdLayout.registrations.map (fun c => (c.path,c.slot.val,c.field.offset,c.field.width)) =
    [(sdPath "xs",0,0,32),(sdPath "marker",1,0,32),(sdPath "ys",2,0,32)] := rfl

def sdXEntry : {entry // entry ∈ sdLayout.integerTrace} := ⟨(sdName "xs",sdI16,0),by decide⟩
def sdYEntry : {entry // entry ∈ sdLayout.integerTrace} := ⟨(sdName "ys",sdI24,64),by decide⟩
def sdX := sdLayout.integerHeader sdXEntry
def sdY := sdLayout.integerHeader sdYEntry

theorem sd_legacy_trace_unchanged : sdLayout.headerTrace = [] ∧ sdLayout.header? (sdName "xs") = none := ⟨rfl,rfl⟩

def sdFixed : Roadmap.Evm.Fixed where
  keccak b := if b = layoutPreimageBytes (.data 0) then 1000 else 2000
  keccak_lt _ := by split <;> decide
  precompile _ _ := none
  precompileGas _ _ := 0

theorem sd_i16_coordinates : [0,15,16,17].map (fun i => ((sdX.element sdFixed account i).slot.val,(sdX.element sdFixed account i).field.offset)) =
    [(1000,0),(1000,30),(1001,0),(1001,2)] := rfl

theorem sd_i24_coordinates : [0,9,10].map (fun i => ((sdY.element sdFixed account i).slot.val,(sdY.element sdFixed account i).field.offset)) =
    [(2000,0),(2000,27),(2001,0)] := rfl

theorem sd_i24_padding : (sdY.element sdFixed account 9).field.offset + (sdY.element sdFixed account 9).field.width = 30 := rfl

def sdWord0 : Roadmap.Word := ⟨0xffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0000ffff7fff8000,by decide⟩
def sdWord1 : Roadmap.Word := ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc8000ffff,by decide⟩
def sdWord24 : Roadmap.Word := ⟨0xaabb800000eeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000ffffff7fffff800000,by decide⟩
def sdWord24Tail : Roadmap.Word := ⟨0xddddddddddddddddddddddddddddddddddddddddddddddddddddddddddffffff,by decide⟩
def sdRaw : SlotView := fun q => if q = 0 ∨ q = 1 ∨ q = 2 then 0 else if q = 1000 then sdWord0 else if q = 1001 then sdWord1 else if q = 2000 then sdWord24 else if q = 2001 then sdWord24Tail else if q = 3 then 999 else 77

def sdState : Source.EMState sdEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := sdEnv.layout) (sdEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩
def sdResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask sdLayout.registrations sdRaw k.slot,[]⟩

theorem sd_initial_view : finiteView sdLayout.registrations (sdState.2.ex.world.accounts account).storage sdRaw := by
  intro c member
  change c ∈ [_,_,_] at member
  rcases List.mem_cons.mp member with same | member
  · subst c; rfl
  · rcases List.mem_cons.mp member with same | member
    · subst c; rfl
    · have same := List.mem_singleton.mp member
      subst c; rfl

theorem sd_empty_inventory : sdLayout.integerSnapshot sdFixed sdRaw = sdLayout.registrations := rfl

theorem sd_initial_encoding : finiteEncode (sdLayout.integerSnapshot sdFixed sdRaw)
    (sdState.2.ex.world.accounts account).storage (fun q => sdResidual.cells (complementKey false account q)) = some sdRaw := by
  rw [sd_empty_inventory]
  exact finiteEncode_fromComplement _ _ _ sdLayout.separated sd_initial_view

theorem sd_fill_decoded : (finiteAccountWrite? (T := sdEnv.lay) account
    (sdLayout.integerSnapshot sdFixed (saveSlot sdRaw 0 17)) (saveSlot sdRaw 0 17)).isSome := by decide

theorem sd_fill_separated : packedSeparationCheck (sdLayout.integerSnapshot sdFixed (saveSlot sdRaw 0 17)) = true := by decide

def sdFillOp : Source.Op sdEnv.layout sdEnv.lay sdEnv.lay :=
  (finiteAccountWrite? account (sdLayout.integerSnapshot sdFixed (saveSlot sdRaw 0 17)) (saveSlot sdRaw 0 17)).get sd_fill_decoded

@[irreducible]
def sdFill : IntOwnershipPlan packedStepFrame sdLayout sdFixed 0 17 sdState sdResidual :=
  ⟨sdLayout.integerSnapshot sdFixed sdRaw,
   sdLayout.integerSourceInventory_view packedStepFrame sdFixed sdState sdRaw sd_initial_view,
   sdRaw,sd_initial_encoding,(by rw [sd_empty_inventory]; exact (packedSeparationCheck_iff _).mpr sdLayout.separated),
   sd_fill_separated,sdFillOp,Option.get_mem sd_fill_decoded⟩

theorem sd_fill_raw : sdFill.raw = sdRaw := by unfold sdFill; rfl

theorem sd_fill_map : finiteEncode sdFill.next (sdFill.step.1.2.2.ex.world.accounts account).storage
    (fun q => sdFill.step.2.cells (complementKey false account q)) = some (saveSlot sdRaw 0 17) :=
  (sdFill.reencode rfl).trans (congrArg some (congrArg (fun m => saveSlot m 0 17) sd_fill_raw))

end Solidity.Yul.Views.Controls

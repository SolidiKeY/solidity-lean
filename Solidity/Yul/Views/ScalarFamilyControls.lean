import Solidity.Yul.Views.ScalarOwnershipBatch

namespace Solidity.Yul.Views.Controls

def sfBytes : DynamicScalarKind := .fixedBytes 3 (by decide)
def sfAddress : DynamicScalarKind := .address false
def sfName (s : String) : Source.DeclName := ⟨some "SF",s⟩
def sfPath (s : String) : Source.SPath := ⟨sfName s,[]⟩
def sfEnv : Source.Env := ⟨[
  ⟨.contract,"SF",none,true,.contract false "SF" .none .nil .nil⟩,
  ⟨.stateVar,"xs",some "SF",false,.stateVar (.array (.elem .bool) .none) none none none false "xs" .none⟩,
  ⟨.stateVar,"marker",some "SF",false,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩,
  ⟨.stateVar,"ys",some "SF",false,.stateVar (.array (.elem (.fixedBytes 3 (by decide))) .none) none none none false "ys" .none⟩,
  ⟨.stateVar,"zs",some "SF",false,.stateVar (.array (.elem .address) .none) none none none false "zs" .none⟩]⟩
def sfTypes := [(sfName "xs",Source.STy.array .storage .bool none),
  (sfName "marker",.int .u256),(sfName "ys",.array .storage sfBytes.ty none),(sfName "zs",.array .storage sfAddress.ty none)]
def sfDeclarations : StorageDeclarations sfEnv sfTypes :=
  .cons (.scalarArray .bool) (.cons (.fixed (.scalar (.int .u256) rfl))
    (.cons (.scalarArray sfBytes) (.cons (.scalarArray sfAddress) .nil)))
theorem sf_layout_ready : (prepareComputedStorage sfDeclarations "SF" account).toOption.isSome := by decide
def sfLayout := (prepareComputedStorage sfDeclarations "SF" account).toOption.get sf_layout_ready

theorem sf_header_coordinates : sfLayout.registrations.map (fun c => (c.path,c.slot.val,c.field.offset,c.field.width)) =
    [(sfPath "xs",0,0,32),(sfPath "marker",1,0,32),(sfPath "ys",2,0,32),(sfPath "zs",3,0,32)] := rfl

def sfXEntry : {entry // entry ∈ sfLayout.scalarFamilyTrace} := ⟨(sfName "xs",.bool,0),by decide⟩
def sfYEntry : {entry // entry ∈ sfLayout.scalarFamilyTrace} := ⟨(sfName "ys",sfBytes,64),by decide⟩
def sfX := sfLayout.scalarFamilyHeader sfXEntry
def sfY := sfLayout.scalarFamilyHeader sfYEntry
def sfZEntry : {entry // entry ∈ sfLayout.scalarFamilyTrace} := ⟨(sfName "zs",sfAddress,96),by decide⟩
def sfZ := sfLayout.scalarFamilyHeader sfZEntry

theorem sf_legacy_trace_unchanged : sfLayout.headerTrace = [] ∧ sfLayout.header? (sfName "xs") = none := ⟨rfl,rfl⟩

def sfFixed : Roadmap.Evm.Fixed where
  keccak b := if b = layoutPreimageBytes (.data 0) then 1000 else if b = layoutPreimageBytes (.data 2) then 2000 else 3000
  keccak_lt _ := by
    split
    · decide
    · split <;> decide
  precompile _ _ := none
  precompileGas _ _ := 0

theorem sf_coordinates : [0,31,32,33].map (fun i => ((sfX.element sfFixed account i).slot.val,(sfX.element sfFixed account i).field.offset)) =
    [(1000,0),(1000,31),(1001,0),(1001,1)] := rfl
theorem sf_bytes_coordinates : [0,9,10,11].map (fun i => ((sfY.element sfFixed account i).slot.val,(sfY.element sfFixed account i).field.offset)) =
    [(2000,0),(2000,27),(2001,0),(2001,3)] := rfl
theorem sf_address_coordinates : [0,1,2].map (fun i => ((sfZ.element sfFixed account i).slot.val,(sfZ.element sfFixed account i).field.offset)) =
    [(3000,0),(3001,0),(3002,0)] := rfl
def sfWord0 : Roadmap.Word := ⟨452319750434927077568233343438225443052370734331334163334113702693610455296,by decide⟩
def sfWord1 : Roadmap.Word := ⟨92633671389852956338856788006950326282615987732512451231566067206327067869441,by decide⟩
def sfWordBytes : Roadmap.Word := ⟨77225343654666454986018009180904033091951020676197328057656743986486896034307,by decide⟩
def sfWordBytesTail : Roadmap.Word := ⟨100353144005674036033761520340862853472833986710221822167529905915084998180863,by decide⟩
def sfAddr0 : Roadmap.Word := ⟨0xaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000001234,by decide⟩
def sfAddr1 : Roadmap.Word := ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbffffffffffffffffffffffffffffffffffffffff,by decide⟩
def sfAddr2 : Roadmap.Word := ⟨0xcccccccccccccccccccccccc1122334455667788990011223344556677889900,by decide⟩
def sfRaw : SlotView := fun q => if q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 then 0 else if q = 1000 then sfWord0 else if q = 1001 then sfWord1 else if q = 2000 then sfWordBytes else if q = 2001 then sfWordBytesTail else if q = 3000 then sfAddr0 else if q = 3001 then sfAddr1 else if q = 3002 then sfAddr2 else if q = 4 then 999 else 77

def sfState : Source.EMState sfEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := sfEnv.layout) (sfEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩
def sfResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask sfLayout.registrations sfRaw k.slot,[]⟩

theorem sf_initial_view : finiteView sfLayout.registrations (sfState.2.ex.world.accounts account).storage sfRaw := by
  intro c member
  change c ∈ [_,_,_,_] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem sf_empty_inventory : sfLayout.scalarFamilySnapshot sfFixed sfRaw = sfLayout.registrations := rfl

theorem sf_initial_encoding : finiteEncode (sfLayout.scalarFamilySnapshot sfFixed sfRaw)
    (sfState.2.ex.world.accounts account).storage (fun q => sfResidual.cells (complementKey false account q)) = some sfRaw := by
  rw [sf_empty_inventory]
  exact finiteEncode_fromComplement _ _ _ sfLayout.separated sf_initial_view

theorem sf_fill_decoded : (finiteAccountWrite? (T := sfEnv.lay) account
    (sfLayout.scalarFamilySnapshot sfFixed (saveSlot sfRaw 0 33)) (saveSlot sfRaw 0 33)).isSome := by decide

theorem sf_fill_separated : packedSeparationCheck (sfLayout.scalarFamilySnapshot sfFixed (saveSlot sfRaw 0 33)) = true := by decide

def sfFillOp : Source.Op sfEnv.layout sfEnv.lay sfEnv.lay :=
  (finiteAccountWrite? account (sfLayout.scalarFamilySnapshot sfFixed (saveSlot sfRaw 0 33)) (saveSlot sfRaw 0 33)).get sf_fill_decoded

@[irreducible]
def sfFill : ScalarOwnershipPlan packedStepFrame sfLayout sfFixed 0 33 sfState sfResidual :=
  ⟨sfLayout.scalarFamilySnapshot sfFixed sfRaw,
   sfLayout.scalarFamilySourceInventory_view packedStepFrame sfFixed sfState sfRaw sf_initial_view,
   sfRaw,sf_initial_encoding,(by rw [sf_empty_inventory]; exact (packedSeparationCheck_iff _).mpr sfLayout.separated),
   sf_fill_separated,sfFillOp,Option.get_mem sf_fill_decoded⟩

theorem sf_fill_raw : sfFill.raw = sfRaw := by unfold sfFill; rfl

theorem sf_fill_map : finiteEncode sfFill.next (sfFill.step.1.2.2.ex.world.accounts account).storage
    (fun q => sfFill.step.2.cells (complementKey false account q)) = some (saveSlot sfRaw 0 33) :=
  (sfFill.reencode rfl).trans (congrArg some (congrArg (fun m => saveSlot m 0 33) sf_fill_raw))

end Solidity.Yul.Views.Controls

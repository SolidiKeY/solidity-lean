import Solidity.Yul.Views.PrimitiveOwnershipPreservation
import Solidity.Yul.Views.IntDynamicValues
import Solidity.Yul.Views.ScalarDynamicValues

namespace Solidity.Yul.Views.Controls

def pcI16 : Source.IntTy := ⟨true,16,by decide⟩
def pcU24 : Source.IntTy := ⟨false,24,by decide⟩
def pcBytes : DynamicScalarKind := .fixedBytes 3 (by decide)
def pcAddress : DynamicScalarKind := .address false
def pcName (s : String) : Source.DeclName := ⟨some "PC",s⟩
def pcPath (s : String) : Source.SPath := ⟨pcName s,[]⟩
def pcEnv : Source.Env := ⟨[
  ⟨.contract,"PC",none,true,.contract false "PC" .none .nil .nil⟩,
  ⟨.stateVar,"ss",some "PC",false,.stateVar (.array (.elem (.int true 16 (by decide))) .none) none none none false "ss" .none⟩,
  ⟨.stateVar,"us",some "PC",false,.stateVar (.array (.elem (.int false 24 (by decide))) .none) none none none false "us" .none⟩,
  ⟨.stateVar,"ws",some "PC",false,.stateVar (.array (.elem (.int false 256 (by decide))) .none) none none none false "ws" .none⟩,
  ⟨.stateVar,"bs",some "PC",false,.stateVar (.array (.elem .bool) .none) none none none false "bs" .none⟩,
  ⟨.stateVar,"ys",some "PC",false,.stateVar (.array (.elem (.fixedBytes 3 (by decide))) .none) none none none false "ys" .none⟩,
  ⟨.stateVar,"zs",some "PC",false,.stateVar (.array (.elem .address) .none) none none none false "zs" .none⟩,
  ⟨.stateVar,"marker",some "PC",false,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩]⟩
def pcTypes := [(pcName "ss",Source.STy.array .storage (.int pcI16) none),(pcName "us",Source.STy.array .storage (.int pcU24) none),(pcName "ws",Source.STy.array .storage (.int .u256) none),(pcName "bs",Source.STy.array .storage .bool none),(pcName "ys",Source.STy.array .storage pcBytes.ty none),(pcName "zs",Source.STy.array .storage pcAddress.ty none),(pcName "marker",.int .u256)]
def pcDeclarations : StorageDeclarations pcEnv pcTypes :=
  .cons (.signedArray pcI16 rfl) (.cons (.packedUnsignedArray pcU24 rfl (by decide)) (.cons .uintArray
    (.cons (.scalarArray .bool) (.cons (.scalarArray pcBytes) (.cons (.scalarArray pcAddress)
      (.cons (.fixed (.scalar (.int .u256) rfl)) .nil))))))
theorem pc_layout_ready : (prepareComputedStorage pcDeclarations "PC" account).toOption.isSome := by decide
def pcLayout := (prepareComputedStorage pcDeclarations "PC" account).toOption.get pc_layout_ready
def pcSEntry : {entry // entry ∈ pcLayout.integerTrace} := ⟨(pcName "ss",pcI16,0),by decide⟩
def pcS := pcLayout.integerHeader pcSEntry
def pcUEntry : {entry // entry ∈ pcLayout.integerTrace} := ⟨(pcName "us",pcU24,32),by decide⟩
def pcU := pcLayout.integerHeader pcUEntry
def pcWEntry : {entry // entry ∈ pcLayout.integerTrace} := ⟨(pcName "ws",Source.IntTy.u256,64),by decide⟩
def pcW := pcLayout.integerHeader pcWEntry
def pcBEntry : {entry // entry ∈ pcLayout.scalarFamilyTrace} := ⟨(pcName "bs",DynamicScalarKind.bool,96),by decide⟩
def pcB := pcLayout.scalarFamilyHeader pcBEntry
def pcYEntry : {entry // entry ∈ pcLayout.scalarFamilyTrace} := ⟨(pcName "ys",pcBytes,128),by decide⟩
def pcY := pcLayout.scalarFamilyHeader pcYEntry
def pcZEntry : {entry // entry ∈ pcLayout.scalarFamilyTrace} := ⟨(pcName "zs",pcAddress,160),by decide⟩
def pcZ := pcLayout.scalarFamilyHeader pcZEntry
def pcFixed : Roadmap.Evm.Fixed where
  keccak b := if b = layoutPreimageBytes (.data 0) then 1000 else if b = layoutPreimageBytes (.data 1) then 2000 else
    if b = layoutPreimageBytes (.data 2) then 3000 else if b = layoutPreimageBytes (.data 3) then 4000 else
    if b = layoutPreimageBytes (.data 4) then 5000 else 6000
  keccak_lt _ := by
    split
    · decide
    · split
      · decide
      · split
        · decide
        · split
          · decide
          · split <;> decide
  precompile _ _ := none
  precompileGas _ _ := 0
def pcS0 : Roadmap.Word := ⟨115791971447511876864615679455521191658702262833380772331509825747099588820991,by decide⟩
def pcS1 : Roadmap.Word := ⟨92633671389852956338856788006950326282615987732512451231566067206329215221837,by decide⟩
def pcU0 : Roadmap.Word := ⟨77707819007715130266253686141994171000598470746112337144744427519547199717377,by decide⟩
def pcU1 : Roadmap.Word := ⟨100353144005674036033761520340862853472833986710221822167529906140191364481101,by decide⟩
def pcB0 : Roadmap.Word := ⟨108072616621495115728666252674775380663051985687931193103493745074048279314688,by decide⟩
def pcY0 : Roadmap.Word := ⟨110797136368255496797456158204391566730187750033005088723432935885259942199811,by decide⟩
def pcZ0 : Roadmap.Word := ⟨77194726158210796949047323338150937477292721164957919471160867325504798069300,by decide⟩
def pcZ1 : Roadmap.Word := ⟨84914198774031876643952055673427532862352896199657396250993237077711210414079,by decide⟩
def pcRaw : SlotView := fun q => if q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 then 0 else
  if q = 1000 then pcS0 else if q = 1001 then pcS1 else if q = 2000 then pcU0 else if q = 2001 then pcU1 else
  if q = 3000 then ⟨2^256-1,by decide⟩ else if q = 3001 then 77 else if q = 4000 then pcB0 else if q = 5000 then pcY0 else
  if q = 6000 then pcZ0 else if q = 6001 then pcZ1 else if q = 7 then 999 else 77

def pcState : Source.EMState pcEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := pcEnv.layout) (pcEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩
def pcResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask pcLayout.registrations pcRaw k.slot,[]⟩

theorem pc_initial_view : finiteView pcLayout.registrations (pcState.2.ex.world.accounts account).storage pcRaw := by
  intro c member
  change c ∈ [_,_,_,_,_,_,_] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem pc_empty_inventory : pcLayout.primitiveSnapshot pcFixed pcRaw = pcLayout.registrations := rfl

theorem pc_initial_encoding : finiteEncode (pcLayout.primitiveSnapshot pcFixed pcRaw)
    (pcState.2.ex.world.accounts account).storage (fun q => pcResidual.cells (complementKey false account q)) = some pcRaw := by
  rw [pc_empty_inventory]
  exact finiteEncode_fromComplement _ _ _ pcLayout.separated pc_initial_view

theorem pc_signed_decoded : (finiteAccountWrite? (T := pcEnv.lay) account
    (pcLayout.primitiveSnapshot pcFixed (saveSlot pcRaw 0 17)) (saveSlot pcRaw 0 17)).isSome := by decide

theorem pc_signed_separated : packedSeparationCheck (pcLayout.primitiveSnapshot pcFixed (saveSlot pcRaw 0 17)) = true := by decide

def pcSignedOp : Source.Op pcEnv.layout pcEnv.lay pcEnv.lay :=
  (finiteAccountWrite? account (pcLayout.primitiveSnapshot pcFixed (saveSlot pcRaw 0 17)) (saveSlot pcRaw 0 17)).get pc_signed_decoded
@[irreducible]
def pcSigned : PrimitiveOwnershipPlan packedStepFrame pcLayout pcFixed 0 17 pcState pcResidual :=
  ⟨pcLayout.primitiveSnapshot pcFixed pcRaw,
   pcLayout.primitiveSourceInventory_view packedStepFrame pcFixed pcState pcRaw pc_initial_view,
   pcRaw,pc_initial_encoding,(by rw [pc_empty_inventory]; exact (packedSeparationCheck_iff _).mpr pcLayout.separated),
   pc_signed_separated,pcSignedOp,Option.get_mem pc_signed_decoded⟩
def pcRawSigned := saveSlot pcRaw 0 17
theorem pc_signed_raw : pcSigned.raw = pcRaw := by unfold pcSigned; rfl
theorem pc_signed_next : pcSigned.nextRaw = pcRawSigned := congrArg (fun m => saveSlot m 0 17) pc_signed_raw

theorem pc_signed_map : finiteEncode pcSigned.next (pcSigned.step.1.2.2.ex.world.accounts account).storage
    (fun q => pcSigned.step.2.cells (complementKey false account q)) = some pcRawSigned :=
  (pcSigned.reencode rfl).trans (congrArg some pc_signed_next)

end Solidity.Yul.Views.Controls

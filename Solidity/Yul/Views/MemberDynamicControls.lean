import Solidity.Yul.Views.MemberOwnershipResidual

namespace Solidity.Yul.Views.Controls

def mdU16 : Source.IntTy := ⟨false,16,by decide⟩
def mdI24 : Source.IntTy := ⟨true,24,by decide⟩
def mdBytes : DynamicScalarKind := .fixedBytes 3 (by decide)
def mdAddress : DynamicScalarKind := .address false
def mdName (s : String) : Source.DeclName := ⟨some "ND",s⟩
def mdPath (s : String) : Source.SPath := ⟨mdName s,[]⟩
def mdStruct : Source.DeclName := ⟨none,"S"⟩
def mdEnv : Source.Env := ⟨[
  ⟨.contract,"ND",none,true,.contract false "ND" .none .nil .nil⟩,
  ⟨.struct,"S",none,true,.struct "S" (.structMember (.elem (.int false 16 (by decide))) "guard")
    (.cons (.structMember (.array (.elem (.int false 16 (by decide))) .none) "xs")
    (.cons (.structMember (.array (.elem (.int true 24 (by decide))) .none) "ys")
    (.cons (.structMember (.elem (.fixedBytes 3 (by decide))) "tag")
    (.cons (.structMember (.elem .address) "who") .nil))))⟩,
  ⟨.stateVar,"box",some "ND",false,.stateVar (.userType ⟨"S",[]⟩) none none none false "box" .none⟩,
  ⟨.stateVar,"top",some "ND",false,.stateVar (.array (.elem .bool) .none) none none none false "top" .none⟩,
  ⟨.stateVar,"marker",some "ND",false,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩]⟩
def mdFields : List (String × Source.STy) := [("guard",.int mdU16),("xs",.array .storage (.int mdU16) none),
  ("ys",.array .storage (.int mdI24) none),("tag",mdBytes.ty),("who",mdAddress.ty)]
def mdMembers : MemberStorageDeclarations mdEnv (mdFields.map Prod.snd) :=
  .cons (.fixed (.scalar (.int mdU16) rfl)) (.cons (.packedUnsignedArray mdU16 rfl (by decide))
    (.cons (.signedArray mdI24 rfl) (.cons (.fixed (.scalar mdBytes.ty rfl))
      (.cons (.fixed (.scalar mdAddress.ty rfl)) .nil))))
def mdTypes : List (Source.DeclName × Source.STy) := [(mdName "box",.struct .storage mdStruct),
  (mdName "top",.array .storage .bool none),(mdName "marker",.int .u256)]
def mdDeclarations : RootMemberDeclarations mdEnv mdTypes :=
  .cons (.strct mdStruct mdFields rfl mdMembers rfl)
    (.cons (.leaf (.scalarArray .bool)) (.cons (.leaf (.fixed (.scalar (.int .u256) rfl))) .nil))
theorem md_ready : (prepareMemberComputedStorage mdDeclarations "ND" account).toOption.isSome := by decide
def mdLayout := (prepareMemberComputedStorage mdDeclarations "ND" account).toOption.get md_ready

theorem md_coordinates : mdLayout.registrations.map (fun c => (c.path.steps,c.slot.val,c.field.offset,c.field.width)) =
    [([.field 0],0,0,2),([.field 1],1,0,32),([.field 2],2,0,32),([.field 3],3,0,3),([.field 4],3,3,20),([],4,0,32),([],5,0,32)] := rfl

theorem md_header_trace : mdLayout.headerTrace =
    [(mdPath "box" |>.go (.field 1),PathPrimitiveKind.integer mdU16,2),
     (mdPath "box" |>.go (.field 2),PathPrimitiveKind.integer mdI24,64),
     (mdPath "top",PathPrimitiveKind.scalar .bool,128)] := by
  -- The first cursor is two BYTES after guard; its header aligns to slot one.
  rfl

def mdXEntry : {entry // entry ∈ mdLayout.headerTrace} := ⟨((mdPath "box").go (.field 1),.integer mdU16,2),by decide⟩
def mdYEntry : {entry // entry ∈ mdLayout.headerTrace} := ⟨((mdPath "box").go (.field 2),.integer mdI24,64),by decide⟩
def mdBEntry : {entry // entry ∈ mdLayout.headerTrace} := ⟨(mdPath "top",.scalar .bool,128),by decide⟩
def mdX : PathIntHeader mdEnv ((mdPath "box").go (.field 1)) mdU16 2 := mdLayout.header mdXEntry
def mdY : PathIntHeader mdEnv ((mdPath "box").go (.field 2)) mdI24 64 := mdLayout.header mdYEntry
def mdB : PathScalarHeader mdEnv (mdPath "top") .bool 128 := mdLayout.header mdBEntry

def mdFixed : Roadmap.Evm.Fixed where
  keccak b := if b = layoutPreimageBytes (.data 1) then 1000 else if b = layoutPreimageBytes (.data 2) then 2000 else 3000
  keccak_lt _ := by split; decide; split <;> decide
  precompile _ _ := none
  precompileGas _ _ := 0

def mdRaw : SlotView := fun q => if q = 0 then ⟨2^240,by decide⟩ else
  if q = 1 ∨ q = 2 ∨ q = 4 ∨ q = 5 then 0 else if q = 3 then ⟨2^248,by decide⟩ else
  if q = 1000 then ⟨2^256-1,by decide⟩ else if q = 1001 then ⟨77+2^240,by decide⟩ else
  if q = 2000 then ⟨2^256-1,by decide⟩ else if q = 2001 then ⟨77+2^248,by decide⟩ else
  if q = 3000 then ⟨2^248+2^24+2^16+1,by decide⟩ else 999

def mdState : Source.EMState mdEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := mdEnv.layout) (mdEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩
def mdResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask mdLayout.registrations mdRaw k.slot,[]⟩
theorem md_initial_MemOK : Source.MemOK mdEnv mdState.2.heap.ty mdState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
def mdC0 := mdLayout.registrations[0]'(by decide)
theorem md_view0 : scalarPathView mdC0.path mdC0.codec mdC0.slot
    (mdState.2.ex.world.accounts account).storage mdRaw := rfl
def mdC1 := mdLayout.registrations[1]'(by decide)
theorem md_view1 : scalarPathView mdC1.path mdC1.codec mdC1.slot
    (mdState.2.ex.world.accounts account).storage mdRaw := rfl
def mdC2 := mdLayout.registrations[2]'(by decide)
theorem md_view2 : scalarPathView mdC2.path mdC2.codec mdC2.slot
    (mdState.2.ex.world.accounts account).storage mdRaw := rfl
def mdC3 := mdLayout.registrations[3]'(by decide)
theorem md_view3 : scalarPathView mdC3.path mdC3.codec mdC3.slot
    (mdState.2.ex.world.accounts account).storage mdRaw := rfl
def mdC4 := mdLayout.registrations[4]'(by decide)
theorem md_view4 : scalarPathView mdC4.path mdC4.codec mdC4.slot
    (mdState.2.ex.world.accounts account).storage mdRaw := rfl
def mdC5 := mdLayout.registrations[5]'(by decide)
theorem md_view5 : scalarPathView mdC5.path mdC5.codec mdC5.slot
    (mdState.2.ex.world.accounts account).storage mdRaw := rfl
def mdC6 := mdLayout.registrations[6]'(by decide)
theorem md_view6 : scalarPathView mdC6.path mdC6.codec mdC6.slot
    (mdState.2.ex.world.accounts account).storage mdRaw := rfl
theorem md_registry_list : mdLayout.registrations = [mdC0,mdC1,mdC2,mdC3,mdC4,mdC5,mdC6] := rfl
theorem md_initial_view : finiteView mdLayout.registrations (mdState.2.ex.world.accounts account).storage mdRaw := by
  intro c member
  rw [md_registry_list] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact md_view0
  · exact md_view1
  · exact md_view2
  · exact md_view3
  · exact md_view4
  · exact md_view5
  · exact md_view6
theorem md_empty_inventory : mdLayout.snapshot mdFixed mdRaw = mdLayout.registrations := rfl
theorem md_initial_encoding : finiteEncode (mdLayout.snapshot mdFixed mdRaw)
    (mdState.2.ex.world.accounts account).storage (fun q => mdResidual.cells (complementKey false account q)) = some mdRaw := by
  rw [md_empty_inventory]
  exact finiteEncode_fromComplement _ _ _ mdLayout.separated md_initial_view

theorem md_x_decoded : (finiteAccountWrite? (T := mdEnv.lay) account
    (mdLayout.snapshot mdFixed (saveSlot mdRaw 1 17)) (saveSlot mdRaw 1 17)).isSome := by decide
theorem md_x_separated : packedSeparationCheck (mdLayout.snapshot mdFixed (saveSlot mdRaw 1 17)) = true := by decide
def mdXOp : Source.Op mdEnv.layout mdEnv.lay mdEnv.lay :=
  (finiteAccountWrite? account (mdLayout.snapshot mdFixed (saveSlot mdRaw 1 17)) (saveSlot mdRaw 1 17)).get md_x_decoded
@[irreducible]
def mdGrow : MemberOwnershipPlan packedStepFrame mdLayout mdFixed 1 17 mdState mdResidual :=
  ⟨mdLayout.snapshot mdFixed mdRaw,mdLayout.sourceInventory_view packedStepFrame mdFixed mdState mdRaw md_initial_view,
   mdRaw,md_initial_encoding,(by rw [md_empty_inventory]; exact (packedSeparationCheck_iff _).mpr mdLayout.separated),
   md_x_separated,mdXOp,Option.get_mem md_x_decoded⟩
def mdGrowRaw := saveSlot mdRaw 1 17
theorem md_grow_raw : mdGrow.raw = mdRaw := by unfold mdGrow; rfl
theorem md_grow_next : mdGrow.nextRaw = mdGrowRaw := congrArg (fun m => saveSlot m 1 17) md_grow_raw
theorem md_grow_map : finiteEncode mdGrow.next (mdGrow.step.1.2.2.ex.world.accounts account).storage
    (fun q => mdGrow.step.2.cells (complementKey false account q)) = some mdGrowRaw :=
  (mdGrow.reencode rfl).trans (congrArg some md_grow_next)

end Solidity.Yul.Views.Controls

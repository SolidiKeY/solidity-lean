import Solidity.Yul.Views.RecursiveDynamicLayout

namespace Solidity.Yul.Views.Controls

theorem rc_coordinates : rcLayout.registrations.map (fun c => (c.path.steps,c.slot.val,c.field.offset,c.field.width)) =
 [([.field 0],0,0,1),([.field 1,.field 0],1,0,2),([.field 1,.field 1,.field 0],2,0,32),
  ([.field 1,.field 1,.field 1],3,0,32),([.field 1,.field 1,.field 2],4,0,3),([.field 1,.field 2],5,0,32),([.field 2],6,0,20),([],7,0,32)] := rfl

theorem rc_header_trace : rcLayout.headerTrace = [(rcXPath,.integer rcU16,64),(rcYPath,.integer rcI24,96),(rcBPath,.scalar .bool,160)] := rfl

def rcXEntry : {entry // entry ∈ rcLayout.headerTrace} := ⟨(rcXPath,.integer rcU16,64),by decide⟩
def rcYEntry : {entry // entry ∈ rcLayout.headerTrace} := ⟨(rcYPath,.integer rcI24,96),by decide⟩
def rcBEntry : {entry // entry ∈ rcLayout.headerTrace} := ⟨(rcBPath,.scalar .bool,160),by decide⟩
def rcX : PathIntHeader rcEnv rcXPath rcU16 64 := rcLayout.header rcXEntry
def rcY : PathIntHeader rcEnv rcYPath rcI24 96 := rcLayout.header rcYEntry
def rcB : PathScalarHeader rcEnv rcBPath .bool 160 := rcLayout.header rcBEntry

def rcFixed : Roadmap.Evm.Fixed where
  keccak b := if b = layoutPreimageBytes (.data 2) then 1000 else if b = layoutPreimageBytes (.data 3) then 2000 else 3000
  keccak_lt _ := by split; decide; split <;> decide
  precompile _ _ := none
  precompileGas _ _ := 0

def rcRaw : SlotView := fun q => if q = 0 ∨ q = 4 ∨ q = 6 then ⟨2^248,by decide⟩ else
  if q = 1 then ⟨2^240,by decide⟩ else if q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 then 0 else
  if q = 1000 then ⟨2^256-1,by decide⟩ else if q = 1001 then ⟨77+32768*65536+2^240,by decide⟩ else
  if q = 2000 then ⟨2^256-1,by decide⟩ else if q = 2001 then ⟨77+8388608*2^24+2^248,by decide⟩ else
  if q = 3000 then ⟨2^248+2*2^24+2^16+1,by decide⟩ else 999

def rcState : Source.EMState rcEnv [] :=
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := rcEnv.layout) (rcEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩⟩⟩
def rcResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun k => if k.transient then 0 else packedMask rcLayout.registrations rcRaw k.slot,[]⟩
theorem rc_initial_MemOK : Source.MemOK rcEnv rcState.2.heap.ty rcState :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
def rcC0 := rcLayout.registrations[0]'(by decide)
theorem rc_view0 : scalarPathView rcC0.path rcC0.codec rcC0.slot
    (rcState.2.ex.world.accounts account).storage rcRaw := rfl
def rcC1 := rcLayout.registrations[1]'(by decide)
theorem rc_view1 : scalarPathView rcC1.path rcC1.codec rcC1.slot
    (rcState.2.ex.world.accounts account).storage rcRaw := rfl
def rcC2 := rcLayout.registrations[2]'(by decide)
theorem rc_view2 : scalarPathView rcC2.path rcC2.codec rcC2.slot
    (rcState.2.ex.world.accounts account).storage rcRaw := rfl
def rcC3 := rcLayout.registrations[3]'(by decide)
theorem rc_view3 : scalarPathView rcC3.path rcC3.codec rcC3.slot
    (rcState.2.ex.world.accounts account).storage rcRaw := rfl
def rcC4 := rcLayout.registrations[4]'(by decide)
theorem rc_view4 : scalarPathView rcC4.path rcC4.codec rcC4.slot
    (rcState.2.ex.world.accounts account).storage rcRaw := rfl
def rcC5 := rcLayout.registrations[5]'(by decide)
theorem rc_view5 : scalarPathView rcC5.path rcC5.codec rcC5.slot
    (rcState.2.ex.world.accounts account).storage rcRaw := rfl
def rcC6 := rcLayout.registrations[6]'(by decide)
theorem rc_view6 : scalarPathView rcC6.path rcC6.codec rcC6.slot
    (rcState.2.ex.world.accounts account).storage rcRaw := rfl
def rcC7 := rcLayout.registrations[7]'(by decide)
theorem rc_view7 : scalarPathView rcC7.path rcC7.codec rcC7.slot
    (rcState.2.ex.world.accounts account).storage rcRaw := rfl
theorem rc_registry_list : rcLayout.registrations = [rcC0,rcC1,rcC2,rcC3,rcC4,rcC5,rcC6,rcC7] := rfl
theorem rc_initial_view : finiteView rcLayout.registrations (rcState.2.ex.world.accounts account).storage rcRaw := by
  intro c member
  rw [rc_registry_list] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rc_view0
  · exact rc_view1
  · exact rc_view2
  · exact rc_view3
  · exact rc_view4
  · exact rc_view5
  · exact rc_view6
  · exact rc_view7
theorem rc_empty_inventory : rcLayout.snapshot rcFixed rcRaw = rcLayout.registrations := rfl
theorem rc_initial_encoding : finiteEncode (rcLayout.snapshot rcFixed rcRaw)
    (rcState.2.ex.world.accounts account).storage (fun q => rcResidual.cells (complementKey false account q)) = some rcRaw := by
  rw [rc_empty_inventory]
  exact finiteEncode_fromComplement _ _ _ rcLayout.separated rc_initial_view

theorem rc_x_decoded : (finiteAccountWrite? (T := rcEnv.lay) account
    (rcLayout.snapshot rcFixed (saveSlot rcRaw 2 17)) (saveSlot rcRaw 2 17)).isSome := by decide
theorem rc_x_separated : packedSeparationCheck (rcLayout.snapshot rcFixed (saveSlot rcRaw 2 17)) = true := by decide
def rcXOp : Source.Op rcEnv.layout rcEnv.lay rcEnv.lay :=
  (finiteAccountWrite? account (rcLayout.snapshot rcFixed (saveSlot rcRaw 2 17)) (saveSlot rcRaw 2 17)).get rc_x_decoded
@[irreducible]
def rcGrow : RecursiveOwnershipPlan packedStepFrame rcLayout rcFixed 2 17 rcState rcResidual :=
  ⟨rcLayout.snapshot rcFixed rcRaw,rcLayout.sourceInventory_view packedStepFrame rcFixed rcState rcRaw rc_initial_view,
   rcRaw,rc_initial_encoding,(by rw [rc_empty_inventory]; exact (packedSeparationCheck_iff _).mpr rcLayout.separated),
   rc_x_separated,rcXOp,Option.get_mem rc_x_decoded⟩
def rcGrowRaw := saveSlot rcRaw 2 17
theorem rc_grow_raw : rcGrow.raw = rcRaw := by unfold rcGrow; rfl
theorem rc_grow_next : rcGrow.nextRaw = rcGrowRaw := congrArg (fun m => saveSlot m 2 17) rc_grow_raw
theorem rc_grow_map : finiteEncode rcGrow.next (rcGrow.step.1.2.2.ex.world.accounts account).storage
    (fun q => rcGrow.step.2.cells (complementKey false account q)) = some rcGrowRaw :=
  (rcGrow.reencode rfl).trans (congrArg some rc_grow_next)

end Solidity.Yul.Views.Controls

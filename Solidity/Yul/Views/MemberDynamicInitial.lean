import Solidity.Yul.Views.MemberDynamicLayout

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls
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
  ⟨.nil,⟨⟨⟨fun _ => Source.Account.empty (D := mdEnv.layout) (mdEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩
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

end Solidity.Yul.Views.Controls

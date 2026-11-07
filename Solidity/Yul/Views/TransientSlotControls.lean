import Solidity.Yul.Views.TransientSlots
import Solidity.Yul.Views.RootDeclarationControls

namespace Solidity.Yul.Views.TransientSlotControls
open Controls

def ps := rootRegistry
def ts := rootTempRegistry

def frame : Source.Fr := {this:=account,sender:=account,value:=0,static:=false,contract:="Slots",checked:=true,depth:=0,cd:=[]}
def state : Source.EMState rootEnv [] :=
  ⟨.nil,⟨⟨⟨fun _=>Source.Account.empty (D:=rootEnv.layout) (rootEnv.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩
def residual := initialPackedComplement ps ts (fun _=>0xbeef0000)
def initial : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨state.2.ex,residual⟩
def rawA : Roadmap.Word := 0xa5a51234
def rawB : Roadmap.Word := 0xb6b6abcd
def rawMax : Roadmap.Word := ⟨2^256-1,by omega⟩

def persistentPlan := (preparePackedFrame (ps:=ps) (ts:=ts) frame false 0 777).get (by decide)
def firstPlan := (preparePackedFrame (ps:=ps) (ts:=ts) frame true 0 rawA).get (by decide)
def secondPlan := (preparePackedFrame (ps:=ps) (ts:=ts) frame true 0 rawB).get (by decide)
def unknownPlan := (preparePackedFrame (ps:=ps) (ts:=ts) frame true 99 rawMax).get (by decide)
def caller := runPackedSource frame [persistentPlan,firstPlan] state residual
def child := runPackedSource frame [secondPlan,unknownPlan] caller.1.2 caller.2
def callerCore : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨caller.1.2.2.ex,caller.2⟩
def childCore : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership := ⟨child.1.2.2.ex,child.2⟩

theorem actual_transient_declaration : rootEnv.transientRoot (rootPath "temp")=true ∧
    ordinaryRootNames rootEnv none true=[rootName "temp"] := ⟨rfl,rfl⟩
theorem actual_bank_coordinates : (ts account).map (fun c=>(c.slot.val,c.field.offset,c.field.width))=[(0,0,2)] := rfl

theorem initial_nonzero_padding : transientSlotLoad ts initial account 0=some 0xbeef0000 := by decide

theorem caller_full_readback : transientSlotLoad ts callerCore account 0=some rawA ∧
    reencodePersistentSlot ps callerCore account 0=some 777 := by decide

theorem child_full_readback : transientSlotLoad ts childCore account 0=some rawB ∧
    transientSlotLoad ts childCore account 99=some rawMax ∧
    reencodePersistentSlot ps childCore account 0=some 777 := by decide

theorem typed_and_padding : (child.1.2.2.ex.transient.cells account).read (rootPath "temp")=
    some (.int 0xabcd (by decide)) ∧
    child.2.cells (complementKey true account 0)=0xb6b60000 := ⟨rfl,by decide⟩

theorem other_account : transientSlotLoad ts childCore 2 0=transientSlotLoad ts initial 2 0 := by decide

theorem source_prefix_and_journals : caller.1.1=.ok () ∧ child.1.1=.ok () ∧
    caller.1.2.2.ex.journal.length=2 ∧ caller.2.journal.length=2 ∧
    child.1.2.2.ex.journal.length=4 ∧ child.2.journal.length=4 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem static_keeps_caller : transientSlotStore? (ps:=ps) (ts:=ts) {frame with static:=true}
    0 rawB caller.1.2 caller.2=some ((.error (.revert []),caller.1.2),caller.2) :=
  transientSlot_static _ _ _ _ _ rfl (by decide)

theorem same_value_static_also_fails : transientSlotStore? (ps:=ps) (ts:=ts) {frame with static:=true}
    0 rawA caller.1.2 caller.2=some ((.error (.revert []),caller.1.2),caller.2) :=
  transientSlot_static _ _ _ _ _ rfl (by decide)

theorem actual_child_rollback : companionRollback (companionEnter callerCore account account 0 [] false) childCore=callerCore :=
  transientSlot_child_rollback frame [persistentPlan,firstPlan] [secondPlan,unknownPlan] state residual rfl

theorem committed_child_outer_rollback : companionRollback (companionEnter initial account account 0 [] false)
    (companionCommit (companionEnter callerCore account account 0 [] false) childCore)=initial :=
  transientSlot_outer_rollback_after_commit frame [persistentPlan,firstPlan] [secondPlan,unknownPlan] state residual rfl

/-- The concrete declaration-derived codec supplies the reset fact; no whole
view/zero safety premise is postulated. -/
theorem actual_zero_defaults (a : Roadmap.Address) (c : ScalarPath rootEnv.layout (rootEnv.lay a)) (member : c∈ts a) :
    ∃ v, Source.Val.default rootEnv.layout (rootEnv.lay a c.path)=some v ∧ (c.codec.encode v).val=0 := by
  change c∈[⟨rootPath "temp",0,intField unsigned16 0 (by decide),intCodec rootEnv.layout unsigned16 0 (by decide),.int unsigned16⟩] at member
  have same:=List.mem_singleton.mp member
  subst c
  exact ⟨.int 0 (by decide),rfl,rfl⟩

theorem every_slot_resets (a : Roadmap.Address) (slot : Roadmap.Word) :
    transientSlotLoad ts (companionEndTx childCore) a slot=some 0 :=
  transientSlot_endTx ts childCore actual_zero_defaults a slot

theorem persistent_survives : reencodePersistentSlot ps (companionEndTx childCore) account 0=some 777 := by
  rw [packedEndTx_persistent]
  exact child_full_readback.2.2

theorem journals_reset : (companionEndTx childCore).source.journal=[] ∧ (companionEndTx childCore).residual.journal=[] := ⟨rfl,rfl⟩

theorem actual_initial_MemOK : Source.MemOK rootEnv state.2.heap.ty state :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

theorem every_H_after_both (H : Source.HeapTy) (ok : Source.MemOK rootEnv H state) : Source.MemOK rootEnv H child.1.2 :=
  runPackedSource_MemOK frame [secondPlan,unknownPlan] caller.1.2 caller.2 H
    (runPackedSource_MemOK frame [persistentPlan,firstPlan] state residual H ok)

theorem padding_not_erased : transientSlotLoad ts childCore account 0≠some 0xabcd := by
  rw [child_full_readback.1]
  decide

theorem no_bank_alias : transientSlotLoad ts childCore account 0≠reencodePersistentSlot ps childCore account 0 := by
  rw [child_full_readback.1,child_full_readback.2.2]
  decide

end Solidity.Yul.Views.TransientSlotControls

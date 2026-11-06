import Solidity.Yul.Views.NestedMappingSlots
import Solidity.Yul.Views.TransientSlots
import Solidity.Yul.Views.Controls

namespace Solidity.Yul.Views.NestedMappingControls

def name : Source.DeclName := ⟨none,"table"⟩
def uintSyn : Source.Syn .typeName := .elem (.int false 256 (by decide))
def mapSyn (value : Source.Syn .typeName) : Source.Syn .typeName :=
  .mapping (.elem (.int false 256 (by decide)) (by decide)) none value none

def env : Source.Env := ⟨[
  ⟨.stateVar,"table",none,true,.stateVar (mapSyn (mapSyn uintSyn)) none none none false "table" .none⟩,
  ⟨.stateVar,"marker",none,true,.stateVar (.elem .bool) none none none false "marker" .none⟩]⟩
def mapping : NestedWordMappingRoot env name := ⟨2,by decide,rfl,rfl⟩
def first : mapping.Keys := ⟨[1,2],rfl⟩
def second : mapping.Keys := ⟨[1,3],rfl⟩
def third : mapping.Keys := ⟨[2,2],rfl⟩
def keys : List mapping.Keys := [first,second,third]
def fixed : Roadmap.Evm.Fixed where
  keccak bytes := (bytes[31]?.getD 0).toNat*16+(bytes[63]?.getD 0).toNat*8+16
  keccak_lt bytes := by
    have a := (bytes[31]?.getD 0).toNat_lt
    have b := (bytes[63]?.getD 0).toNat_lt
    omega
  precompile _ _ := none
  precompileGas _ _ := 0

def account : Roadmap.Address := 1
def path1 := (mapping.entry fixed first).path
def path2 := (mapping.entry fixed second).path
def path3 := (mapping.entry fixed third).path
def other : Source.SPath := ⟨⟨none,"marker"⟩,[]⟩
def empty : Source.Storage env.layout (env.lay account) := .empty
def explicit := empty.write path1 (.int 0 (by decide))
def changed := (empty.write path1 (.int 77 (by decide))).write path2 (.int 999 (by decide))
def residual : SlotView := fun _ => 0xa5

theorem prepared : prepareNestedWordMappingRoot env name=some mapping := rfl
theorem nonmapping_rejected : (prepareNestedWordMappingRoot env ⟨none,"marker"⟩).isNone=true := rfl

def tripleEnv : Source.Env := ⟨[
  ⟨.stateVar,"table",none,true,.stateVar (mapSyn (mapSyn (mapSyn uintSyn))) none none none false "table" .none⟩]⟩
def tripleRoot : NestedWordMappingRoot tripleEnv name := ⟨3,by decide,rfl,rfl⟩
def tripleKeys : tripleRoot.Keys := ⟨[1,2,3],rfl⟩
theorem triple_prepared : prepareNestedWordMappingRoot tripleEnv name=some tripleRoot := rfl
theorem triple_path : (tripleRoot.entry fixed tripleKeys).path.steps=
    [.key (Source.wordBytes 1),.key (Source.wordBytes 2),.key (Source.wordBytes 3)] := rfl

theorem key_count : first.val.length=mapping.depth := rfl
theorem malformed_depth : ([1] : List Roadmap.Word).length≠mapping.depth := by decide
theorem distinct : keys.Nodup := by decide
theorem regions : Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash fixed) (List.range 1)
    (locatedInventoryPreimages (mapping.entries fixed keys)) := by decide

theorem actual_paths : path1=⟨name,[.key (Source.wordBytes 1),.key (Source.wordBytes 2)]⟩ ∧
    path3=⟨name,[.key (Source.wordBytes 2),.key (Source.wordBytes 2)]⟩ := ⟨rfl,rfl⟩
theorem exact_slots : (mapping.registry fixed keys account).map (fun c=>c.slot.val)=[304,320,432] := by decide
/-- Intermediate preimages are retained, including shared prefixes. -/
theorem exact_preimages : locatedInventoryPreimages (mapping.entries fixed keys)=
    [.entry 1 0,.entry 2 32,.entry 1 0,.entry 3 32,.entry 2 0,.entry 2 48] := rfl

theorem arbitrary_store_roundtrip (s : Source.Storage env.layout (env.lay account)) :
    mapping.decode fixed keys account (mapping.encode fixed keys account s residual) s=some s :=
  mapping.decode_encode fixed keys distinct regions account s residual

theorem none_roundtrip : mapping.decode fixed keys account (mapping.encode fixed keys account empty residual) empty=some empty :=
  arbitrary_store_roundtrip empty
theorem explicit_default_roundtrip : mapping.decode fixed keys account (mapping.encode fixed keys account explicit residual) explicit=some explicit :=
  arbitrary_store_roundtrip explicit
theorem administrative_distinction : empty.cell path1=none ∧ explicit.cell path1=some (.int 0 (by decide)) := ⟨rfl,rfl⟩

def raw : SlotView := fun slot => if slot=304 then 77 else if slot=320 then 999 else if slot=432 then 0 else 0xa5

theorem decoded_changed : mapping.decode fixed keys account raw empty=some changed := rfl
theorem whole_map : mapping.encode fixed keys account changed raw=raw :=
  mapping.reencode_decode fixed keys distinct regions account empty changed raw decoded_changed

theorem other_path : changed.cell other=empty.cell other := rfl
theorem untouched_padding : mapping.encode fixed keys account changed raw 79=0xa5 := by decide
theorem root_header_residual : mapping.encode fixed keys account changed raw 0=0xa5 := by decide
theorem wrong_order_discriminates : (mapping.entry fixed first).location≠
    nestedMappingLocation (.root 0) ([2,1] : List Roadmap.Word) := by decide
theorem duplicate_inventory_rejected : locatedInventoryCheck (mapping.entries fixed [first,first])=false := by decide

def collision : Roadmap.Evm.Fixed where
  keccak _ := 0
  keccak_lt _ := by decide
  precompile _ _ := none
  precompileGas _ _ := 0

theorem collision_not_assumed_away : ¬ Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash collision) (List.range 1)
    (locatedInventoryPreimages (mapping.entries collision keys)) := by decide

/-- Real source operations use the derived nested registrations. Transient
mapping declarations are not introduced by the empty transient registry. -/
def ps (a : Roadmap.Address) := mapping.registry fixed keys a
def ts (_ : Roadmap.Address) : List (ScalarPath env.layout (env.lay account)) := []
def frame : Source.Fr := {this:=account,sender:=account,value:=0,static:=false,contract:="Nested",checked:=true,depth:=0,cd:=[]}
def state : Source.EMState env [] :=
  ⟨.nil,⟨⟨⟨fun _=>Source.Account.empty (D:=env.layout) (env.lay account)⟩,.empty,[]⟩,.empty,[],[],⟨[],.nil⟩, Source.FailureExecution.Cursor.empty⟩⟩
def complement := initialPackedComplement ps ts (fun _=>0xa5)
def plan1 := (preparePackedFrame (ps:=ps) (ts:=ts) frame false 304 77).get (by decide)
def plan2 := (preparePackedFrame (ps:=ps) (ts:=ts) frame false 320 999).get (by decide)
def caller := runPackedSource frame [plan1] state complement
def child := runPackedSource frame [plan2] caller.1.2 caller.2
def initial : ResidualCompanion env.layout env.lay env.lay complementCarrierOwnership := ⟨state.2.ex,complement⟩
def callerCore : ResidualCompanion env.layout env.lay env.lay complementCarrierOwnership := ⟨caller.1.2.2.ex,caller.2⟩
def childCore : ResidualCompanion env.layout env.lay env.lay complementCarrierOwnership := ⟨child.1.2.2.ex,child.2⟩

theorem source_success : caller.1.1=.ok () ∧ child.1.1=.ok () := ⟨rfl,rfl⟩
theorem source_reads : (child.1.2.2.ex.world.accounts account).storage.read path1=some (.int 77 (by decide)) ∧
    (child.1.2.2.ex.world.accounts account).storage.read path2=some (.int 999 (by decide)) := ⟨rfl,rfl⟩
theorem raw_reads : reencodePersistentSlot ps childCore account 304=some 77 ∧
    reencodePersistentSlot ps childCore account 320=some 999 ∧
    reencodePersistentSlot ps childCore account 79=some 0xa5 := by decide

theorem static_preserves_caller : runPackedSource {frame with static:=true} [plan2] caller.1.2 caller.2=
    ((.error (.revert []),caller.1.2),caller.2) := rfl

theorem child_rollback : companionRollback (companionEnter callerCore account account 0 [] false) childCore=callerCore :=
  transientSlot_child_rollback frame [plan1] [plan2] state complement rfl

theorem enclosing_rollback : companionRollback (companionEnter initial account account 0 [] false)
    (companionCommit (companionEnter callerCore account account 0 [] false) childCore)=initial :=
  transientSlot_outer_rollback_after_commit frame [plan1] [plan2] state complement rfl

theorem persistent_endTx : reencodePersistentSlot ps (companionEndTx childCore) account 304=some 77 := by
  rw [packedEndTx_persistent]
  exact raw_reads.1

theorem every_H (H : Source.HeapTy) (ok : Source.MemOK env H state) : Source.MemOK env H child.1.2 :=
  runPackedSource_MemOK frame [plan2] caller.1.2 caller.2 H
    (runPackedSource_MemOK frame [plan1] state complement H ok)

theorem other_account : reencodePersistentSlot ps childCore 2 304=reencodePersistentSlot ps initial 2 304 := by decide

theorem actual_initial_MemOK : Source.MemOK env state.2.heap.ty state :=
  ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩

end Solidity.Yul.Views.NestedMappingControls

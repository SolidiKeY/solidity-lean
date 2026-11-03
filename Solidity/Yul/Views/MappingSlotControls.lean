import Solidity.Yul.Views.MappingSlots
import Solidity.Yul.Views.Controls

namespace Solidity.Yul.Views.MappingSlotControls

def name : Source.DeclName := ⟨none,"table"⟩
def uintSyn : Source.Syn .typeName := .elem (.int false 256 (by decide))
def env : Source.Env := ⟨[
  ⟨.stateVar,"table",none,true,.stateVar (.mapping (.elem (.int false 256 (by decide)) (by decide)) none uintSyn none) none none none false "table" .none⟩,
  ⟨.stateVar,"marker",none,true,.stateVar (.elem .bool) none none none false "marker" .none⟩]⟩

def mapping : WordMappingRoot env name := ⟨rfl,rfl⟩
def fixed : Roadmap.Evm.Fixed where
  keccak bytes := if bytes=layoutPreimageBytes (.entry 1 0) then 16 else 32
  keccak_lt bytes := by split <;> decide
  precompile _ _ := none
  precompileGas _ _ := 0

def keys : List Roadmap.Word := [1,2]
def account : Roadmap.Address := 1
def first := (mapping.entry fixed 1).path
def second := (mapping.entry fixed 2).path
def other : Source.SPath := ⟨⟨none,"marker"⟩,[]⟩
def empty : Source.Storage env.layout (env.lay account) := .empty
def explicit := empty.write first (.int 0 (by decide))
def changed := (empty.write first (.int 77 (by decide))).write second (.int 999 (by decide))
def residual : SlotView := fun _=>0xa5

theorem prepared : prepareWordMappingRoot env name=some mapping := rfl
theorem two_keys_distinct : keys.Nodup := by decide
theorem regions : Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash fixed) (List.range 1)
    (locatedInventoryPreimages (mapping.entries fixed keys)) := by decide

theorem exact_slots : ((mapping.entry fixed 1).registration account).slot=16 ∧
    ((mapping.entry fixed 2).registration account).slot=32 := by decide

theorem exact_preimages : locatedInventoryPreimages (mapping.entries fixed keys)=[.entry 1 0,.entry 2 0] := rfl

theorem whole_store_roundtrip (store : Source.Storage env.layout (env.lay account)) :
    mapping.decode fixed keys account (mapping.encode fixed keys account store residual) store=some store :=
  mapping.decode_encode fixed keys two_keys_distinct regions account store residual

theorem unwritten_and_written_default : empty.cell first=none ∧ explicit.cell first=some (.int 0 (by decide)) ∧
    mapping.decode fixed keys account (mapping.encode fixed keys account empty residual) empty=some empty ∧
    mapping.decode fixed keys account (mapping.encode fixed keys account explicit residual) explicit=some explicit :=
  ⟨rfl,rfl,whole_store_roundtrip empty,whole_store_roundtrip explicit⟩

theorem encoded_reads : mapping.encode fixed keys account changed residual 16=77 ∧
    mapping.encode fixed keys account changed residual 32=999 ∧
    mapping.encode fixed keys account changed residual 0=0xa5 ∧
    mapping.encode fixed keys account changed residual 79=0xa5 := by decide

theorem actual_changed_writeback : mapping.decode fixed keys account (mapping.encode fixed keys account changed residual) empty=some changed := rfl

theorem entire_raw_reconstruction : mapping.encode fixed keys account changed
    (mapping.encode fixed keys account changed residual)=mapping.encode fixed keys account changed residual :=
  mapping.reencode_decode fixed keys two_keys_distinct regions account empty changed _ actual_changed_writeback

theorem unchanged_view : mapping.decode fixed keys account (mapping.encode fixed keys account changed residual) changed=some changed :=
  mapping.writeback_unchanged fixed keys account changed _
    (finiteEncode_view _ _ _ _ (mapping.separated fixed keys two_keys_distinct regions account)
      (mapping.encode_spec fixed keys account changed residual))

theorem outside_administration (raw : SlotView) (out : Source.Storage env.layout (env.lay account))
    (decoded : mapping.decode fixed keys account raw changed=some out) : out.cell other=changed.cell other := by
  apply mapping.decode_other fixed keys account changed out raw decoded
  intro c member
  change c∈[(mapping.entry fixed 1).registration account,(mapping.entry fixed 2).registration account] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> decide

theorem missing_root : prepareWordMappingRoot env ⟨none,"absent"⟩=none := rfl
theorem wrong_type : prepareWordMappingRoot env ⟨none,"marker"⟩=none := rfl
theorem duplicate_detected : locatedInventoryCheck (mapping.entries fixed [1,1])=false := by rfl

def collisionFixed : Roadmap.Evm.Fixed := {fixed with keccak:=fun _=>0,keccak_lt:=fun _=>by decide}
theorem collision_not_a_view_premise : ¬Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash collisionFixed) (List.range 1)
    (locatedInventoryPreimages (mapping.entries collisionFixed keys)) := by decide

theorem keys_not_aliases : first≠second := by
  intro same
  have impossible:=mapping.key_path_inj fixed 1 2 same
  cases impossible

end Solidity.Yul.Views.MappingSlotControls

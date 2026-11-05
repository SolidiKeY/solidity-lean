import Solidity.Yul.Views.LocatedInventory
import Solidity.Yul.Views.FiniteResidual

namespace Solidity.Yul.Views

/-- The actual persistent source mapping declaration. Physical root0 is the
existing HashedLayout owner placement, NOT an inferred global declaration slot. -/
structure WordMappingRoot (E : Source.Env) (root : Source.DeclName) : Type where
  found : E.rootTy root=some (.mapping (.int .u256) (.int .u256))
  persistent : E.transientRoot ⟨root,[]⟩=false

def prepareWordMappingRoot (E : Source.Env) (root : Source.DeclName) : Option (WordMappingRoot E root) :=
  if found : E.rootTy root=some (.mapping (.int .u256) (.int .u256)) then
    if bank : E.transientRoot ⟨root,[]⟩=false then some ⟨found,bank⟩ else none
  else none

def WordMappingRoot.entry {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (key : Roadmap.Word) : LocatedWord E fixed root (.map .word) [.key key.val] where
  rootType := .mapping (.int .u256) (.int .u256)
  rootFound := mapping.found
  layout := .mapping .word
  sourceSteps := [.key (Source.wordBytes key)]
  translated := by simp only [sourceLayoutSteps,dif_pos key.isLt,Except.map]
  reached := .word
  location := .hash key.val (.root 0) 0
  located := rfl
  positive := by decide
  cellType := by
    simp only [Source.Env.cellTy,Source.Env.pathTy,mapping.found,List.foldl_cons,List.foldl_nil,
      Option.bind_some,Source.Env.stepTy,Option.map_some,Option.getD_some,Source.STy.cell]
    rfl

def WordMappingRoot.entries {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) : List (LocatedEntry E fixed root (.map .word)) :=
  keys.map (fun key=>(⟨[.key key.val],mapping.entry fixed key⟩ : LocatedEntry E fixed root (.map .word)))

def WordMappingRoot.registry {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (a : Roadmap.Address) := locatedInventory (mapping.entries fixed keys) a

theorem WordMappingRoot.key_path_inj {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (left right : Roadmap.Word) (same : (mapping.entry fixed left).path=(mapping.entry fixed right).path) : left=right := by
  have steps:=congrArg Source.SPath.steps same
  change [Source.Step.key (Source.wordBytes left)]=[Source.Step.key (Source.wordBytes right)] at steps
  have bytes:=Source.Step.key.inj (List.cons.inj steps).1
  have words:=congrArg Source.beValue bytes
  rw [Source.wordBytes_value,Source.wordBytes_value] at words
  exact Fin.ext words

theorem WordMappingRoot.apart {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (distinct : keys.Nodup) : locatedInventoryApart (mapping.entries fixed keys) := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ distinct
  intro left right _ _ ne
  constructor
  · exact fun same=>ne (mapping.key_path_inj fixed left right same)
  · intro same
    have values := (Storage.Loc.hash.inj same).1
    exact ne (Fin.ext values)

/-- The SAME per-run region condition as HashedLayout, with root/region
bounds derived for the single-word mapping. No global hash injection. -/
theorem WordMappingRoot.separated {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (distinct : keys.Nodup)
    (regions : Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash fixed) (List.range 1)
      (locatedInventoryPreimages (mapping.entries fixed keys))) (a : Roadmap.Address) :
    finiteSeparated (mapping.registry fixed keys a) :=
  located_inventory_separated (mapping.entries fixed keys) 1 1 (show Storage.STy.Fits 1 (.map .word) from ⟨by decide,trivial⟩) (by decide) (by decide) (by decide)
    regions (mapping.apart fixed keys distinct) a

theorem WordMappingRoot.defaults {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (a : Roadmap.Address) :
    ∀ c ∈ mapping.registry fixed keys a, ∃ v, Source.Val.default E.layout (E.lay a c.path)=some v := by
  intro c member
  obtain ⟨entry,_,same⟩:=List.mem_map.mp member
  subst c
  change ∃ v, Source.Val.default E.layout (E.cellTy entry.2.path)=some v
  rw [show E.cellTy entry.2.path=.int .u256 from entry.2.cellType]
  exact ⟨.int 0 (by decide),rfl⟩

theorem WordMappingRoot.encode_ready {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView) :
    (finiteEncode (mapping.registry fixed keys a) s residual).isSome=true := by
  obtain ⟨out,encoded⟩:=finiteEncode_exists (mapping.registry fixed keys a) s residual (by
    intro c member
    obtain ⟨value,zero⟩:=mapping.defaults fixed keys a c member
    exact scalar_read_available c.path value zero s)
  rw [encoded]
  rfl

/-- Total constructive finite mapping encoder; the finite keys are the actual
run inventory, not an arbitrary length cap or a claim of infinite hash injection. -/
def WordMappingRoot.encode {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView) : SlotView :=
  (finiteEncode (mapping.registry fixed keys a) s residual).get (mapping.encode_ready fixed keys a s residual)

def WordMappingRoot.decode {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (a : Roadmap.Address) (raw : SlotView) (original : Source.Storage E.layout (E.lay a)) :=
  finiteWriteback (mapping.registry fixed keys a) raw original

theorem WordMappingRoot.encode_spec {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView) :
    finiteEncode (mapping.registry fixed keys a) s residual=some (mapping.encode fixed keys a s residual) :=
  (Option.some_get _).symm

/-- decode o encode preserves the WHOLE actual administrative store, including
unwritten versus explicitly written defaults and all nonselected paths. -/
theorem WordMappingRoot.decode_encode {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (distinct : keys.Nodup)
    (regions : Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash fixed) (List.range 1)
      (locatedInventoryPreimages (mapping.entries fixed keys)))
    (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView) :
    mapping.decode fixed keys a (mapping.encode fixed keys a s residual) s=some s :=
  finiteWriteback_encode _ _ _ _ (mapping.separated fixed keys distinct regions a) (mapping.encode_spec fixed keys a s residual)

theorem WordMappingRoot.writeback_unchanged {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (raw : SlotView)
    (view : finiteView (mapping.registry fixed keys a) s raw) : mapping.decode fixed keys a raw s=some s :=
  finiteWriteback_unchanged _ _ _ view

theorem WordMappingRoot.encode_unowned {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (q : Roadmap.Word) (unowned : ∀ c ∈ mapping.registry fixed keys a, q≠c.slot) :
    mapping.encode fixed keys a s residual q=residual q :=
  finiteEncode_unowned_slot _ _ _ _ (mapping.encode_spec fixed keys a s residual) q (fun c member=>Ne.symm (unowned c member))

/-- The complete supplied physical map is reconstructed after successful
canonical writeback, including every nonselected residual slot. -/
theorem WordMappingRoot.reencode_decode {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (distinct : keys.Nodup)
    (regions : Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash fixed) (List.range 1)
      (locatedInventoryPreimages (mapping.entries fixed keys)))
    (a : Roadmap.Address) (s out : Source.Storage E.layout (E.lay a)) (raw : SlotView)
    (decoded : mapping.decode fixed keys a raw s=some out) : mapping.encode fixed keys a out raw=raw := by
  have encoded:=finiteEncode_after_writeback (mapping.registry fixed keys a) raw s out
    (mapping.separated fixed keys distinct regions a) decoded
  exact Option.some.inj ((mapping.encode_spec fixed keys a out raw).symm.trans encoded)

theorem WordMappingRoot.decode_other {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List Roadmap.Word) (a : Roadmap.Address) (s out : Source.Storage E.layout (E.lay a)) (raw : SlotView)
    (decoded : mapping.decode fixed keys a raw s=some out) (path : Source.SPath)
    (outside : ∀ c ∈ mapping.registry fixed keys a, path≠c.path) : out.cell path=s.cell path :=
  finiteWriteback_other _ _ _ _ decoded path outside

/-- Exact approved Fixed preimage: key word || root word, each big-endian32. -/
theorem WordMappingRoot.slot_hash {E root} (mapping : WordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (key : Roadmap.Word) (a : Roadmap.Address) :
    ((mapping.entry fixed key).registration a).slot.val=fixed.keccak (layoutPreimageBytes (.entry key.val 0)) := by
  change (fixed.keccak (layoutPreimageBytes (.entry key.val 0))+0)%(2^256)=_
  rw [Nat.add_zero,Nat.mod_eq_of_lt (fixed.keccak_lt _)]

end Solidity.Yul.Views

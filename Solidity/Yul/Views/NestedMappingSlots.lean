import Solidity.Yul.Views.NestedMappingLayout

namespace Solidity.Yul.Views

private def mappingLocationKeys : Storage.Loc → List Nat
  | .root _ => []
  | .hash k parent _ => mappingLocationKeys parent ++ [k]
  | .data parent _ => mappingLocationKeys parent

private theorem mappingLocationKeys_chain (loc : Storage.Loc) (keys : List Roadmap.Word) :
    mappingLocationKeys (nestedMappingLocation loc keys)=mappingLocationKeys loc ++ keys.map Fin.val := by
  induction keys generalizing loc with
  | nil => simp only [nestedMappingLocation,List.map_nil,List.append_nil]
  | cons k ks ih =>
    rw [nestedMappingLocation,ih]
    simp only [mappingLocationKeys,List.map_cons,List.append_assoc,List.singleton_append]

private theorem mappingWordValues_inj (left right : List Roadmap.Word)
    (same : left.map Fin.val=right.map Fin.val) : left=right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons y ys => cases same
  | cons x xs ih =>
    cases right with
    | nil => cases same
    | cons y ys =>
      have pair := List.cons.inj same
      have head : x=y := Fin.ext pair.1
      have tail := ih ys pair.2
      rw [head,tail]

private theorem mappingSteps_values (keys : List Roadmap.Word) :
    (nestedMappingSteps keys).map (fun step => match step with
      | .key bytes => Source.beValue bytes
      | _ => 0)=keys.map Fin.val := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    simp only [nestedMappingSteps,List.map_cons,Source.wordBytes_value] at *
    rw [ih]

namespace NestedWordMappingRoot

def entries {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) : List (LocatedEntry E fixed root (nestedMappingTree mapping.depth)) :=
  keys.map (fun ks => ⟨nestedMappingAccess ks.val,mapping.entry fixed ks⟩)

def registry {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (a : Roadmap.Address) := locatedInventory (mapping.entries fixed keys) a

theorem path_inj {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (left right : mapping.Keys) (same : (mapping.entry fixed left).path=(mapping.entry fixed right).path) : left=right := by
  apply Subtype.ext
  have steps := congrArg Source.SPath.steps same
  change nestedMappingSteps left.val=nestedMappingSteps right.val at steps
  have values := congrArg (List.map (fun step => match step with
    | Source.Step.key bytes => Source.beValue bytes
    | _ => 0)) steps
  rw [mappingSteps_values,mappingSteps_values] at values
  exact mappingWordValues_inj left.val right.val values

theorem location_inj {E root} (mapping : NestedWordMappingRoot E root)
    (left right : mapping.Keys)
    (same : nestedMappingLocation (.root 0) left.val=nestedMappingLocation (.root 0) right.val) : left=right := by
  apply Subtype.ext
  have values := congrArg mappingLocationKeys same
  simp only [mappingLocationKeys_chain,mappingLocationKeys,List.nil_append] at values
  exact mappingWordValues_inj left.val right.val values

theorem apart {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (distinct : keys.Nodup) : locatedInventoryApart (mapping.entries fixed keys) := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ distinct
  intro left right _ _ ne
  exact ⟨fun same => ne (mapping.path_inj fixed left right same),
    fun same => ne (mapping.location_inj left right same)⟩

/-- Numeric separation uses the owner's exact finite-run region premise for
ALL intermediate preimages. Symbolic path injectivity is proved separately. -/
theorem separated {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (distinct : keys.Nodup)
    (regions : Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash fixed) (List.range 1)
      (locatedInventoryPreimages (mapping.entries fixed keys))) (a : Roadmap.Address) :
    finiteSeparated (mapping.registry fixed keys a) :=
  located_inventory_separated (mapping.entries fixed keys) 1 1 (nestedMapping_fits mapping.depth)
    (by rw [nestedMapping_size]; exact Nat.le_refl 1) (by decide) (by decide) regions (mapping.apart fixed keys distinct) a

theorem defaults {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (a : Roadmap.Address) :
    ∀ c ∈ mapping.registry fixed keys a, ∃ v, Source.Val.default E.layout (E.lay a c.path)=some v := by
  intro c member
  obtain ⟨entry,_,same⟩ := List.mem_map.mp member
  subst c
  change ∃ v, Source.Val.default E.layout (E.cellTy entry.2.path)=some v
  rw [show E.cellTy entry.2.path=.int .u256 from entry.2.cellType]
  exact ⟨.int 0 (by decide),rfl⟩

theorem encode_ready {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView) :
    (finiteEncode (mapping.registry fixed keys a) s residual).isSome=true := by
  obtain ⟨out,encoded⟩ := finiteEncode_exists (mapping.registry fixed keys a) s residual (by
    intro c member
    obtain ⟨value,zero⟩ := mapping.defaults fixed keys a c member
    exact scalar_read_available c.path value zero s)
  rw [encoded]
  rfl

def encode {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView) : SlotView :=
  (finiteEncode (mapping.registry fixed keys a) s residual).get (mapping.encode_ready fixed keys a s residual)

def decode {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (a : Roadmap.Address) (raw : SlotView) (original : Source.Storage E.layout (E.lay a)) :=
  finiteWriteback (mapping.registry fixed keys a) raw original

theorem encode_spec {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView) :
    finiteEncode (mapping.registry fixed keys a) s residual=some (mapping.encode fixed keys a s residual) :=
  (Option.some_get _).symm

theorem decode_encode {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (distinct : keys.Nodup)
    (regions : Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash fixed) (List.range 1)
      (locatedInventoryPreimages (mapping.entries fixed keys)))
    (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView) :
    mapping.decode fixed keys a (mapping.encode fixed keys a s residual) s=some s :=
  finiteWriteback_encode _ _ _ _ (mapping.separated fixed keys distinct regions a) (mapping.encode_spec fixed keys a s residual)

theorem writeback_unchanged {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (raw : SlotView)
    (view : finiteView (mapping.registry fixed keys a) s raw) : mapping.decode fixed keys a raw s=some s :=
  finiteWriteback_unchanged _ _ _ view

theorem reencode_decode {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (distinct : keys.Nodup)
    (regions : Hash.RegionsDisjoint (2^256) 1 (fixedLayoutHash fixed) (List.range 1)
      (locatedInventoryPreimages (mapping.entries fixed keys)))
    (a : Roadmap.Address) (s out : Source.Storage E.layout (E.lay a)) (raw : SlotView)
    (decoded : mapping.decode fixed keys a raw s=some out) : mapping.encode fixed keys a out raw=raw := by
  have encoded := finiteEncode_after_writeback (mapping.registry fixed keys a) raw s out
    (mapping.separated fixed keys distinct regions a) decoded
  exact Option.some.inj ((mapping.encode_spec fixed keys a out raw).symm.trans encoded)

theorem encode_unowned {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a)) (residual : SlotView)
    (q : Roadmap.Word) (outside : ∀ c ∈ mapping.registry fixed keys a, q≠c.slot) :
    mapping.encode fixed keys a s residual q=residual q :=
  finiteEncode_unowned_slot _ _ _ _ (mapping.encode_spec fixed keys a s residual) q (fun c member => Ne.symm (outside c member))

theorem decode_other {E root} (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : List mapping.Keys) (a : Roadmap.Address) (s out : Source.Storage E.layout (E.lay a)) (raw : SlotView)
    (decoded : mapping.decode fixed keys a raw s=some out) (path : Source.SPath)
    (outside : ∀ c ∈ mapping.registry fixed keys a, path≠c.path) : out.cell path=s.cell path :=
  finiteWriteback_other _ _ _ _ decoded path outside

end NestedWordMappingRoot
end Solidity.Yul.Views

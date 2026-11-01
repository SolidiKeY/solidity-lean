import Solidity.Yul.Views.LocatedSeparation

namespace Solidity.Yul.Views

abbrev LocatedEntry (E : Source.Env) (fixed : Roadmap.Evm.Fixed) (root : Source.DeclName) (tree : Storage.STy) :=
  (access : List Storage.Step) × LocatedWord E fixed root tree access

def locatedInventoryPreimages {E fixed root tree} (es : List (LocatedEntry E fixed root tree)) : List Storage.Pre :=
  es.flatMap (fun e => e.2.location.pres (2^256) (fixedLayoutHash fixed))

def locatedInventory {E fixed root tree} (es : List (LocatedEntry E fixed root tree)) (a : Roadmap.Address) :=
  es.map (fun e => e.2.registration a)

/-- Symbolic/source alias diagnostics, prior to the separate real per-run region
condition. This checks actual computed terms, not a desired numeric separation. -/
def locatedInventoryApart {E fixed root tree} (es : List (LocatedEntry E fixed root tree)) : Prop :=
  es.Pairwise (fun e f => e.2.path ≠ f.2.path ∧ e.2.location ≠ f.2.location)

theorem located_inventory_separated {E fixed root tree}
    (es : List (LocatedEntry E fixed root tree)) (L R : Nat) (fits : tree.Fits L) (rootFits : tree.size ≤ R)
    (lb : L ≤ 2^256) (rb : R ≤ 2^256)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) (List.range R) (locatedInventoryPreimages es))
    (apart : locatedInventoryApart es) (a : Roadmap.Address) : finiteSeparated (locatedInventory es a) := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ apart
  intro e f em fm distinct
  refine ⟨distinct.1,Or.inl ?_⟩
  intro same
  apply distinct.2
  have numeric := congrArg Fin.val same
  have separated := Storage.located_word_inj (fixedLayoutHash_lt fixed) lb rb regions fits rootFits
    e.2.located f.2.located e.2.positive f.2.positive
    (fun x hx => List.mem_flatMap.mpr ⟨e,em,hx⟩)
    (fun x hx => List.mem_flatMap.mpr ⟨f,fm,hx⟩)
    (show (e.2.location.add 0).word (2^256) (fixedLayoutHash fixed) =
      (f.2.location.add 0).word (2^256) (fixedLayoutHash fixed) from by
      simpa only [Storage.Loc.add_zero] using numeric)
  simpa only [Storage.Loc.add_zero] using separated

def locatedInventoryCheck {E fixed root tree} : List (LocatedEntry E fixed root tree) → Bool
  | [] => true
  | e::es => es.all (fun f => decide (e.2.path ≠ f.2.path ∧ e.2.location ≠ f.2.location)) && locatedInventoryCheck es

theorem locatedInventoryCheck_iff {E fixed root tree} (es : List (LocatedEntry E fixed root tree)) :
    locatedInventoryCheck es = true ↔ locatedInventoryApart es := by
  induction es with
  | nil => exact ⟨fun _ => .nil,fun _ => rfl⟩
  | cons e es ih =>
    simp only [locatedInventoryCheck,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,ih,
      locatedInventoryApart,List.pairwise_cons]

noncomputable def locatedInventoryLocation {E fixed root tree}
    (es : List (LocatedEntry E fixed root tree)) (a : Roadmap.Address)
    (c : {c // c ∈ locatedInventory es a}) : Storage.Loc :=
  (Classical.choose (List.mem_map.mp c.property)).2.location

theorem locatedInventoryLocation_slot {E fixed root tree}
    (es : List (LocatedEntry E fixed root tree)) (a : Roadmap.Address)
    (c : {c // c ∈ locatedInventory es a}) :
    c.val.slot = physicalSlot (fixedLayoutHash fixed) (locatedInventoryLocation es a c) := by
  have equal := (Classical.choose_spec (List.mem_map.mp c.property)).2
  rw [← equal]
  rfl

/-- Finite concrete instance removes supplied loc/slot/default fields. Its
only layout premises are the owner's bounds/regions and checked symbolic aliases. -/
noncomputable def locatedInventoryObligations {E fixed root tree}
    (es : List (LocatedEntry E fixed root tree)) (L R : Nat) (fits : tree.Fits L) (rootFits : tree.size ≤ R)
    (lb : L ≤ 2^256) (rb : R ≤ 2^256)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) (List.range R) (locatedInventoryPreimages es))
    (checked : locatedInventoryCheck es = true) (a : Roadmap.Address) (residual : SlotView) :
    ScalarStorageObligations E.layout (E.lay a) {c // c ∈ locatedInventory es a} :=
  finiteScalarObligations _ (located_inventory_separated es L R fits rootFits lb rb regions
      ((locatedInventoryCheck_iff es).mp checked) a)
    (fixedLayoutHash fixed) (locatedInventoryLocation es a) (locatedInventoryLocation_slot es a)
    (by
      intro c member
      obtain ⟨entry,_,same⟩ := List.mem_map.mp member
      subst c
      change ∃ v, Source.Val.default E.layout (E.cellTy entry.2.path) = some v
      rw [show E.cellTy entry.2.path = .int .u256 from entry.2.cellType]
      exact ⟨.int 0 (by decide),rfl⟩) residual

theorem located_inventory_encode_identity {E fixed root tree}
    (es : List (LocatedEntry E fixed root tree)) (L R : Nat) (fits : tree.Fits L) (rootFits : tree.size ≤ R)
    (lb : L ≤ 2^256) (rb : R ≤ 2^256)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) (List.range R) (locatedInventoryPreimages es))
    (apart : locatedInventoryApart es) (a : Roadmap.Address) (s : Source.Storage E.layout (E.lay a))
    (m out : SlotView) (encoded : finiteEncode (locatedInventory es a) s m = some out) :
    finiteWriteback (locatedInventory es a) out s = some s :=
  finiteWriteback_encode _ _ _ _ (located_inventory_separated es L R fits rootFits lb rb regions apart a) encoded

end Solidity.Yul.Views

import Solidity.Semantics.IntrinsicStorage.Preimages.Frames

/-! Structural coverage regressions. These proofs use actual dependent values
and arbitrary installed accounts; they never evaluate the preimage universe. -/
namespace Solidity.Examples.IntrinsicStorage.Preimages.Frames

open Solidity.Semantics Solidity.Semantics.IntrinsicStorage Solidity.Storage

/-- A `T[][]` with one live and one shadow empty array retains both data origins,
even though neither inner array contains an element. -/
example (E : Ty) (o : Nat) :
    let inner : SVal (.ref (.array E)) := .array .nil .nil (by decide)
    let outer := SVal.array (.cons inner .nil) (.cons inner .nil) (by decide)
    encoded (.data ((Storage.Loc.data (.root o) 0).word (2 ^ 256) keccakH)) ∈
      valueInputs outer (.root o) ∧
    encoded (.data ((Storage.Loc.data (.root o) (size (.ref (.array E)))).word (2 ^ 256) keccakH)) ∈
      valueInputs outer (.root o) := by
  dsimp only
  constructor
  · apply valueInputs_covers _ (.root o) True.intro
    apply ValueInput.child (Child.live _ _ _ (i := 0) (v := .array .nil .nil (by decide))
        (by simp only [SVec.toList_cons, List.getElem?_cons_zero]) (.root o))
    exact ⟨_, _, _, .refl _ _, .data _ _ _ _⟩
  · apply valueInputs_covers _ (.root o) True.intro
    apply ValueInput.child (Child.shadow _ _ _ (i := 0) (v := .array .nil .nil (by decide))
        (by simp only [SList.toList_cons, List.getElem?_cons_zero]) (.root o))
    exact ⟨_, _, _, .refl _ _, .data _ _ _ _⟩

/-- For `mapping(K => T[])`, an overwritten explicit entry still contributes
its nested array origin, regardless of the current entry or default value. -/
example {K : PrimTy} {E : Ty} (k : K.Denote)
    (current fallback : SVal (.ref (.array E))) {n : Nat}
    (vs : SVec E n) (sh : SList E) (hn : n < 2 ^ 256) (o : Nat) :
    let old := SVal.array vs sh hn
    let entries := SMap.cons k current (.cons k old .nil)
    encoded (.data ((Storage.Loc.hash (keyWord k) (.root o) 0).word (2 ^ 256) keccakH)) ∈
      valueInputs (.map entries fallback) (.root o) := by
  dsimp only
  apply valueInputs_covers _ (.root o) True.intro
  apply ValueInput.child (Child.entry _ _ (k := k) (v := .array vs sh hn) ?_ _)
  · exact ⟨_, _, _, .refl _ _, .data vs sh hn _⟩
  · rw [SMap.toList_cons, SMap.toList_cons, SMap.toList_nil]
    exact List.mem_cons_of_mem _ (List.mem_cons_self)

/-- Every absent key in `mapping(K => T[])` contributes the arbitrary default
array's origin; there is no finite list of keys supplied to the coverage law. -/
example {K : PrimTy} {E : Ty} (k : K.Denote) {n : Nat}
    (vs : SVec E n) (sh : SList E) (hn : n < 2 ^ 256) (o : Nat) :
    encoded (.data ((Storage.Loc.hash (keyWord k) (.root o) 0).word (2 ^ 256) keccakH)) ∈
      valueInputs (.map (SMap.nil (K := K)) (.array vs sh hn)) (.root o) := by
  apply valueInputs_covers _ (.root o) True.intro
  apply ValueInput.child (Child.fallback _ _ k (by simp only [SMap.toList_nil, lookupBy]) (.root o))
  exact ⟨_, _, _, .refl _ _, .data vs sh hn _⟩

/-- An installed account's array field contributes its origin even at length
zero. The world, address, catalog, other accounts and funding stay arbitrary. -/
example {K : Type} {contracts : K → Contract} (w : ContractWorld.World contracts)
    (a : ContractWorld.Address) (k : K) (st : Solidity.Storage (contracts k))
    (ha : w.accounts a = some ⟨k, st⟩) {f : Name} {E : Ty}
    (hf : lookupBy f (contracts k).vars = some (.ref (.array E)))
    (sh : SList E) (hv : st.get hf = SVal.array .nil sh (by decide)) :
    encoded (.data ((Storage.Loc.root (offsetIn (contracts k).vars f)).word (2 ^ 256) keccakH)) ∈
      stored w := by
  apply (mem_stored w _).mpr
  refine ⟨_, ⟨a, k, st, ha, _, st.get hf, offsetIn _ f, fieldCell_get st hf, ?_⟩, rfl⟩
  rw [hv]
  exact ⟨_, _, _, .refl _ _, .data _ _ _ _⟩

end Solidity.Examples.IntrinsicStorage.Preimages.Frames

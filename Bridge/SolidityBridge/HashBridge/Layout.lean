import SolidityBridge.HashBridge.Queries

/-! Per-observed-query storage separation for the actual opaque EVM hash.
No global injectivity or native/mathematical hash equality is installed. -/
namespace Solidity.HashBridge

def actualPreHash (pre : Storage.Pre) : Nat := actualHash (Storage.encode pre)

theorem entry_words (key parent : EvmYul.UInt256) :
    (Storage.Pre.entry key.toNat parent.toNat).Words := ⟨key.val.isLt,parent.val.isLt⟩

theorem data_words (parent : EvmYul.UInt256) :
    (Storage.Pre.data parent.toNat).Words := parent.val.isLt

/-- Only the actually included encoded preimages inherit the per-query premise. -/
theorem actual_regions_of_queries {N L : Nat} {roots : List Nat}
    {pres : List Storage.Pre} {queries : List (List Nat)}
    (hw : ∀ p ∈ pres, p.Words)
    (hq : ∀ p ∈ pres, Storage.encode p ∈ queries)
    (hr : Hash.RegionsDisjoint N L actualHash roots queries) :
    Hash.RegionsDisjoint N L actualPreHash roots pres := by
  constructor
  · intro p hp q hq' hne
    exact hr.1 _ (hq p hp) _ (hq q hq')
      (fun he => hne (Storage.encode_inj (hw p hp) (hw q hq') he))
  · intro p hp r hh
    exact hr.2 _ (hq p hp) r hh

/-- A concrete importing client of the proved layout, retaining actual native
hash output rather than identifying it with pure keccak by assertion. -/
theorem actual_slot_injective {L R : Nat} {pres : List Storage.Pre}
    {queries : List (List Nat)} (hL : L ≤ 2^256) (hR : R ≤ 2^256)
    (hw : ∀ p ∈ pres, p.Words) (hq : ∀ p ∈ pres, Storage.encode p ∈ queries)
    (hr : Hash.RegionsDisjoint (2^256) L actualHash (List.range R) queries)
    {a b : Storage.Loc} (ha : a.Bounded L R) (hb : b.Bounded L R)
    (hpa : ∀ p ∈ Storage.Loc.pres (2^256) actualPreHash a, p ∈ pres)
    (hpb : ∀ p ∈ Storage.Loc.pres (2^256) actualPreHash b, p ∈ pres)
    (he : Storage.Loc.word (2^256) actualPreHash a =
      Storage.Loc.word (2^256) actualPreHash b) : a = b :=
  Storage.Loc.word_inj (fun p => actual_hash_bound (Storage.encode p)) hL hR
    (actual_regions_of_queries hw hq hr) a b ha hb hpa hpb he

/-- Explicit missing compatibility obligation, not an axiom or a provider adoption.
Existing scanner/padding approval says nothing about opaque native keccak. -/
def NativeAgreesOn (queries : List (List Nat)) : Prop :=
  ∀ bytes ∈ queries, actualHash bytes = Keccak.keccak256Nat bytes

theorem native_regions_to_mathematical {N L : Nat} {roots : List Nat}
    {queries : List (List Nat)} (hc : NativeAgreesOn queries)
    (hr : Hash.RegionsDisjoint N L actualHash roots queries) :
    Hash.RegionsDisjoint N L Keccak.keccak256Nat roots queries := by
  constructor
  · intro a ha b hb hne
    have h : ¬ Hash.Near N L (actualHash a) (actualHash b) := hr.1 a ha b hb hne
    rw [hc a ha,hc b hb] at h
    exact h
  · intro a ha r hh
    have h : ¬ Hash.Covers N L (actualHash a) r := hr.2 a ha r hh
    rw [hc a ha] at h
    exact h

/-- The adaptive bound applies to sampled functions on this byte-query domain.
It does not assert that the actual fixed native provider is sampled uniformly. -/
theorem byte_query_adaptive_bound (dom : List (List Nat))
    (strategy : List Nat → List Nat) (hs : ∀ answers, strategy answers ∈ dom) (q : Nat) :
    2 * (2^256) * (Hash.tuples (2^256) dom.length).countP
      (Hash.eagerCollides strategy dom q) ≤ q*(q-1)*(2^256)^dom.length :=
  Hash.two_mul_eagerCollides_le hs (2^256) q

theorem byte_region_adaptive_bound (dom : List (List Nat))
    (strategy : List Nat → List Nat) (hs : ∀ answers, strategy answers ∈ dom)
    (L : Nat) {roots : List Nat} (hr : ∀ r ∈ roots, r < 2^256) (q : Nat) :
    2 * (2^256) * (Hash.tuples (2^256) dom.length).countP
      (Hash.eagerRegionsFail strategy dom (2^256) L roots q) ≤
      (q*(q-1)*(2*L-1)+2*q*roots.length*L)*(2^256)^dom.length :=
  Hash.two_mul_eagerRegionsFail_le hs (2^256) L hr q

end Solidity.HashBridge

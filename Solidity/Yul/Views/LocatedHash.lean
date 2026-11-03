import Solidity.Yul.Views.Agreements

/-! Concrete approved-Fixed hash inputs for the EXISTING word-granular layout.
No packing agreement or global collision/injectivity premise is introduced. -/
namespace Solidity.Yul.Views

def layoutPreimageBytes (p : Storage.Pre) : List UInt8 := (Storage.encode p).map UInt8.ofNat

def fixedLayoutHash (fixed : Roadmap.Evm.Fixed) (p : Storage.Pre) : Nat := fixed.keccak (layoutPreimageBytes p)

theorem fixedLayoutHash_agreement (fixed : Roadmap.Evm.Fixed) : HashInputAgreement fixed (fixedLayoutHash fixed) := fun _ => rfl

theorem fixedLayoutHash_lt (fixed : Roadmap.Evm.Fixed) (p : Storage.Pre) : fixedLayoutHash fixed p < 2^256 := fixed.keccak_lt _

theorem layout_bytesBE_bound (n value : Nat) : ∀ b ∈ Storage.bytesBE n value, b < 256 := by
  induction n generalizing value with
  | zero => intro b member; cases member
  | succ n ih =>
    intro b member
    rcases List.mem_append.mp member with old | last
    · exact ih _ b old
    · have same : b = value % 256 := List.mem_singleton.mp last
      rw [same]
      exact Nat.mod_lt _ (by decide)

theorem layout_encode_bound (p : Storage.Pre) : ∀ b ∈ Storage.encode p, b < 256 := by
  cases p with
  | data w => exact layout_bytesBE_bound 32 w
  | entry k w =>
    intro b member
    rcases List.mem_append.mp member with key | word
    · exact layout_bytesBE_bound 32 k b key
    · exact layout_bytesBE_bound 32 w b word

theorem layoutPreimageBytes_roundtrip (p : Storage.Pre) : (layoutPreimageBytes p).map UInt8.toNat = Storage.encode p := by
  rw [layoutPreimageBytes,List.map_map]
  calc
    _ = (Storage.encode p).map id := by
      apply List.map_congr_left
      intro b member
      exact UInt8.toNat_ofNat_of_lt (layout_encode_bound p b member)
    _ = _ := List.map_id _

theorem layoutPreimageBytes_inj {p q : Storage.Pre} (pw : p.Words) (qw : q.Words)
    (same : layoutPreimageBytes p = layoutPreimageBytes q) : p = q := by
  apply Storage.encode_inj pw qw
  have raw := congrArg (List.map UInt8.toNat) same
  rwa [layoutPreimageBytes_roundtrip,layoutPreimageBytes_roundtrip] at raw

/-- The approved real-keccak specialization, using the actual Fixed contract,
not an assumed hash-output equality for each generated registration. -/
theorem fixedLayoutHash_real (fixed : Roadmap.Evm.Fixed)
    (real : ∀ b, fixed.keccak b = Roadmap.Evm.keccakWord b) (p : Storage.Pre) :
    fixedLayoutHash fixed p = Storage.keccakH p := by
  rw [fixedLayoutHash,real,Roadmap.Evm.keccakWord,layoutPreimageBytes_roundtrip]
  exact Nat.mod_eq_of_lt (Storage.keccakH_lt p)

/-- EXACT original per-run region premise transported to the bytes really
supplied to Fixed.keccak; no stronger convenience collision premise. -/
theorem fixedLayoutHash_regions {N L : Nat} {roots : List Nat} (fixed : Roadmap.Evm.Fixed)
    (ps : List Storage.Pre) (words : ∀ p ∈ ps, p.Words) :
    Hash.RegionsDisjoint N L (fixedLayoutHash fixed) roots ps ↔
      Hash.RegionsDisjoint N L fixed.keccak roots (ps.map layoutPreimageBytes) := by
  constructor
  · intro h
    constructor
    · intro a ha b hb different
      obtain ⟨p,pm,rfl⟩ := List.mem_map.mp ha
      obtain ⟨q,qm,rfl⟩ := List.mem_map.mp hb
      exact h.1 p pm q qm (fun eq => different (congrArg layoutPreimageBytes eq))
    · intro a ha
      obtain ⟨p,pm,rfl⟩ := List.mem_map.mp ha
      exact h.2 p pm
  · intro h
    constructor
    · intro p pm q qm different
      exact h.1 _ (List.mem_map_of_mem pm) _ (List.mem_map_of_mem qm)
        (fun eq => different (layoutPreimageBytes_inj (words p pm) (words q qm) eq))
    · intro p pm
      exact h.2 _ (List.mem_map_of_mem pm)

end Solidity.Yul.Views

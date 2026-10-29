import Solidity.Keccak
import Solidity.Storage.HashedLayout

/-!
# The hashed layout under keccak-256

The hash parameter of `Solidity/Storage/HashedLayout.lean` instantiated with
`Solidity.Keccak.keccak256Nat` over the ABI encoding of each preimage, as
solc computes storage slots: a mapping entry hashes the key's 32-byte word
followed by the mapping's slot (`abi.encode(k, p)`), a dynamic array's data
hashes the array's slot (`abi.encode(p)`).

* `encode` is injective on preimages whose parts are words (`encode_inj`;
  keys must be below `2^256`, since `bytesBE` truncates), so for such
  preimages a collision of `keccakH` is exactly a collision of keccak-256 on
  the encoded byte strings (`keccakH_eq_iff`). The layout's premises on `P`
  are the premises on the layout's own `KECCAK256` inputs `P.map encode`
  (`collisionFree_keccakH_iff`, `regionsDisjoint_keccakH_iff`); a run that
  hashes more gives them by `RegionsDisjoint.mono` once `P.map encode` is
  shown to be among its inputs.
* `keccakH p < 2^256` (`keccakH_lt`), the hypothesis `Loc.word_inj` asks of
  the hash parameter.
* `#guard` vectors check `Loc.word W keccakH` against solc's slot formula
  for value-type keys, each entering as its ABI word (`uint`, `bool`,
  `address` left-padded; `int` sign-extended, two's complement; `bytesN`
  left-aligned, `v · 256^(32-N)`), nested mappings and dynamic arrays. The
  digests were computed independently with pycryptodome's keccak-256 (the
  call is in `docs/feature-work/storage-hashed-layout.md`); the first ones
  (`keccak256(uint256(0))`, `keccak256(0 ‖ 0)`, …) are constants common
  tooling quotes.

String and `bytes` keys hash their unpadded bytes and are not in this model
(`Pre.entry` takes a word).
-/

namespace Solidity.Storage

open Solidity.Keccak

/-- The `m` low bytes of `n`, big-endian. -/
def bytesBE : Nat → Nat → List Nat
  | 0, _ => []
  | m + 1, n => bytesBE m (n / 256) ++ [n % 256]

theorem length_bytesBE : ∀ (m n : Nat), (bytesBE m n).length = m
  | 0, _ => rfl
  | m + 1, n => by
    simp only [bytesBE, List.length_append, length_bytesBE m (n / 256), List.length_singleton]

theorem ofBytes_append_singleton (bs : List Nat) (b : Nat) :
    ofBytes (bs ++ [b]) = 256 * ofBytes bs + b := by
  simp only [ofBytes, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ofBytes_bytesBE : ∀ (m n : Nat), ofBytes (bytesBE m n) = n % 256 ^ m
  | 0, n => by simp only [bytesBE, ofBytes, List.foldl_nil, Nat.pow_zero, Nat.mod_one]
  | m + 1, n => by
    rw [bytesBE, ofBytes_append_singleton, ofBytes_bytesBE m (n / 256), Nat.pow_succ',
      Nat.mod_mul]
    omega

/-- A 32-byte word encoding is injective on words. -/
theorem bytesBE_inj {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : bytesBE 32 a = bytesBE 32 b) : a = b := by
  have e : ofBytes (bytesBE 32 a) = ofBytes (bytesBE 32 b) := congrArg ofBytes h
  have hw : (2 : Nat) ^ 256 = 256 ^ 32 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  rw [ofBytes_bytesBE, ofBytes_bytesBE, Nat.mod_eq_of_lt (hw ▸ ha),
    Nat.mod_eq_of_lt (hw ▸ hb)] at e
  exact e

/-- The ABI encoding of a preimage: `abi.encode(k, w)` or `abi.encode(w)`. -/
def encode : Pre → List Nat
  | .entry k w => bytesBE 32 k ++ bytesBE 32 w
  | .data w => bytesBE 32 w

/-- The parts of a preimage are words. -/
def Pre.Words : Pre → Prop
  | .entry k w => k < 2 ^ 256 ∧ w < 2 ^ 256
  | .data w => w < 2 ^ 256

theorem encode_inj {p q : Pre} (hp : p.Words) (hq : q.Words) (h : encode p = encode q) :
    p = q := by
  cases p with
  | entry k w =>
    cases q with
    | entry k' w' =>
      obtain ⟨hk, hw⟩ := List.append_inj h (by simp only [length_bytesBE])
      rw [bytesBE_inj hp.1 hq.1 hk, bytesBE_inj hp.2 hq.2 hw]
    | data w' =>
      have hl : (encode (.entry k w)).length = (encode (.data w')).length := congrArg List.length h
      simp only [encode, List.length_append, length_bytesBE] at hl
      omega
  | data w =>
    cases q with
    | entry k' w' =>
      have hl : (encode (.data w)).length = (encode (.entry k' w')).length := congrArg List.length h
      simp only [encode, List.length_append, length_bytesBE] at hl
      omega
    | data w' => rw [bytesBE_inj hp hq h]

/-- The hash parameter: keccak-256 of the ABI encoding, as a number. -/
def keccakH (p : Pre) : Nat := keccak256Nat (encode p)

theorem ofBytes_lt_aux : ∀ (bs : List Nat) (a : Nat), (∀ b ∈ bs, b < 256) →
    bs.foldl (fun n b => 256 * n + b) a < (a + 1) * 256 ^ bs.length
  | [], a, _ => by simp only [List.foldl_nil, List.length_nil, Nat.pow_zero, Nat.mul_one]; omega
  | b :: bs, a, h => by
    have hb : b < 256 := h b (List.mem_cons_self ..)
    have ih : bs.foldl (fun n b => 256 * n + b) (256 * a + b) <
        (256 * a + b + 1) * 256 ^ bs.length :=
      ofBytes_lt_aux bs _ fun c hc => h c (List.mem_cons_of_mem b hc)
    have hle : (256 * a + b + 1) * 256 ^ bs.length ≤ (a + 1) * 256 ^ (bs.length + 1) := by
      rw [Nat.pow_succ', ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem ofBytes_lt {bs : List Nat} (h : ∀ b ∈ bs, b < 256) : ofBytes bs < 256 ^ bs.length := by
  have hlt : bs.foldl (fun n b => 256 * n + b) 0 < (0 + 1) * 256 ^ bs.length :=
    ofBytes_lt_aux bs 0 h
  simp only [Nat.zero_add, Nat.one_mul] at hlt
  exact hlt

theorem length_digest_le (ws : List Nat) (h : ws.length ≤ 4) :
    ((ws.map fun w => (List.range 8).map fun j => (w >>> (8 * j)) % 256).flatten).length ≤ 32 := by
  rw [List.length_flatten, List.map_map]
  have e : ws.map (List.length ∘ fun w => (List.range 8).map fun j => (w >>> (8 * j)) % 256) =
      ws.map (fun _ => 8) := by
    apply List.map_congr_left
    intro w _
    simp only [Function.comp_apply, List.length_map, List.length_range]
  rw [e, show (ws.map (fun _ => 8)).sum = Solidity.Hash.sumOver ws (fun _ => 8) from rfl,
    Solidity.Hash.sumOver_const]
  omega

/-- The digest is at most 32 bytes, each below 256. -/
theorem keccak256_bytes (msg : List Nat) :
    (∀ b ∈ keccak256 msg, b < 256) ∧ (keccak256 msg).length ≤ 32 := by
  constructor
  · intro b hb
    simp only [keccak256, sponge] at hb
    obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp hb
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hbl
    exact Nat.mod_lt _ (by omega)
  · simp only [keccak256, sponge]
    exact length_digest_le _ (List.length_take_le 4 _)

/-- The hash parameter takes word values. -/
theorem keccakH_lt (p : Pre) : keccakH p < 2 ^ 256 := by
  have hb : (∀ b ∈ keccak256 (encode p), b < 256) ∧ (keccak256 (encode p)).length ≤ 32 :=
    keccak256_bytes (encode p)
  have h1 : keccakH p < 256 ^ (keccak256 (encode p)).length := ofBytes_lt hb.1
  have h2 : 256 ^ (keccak256 (encode p)).length ≤ 256 ^ 32 := Nat.pow_le_pow_right (by omega) hb.2
  have hw : (2 : Nat) ^ 256 = 256 ^ 32 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  rw [hw]
  exact Nat.lt_of_lt_of_le h1 h2

/-- On word preimages, `keccakH` collides exactly when keccak-256 collides on
the encoded byte strings. -/
theorem keccakH_eq_iff {p q : Pre} (hp : p.Words) (hq : q.Words) :
    (keccakH p = keccakH q ∧ p ≠ q) ↔
      (keccak256Nat (encode p) = keccak256Nat (encode q) ∧ encode p ≠ encode q) :=
  ⟨fun ⟨h, hne⟩ => ⟨h, fun e => hne (encode_inj hp hq e)⟩,
    fun ⟨h, hne⟩ => ⟨h, fun e => hne (congrArg encode e)⟩⟩

/-- The per-run premise read on bytes: on word preimages, `CollisionFree keccakH`
is `CollisionFree keccak256Nat` on the encoded `KECCAK256` inputs. -/
theorem collisionFree_keccakH_iff {ps : List Pre} (hw : ∀ p ∈ ps, p.Words) :
    Solidity.Hash.CollisionFree keccakH ps ↔
      Solidity.Hash.CollisionFree keccak256Nat (ps.map encode) := by
  constructor
  · intro h a ha b hb e
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    rw [h p hp q hq e]
  · intro h p hp q hq e
    exact encode_inj (hw p hp) (hw q hq)
      (h _ (List.mem_map_of_mem hp) _ (List.mem_map_of_mem hq) e)

/-- The region premise read on bytes: on word preimages, `RegionsDisjoint` for
`keccakH` is `RegionsDisjoint` for `keccak256Nat` on the encoded inputs. -/
theorem regionsDisjoint_keccakH_iff {N L : Nat} {roots : List Nat} {ps : List Pre}
    (hw : ∀ p ∈ ps, p.Words) :
    Solidity.Hash.RegionsDisjoint N L keccakH roots ps ↔
      Solidity.Hash.RegionsDisjoint N L keccak256Nat roots (ps.map encode) := by
  constructor
  · intro ⟨hn, hc⟩
    refine ⟨fun a ha b hb hab => ?_, fun a ha => ?_⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
      exact hn p hp q hq fun e => hab (congrArg encode e)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact hc p hp
  · intro ⟨hn, hc⟩
    refine ⟨fun p hp q hq hpq => ?_, fun p hp => hc _ (List.mem_map_of_mem hp)⟩
    exact hn _ (List.mem_map_of_mem hp) _ (List.mem_map_of_mem hq)
      fun e => hpq (encode_inj (hw p hp) (hw q hq) e)

/-- **Separation under keccak.** Two bounded slot terms whose preimages (all
word preimages) lie in the run's list `P` denote the same 256-bit word only
if they are equal, when the run's `KECCAK256` inputs `P.map encode` satisfy
the region premise. -/
theorem keccak_word_inj {L R : Nat} {P : List Pre} (hL : L ≤ 2 ^ 256) (hR : R ≤ 2 ^ 256)
    (hw : ∀ p ∈ P, p.Words)
    (hRD : Solidity.Hash.RegionsDisjoint (2 ^ 256) L keccak256Nat (List.range R) (P.map encode))
    {l₁ l₂ : Loc} (hb₁ : Loc.Bounded L R l₁) (hb₂ : Loc.Bounded L R l₂)
    (hP₁ : ∀ p ∈ Loc.pres (2 ^ 256) keccakH l₁, p ∈ P)
    (hP₂ : ∀ p ∈ Loc.pres (2 ^ 256) keccakH l₂, p ∈ P)
    (h : Loc.word (2 ^ 256) keccakH l₁ = Loc.word (2 ^ 256) keccakH l₂) : l₁ = l₂ :=
  Loc.word_inj keccakH_lt hL hR ((regionsDisjoint_keccakH_iff hw).mpr hRD) l₁ l₂ hb₁ hb₂ hP₁ hP₂ h

/-! ## solc's slot formula

`W = 2^256`. A state variable at slot `p`: a mapping's entry at key `k` is at
`keccak256(abi.encode(k, p))`, a dynamic array's element `i` (of `s` words)
at `keccak256(abi.encode(p)) + i·s`. The digests below were computed
independently with pycryptodome's keccak-256. -/

-- `uint256[] a` at slot `0`: `a[0]` is at `keccak256(uint256(0))`.
#guard Loc.word (2 ^ 256) keccakH (.data (.root 0) 0) ==
  0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563
#guard Loc.word (2 ^ 256) keccakH (.data (.root 1) 0) ==
  0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6
-- `S[] a` at slot `2`, `S` of two words: `a[3].y` is `keccak256(2) + 3·2 + 1`.
#guard Loc.word (2 ^ 256) keccakH (.data (.root 2) (3 * 2 + 1)) ==
  0x405787fa12a823e0f2b7631cc41b3ba8828b3321ca811111fa75cd3aa3bb5ace + 7
-- `mapping(uint256 => ·) m` at slot `0`: `m[0]`, `m[1]`; a `bool` key `true` is `1`.
#guard Loc.word (2 ^ 256) keccakH (.hash 0 (.root 0) 0) ==
  0xad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5
#guard Loc.word (2 ^ 256) keccakH (.hash 1 (.root 0) 0) ==
  0xada5013122d395ba3c54772283fb069b10426056ef8ca54750cb9bb552a59e7d
-- `m[5]` for a mapping at slot `3`.
#guard Loc.word (2 ^ 256) keccakH (.hash 5 (.root 3) 0) ==
  0x405aad32e1adbac89bb7f176e338b8fc6e994ca210c9bb7bdca249b465942250
-- `mapping(int256 => ·)` at slot `0`: the key `-1` is the word `2^256 - 1`.
#guard Loc.word (2 ^ 256) keccakH (.hash (2 ^ 256 - 1) (.root 0) 0) ==
  0xbbd6e7dddd4326dd7c827841ab9733c6e3fcdf38a516374bd10feec8f674ea8a
-- `mapping(address => ·)` at slot `4`, key `0xdeadbeef` (left-padded).
#guard Loc.word (2 ^ 256) keccakH (.hash 0xdeadbeef (.root 4) 0) ==
  0x36d975060e33224d20b5b4277dd6c8025812812e010c2889b72c3ed4e0d75dd5
-- Nested `mapping(uint => mapping(uint => ·)) n` at slot `2`: `n[7][9]` is
-- `keccak256(9 ‖ keccak256(7 ‖ 2))`.
#guard Loc.word (2 ^ 256) keccakH (.hash 9 (.hash 7 (.root 2) 0) 0) ==
  0x6a8a76f6c6fa83d93d4624db9ec9f6abb18905aac3028bb068b229e35b35802d
-- `mapping(uint => uint[]) d` at slot `0`: `d[1][0]` is
-- `keccak256(keccak256(1 ‖ 0))`.
#guard Loc.word (2 ^ 256) keccakH (.data (.hash 1 (.root 0) 0) 0) ==
  0x3f9553dc324cd1fd24b54243720c42e18e5c20165bc5e523e42b440a8654abd1
-- `mapping(bytes32 => ·)` at slot `1`, key `0xff00…00ab`; `mapping(bytes4 => ·)`
-- at slot `1`, key `0x12345678` left-aligned.
#guard Loc.word (2 ^ 256) keccakH (.hash (0xff * 2 ^ 248 + 0xab) (.root 1) 0) ==
  0x68fdbafcd9d6403748641b179e98637175e2ddc787687c11385593d40da2c860
#guard Loc.word (2 ^ 256) keccakH (.hash (0x12345678 * 256 ^ 28) (.root 1) 0) ==
  0xd61b4b4c4215a3b160e238a68f0842f5b49688e7c37f01f944c1453922187815
-- The layout's own path: in `struct { uint a; uint b; mapping(uint => uint[]) m; }`
-- at slot `0`, `m[1][0]` is `keccak256(keccak256(1 ‖ 2))`.
#guard (STy.locate (.strct [.word, .word, .map (.darr .word)]) (.root 0)
    [.field 2, .key 1, .index 0]).map (fun r => Loc.word (2 ^ 256) keccakH r.2) ==
  some 0x7fef4bf8f63cf9dd467136c679c02b5c17fcf6322d9562512bf5eb952cf7cc53

end Solidity.Storage

/-- info: 'Solidity.Storage.keccakH_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.keccakH_lt

/-- info: 'Solidity.Storage.collisionFree_keccakH_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.collisionFree_keccakH_iff

/-- info: 'Solidity.Storage.keccak_word_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.keccak_word_inj

/-- info: 'Solidity.Storage.encode_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.encode_inj

/-- info: 'Solidity.Storage.regionsDisjoint_keccakH_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Storage.regionsDisjoint_keccakH_iff

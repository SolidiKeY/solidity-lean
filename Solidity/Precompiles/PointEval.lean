import Solidity.Precompiles.Bls12381
import Solidity.Precompiles.Basic

/-!
# `POINT_EVALUATION` (0x0a)

EIP-4844's KZG point-evaluation precompile, as Osaka's execution
specification (`point_evaluation.py`, `ethereum/crypto/kzg.py`) runs it.
The input is exactly 192 bytes: a versioned hash (32), the evaluation point
`z` and value `y` (32 each, below the BLS12-381 group order `r`), and a
commitment and a proof (48 each, compressed `G1` points in the zcash format).

- **Failure**: a length other than 192, a versioned hash other than
  `0x01 ‖ sha256(commitment)[1:]`, `z` or `y` at or above `r`, a commitment
  or proof that does not decompress to a point of the order-`r` subgroup
  (the infinity encoding `0xc0 0…0` aside), or a proof that does not verify
  (`pointEval_length`; `check` makes the rest, in the specification's
  order).
- **Result**: `FIELD_ELEMENTS_PER_BLOB` and `r` as two 32-byte words
  (`pointEval_result`).
- **Gas**: 50000.

The proof verifies when `e(C - y·G₁, -G₂) · e(π, [τ]G₂ - z·G₂) = 1`, with
`[τ]G₂` the trusted setup's `KZG_SETUP_G2_MONOMIAL_1`, embedded here as its
decompressed point (`setupG2`) and checked against its compressed bytes.
-/

namespace Solidity.Precompiles.PointEval

open Solidity.Roadmap.Evm (Bytes)
open Bls12381 (Fp F2 curve1 curve2 r)

def g1Gen : Pt Fp :=
  .aff (Fin.ofNat _ 3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507)
       (Fin.ofNat _ 1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569)

def g2Gen : Pt F2 :=
  .aff (Bls12381.f2 (352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160,
                     3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758))
       (Bls12381.f2 (1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905,
                     927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582))

/-- The trusted setup's `[τ]G₂` (`KZG_SETUP_G2_MONOMIAL_1`), decompressed. -/
def setupG2 : Pt F2 :=
  .aff (Bls12381.f2 (3749701713850085193403383609513386037494151572263731328608276629425322978272408394373143740944003571525027436289778,
                     3347537128081568434923729147580015899756771550835613107520576615563260658656019591232316627827007503930666726825842))
       (Bls12381.f2 (194392958648403190675529552496435226424111592982833162118538452666741235889530674000225873281133418439621742897817,
                     3447898402727835650716129438012169492682148398295533958400255525306573911008434577489634554212211450783070687991119))

/-- `KZG_SETUP_G2_MONOMIAL_1` as published (compressed, `x.c₁` then `x.c₀`). -/
def setupG2Compressed : Bytes := ofHex
  "b5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2"

-- The embedded point is the published one: its `x` is the compressed
-- bytes' (flags masked), it is on the twist and in the order-`r` subgroup.
#guard match setupG2 with
  | .aff x _ =>
    x.im.val == readNat setupG2Compressed 0 48 % 2 ^ 381 && x.re.val == readNat setupG2Compressed 48 48
  | .inf => false
#guard curve2.onCurve setupG2 && curve2.mul r setupG2 == .inf
#guard curve1.onCurve g1Gen && curve2.onCurve g2Gen

/-- The zcash encoding of `G1`'s infinity. -/
def infinityBytes : List Nat := 0xc0 :: List.replicate 47 0

/-- A compressed `G1` point in 48 bytes, if it decompresses to a point of
the order-`r` subgroup (py_ecc's `KeyValidate`), or is the infinity
encoding. -/
def decompress (b : List Nat) : Option (Pt Fp) :=
  if b = infinityBytes then some .inf else
  let z := ofBE b
  let c := z / 2 ^ 383 % 2
  let bf := z / 2 ^ 382 % 2
  let a := z / 2 ^ 381 % 2
  let x := z % 2 ^ 381
  if c ≠ 1 ∨ bf ≠ 0 ∨ x = 0 ∨ Bls12381.p ≤ x then none else
  let xf : Fp := Fin.ofNat _ x
  match Bls12381.sqrtFp (xf * xf * xf + 4) with
  | none => none
  | some y =>
    let y := if (y.val * 2) / Bls12381.p = a then y else -y
    if curve1.mul r (.aff xf y) = .inf then some (.aff xf y) else none

def gas (_ : Bytes) : Nat := 50000

def fieldElementsPerBlob : Nat := 4096

/-- The checks of `POINT_EVALUATION`, in the specification's order. -/
def check (d : Bytes) : Option Unit := do
  if d.length ≠ 192 then none
  let b := d.map UInt8.toNat
  let commitment := (b.drop 96).take 48
  let hash := (sha256 ((d.drop 96).take 48)).getD []
  if b.take 32 ≠ 1 :: (hash.drop 1).map UInt8.toNat then none
  let z := ofBE ((b.drop 32).take 32)
  let y := ofBE ((b.drop 64).take 32)
  if r ≤ z ∨ r ≤ y then none
  let C ← decompress commitment
  let π ← decompress ((b.drop 144).take 48)
  let xMinusZ := curve2.add setupG2 (curve2.mul ((r - z) % r) g2Gen)
  let pMinusY := curve1.add C (curve1.mul ((r - y) % r) g1Gen)
  if Bls12381.pairingCurve.check [(pMinusY, Curve.neg g2Gen), (π, xMinusZ)] then some () else none

/-- `POINT_EVALUATION` (0x0a). -/
def pointEval (d : Bytes) : Option Bytes :=
  (check d).map fun _ => word fieldElementsPerBlob ++ word r

theorem pointEval_eq_none_iff (d : Bytes) : pointEval d = none ↔ check d = none := by
  unfold pointEval
  cases check d <;> simp only [Option.map_none, Option.map_some, reduceCtorEq]

theorem pointEval_length {d : Bytes} (h : d.length ≠ 192) : pointEval d = none := by
  rw [pointEval_eq_none_iff]
  simp only [check, h, ne_eq, not_false_eq_true, if_true]
  exact rfl

/-- A successful call returns the two constants. -/
theorem pointEval_result {d o : Bytes} (h : pointEval d = some o) :
    o = word fieldElementsPerBlob ++ word r := by
  unfold pointEval at h
  cases hc : check d <;> simp only [hc, Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq] at h
  exact h.symm

/-! ## Vectors (proofs by c-kzg-4844, run by Osaka's execution specification) -/

#guard pointEval (ofHex "012fbcce4b727c5aac28fa0f5223d397bc6050019d43728e2fbdb8c1c3df659800000000000000000000000000000000000000000000000000000000075bcd1516ea6606c7536a08f3b90ee19580dd81884d539a6c7b13741e8031e2db3188ae9557ada58d1ea7f48806d66720bb05d148ce52dfab866d26b638e3c838db4d390a37ff3ea7fedf29e9c9181b3ea9e5898223d196e9763af85715f1f78d7084c8860316d70df5e0840b535a6f69003cdabfd7f59f307d06a97d1486551e0ced8f") == some (ofHex "000000000000000000000000000000000000000000000000000000000000100073eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001")
#guard gas (ofHex "012fbcce4b727c5aac28fa0f5223d397bc6050019d43728e2fbdb8c1c3df659800000000000000000000000000000000000000000000000000000000075bcd1516ea6606c7536a08f3b90ee19580dd81884d539a6c7b13741e8031e2db3188ae9557ada58d1ea7f48806d66720bb05d148ce52dfab866d26b638e3c838db4d390a37ff3ea7fedf29e9c9181b3ea9e5898223d196e9763af85715f1f78d7084c8860316d70df5e0840b535a6f69003cdabfd7f59f307d06a97d1486551e0ced8f") == 50000
#guard pointEval (ofHex "012fbcce4b727c5aac28fa0f5223d397bc6050019d43728e2fbdb8c1c3df659800000000000000000000000000000000000000000000000000000000075bcd1516ea6606c7536a08f3b90ee19580dd81884d539a6c7b13741e8031e2db3188ae9557ada58d1ea7f48806d66720bb05d148ce52dfab866d26b638e3c838db4d390a37ff3ea7fedf29e9c9181b3ea9e5898223d196e9763af85715f1f78d7084c8860316d70df5e0840b535a6f69003cdabfd7f59f307d06a97d1486551e0ced") == none
#guard pointEval (ofHex "012fbcce4b727c5aac28fa0f5223d397bc6050019d43728e2fbdb8c1c3df659800000000000000000000000000000000000000000000000000000000075bcd1516ea6606c7536a08f3b90ee19580dd81884d539a6c7b13741e8031e2db3188af9557ada58d1ea7f48806d66720bb05d148ce52dfab866d26b638e3c838db4d390a37ff3ea7fedf29e9c9181b3ea9e5898223d196e9763af85715f1f78d7084c8860316d70df5e0840b535a6f69003cdabfd7f59f307d06a97d1486551e0ced8f") == none
#guard pointEval (ofHex "022fbcce4b727c5aac28fa0f5223d397bc6050019d43728e2fbdb8c1c3df659800000000000000000000000000000000000000000000000000000000075bcd1516ea6606c7536a08f3b90ee19580dd81884d539a6c7b13741e8031e2db3188ae9557ada58d1ea7f48806d66720bb05d148ce52dfab866d26b638e3c838db4d390a37ff3ea7fedf29e9c9181b3ea9e5898223d196e9763af85715f1f78d7084c8860316d70df5e0840b535a6f69003cdabfd7f59f307d06a97d1486551e0ced8f") == none
#guard pointEval (ofHex "012fbcce4b727c5aac28fa0f5223d397bc6050019d43728e2fbdb8c1c3df659873eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff0000000116ea6606c7536a08f3b90ee19580dd81884d539a6c7b13741e8031e2db3188ae9557ada58d1ea7f48806d66720bb05d148ce52dfab866d26b638e3c838db4d390a37ff3ea7fedf29e9c9181b3ea9e5898223d196e9763af85715f1f78d7084c8860316d70df5e0840b535a6f69003cdabfd7f59f307d06a97d1486551e0ced8f") == none
#guard pointEval (ofHex "010657f37554c781402a22917dee2f75def7ab966d7b770905398eba3c44401400000000000000000000000000000000000000000000000000000000075bcd150000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == some (ofHex "000000000000000000000000000000000000000000000000000000000000100073eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001")
#guard gas (ofHex "010657f37554c781402a22917dee2f75def7ab966d7b770905398eba3c44401400000000000000000000000000000000000000000000000000000000075bcd150000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000") == 50000

end Solidity.Precompiles.PointEval

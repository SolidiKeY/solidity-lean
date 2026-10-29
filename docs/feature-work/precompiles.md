# Osaka precompiles as fixed functions

Lane `lane-precompiles` of batch `roadmap-l1-20261029`. It instantiates the
`Fixed` parameter of roadmap G06 (`Solidity/Roadmap/Evm.lean`, merged from
`cloud/roadmap-w1-20261029/g06-evm-interface`) with computed definitions of
all 18 Osaka precompiles, and checks them against the external EVM of
`Bridge/`. The stipend cost rule of the same lane is in
[stipend-cost-rule.md](stipend-cost-rule.md).

Decisions in force ([solidity-scope.md](../solidity-scope.md#user-decisions-2026-10-29)):
calls to the Osaka precompiles behave as their EVM definitions, the crypto
ones through approved fixed functions; hashes and `ecrecover` are approved
fixed functions (`Solidity/Keccak.lean`, `Solidity/Hashes.lean`,
`Solidity/Secp256k1.lean`), reused here unchanged.

## Design

- **Core and dependency-free.** Every module under `Solidity/Precompiles/`
  imports only `Solidity.Roadmap.Evm`, `Solidity.Hashes`,
  `Solidity.Secp256k1` and each other. Arithmetic is over `Nat`, `Fin p`
  and `UInt64` (BLAKE2b); every recursion is structural or fuelled by a
  bit count, so `#guard` evaluates each precompile.
- **Intrinsic inputs, total computation.** A decoded point carries its
  curve equation (and, where the EIP checks it, membership of the
  order-`r` subgroup) as a subtype (`Bn254.G1`, `Bn254.G2`, `Bls12381.G1`,
  `P256.Key`, …). The group operations are the textbook affine formulas,
  total on every input. So a precompile fails exactly when decoding fails,
  and that is provable without field laws. No field or group law is proved
  or assumed; the vectors are the evidence that the formulas compute the
  groups.
- **Failure is `none`**, as `Fixed.precompile` reads it: an exceptional
  halt. `ECRECOVER` and `P256VERIFY` answer a bad signature with empty
  output, not a halt, as the EIPs say.
- **Gas** is `Fixed.precompileGas`, fixed to Osaka's. On a malformed input
  the frame's whole gas is consumed whatever the formula says; `MODEXP`'s
  formula returns `0` there, so that it never reads an over-long length.

## Checkpoint 1: the precompile functions

| Address | Module, function | EIPs | Gas | Fails on |
|---|---|---|---|---|
| 0x01 | `Basic`, `ecrecover` | Frontier | 3000 | never (bad signature: empty output) |
| 0x02 | `Basic`, `sha256` | Frontier | `60 + 12·words` | never |
| 0x03 | `Basic`, `ripemd160` | Frontier | `600 + 120·words` | never |
| 0x04 | `Basic`, `identity` | Frontier | `15 + 3·words` | never |
| 0x05 | `Modexp`, `modexp` | 198, 2565, 7823, 7883 | `max 500 (complexity·iterations)` | a length above 1024 |
| 0x06 | `Bn254`, `add` | 196, 1108 | 150 | a coordinate `≥ p`, a point off the curve |
| 0x07 | `Bn254`, `mul` | 196, 1108 | 6000 | as 0x06 |
| 0x08 | `Bn254`, `pairing` | 197, 1108 | `45000 + 34000·k` | length not `192·k`; a bad point; `G2` outside the subgroup |
| 0x09 | `Blake2f`, `blake2f` | 152 | `rounds` | length not 213; flag above 1 |
| 0x0a | `PointEval`, `pointEval` | 4844 | 50000 | length, versioned hash, `z`/`y ≥ r`, bad compressed point, failed proof |
| 0x0b | `Bls12381`, `g1Add` | 2537 | 375 | length not 256; a bad point |
| 0x0c | `Bls12381`, `g1Msm` | 2537 | `k·12000·discount/1000` | length not `160·k`, `k ≥ 1`; a point outside the subgroup |
| 0x0d | `Bls12381`, `g2Add` | 2537 | 600 | length not 512; a bad point |
| 0x0e | `Bls12381`, `g2Msm` | 2537 | `k·22500·discount/1000` | length not `288·k`, `k ≥ 1`; a point outside the subgroup |
| 0x0f | `Bls12381`, `pairing` | 2537 | `32600·k + 37700` | length not `384·k`, `k ≥ 1`; a bad point |
| 0x10 | `Bls12381`, `mapFpToG1` | 2537 | 5500 | length not 64; element `≥ p` |
| 0x11 | `Bls12381`, `mapFp2ToG2` | 2537 | 23800 | length not 128; element `≥ p` |
| 0x100 | `P256`, `p256Verify` | 7951 | 6900 | never (bad input or signature: empty output) |

All 18 have full definitions. BLS12-381 and point evaluation were allowed
to stay interfaces; they did not need to:

- **BLS12-381** reuses the generic pairing check (`Pairing.lean`) with
  BLS12-381's `Fp12` reduction and M-twist. Its maps are RFC 9380's
  straight-line simplified SWU, the isogeny of `Bls12381Iso.lean` and
  cofactor clearing by the effective cofactor.
- **Point evaluation** decompresses zcash-encoded `G1` points and checks
  `e(C - y·G₁, -G₂) · e(π, [τ]G₂ - z·G₂) = 1`. `[τ]G₂` is the trusted
  setup's `KZG_SETUP_G2_MONOMIAL_1`, embedded decompressed, and a `#guard`
  checks it against its published compressed bytes, its curve and its
  subgroup.

### Vector provenance

The `#guard` vectors are not hand-written. A script ran **Osaka's execution
specification** (`ethereum-execution` 2.20.0, `ethereum/forks/osaka/vm/
precompiled_contracts/`) on each input through a stub frame, and recorded
the output, or `none` for a raised exception, and the gas charged. Inputs
include the EIPs' own examples: EIP-198's two `MODEXP` cases, EIP-152's
`F` vector with 12 rounds (`ba80a53f…`), the BN254 and BLS12-381
generators, and bilinearity checks such as `e(2P, Q)·e(-P, 2Q) = 1`.
Further inputs come from independent libraries:

- `coincurve` signs the `ECRECOVER` vector;
- `cryptography` (OpenSSL) signs the `P256VERIFY` vectors;
- c-kzg-4844 with the mainnet trusted setup computes the KZG proof;
- py_ecc builds the curve points.

Failing cases cover each failure class: wrong lengths, coordinates at `p`,
points off the curve, BLS12-381 points on the curve but outside the
subgroup (accepted by `G1ADD`, refused by the MSMs and the pairing),
`MODEXP` lengths of 1025 and `2²⁵⁶ - 1`, and a BLAKE2F flag of 2.

A deliberately wrong `#guard` was checked to fail, to confirm that the
vectors run. The generator scripts are not committed. They read the
vendored specification package, which is not part of the repository; the
vectors in the files are the record.

## Checkpoint 2: the `Fixed` instance and its laws

`Solidity/Precompiles/Osaka.lean`:

- `Osaka.run`, `Osaka.gas`: dispatch over G06's `Precompile`.
- `Osaka.fixed : Fixed`: `keccakWord`, `run`, `gas`.
  `fixed_precompileGas : fixed.precompileGas = gas`.
- `Osaka.Malformed p d`: the decoding failures of each EIP, in the terms of
  each module (`Bn254.decodeG1`, `Bls12381.decodeG1Sub`,
  `Modexp.Malformed`, …).
- **`run_eq_none_iff`** (and `fixed_precompile_eq_none_iff`): a precompile
  halts exceptionally exactly on malformed input. It is assembled from
  per-module laws: `Modexp.modexp_eq_none_iff`, `Bn254.add_eq_none_iff`,
  `Bn254.mul_eq_none_iff`, `Bn254.pairing_eq_none_iff`,
  `Blake2f.blake2f_eq_none_iff`, `PointEval.pointEval_eq_none_iff`,
  `Bls12381.g1Add_eq_none_iff`, `g2Add_eq_none_iff`, `g1Msm_eq_none_iff`,
  `g2Msm_eq_none_iff`, `pairing_eq_none_iff`, `mapFpToG1_eq_none_iff`,
  `mapFp2ToG2_eq_none_iff`.
- Decoding is characterized down to numbers where it matters:
  `Bn254.decodeG1_eq_none_iff` states `p ≤ x ∨ p ≤ y ∨ (x, y) ≠ (0, 0) ∧
  y² ≢ x³ + 3 (mod p)`, through `Bn254.onCurve_aff`, and
  `Bls12381.decodeFp_eq_none_iff` and `decodeFp2_eq_none_iff` state the
  `≥ p` bound.
- **`gas_mono`**: gas is monotonic in the input length for every
  precompile the EIPs price by length (`LengthPriced`: all but `MODEXP` and
  `BLAKE2F`, whose gas reads the header). The non-trivial cases are
  `sha256Gas_mono`, `ripemd160Gas_mono`, `identityGas_mono`, BN254's
  pairing, and `Bls12381.g1MsmGas_mono`, `g2MsmGas_mono` and
  `pairingGas_mono`. The MSM lemma `msmGas_mono` holds for any discount
  table on which `k·discount(k)` does not decrease, which `decide` checks
  for EIP-2537's two tables.
- **Further laws**: `Modexp.modexp_length` (the output has `Lm` bytes),
  `Modexp.gas_ge` (at least 500), `Blake2f.blake2f_length` (64 bytes),
  `PointEval.pointEval_result` (the two constants), and the never-failing
  `ecrecover_isSome`, `sha256_isSome`, `ripemd160_isSome`, `identity_eq`
  and `p256Verify_isSome`.
- **Stipend facts** for G06 §3.2 and G43: `ecrecover_exceeds_stipend`
  (a stipend payment to 0x01 always fails). A `#guard` on `stipendFits`
  lists the precompiles a stipend payment with empty data reaches
  successfully: `SHA256`, `RIPEMD160`, `IDENTITY`, `MODEXP`, `ECADD`.

Axiom pins (`#guard_msgs`): `run_eq_none_iff` and `gas_mono` use
`[propext, Quot.sound]`; `ecrecover_exceeds_stipend` uses none.

### Handoff (checkpoints 1–2)

- **Revision:** see the branch head of the commit "Precompiles: the Osaka
  `Fixed` instance".
- **Theorems:** as listed above; no `sorry`, no new axiom, no
  `native_decide`, `implemented_by` or `maxHeartbeats` change.
- **Premises:** none. The public theorem still quantifies over
  `Fixed.precompile`, and `Osaka.fixed` is its intended instance.
- **Checks:** `lean_diagnostic_messages` is clean on all eleven modules.
  `check-layers`, `check-orphans` and `check-trust` pass.
- **Remaining:**
  - no proof that the affine formulas compute the group law, or that
    `PairingCurve.check` is the pairing: vectors only;
  - the source's `sha256`/`ripemd160`/`ecrecover` builtins
    (`Semantics/Heap.lean`) are not yet stated equal to `Osaka.run` at
    0x01–0x03; that is S05's correspondence, made easy by sharing the
    definitions;
  - B16's identification with the pinned EVM is checkpoint 3.

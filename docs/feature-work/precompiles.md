# Osaka precompiles as fixed functions

Lane `lane-precompiles` of batch `roadmap-l1-20261029`. It instantiates the
`Fixed` parameter of roadmap G06 (`Solidity/Roadmap/Evm.lean`, merged from
`cloud/roadmap-w1-20261029/g06-evm-interface`) with computed definitions of
all 18 Osaka precompiles, checked against vectors that Osaka's execution
specification computed. Their agreement with the external EVM of `Bridge/`
is recorded by reading in checkpoint 3; it is not yet checked by Lean,
because the Bridge cannot be built in this lane's environment. The stipend
cost rule of the same lane is in
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
  curve equation as a subtype (`Bn254.G1`, `Bls12381.G1`, `Bls12381.G2`,
  `P256.Key`); `Bn254.G2` also carries membership of the order-`r`
  subgroup. The other subgroup checks (`Bls12381.decodeG1Sub`,
  `decodeG2Sub`, BN254's `G1` check in `decodePair`) are runtime tests that
  the type does not record. The group operations are the textbook affine formulas,
  total on every input. So a precompile fails exactly when decoding fails
  (for point evaluation: or the proof does not verify), and that is
  provable without field laws. No field or group law is proved
  or assumed; the vectors are the evidence that the formulas compute the
  groups.
- **Failure is `none`**, as `Fixed.precompile` reads it: an exceptional
  halt. `ECRECOVER` and `P256VERIFY` answer a bad signature with empty
  output, not a halt, as the EIPs say.
- **Gas** is `Fixed.precompileGas`, fixed to Osaka's. On a malformed input
  the frame's whole gas is consumed whatever the formula says; `MODEXP`'s
  formula returns `0` there, so that it never reads an over-long length.
  `precompileGas` is therefore meaningful only where `precompile` succeeds:
  a stipend argument must read both (as `Osaka.stipendFits` does), never
  `gas ≤ 2300` alone.
- **Not drawn from approved functions.** The hashes and `ecrecover` reuse
  the approved fixed functions unchanged. The BN254, BLS12-381, KZG and
  P-256 definitions are new. This is acceptable because they serve as an
  *instance*: the public theorem quantifies over `Fixed.precompile`, so it
  does not depend on them.

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
  `Modexp.Malformed`, …). Point evaluation is the exception: its
  `Malformed` is `PointEval.decode d = none` or a decoded input whose proof
  does not verify (`PointEval.verifies`), because the EIP halts on both.
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
  `pairingGas_mono`. Ten of the sixteen `LengthPriced` cases are constant
  gas, where the law is trivial. The MSM lemma `msmGas_mono` holds for any discount
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

- **Revision:** `2b0bd1b` (checkpoints 1–2); review fixes in `dff640c`.
- **Theorems:** as listed above; no `sorry`, no new axiom, no
  `native_decide`, `implemented_by` or `maxHeartbeats` change.
- **Premises:** none. The public theorem still quantifies over
  `Fixed.precompile`, and `Osaka.fixed` is its intended instance.
- **Checks:** `lean_diagnostic_messages` is clean on all eleven modules.
  `check-layers`, `check-orphans` and `check-trust` pass.
- **Remaining:**
  - no proof that the affine formulas compute the group law, or that
    `PairingCurve.check` is the pairing: vectors only. Fermat inversion
    assumes `p` prime, which is unproved. The SSWU square-root default
    (`Bls12381.sswu`) is unreachable only by RFC 9380's theorem, also
    unproved;
  - the source's `sha256`/`ripemd160`/`ecrecover` builtins
    (`Semantics/Heap.lean`) are not yet stated equal to `Osaka.run` at
    0x01–0x03; that is S05's correspondence, made easy by sharing the
    definitions;
  - B16's identification with the pinned EVM is checkpoint 3.

## Checkpoint 3: agreement with the vendored EVM (blocked)

The assignment asks for a `Bridge/` adapter that checks the core functions
against EVMYulLean's vendored ones: by proof where feasible, otherwise by
`#guard` vectors. Neither can run in this lane, for two reasons.

**The Bridge cannot be built here.** `Bridge/` needs Mathlib. `lake exe
cache get` reaches neither Mathlib cache host:
`lakecache.blob.core.windows.net` (CONNECT 403) and
`mathlib4.lean-cache.cloud`. Building Mathlib from source is a multi-hour
build. The Lean server serves the core only. An adapter written here could
not be checked, so none is committed.

**Most vendored functions cannot be evaluated or reasoned about anyway.**
Running a `#guard` vector at elaboration would execute the subprocess.
Neither proof nor vector can reach a vendored function that:

- runs `python3 EvmYul/EllipticCurvesPy/*.py` through
  `totallySafePerformIO`: `RIP160.lean`, `BN_ADD.lean`, `BN_MUL.lean`,
  `SNARKV.lean`, `BLAKE2_F.lean` (only its wrapper) and `PointEval.lean`
  (the scripts are not vendored);
- or is an opaque `@[extern]`: `ffi.SHA256`, `ffi.BLAKE2`, `ffi.KEC`,
  `ECDSARECOVER`.

What reading `Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean` and
`EVM/Semantics.lean` (`:785`–`:796`; `π = {1..10}`, `State/Account.lean:15`) establishes, for the adapter to prove
once the Bridge builds:

| Precompile | Vendored (Cancun, M5) | Agreement with `Osaka.run`/`Osaka.gas` |
|---|---|---|
| 0x01 `Ξ_ECREC` | gas 3000; the same `v`, `r`, `s` validity checks; empty output on failure | gas: by definition. Output: opaque (`ECDSARECOVER`, `ffi.KEC`). |
| 0x02 `Ξ_SHA256` | `60 + 12·⌈l/32⌉` | gas: by definition. Output: opaque `ffi.SHA256`. |
| 0x03 `Ξ_RIP160` | `600 + 120·⌈l/32⌉` | gas: by definition. Output: Python. |
| 0x04 `Ξ_ID` | `15 + 3·⌈l/32⌉`, output the calldata | gas and output: by definition (the provable case). |
| 0x05 `Ξ_EXPMOD` | EIP-2565 (Berlin) gas: `max 200 (⌈max(Lb,Lm)/8⌉²·it/3)`, `8·(Le-32)`; no length bound | **Disagrees.** Osaka has EIP-7883 gas (`max 500`, complexity 16 or `2·words²`, `16·(Le-32)`) and EIP-7823's 1024-byte bound. The output also **disagrees** for a base of 2²⁵⁶ or more: `expMod modulus (.ofNat base) exp` truncates the base to a `UInt256` (e.g. `Lb = 33`, base `0x01‖00×32`, `Le = 1`, `exp = 1`, `Lm = 33`, `mod = 2²⁶⁴−1`: Osaka returns 2²⁵⁶, the vendored function 0). |
| 0x06/0x07 `Ξ_BN_ADD`/`Ξ_BN_MUL` | gas 150 / 6000 | gas: by definition. Output: Python. |
| 0x08 `Ξ_SNARKV` | `34000·⌊l/192⌋ + 45000`, no length test before Python | gas: by definition. Output and the length test: Python. |
| 0x09 `Ξ_BLAKE2_F` | gas = the first four bytes, read before the length test | gas: by definition on a 213-byte input. Output: opaque `ffi.BLAKE2`. |
| 0x0a `Ξ_PointEval` | gas 50000 | gas: by definition. Output: Python. |
| 0x0b–0x11, 0x100 | absent: a call reaches an empty account and succeeds with no output | **Disagrees** (G06 D9; repin B01). |

This is G06's B16 (instances) and B01 (Osaka repin) for the precompiles. It
needs a Bridge build and, for the crypto outputs, a vendor patch replacing
the Python and FFI calls with the core definitions (D13's route for
Keccak).

### Gates (lane end)

`./run-lean.sh`, run alone at `8da2c17`:

- **Layers and build.** `check-layers` passes; the default `lake build`
  completes ("Build completed successfully (731 jobs)").
- **SolkeyTestSuite.** The first run killed `Derived17` with code 137, the
  known baseline OOM. A second run, alone, completed (262 jobs).
- **`check-solkey.sh`.** It reports the baseline drift of 37 mismatches,
  owned by a Codex lane.
- **Elaboration times.** `Solidity.Precompiles.Osaka` takes 4.5 s and
  `Solidity.Stipend.Rule` 15 s. The other precompile modules were built by
  the Lean server, so the build log has no times for them. Their vector
  files are the heaviest: `Bls12381` and `PointEval` evaluate pairings in
  their `#guard`s.
- **Proof that nearly evaluated a pairing.** Proofs that reached
  `PointEval.verifies` by unfolding made elaboration evaluate a pairing;
  they ran out of memory. `decode` and `verifies` are now
  `@[irreducible]`, and the laws go through `bind_check_eq_none` and
  `bind_check_eq_some`.
- **Other scripts.** `check-orphans`, `check-trust` (0 findings) and
  `check-doc-paths` (46 missing, the baseline) pass.

### Handoff (checkpoint 3)

- **Status:** blocked. No Bridge adapter is committed, because no Lean check of one is possible here.
- **Done:** the agreement table above, by reading.
- **Needed:** network access to a Mathlib cache host (or a multi-hour Mathlib build), then
  `Bridge/SolidityBridge/Precompiles.lean` proving the gas rows and `IDENTITY` by definition,
  and recording the `MODEXP` and 0x0b–0x11/0x100 disagreements as B01's repin obligations.

## Review

Read-only finder and skeptic subagents reviewed checkpoints 1–2, without
the Lean server. They checked against Osaka's execution specification and
the repository's constraints. The skeptic's confirmed findings, all fixed:

1. A broken link to `stipend-cost-rule.md`: the document was not yet
   written. It is now.
2. An overclaim that the functions are "checked against the Bridge": the
   wording is corrected and checkpoint 3 is marked blocked.
3. Point evaluation's `Malformed` was `check d = none`, which is
   tautological and called a decoding failure. It is now split into
   `PointEval.decode` and `PointEval.verifies`; `pointEval_eq_none_iff`
   states the failure as a decoding failure or a failed proof, and
   `Osaka.lean`'s docstrings say so.
4. An overclaim that subgroup membership is intrinsic: corrected above.
5. `gas_mono` is mostly trivial, and `MODEXP`'s malformed-input gas is
   `0`: both are disclosed above.
6. The SSWU default: a comment at `Bls12381.sswu` names the invariant.

Checked and found fine: the core stays dependency-free; the imports are
registered; there is no `sorry`, `native_decide`, `implemented_by` or bare
`simp`; the axiom pins hold; BLAKE2F's huge rounds and MODEXP's huge
lengths are handled; P-256's `h ≥ n`, range and key checks are right; the
extra `x = 0` rejection in `PointEval.decompress` is equivalent, since
`(0, ±2)` has order 3; the BLS12-381 `≥ p` test covers the 16 zero bytes;
`G1ADD` correctly has no subgroup check; the `stipendFits` list is right.

The finder review was cut off by a container restart and resumed after
these fixes, covering checkpoints 1–4. It found no behavioural discrepancy
of any precompile with the execution specification; it also re-checked the
isogeny constants, the MSM discount tables and the Miller loop's bit range
against py_ecc by script. Its confirmed findings, all fixed:

1. The stipend rule charged `**` one unit, while `EXP` costs 50 gas per
   exponent byte: `**` is now rejected (`pow_not_fits`).
2. The stipend rule ignored an internal call's return, though a memory
   return allocates an object of any size: only no return or one value
   return is admitted (`retOk`).
3. The Bridge table claimed `MODEXP`'s vendored output agrees on bounded
   inputs; it truncates the base to 256 bits. The row now records the
   disagreement with a counterexample.
4. Stale docstrings: `Field.lean` (failure cases), `Bn254.lean` (theorem
   names), `PointEval.decode` (check order), `Modexp.lean` (head bit
   length); the stipend docs now say compound assignments on locals are
   rejected too.

Not covered by a vector: SSWU's exceptional case `tv = 0`, which can occur
for `G1` with `u ≠ 0`; its formula is the RFC's and py_ecc's.

<!-- Generated from docs/module-map/precompiles.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
# Precompiles

| Module | What it defines |
|---|---|
| `Precompiles/Field.lean` | Shared arithmetic of the computed precompiles: `buffer_read` (`readPad`, `readNat`), big-endian words, `powMod`, `FieldOps` with `Fin p` and `Fp2 p`, affine short Weierstrass curves (`Curve`, `Pt`), `chunks`, `ofHex`, `mapM_eq_none_iff` ([precompiles.md](../feature-work/precompiles.md)). |
| `Precompiles/Pairing.lean` | `Fp12` and the optimal ate pairing check generic over BN254 and BLS12-381 (`PairingCurve.check`). |
| `Precompiles/Basic.lean` | `ECRECOVER`, `SHA256`, `RIPEMD160`, `IDENTITY` (0x01–0x04) over the approved `Hashes`/`Secp256k1` functions, with Osaka gas, never failing; length-monotonic gas. |
| `Precompiles/Modexp.lean` | `MODEXP` (0x05) with EIP-7823 bounds and EIP-7883 gas; `modexp_eq_none_iff`, `modexp_length`. |
| `Precompiles/Bn254.lean` | BN254 `ECADD`, `ECMUL`, pairing check (0x06–0x08); decoding laws (`decodeG1_eq_none_iff`) and failure cases. |
| `Precompiles/Blake2f.lean` | `BLAKE2F` (0x09), EIP-152's compression on `UInt64`; `blake2f_eq_none_iff`. |
| `Precompiles/P256.lean` | `P256VERIFY` (0x100), EIP-7951's ECDSA check on secp256r1, never failing. |
| `Precompiles/Bls12381Iso.lean` | RFC 9380's BLS12-381 isogeny constants and `G2`'s effective cofactor, as data. |
| `Precompiles/Bls12381.lean` | EIP-2537 (0x0b–0x11): `G1`/`G2` addition and MSM, pairing check, SSWU maps; failure laws and MSM gas monotonicity. |
| `Precompiles/PointEval.lean` | EIP-4844 point evaluation (0x0a): zcash `G1` decompression, the trusted setup's `[τ]G₂`, the KZG check. |
| `Precompiles/Osaka.lean` | G06's `Fixed` instantiated (`Osaka.fixed`): dispatch `run`/`gas` over `Precompile`, failure exactly on `Malformed` input (`run_eq_none_iff`), length-monotonic gas (`gas_mono`), the stipend facts. |
| `Stipend/Rule.lean` | The stipend cost rule (G06 Q3): which `receive`/fallback bodies fit 2300 gas under cold access costs (`Stipend.rule`, `progCost`, `fits_iff`), its examples and non-examples, and the compiler obligation `Obligation` (G43) ([stipend-cost-rule.md](../feature-work/stipend-cost-rule.md)). |
| `Bridge/SolidityBridge/PrecompileAgreement/Bytes.lean` | Bounded precompile-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/PrecompileAgreement/Controls.lean` | Bounded precompile-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/PrecompileAgreement/Gas.lean` | Bounded precompile-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/PrecompileAgreement/Header.lean` | Bounded precompile-agreement checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/PrecompileAgreement/Identity.lean` | Bounded precompile-agreement checkpoint; typed scope and retained obligations are stated in the module. |

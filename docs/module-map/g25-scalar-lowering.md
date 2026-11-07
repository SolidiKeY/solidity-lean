<!-- Generated from docs/module-map/g25-scalar-lowering.d/ by scripts/coord-tools/fragments.sh; edit the fragments there, not this file. -->
# G25 scalar lowering preparation

| Module | What it defines |
|---|---|
| `Backend/Scalar/Slice.lean` | Independent numeric semantics for real Backend instructions, PUSH32, sequencing and untouched tails. |
| `Backend/Scalar/Typed.lean` | Intrinsic value relation, literal selection and Boolean operation certificates. |
| `Backend/Scalar/Widths.lean` | All byte-multiple widths, signed/unsigned cleanup and unsigned cast chains. |
| `Backend/Scalar/Comparisons.lean` | Source-exact signed and unsigned ordering certificates. |
| `Backend/Scalar/Wrapping.lean` | Intrinsic unsigned wrapping add/sub/mul and width-cleanup composition. |
| `Backend/Scalar/Casts.lean` | Source-exact word-preserving uint/int casts. |
| `Backend/Scalar/Guards.lean` | Retained-operand zero tests and existing panic-byte failure selection at the component boundary. |
| `Backend/Scalar/Modular.lean` | Source-exact addmod/mulmod with unbounded intermediate arithmetic and zero-modulus failure. |
| `Backend/Scalar/Bitwise.lean` | Intrinsic unsigned bitwise AND/OR/XOR certificates. |
| `Backend/Scalar/Values.lean` | State-uniform closed intrinsic Val certificates and actual encoded-byte controls. |
| `Backend/Scalar/Checked.lean` | Scalar instruction-slice Checked contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/Division.lean` | Scalar instruction-slice Division contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/Exponentiation.lean` | Scalar instruction-slice Exponentiation contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/Heights.lean` | Scalar instruction-slice Heights contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/Negation.lean` | Scalar instruction-slice Negation contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/PowerBounds.lean` | Scalar instruction-slice PowerBounds contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/PowerGuard.lean` | Scalar instruction-slice PowerGuard contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/Shifts.lean` | Scalar instruction-slice Shifts contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/SignedBits.lean` | Scalar instruction-slice SignedBits contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/SignedChecked.lean` | Scalar instruction-slice SignedChecked contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/SignedDivision.lean` | Scalar instruction-slice SignedDivision contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/SignedGuards.lean` | Scalar instruction-slice SignedGuards contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/SignedMul.lean` | Scalar instruction-slice SignedMul contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/SignedShift.lean` | Scalar instruction-slice SignedShift contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/UnsignedMul.lean` | Scalar instruction-slice UnsignedMul contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/Axioms.lean` | Scalar instruction-slice Axioms contracts; see backend-scalar-lowering.md for exact premises and boundaries. |
| `Backend/Scalar/ArithmeticWidths.lean` | Scalar ArithmeticWidths contracts; exact source/bytecode and resource boundaries in backend-scalar-lowering.md. |
| `Backend/Scalar/Capacity.lean` | Scalar Capacity contracts; exact source/bytecode and resource boundaries in backend-scalar-lowering.md. |
| `Backend/Scalar/CastChains.lean` | Scalar CastChains contracts; exact source/bytecode and resource boundaries in backend-scalar-lowering.md. |
| `Backend/Scalar/Combinations.lean` | Scalar Combinations contracts; exact source/bytecode and resource boundaries in backend-scalar-lowering.md. |
| `Backend/Scalar/Composition.lean` | Scalar Composition contracts; exact source/bytecode and resource boundaries in backend-scalar-lowering.md. |
| `Backend/Scalar/FixedBytes.lean` | Scalar FixedBytes contracts; exact source/bytecode and resource boundaries in backend-scalar-lowering.md. |
| `Backend/Scalar/Select.lean` | Scalar Select contracts; exact source/bytecode and resource boundaries in backend-scalar-lowering.md. |
| `Backend/Scalar/WidthGuards.lean` | Scalar WidthGuards contracts; exact source/bytecode and resource boundaries in backend-scalar-lowering.md. |
| `Backend/Scalar/SignedPower.lean` | Intrinsic signed-power SignedPower slice/source/capacity contracts; see backend-scalar-lowering.md. |
| `Backend/Scalar/SignedPowerPost.lean` | Intrinsic signed-power SignedPowerPost slice/source/capacity contracts; see backend-scalar-lowering.md. |
| `Backend/Scalar/SignedPowerPrefix.lean` | Intrinsic signed-power SignedPowerPrefix slice/source/capacity contracts; see backend-scalar-lowering.md. |

| G31 preparation module | Purpose |
|---|---|
| `Backend/Environment/Observations.lean` | Actual environment opcode selection, local stack semantics, address truncation and intrinsic expression/world observation certificates. |
| `Backend/Environment/ObservationsChecks.lean` | Inhabited environment witnesses, distinguishing negative controls and headline axiom pins. |
| `Backend/Environment/Metadata.lean` | Typed metadata PUSH encoding, source declaration selection, selector numeric/ABI alignment, truncation and function/address projections. |
| `Backend/Environment/ByteConstants.lean` | Byte-valued resolved metadata materialization through PUSH/MSTORE8, exact byte order and memory-frame laws. |
| `Backend/Environment/MetadataChecks.lean` | Metadata byte regressions, UTF-8 witness, missing metadata refusals and axiom pins. |
| `Backend/Environment/Crypto.lean` | Executable memory Keccak slices, existing intrinsic hash denotation, exact normalized bytes, argument failure/success, and read-only precompile invocation selection. |
| `Backend/Environment/Namespace.lean` | ERC-7201's actual two-hash instruction slice, wrapping predecessor, exact ABI-word second preimage and low-byte clearing. |
| `Backend/Environment/CryptoChecks.lean` | Inhabited typed heap/path hash controls, ecrecover positive/fallback, exact opcode bytes, namespace witness and axiom pins. |
| `Backend/Environment/Composition.lean` | Constructed intrinsic Val certificates, exact target concatenation/stack order, materialization/hash adapters and typed source-sequence fallback. |
| `Backend/Environment/Frames.lean` | Exact environment/ledger-footprint stability, repeated BALANCE/EnvKey reads, source/oracle framing and exhaustive composed opcode refusals. |
| `Backend/Environment/CompositionChecks.lean` | Inhabited mixed environment/metadata/hash certificate, retained source effects, order/forced-credit/time counterexamples and axiom pins. |

# VX1 OOM split of the power thresholds

| Module | What it defines |
|---|---|
| `Backend/Scalar/PowerBounds/Part01.lean` | Generated power-threshold rows for widths 8–32 and their kernel-checked bounds (`rowBounds`); split from `PowerBounds.lean`, which assembles `threshold_bounds`, to keep each module under the 8 GiB pre-gate bound. |
| `Backend/Scalar/PowerBounds/Part02.lean` | Generated power-threshold rows for widths 40–64 and their kernel-checked bounds (`rowBounds`); split from `PowerBounds.lean`, which assembles `threshold_bounds`, to keep each module under the 8 GiB pre-gate bound. |
| `Backend/Scalar/PowerBounds/Part03.lean` | Generated power-threshold rows for widths 72–96 and their kernel-checked bounds (`rowBounds`); split from `PowerBounds.lean`, which assembles `threshold_bounds`, to keep each module under the 8 GiB pre-gate bound. |
| `Backend/Scalar/PowerBounds/Part04.lean` | Generated power-threshold rows for widths 104–128 and their kernel-checked bounds (`rowBounds`); split from `PowerBounds.lean`, which assembles `threshold_bounds`, to keep each module under the 8 GiB pre-gate bound. |
| `Backend/Scalar/PowerBounds/Part05.lean` | Generated power-threshold rows for widths 136–160 and their kernel-checked bounds (`rowBounds`); split from `PowerBounds.lean`, which assembles `threshold_bounds`, to keep each module under the 8 GiB pre-gate bound. |
| `Backend/Scalar/PowerBounds/Part06.lean` | Generated power-threshold rows for widths 168–192 and their kernel-checked bounds (`rowBounds`); split from `PowerBounds.lean`, which assembles `threshold_bounds`, to keep each module under the 8 GiB pre-gate bound. |
| `Backend/Scalar/PowerBounds/Part07.lean` | Generated power-threshold rows for widths 200–224 and their kernel-checked bounds (`rowBounds`); split from `PowerBounds.lean`, which assembles `threshold_bounds`, to keep each module under the 8 GiB pre-gate bound. |
| `Backend/Scalar/PowerBounds/Part08.lean` | Generated power-threshold rows for widths 232–256 and their kernel-checked bounds (`rowBounds`); split from `PowerBounds.lean`, which assembles `threshold_bounds`, to keep each module under the 8 GiB pre-gate bound. |

Memory-loop validation helpers: `scripts/memory-loop-evm.mjs` records actual
four-mode upstream EVM observations and refusal controls;
`scripts/check-memory-loop-timing.py` freshly checks the entire original
`Derived17` group; `scripts/check-memory-loop-timing.mjs` validates cumulative
300-second evidence, with negative controls in its `.test.mjs` companion.

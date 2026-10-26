# ABI, hashes and concatenation

Inventory status: partial. Regressions: `Examples/Tactics/AbiFeatures.lean`,
`Examples/Tactics/AbiFeaturesImport.lean` (`tests/abi-0.8.38/Features.sol`),
`Examples/Tactics/Recovery.lean`, `Examples/Tactics/AbiHexCall.lean`
(`tests/abi-0.8.38/HexCall.sol`).

## Supported

- **ERC-7201** (`Solidity/ERC7201.lean`). `ERC7201.root` is the namespace
  formula over bytes: Keccak-256, minus one modulo 2^256, ABI-encode, hash
  again, clear the low byte. Literal calls fold at elaboration; runtime calls
  use the same hash, encoding and wrapping arithmetic. `root_aligned` proves
  the low-byte invariant for every identifier. The result gives no access to
  physical storage layout.
- **`ecrecover`** (`Solidity/Secp256k1.lean`): a bounded 256-bit modular
  exponentiation and scalar walk. Coordinates and scalars are `Fin`; points
  carry their curve equation and every result is checked. Inputs enter as
  naturals, so malformed ABI input is admitted and then validated. High-s
  signatures, v = 27/28 and 0 < r, s < n are accepted; a missing square root or
  infinity fails. The hash symbol and taclet read an `@[irreducible]`
  interpretation, so symbolic proofs do not unfold recovery.
- **`abi.encodeWithSignature`** hashes the literal's UTF-8 bytes once.
- **External function values** keep their ABI `bytes24` type before address
  and selector become arithmetic: standard encoding right-pads to 32 bytes,
  packed takes 24.
- **`abi.encodeCall`** reads parameter spellings before dispatch
  canonicalization erases widths, then checks arity, primitive kinds, integer
  widths, fixed-byte widening and function components, and applies contextual
  conversions. A computed receiver is evaluated before the arguments even when
  its selector folds. Local function values and `this.f` keep their own
  identities when a local shadows `f`. Discarded builtin calls go through the
  same validation.
- **Exact-width hex arguments.** The target is resolved by solc's
  `referencedDeclaration`. A direct numeric hex literal gets `bytesN` context
  only when its token has exactly `2*N` hex digits and its compiler type is a
  numeric constant (leading zeros, mixed case, separators and parentheses
  around one argument allowed). The result is `Fin (2^(8*N))`; the raw AST is
  importer evidence only. Parentheses around a whole multi-argument tuple make
  one component and are not flattened.
- **`bytes.concat`/`string.concat`** check their argument kinds, nested
  concatenations and explicit casts included.
- **Decoder bounds.** Offsets and lengths are checked against the remaining
  input before arithmetic, traversal or allocation, so a maximal encoded length
  cannot overflow the check or start a huge allocation. Unaligned and
  overlapping offsets that solc accepts stay accepted: a decoder must not
  impose the encoder's canonical layout.

## Refused, and why

- Internal function markers in an encoding, where the metadata keeps them.
- An implicit fixed-byte narrowing in `encodeCall`.
- Decimal numerals, short or long hex tokens, arithmetic, typed numeric locals
  and 40-digit address literals as `bytesN` arguments: no contextual coercion.
  `abi.encode(0xabcd)` keeps its numeric word layout. The `sol{}` DSL erases
  literal spelling, so it needs an explicit `bytes2(0xabcd)`.

## Decisions

- No collision-freedom, authorization, primality, group-law or recovery axiom.
  The vector proofs are concrete reductions, not a theorem of equivalence with
  the EVM precompile. Semantic and calculus proofs refer to the executable
  interpretation. Opacity of recovery dates from `7d57d9c0` as an
  unimplemented boundary, not a speed optimization.
- `scripts/solc-ast.mjs` accepts an explicit compiler only with its checksum,
  source and output, and never repins the frozen SolKeY compiler or fixtures.

## Left

- Struct enum members lose nominal identity and cardinality in
  `Contract.spellTy`/`enumRows`, and function mutability and some aggregate
  function markers are absent, so exact legality and enum decoding wait on
  the declaration metadata ([declarations-metadata.md](declarations-metadata.md)).
- Arrays of hex literals and other aggregate contextual coercions.
- ABI identity of inherited renamed function values.
- ABI traversal of recursive graphs ([recursive-types.md](recursive-types.md)).
- External reference-valued returns: `ExtResult` carries only primitive words.
- Dynamic recursive round-trip proofs; the recovery/precompile equivalence.

## Reproduction

```sh
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/abi-0.8.38/Features.sol --out tests/abi-0.8.38/Features.ast.json \
  --wrapper Solidity/Examples/Tactics/AbiFeaturesImport.lean
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/abi-0.8.38/HexCall.sol --out tests/abi-0.8.38/HexCall.ast.json --no-wrapper
node scripts/check-abi-vectors.mjs COMPILER_FILE EXTERNAL_NODE_MODULES
node scripts/check-abi-hex-call.mjs /external/node_modules \
  /path/to/soljson-v0.8.38+commit.1835d247.js /path/to/soljson-v0.8.34+commit.80d5c536.js
```

The checkers run Cancun bytecode with EthereumJS VM/common/util 10.1.3 and
ethers 6.17.0, installed outside the Lean package.

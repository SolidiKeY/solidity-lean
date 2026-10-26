# ABI, hashes and concatenation

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

## M1: computed recovery and ABI boundary repairs (2026-10-25)

`ERC7201.root` implements the namespace formula over bytes: Keccak-256,
subtract one modulo 2^256, ABI-encode that word, hash again and clear the low
eight bits. Literal calls fold at elaboration; runtime calls use the same
existing hash, encoding and wrapping arithmetic operations. `root_aligned`
proves the low-byte invariant for every identifier; empty, UTF-8 and the
OpenZeppelin ERC20 namespace have kernel-checked value proofs. Source fixtures
exercise both constant declarations and runtime strings, including whitespace.
The resulting integer gives no access to physical storage layout.

`abi.encodeWithSignature` now hashes the literal's original UTF-8 bytes;
it previously encoded each byte as a Unicode character a second time.
External function values retain their ABI `bytes24` type before their address
and selector become arithmetic: standard encoding is right-padded to 32 bytes,
packed encoding occupies 24 bytes. Internal function markers are refused where
the existing metadata retains them.

`abi.encodeCall` obtains parameter spellings before dispatch canonicalization
erases source widths. It checks the tuple's arity, primitive kinds and integer
width conversions, fixed-byte widening and function parameter/return components,
then applies contextual encoding conversions. Fixed-byte literals align to their
parameter type; an implicit narrowing is refused. Bare local function values
and explicit `this.f` members retain their own identities when a local shadows
`f`. A computed receiver is evaluated before the arguments even when its
selector folds to a constant; its failures and effects remain observable.
Discarded builtin calls pass through the same whole-expression validation
and lowering as used values. `bytes.concat` and `string.concat` validate their
source argument kinds, including nested concatenations and explicit casts.

Recursive decoder offsets and lengths are checked against remaining input
before addition, multiplication, traversal or allocation. This prevents a
maximum-size encoded length from overflowing the check or starting an enormous
allocation. Integer range and fixed-byte padding failures remain failures.
Unaligned and overlapping offsets accepted by solc remain accepted; a decoder
must not impose the encoder's strict canonical layout on every input.

`Secp256k1` replaces recovery's executable zero placeholder with a bounded
256-bit modular exponentiation/scalar walk. Coordinates and group scalars have
`Fin` types; points carry their curve equation and every constructed result
is checked. The boundary uses natural numbers to admit malformed ABI inputs,
then validates and enters those bounded types. Recovery accepts high-s
signatures, v=27/28, and 0<r,s<n; a missing square root or infinity fails.
The existing hash symbol and taclet read its `@[irreducible]` interpretation,
so symbolic proofs do not unfold the recovery computation by default.

No collision-freedom, authorization, primality, group-law or recovery axiom
was added. The vector proofs establish concrete reductions, not modular
inversion/group-law correctness or a general equivalence theorem for an
external EVM precompile. Existing semantic and calculus proofs continue to
refer to the executable interpretation. Concrete recovery costs more than
returning zero; three compiled valid recoveries took 16 ms locally. History
`7d57d9c0` introduced opacity as an unimplemented recovery boundary, not as a
previous computational optimization.

### Reproduction and review

`tests/abi-0.8.38/Features.sol` is compiled by exact solc
`0.8.38+commit.1835d247`, SHA-256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
The separate AST and importer hash do not repin the frozen SolKeY compiler or
fixtures. `scripts/solc-ast.mjs` accepts an explicit compiler only together
with its checksum, source and output. The standard invocation still uses
SolKeY's compiler/checksum. Regenerate this fixture with:

```sh
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/abi-0.8.38/Features.sol --out tests/abi-0.8.38/Features.ast.json \
  --wrapper Solidity/Examples/Tactics/AbiFeaturesImport.lean
```

`node scripts/check-abi-vectors.mjs COMPILER_FILE EXTERNAL_NODE_MODULES` checks
that same compiler and executes its Cancun bytecode with EthereumJS
VM/common/util 10.1.3 and ethers 6.17.0. Those are optional reference-test
dependencies, installed outside this dependency-free Lean package. The suite
passes 31 ABI, namespace and recovery vectors and five compiler rejection cases, including invalid values,
nonresidue, infinity, digest reduction, high-s and three different private keys.
`Examples/Tactics/AbiFeatures.lean`, `AbiFeaturesImport.lean` and `Recovery.lean`
pin matching Lean runs, rejected source conversions and kernel proofs. The
false source namespace assertion must panic; it is never reported as proved.

The read-only finder and skeptic reviewed ABI lowering and recovery without
calling Lean. Confirmed fixes cover UTF-8 selector hashing, implicit conversion
checks, discarded builtin statements, explicit-member shadowing, nested string
concatenation type preservation, and frozen-fixture safety of compiler overrides.
They found no concrete arithmetic defect in recovery or remaining decoder-bound
overflow in the reviewed paths. Both reviewers also confirmed the final computed
receiver evaluation order. Final validation results are recorded below.

### Remaining interfaces and proof limits

The feature catalog keeps general ABI coverage partial. Struct enum members
lose nominal identity/cardinality in `Contract.spellTy`/`enumRows`; function
mutability and some aggregate function markers are also absent. Exact legality
and enum decoding require the declarations/type metadata group to preserve them.
The source reader now consumes exact-width hex evidence at direct fixed-byte
`abi.encodeCall` parameters (M2 below). The handwritten `sol{}` DSL still erases
numeric literal spelling and requires an explicit `bytes2(0xabcd)` argument.
It does not accept decimal `43981` as an implicit fixed-byte argument. Arrays
of numeric hex literals and other aggregate contextual coercions remain open.
Inherited renamed function values still need their source ABI identity.
Recursive-type work must supply its agreed graph representation before ABI
traversal can cover those graphs. No second graph representation was introduced.
External reference-valued return decoding needs the calls/world group's typed
return/response interface; the current primitive-word `ExtResult` cannot carry
such decoded values. Dynamic recursive roundtrip proofs and the general
recovery/precompile equivalence theorem remain open. Source/compiler/EVM
conformance tests do not replace a frontend-equivalence proof.

### Final validation

The final `./run-lean.sh` returned success with the frozen rules entry file:
584 library jobs, 243 TestSuite jobs, and 377 taclets/131 read-bearing
annotations with zero mismatches. The existing decision example took 819 s
(the prior group's successful build recorded 890 s). Focused per-file MCP
error diagnostics passed for the computational modules, heap, elaborator and
regression modules. The source namespace assertion and guarded-byte roundtrip
are kernel-checked proofs.

The frozen corpus gate passes all 774 pinned obligations without verdict or
generated-output drift. The TestSuite audit records 552 derived, 11 refuted,
zero pending and one excluded obligation (plus two skips). The automation audit
records 491 automatic and 61 budgeted obligations, 11 refuted and zero pending.
The existing declaration-metadata Node regression also passes. Its subprocess
launcher needs execution outside the PID sandbox (`EPERM` inside); its test
expectations were not changed here.

The namespace/alignment value proofs depend only on `propext`/`Quot.sound`;
the byte and source proofs add only `Classical.choice`. `recover_generator`
uses no axioms; `recover_address` and `ecrecoverKey` use only `propext`.
No new axiom, native-decision proof or external Lean dependency was introduced.
The temporary axiom-audit source was removed.

The optional reference suite passes 31 pinned-solc/EVM vectors and five source
rejection cases. Three compiler-option rejection checks pass, and reproducing
the default frozen TestSuite AST with its original source-header path yields
byte-for-byte identical bytes. The original fixture and wrapper remain intact.

The feature audit covers 211 features/783 upstream symbols. The layer audit
covers 126 core modules with no path to the elaborator. Orphan checking retains
the 33 pre-existing scratch modules; documentation checking retains 13 existing
missing vendor/external references. No new finding was added to either list.
`git diff --check` is clean. Changes are uncommitted; the shared checkout's
other feature-group edits and unrelated logs were preserved.


## M2: source hex-width boundary (2026-10-26; worker handoff was patch_ready_unvalidated)

The source importer resolves an `abi.encodeCall` target by retained solc
`referencedDeclaration`, then reads fixed-byte widths from its public/external
function declaration or external function-variable signature. Before generic
constant normalization, a direct numeric hex literal can acquire `bytesN`
context only when its original token has exactly `2*N` hex digits and its
compiler type is a numeric constant. Leading zeros, mixed case, legal digit
separators and parentheses around individual scalar arguments survive this
check. The admitted result is `Fin (2^(8*N))`; no new core value or statement
representation is introduced. The raw AST is importer evidence only.

Decimal numerals, short/long hex tokens, arithmetic expressions, typed numeric
locals, missing evidence and address-typed 40-digit literals get no new
coercion. Existing type checking handles their rejection. Ordinary
`abi.encode(0xabcd)` keeps its numeric word layout. Byte-typed metadata such as
`this.f.selector` retains its established kind when this contextual path is
used. Tuple arity is preserved: extra parentheses around an entire
multiargument tuple create one component and must not be flattened into a
compiler-accepted call. No decoder, crypto implementation, frame or loop API
changes are included; solc's accepted noncanonical decoder layouts remain
unchanged.

`tests/abi-0.8.38/HexCall.sol` and its independently pinned 0.8.38 AST exercise
eight positive source cases and one deliberately false assertion.
`Examples/Tactics/AbiHexCall.lean` supplies exact-width/rejection proof scripts,
declaration-identity and malformed-input guards, concrete imported executions,
a universal exact-width property and a refutation of the false property. These
Lean scripts have **not** been elaborated or kernel-checked in the patch worker.
The primary integrator owns those checks and the axiom audit after merging.
No axiom, admitted proof, unsafe/native proof shortcut, raised heartbeat limit
or external Lean dependency is introduced by the patch text.

Regenerate only the new fixture (the frozen TestSuite pin remains intact):

```sh
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/abi-0.8.38/HexCall.sol --out tests/abi-0.8.38/HexCall.ast.json --no-wrapper
node scripts/check-abi-hex-call.mjs /external/node_modules \
  /path/to/soljson-v0.8.38+commit.1835d247.js /path/to/soljson-v0.8.34+commit.80d5c536.js
```

The optional reference checker pins both compiler bytes and versions, then
executes legacy and via-IR Cancun code with the M1 external Node dependencies.
In the patch worker it passed 32 positive executions, four assertion panics
with code 1, and 40 compiler rejections across the four configurations.
Rejections cover decimal/width/type/arithmetic/address mismatches, tuple
shape, omitted components and invalid separators. These are concrete vectors,
not a general compiler/frontend or cryptographic correctness theorem.

Read-only finder/skeptic review covered declaration resolution, lexical width,
scalar parentheses, function-variable targets and preserved selector kinds.
Pinned compiler rejection of whole-tuple grouping prompted a correction to
keep direct components. The final review found no further concrete blocker.
The group remains incomplete for enum/cardinality decoding, inherited renamed
ABI identity, recursive ABI graphs, external reference-valued returns and the
general recovery/precompile equivalence theorem. The site manifest is left to
the primary integrator under the patch-only workflow.

# Roadmap G00: profile pins, exclusion evidence and owners

This is the G00 deliverable of the [full compiler roadmap](../coverage-plan.md#wave-0--scope-interfaces-and-measured-baseline-g00g07).
It records the pinned identities, the evidence behind every recorded exclusion,
a mechanical reconciliation of the [feature manifest](../solidity-features.json)
and the [upstream ledger](../solidity-upstream-inventory.json), and an owning
roadmap group for every in-profile obligation. It decides no scope: an
exclusion without an attributable user decision stays **unresolved**, and the
questions that need the user are in [Open scope questions](#open-scope-questions).

- **Base revision:** `127c2ee59de16971e45b08a2def54f4e5fae8e2a` ("Refresh
  integration"). Every count, line number and status below is pinned to it.
- **Changed files:** this document, `scripts/roadmap-g00-scope.py`, one status
  line in `coverage-plan.md`, one index line in `docs/README.md`. No Lean
  module, feature JSON, generated file or TestSuite file changed; no feature
  status was promoted or demoted.
- **Result:** 212 manifest rows = 174 in-profile (all owned) + 8
  upstream-rejected + 30 unresolved exclusions; 783 ledger symbols = 455
  in-profile + 50 combinations with an unresolved part + 52 combinations with
  an upstream-rejected part + 169 unresolved + 57 upstream-rejected.
  **No exclusion is confirmed** by an attributable user decision.

## Method and reproduction

```sh
# Regenerate the ledger tables below (between the generated markers).
python3 -I scripts/roadmap-g00-scope.py --write
# Consistency: every in-profile row owned, every excluded row has an evidence
# entry, every owner is a roadmap group, combination IDs have the stated scope,
# and the generated block is current.
python3 -I scripts/roadmap-g00-scope.py --check
# The manifest's own generated-file and classification check (unchanged).
python3 scripts/solidity-feature-audit.py --check
```

The script is stdlib-only and read-only. It classifies a manifest row by its
recorded `scope`: `model` and `abstract` are **in-profile**; `upstream`
(removed, reserved or upstream-incomplete syntax) is **upstream-rejected**,
which is evidence from the pinned compiler, not a user exclusion, and still
owes a precise rejection; `exclude` is **unresolved** until the user confirms
it. A ledger symbol takes the status of all its target rows, or a
`combination-*` status when it maps to in-profile and other rows. The
evidence tiers and the owner table are data in the script; the history that
backs the tiers is in [Exclusion evidence](#exclusion-evidence).

Pins were collected with `git grep` over the files named in each row; the
exclusion history with `git log -p --follow docs/solidity-scope.md`,
`git log -- docs/solidity-features.json` (each revision's exclusion set was
diffed), `git log -S` on the older out-of-scope prose and a GitHub read of
PR #5. Declarations were located with `git grep -n` at the base.

## Pins

| Identity | Pinned value | Where |
|---|---|---|
| Language/catalog | Solidity **0.8.38**, `argotorg/solidity` tag `v0.8.38`, commit `1835d247de183f23e7b0e2bc4a50732af525b77c`; 19 hashed upstream source files including the ANTLR grammar `docs/grammar/SolidityParser.g4`/`SolidityLexer.g4` at that commit (the pinned grammar; upstream paths, not files of this repository); audited 2026-10-25 | `docs/solidity-features.json` (`upstream`), `docs/solidity-scope.md`, `docs/solidity-upstream-inventory.json` (`commit`) |
| Catalog compiler binary | `soljson-v0.8.38+commit.1835d247.js`, SHA-256 `6c74ffba…4312d390`, version `0.8.38+commit.1835d247.Emscripten.clang` | `Solidity.Frontend.Source.Compiler.version`/`.file`/`.sha256`, `Solidity/Frontend/Source.lean:23`, `:27`, `:31`; `scripts/solc-ast.mjs:141` |
| Legacy SolKey compiler binary | `soljson-v0.8.34+commit.80d5c536.js`, SHA-256 `c8649f8d…a6cfd11d8` | same declarations; `scripts/solc-ast.mjs:138`, `scripts/solc-unit.mjs:15` |
| Upstream test snapshot | `tests/upstream/solidity-0.8.38.tar.gz` (the complete upstream test tree at `1835d247`), schema submodule `937e3484cb4cf408a4e808d62f34285a71fece80`, 11,622 files in `tests/upstream/snapshot.json` | `docs/solidity-upstream-tests.md` |
| SolKey | commit `473da8944ca7329e6b76819863591407db26e7ec`, manifest SHA-256 `c8d6166c…a1b37` | `tests/migration/solkey.pin.json`, `docs/solkey-migration.md` |
| Lean | `leanprover/lean4:v4.24.0` | `lean-toolchain`; `Bridge/lakefile.toml` pins Mathlib `v4.24.0`, CSLib `e1fea78…` |
| Bridge EVM | EVMYulLean commit `047f63070309f436b66c61e276ab3b6d1169265a`, `TargetSchedule := "Cancun"` | `Bridge/vendor/EvmYul/VENDOR.md`, `Bridge/vendor/EvmYul/Wheels.lean:148` |
| Reference EVM (external, not a proof) | EthereumJS vm/common/util/evm 10.1.3, ethers 6.17.0 | `docs/solidity-upstream-tests.md`, `scripts/evm-reference/replay.mjs:187` |
| Accepted provenance settings | keys `viaIR`, `evmVersion` (one of 14 targets `homestead`…`osaka`), `optimizer {enabled, runs}`, `libraries` (must be empty), `remappings` (compilation units only), `outputSelection` = AST only; pipeline `legacy`/`viaIR`; ABI coder v1/v2 (via-IR forces v2) | `validateSettings`, `Solidity/Frontend/Source.lean:169`; `Solidity.Frontend.Source.Pipeline`, `:41`; `Solidity.Frontend.Source.Provenance.effectiveCoder`, `:148` |
| EVM target used by tooling | `osaka`: upstream runner (`scripts/solidity-upstream.mjs:356`, `:533`), generated differential (`scripts/evm-reference/generated.mjs:50`), reference replay (`scripts/evm-reference/replay.mjs:51`), AST helper default (`scripts/solc-ast.mjs:155`); 3,673 fixture `evmVersion` records | as listed |
| Source evaluation order | default legacy; `Contract.evalOrder := .viaIR` selects source order | `Solidity/Syntax/Raw.lean:441`; `docs/options.md` (O9) |

### Pin disagreements

1. **Two solc versions.** The profile, catalog and upstream corpus are 0.8.38;
   the frozen SolKey boundary, `scripts/solc-ast.mjs`'s default and 36
   fixture JSON files (29 under `tests/solc`, 7 under `tests/upstream`) still
   use 0.8.34; 189 fixture JSON files use 0.8.38. `parseCompiler` (`Solidity/Frontend/Source.lean:154`) accepts
   exactly these two. The source pragmas in `tests/solc/*.sol` range from
   `^0.8.0` to `^0.8.38`. Owner: G05 (provenance) and G53 (SolKey re-pin).
2. **Two EVM forks.** Osaka for the upstream runner, generated differential
   and replay; **Cancun** for every hand-written vector script
   (`scripts/check-abi-vectors.mjs:39`, `check-call-exception-vectors.mjs:37`,
   `check-modifier-frames.mjs:27`, `check-recursive-types.mjs:21`,
   `check-slice-copies.mjs:28`, and the other `check-*.mjs` EVM runners), 152
   fixture records (`tests/solc`, `tests/upstream/revert-power`,
   `tests/upstream/step08-transient-world`) and the vendored bridge EVM
   (`TargetSchedule := "Cancun"`). The core `Solidity/Evm` machine records no
   fork at all. The roadmap's "pinned EVM semantics" (G06) has no chosen fork.
3. **Amsterdam.** `blockSlotnum` is described as Amsterdam-gated, but no
   accepted `evmVersion` (the list ends at `osaka`) can express it.
4. **Optimizer settings vary by tool** (upstream runner: on for syntax tests,
   `runs: 200`; replay/AST helper: off; hand vectors: on; generated
   differential: both). These configure the external solc oracle only; this
   repository's compiler has no solc-optimizer setting.
5. **Linked libraries.** `validateSettings` rejects any `libraries` entry
   ("library linking is not in this source boundary"), while
   `externalLibraryCalls` is an in-profile `abstract` row and G42.04/G44.02
   own linking. The provenance boundary is narrower than the profile.
6. **Two evaluation orders.** The source model supports both legacy and
   via-IR operand order; the roadmap requires recording the selection but no
   document says which order(s) the compiled output must implement.

Facts in rows 1, 2 and 5 sit in code that in-flight lanes edit
(`Solidity/Frontend/`, `Solidity/Evm/`, ABI/call paths); they are claims about
the base revision only.

## Exclusion evidence

**History.** The repository history starts at root commit `c3a3eef`
(2026-10-24); earlier history was pruned. All 30 `scope: exclude` rows were
created by commit `419f8a4` ("Audit Solidity language features and define
model scope", 2026-10-24), the single commit of GitHub PR #5 from branch
`codex/solidity-feature-audit`. The PR was opened at 23:21:50Z and merged by
the repository owner at 23:22:28Z with no review and no comment; its body
describes a classification, not a user decision. The scope document it added
calls itself "a proposed scope contract". Diffing every later revision of the
manifest shows the exclusion set unchanged except `creationCode` and
`runtimeCode`, which moved from `exclude` to `model` in `b514bbb` (reverted
and restored again in the `692a60c`/`1bb91e9` merges). No commit message in
the 361-commit history records an approval of any exclusion. The roadmap
(`6f267cc`, "Plan full compiler") calls these families "recorded" and states
that a manifest exclusion without evidence is a scope question.

Before PR #5, the root commit's `docs/semantic-gaps.md` (section "Out of
scope: the EVM inside Solidity", `git show c3a3eef:docs/semantic-gaps.md`,
lines 41–64) already said these are "left out on purpose": inline assembly
other than the canonical rethrow, `address.code`, `extcodesize`, `gasleft()`,
gas stipends beyond `transfer`/`send`, `selfdestruct`, `create2` salts, raw
calldata/returndata and low-level `call(data)`, block and transaction fields
other than `block.timestamp` ("not `block.number`, `tx.origin`,
`block.basefee`, …"), storage layout, and logs. That text is a recorded design
intent, but commits in this repository are authored under the owner's name
whether a person or an agent wrote them, so it is not an attributable
approval either. The section was removed in the later documentation pruning.

**Tiers** (the `evidence` column of the manifest table):
- **B** (12): named in the root-commit text — `inlineAssembly`, `gasleft`,
  `rawCalldata`, `rawReturndata`, `lowLevelCall`, `selfdestruct`,
  `create2Salt`, `addressCode`, `eventLog`, `blockNumber`, `txOrigin`,
  `blockBasefee`.
- **B-** (11): only a generic clause there — `gasOption`, `storageLayout`
  (`layout at` not named), `machineResources` (root
  `compiler-verification.md`: "no gas, no stack limit", a model property),
  `blockCoinbase`, `blockDifficulty`, `blockPrevrandao`, `blockGaslimit`,
  `blockChainid`, `blockBlobbasefee`, `blockSlotnum`, `txGasprice`.
- **C** (7): first appear in `419f8a4` — `delegatecall`,
  `lowLevelStaticcall`, `addressCodehash`, `memoryLayout`, `transientLayout`,
  `blockhashBuiltin`, `blobhashBuiltin`.

**Classification: 0 confirmed-with-evidence, 30 unresolved.** Each is an open
scope question (Q1). Until it is answered the recorded profile is preserved
(the roadmap's rule): admission keeps refusing these rows with their
structured diagnostics, and no further exclusion is added. The Lean catalog
proves the diagnostics match the recorded rows — `Solidity.Language.Unmodelled.excluded`
(`Solidity/Language/Features.lean:1910`) and
`Solidity.Language.Feature.exclusion_complete` (`:1936`), over
`Solidity.Language.Unmodelled` (`:1771`) and `BlockField` (`:1748`); those
theorems are about the recorded classification, not about approval.

**Not exclusions.** Three other recorded boundaries look like exclusions but
are in-profile work under the roadmap's rule that refusals and limits are not
exclusions:
- `docs/solc-alignment.md`, "Remaining deltas (documented, intentionally out
  of scope)": collapsed panic classes (owner `panicCodes`: G21/G38), via-IR
  modifier parameter re-initialisation (`modifiers`/`evaluationOrder`:
  S03.02/G19), `push` over a recycled slot and the missing `2^64` length
  bound with Panic 0x41 (`arrayPush`/`defaultInitialization`: S04.01/G30).
- The importer's `Gap.excluded` for representation limits such as recursive
  structs (`recursiveTypes`: G18.01/G27.04/G35.05), as `solidity-scope.md`
  already says.
- The `libraries`-must-be-empty provenance setting (disagreement 5).

## Open scope questions

None blocks the rest of G00; each needs a user decision.

- **Q1 — the 30 recorded exclusions.** Confirm or reject each row (or each
  tier). Evidence: PR #5 merged unreviewed; tier B/B-/C history above. A
  rejected row becomes in-profile work with the owners its feature family
  implies (environment rows → S04.02/G23/G31/G46.04; call/code rows →
  S03.03/G22/G42/G47; layout rows → G27/G32/G46; logs → G23/G31/G41/G46).
- **Q2 — abstraction premises of the 23 `abstract` rows.** They are
  in-profile, but the roadmap permits "only approved environment/resource/
  cryptographic premises" and their abstraction (no-callback interpretations,
  opaque/externally interpreted hashes and `ecrecover`, `worldAssumptions`,
  the payment-acceptance boolean) was also classified by `419f8a4`. Which
  existing premises are approved as stated? (Rows: `externalFunctionTypes`,
  `tryStatement`, `canonicalRethrow`, `keccakBuiltin`, `sha256Builtin`,
  `ripemd160Builtin`, `ecrecoverBuiltin`, `msgSender`, `msgValue`,
  `thisAddress`, `addressBalance`, `blockTimestamp`, `externalTypedCalls`,
  `sendTransfer`, `emptyDataValueCall`, `newContract`, `creationTry`,
  `callbackSemantics`, `externalLibraryCalls`, `abiEntryValidation`,
  `constructorLifetime`, `staticCallRestriction`, `worldAssumptions`.)
- **Q3 — EVM fork.** Osaka or Cancun (disagreement 2) for the pinned EVM
  semantics and the target of compiled bytecode; and whether `blockSlotnum`
  needs an Amsterdam target if Q1 readmits it.
- **Q4 — evaluation order and settings.** Must the compiler implement both
  legacy and via-IR operand order as a setting, or one of them? Which ABI
  coder settings (v1 pragma) and which solc versions (0.8.34 fixtures) are in
  the frozen profile beyond 0.8.38?
- **Q5 — static code constants.** `creationCode`/`runtimeCode` are in-profile
  only "with matching compiler/source/settings artifact inputs", i.e. solc
  artifacts. For this repository's compiler, the value is its own output; an
  independent source semantics (roadmap obligation: not defined by running
  the compiler) needs an agreed interpretation (G01 decides the interface).

## Owners

**Composition owners of every row** (stated once, not repeated in the table):
S05 (source ledger against G00), G03 (constructor → theorem ledger and
combinations), G15 (admission classification), G48 (frontend coverage), G49
(runtime theorem, coverage, non-vacuity), G50 (deployment/transactions), G51
(calculus soundness and specification transfer), G52 (differential tests),
G53 (SolKey/corpus), G54/G55 (closure and final audit). G01 fixes the
interfaces each owner proves against; G04 maps existing compiler restrictions
to these owners; G06/G46 own the EVM side of every backend column.

**Rejection owners.** Unresolved exclusions: S00 (syntax outside the profile
for precise rejection) and G15 (exact classification), with the observation
boundary in G01/G06. Upstream-rejected rows: S00, G08, G11, G15.

**Ownership gaps** (no roadmap row names the obligation):
1. **Compiler-settings surface** — which settings (evaluation order, ABI
   coder, EVM target, solc version for fixtures) the public theorem
   quantifies over. G01/G05/G06 touch it; none owns the choice (Q3, Q4).
2. **Provenance boundary vs linked libraries** — `validateSettings` rejects
   `libraries`; G42.04/G44.02 own linking but not the frontend settings
   validator. Natural owner G05, not stated there.
3. **Static code constants** (Q5): S04.02 cannot define them without a G01
   decision; G44.02 owns the artifacts.
4. **The fork pin itself** (Q3): G06 owns "pinned EVM semantics" but the
   bridge (Cancun) and tooling (Osaka) disagree; nobody owns reconciling the
   hand-written Cancun vector scripts.
5. **Combinations through shared punctuation** (the `combination-*` symbols
   below) have no feature-level owner; G15 owns them through extraction, and
   the scope document already notes the ledger cannot serve as the extractor.

Every one of the 174 in-profile rows has a source, syntax, lowering and
backend owner in the table (`--check` enforces it); `comments` has no lowering
or backend obligation (`—`).

## Ledger

<!-- BEGIN generated by scripts/roadmap-g00-scope.py -->
Manifest pin: `argotorg/solidity` `v0.8.38` `1835d247de183f23e7b0e2bc4a50732af525b77c`, 19 inspected files; ledger commit `1835d247de183f23e7b0e2bc4a50732af525b77c`.

### Counts

| G00 status | manifest scope | rows |
|---|---|---|
| in-profile | abstract | 23 |
| in-profile | model | 151 |
| unresolved | exclude | 30 |
| upstream-rejected | upstream | 8 |
| **total** | | **212** |

Current statuses at the base (informative; G00 does not change them): abstract/partial 21, abstract/present 2, exclude/notApplicable 30, model/missing 1, model/partial 139, model/present 11, upstream/notApplicable 8.

| upstream symbols | count |
|---|---|
| combination-unresolved | 50 |
| combination-upstream | 52 |
| in-profile | 455 |
| unresolved | 169 |
| upstream-rejected | 57 |
| **total** | **783** |

Manifest rows with no ledger symbol (semantic requirements, enumerated by hand): 26 — `callbackSemantics`, `checkedArithmetic`, `constructorLifetime`, `danglingReferences`, `defaultInitialization`, `deleteMappingTails`, `evaluationOrder`, `extensionCalls`, `implicitConversions`, `machineResources`, `memoryAliasing`, `memoryLayout`, `nonpayableEntry`, `panicCodes`, `recursiveTypes`, `removedGenericSolidity`, `revertPayloads`, `rollback`, `staticCallRestriction`, `storageAliasing`, `storageCopy`, `termination`, `transientLayout`, `typeValidation`, `uncheckedArithmetic`, `worldAssumptions`.

### Manifest rows

Owner columns: source definition / syntax and static checking / lowering / backend and EVM.

| ID | category | scope | G00 status | evidence | source | syntax | lowering | backend |
|---|---|---|---|---|---|---|---|---|
| `abiDecode` | abi | model | in-profile | in profile | S04.02 | G10 G13 | G21 | G40 G41 |
| `abiEncode` | abi | model | in-profile | in profile | S04.02 | G10 G13 | G21 | G40 G41 |
| `abiEncodeCall` | abi | model | in-profile | in profile | S04.02 | G10 G13 | G21 | G40 G41 |
| `abiEncodePacked` | abi | model | in-profile | in profile | S04.02 | G10 G13 | G21 | G40 G41 |
| `abiEncodeWithSelector` | abi | model | in-profile | in profile | S04.02 | G10 G13 | G21 | G40 G41 |
| `abiEncodeWithSignature` | abi | model | in-profile | in profile | S04.02 | G10 G13 | G21 | G40 G41 |
| `addmodBuiltin` | builtins | model | in-profile | in profile | S02 | G10 G13 | G16 | G25 |
| `assertBuiltin` | builtins | model | in-profile | in profile | S02 S04.02 | G10 G13 | G21 | G38 |
| `bytesConcat` | builtins | model | in-profile | in profile | S02 | G10 G13 | G18.03 | G33 G35 |
| `ecrecoverBuiltin` | builtins | abstract | in-profile | in profile (abstraction) | S04.02 | G10 G13 | G23 | G31 G46.05 |
| `erc7201Builtin` | builtins | model | in-profile | in profile | S02 S04.02 | G10 G13 | G23 | G31 G46.05 |
| `keccakBuiltin` | builtins | abstract | in-profile | in profile (abstraction) | S04.02 | G10 G13 | G23 | G31 G46.05 |
| `mulmodBuiltin` | builtins | model | in-profile | in profile | S02 | G10 G13 | G16 | G25 |
| `requireBuiltin` | builtins | model | in-profile | in profile | S02 S04.02 | G10 G13 | G21 | G38 |
| `revertBuiltin` | builtins | model | in-profile | in profile | S02 S04.02 | G10 G13 | G21 | G38 |
| `ripemd160Builtin` | builtins | abstract | in-profile | in profile (abstraction) | S04.02 | G10 G13 | G23 | G31 G46.05 |
| `sha256Builtin` | builtins | abstract | in-profile | in profile (abstraction) | S04.02 | G10 G13 | G23 | G31 G46.05 |
| `stringConcat` | builtins | model | in-profile | in profile | S02 | G10 G13 | G18.03 | G33 G35 |
| `wrapUnwrap` | builtins | model | in-profile | in profile | S02 | G10 G13 | G16 | G25 |
| `callbackSemantics` | calls | abstract | in-profile | in profile (abstraction) | S03.03 S04.03 | G13 | G22.02 | G42.03 |
| `creationTry` | calls | abstract | in-profile | in profile (abstraction) | S03.03 S04.04 | G11 G13 | G22.03 | G44.03 |
| `emptyDataValueCall` | calls | abstract | in-profile | in profile (abstraction) | S03.03 S04.03 | G10 G13 | G22 | G43 |
| `extensionCalls` | calls | model | in-profile | in profile | S03.03 | G10 G14 | G20 | G37 |
| `externalLibraryCalls` | calls | abstract | in-profile | in profile (abstraction) | S03.03 S04.03 | G10 G14 | G22.04 | G42.04 |
| `externalSelfCalls` | calls | model | in-profile | in profile | S03.03 | G10 G14 | G22.01 | G42.01 |
| `externalTypedCalls` | calls | abstract | in-profile | in profile (abstraction) | S03.03 S04.03 | G10 G14 | G22.01 | G42.02 |
| `functionValues` | calls | model | in-profile | in profile | S03.03 | G10 G13 | G20 | G37.03 G42.05 |
| `internalCalls` | calls | model | in-profile | in profile | S03.03 | G10 G14 | G20 | G37 |
| `newContract` | calls | abstract | in-profile | in profile (abstraction) | S03.03 S04.04 | G10 G13 | G22.03 | G44.03 |
| `recursiveCalls` | calls | model | in-profile | in profile | S03.03 S03.04 | G10 G14 | G20 | G37.02 |
| `sendTransfer` | calls | abstract | in-profile | in profile (abstraction) | S03.03 S04.03 | G10 G13 | G22 | G43 |
| `valueOption` | calls | model | in-profile | in profile | S03.03 S04.03 | G10 G13 | G22 | G43 |
| `constants` | declarations | model | in-profile | in profile | S01 | G09 G13 | G16 | G25 |
| `constructors` | declarations | model | in-profile | in profile | S03.02 S04.04 | G11 G14 | G19 G22.03 | G44.01 |
| `contracts` | declarations | model | in-profile | in profile | S00 S01 | G11 G14 | G20 | G40 G44 |
| `enumDeclarations` | declarations | model | in-profile | in profile | S00 S01 | G09 | G16 | G25 |
| `errorDeclarations` | declarations | model | in-profile | in profile | S00 S01 S04.02 | G09 G11 | G21 | G38 G41 |
| `eventDeclarations` | declarations | model | in-profile | in profile | S00 S01 | G09 G11 | G23 | G31 |
| `fallbackFunction` | declarations | model | in-profile | in profile | S03.03 S04.04 | G11 G14 | G20 | G40 |
| `freeFunctions` | declarations | model | in-profile | in profile | S00 S01 | G11 G12 | G20 | G37 |
| `functions` | declarations | model | in-profile | in profile | S00 S01 S03 | G11 G13 | G20 | G37 G40 |
| `immutables` | declarations | model | in-profile | in profile | S01 S04.03 | G09 G13 | G19 | G44.01 |
| `imports` | declarations | model | in-profile | in profile | S00 | G11 G12 | G23 | G44.02 |
| `inheritance` | declarations | model | in-profile | in profile | S01 S03.02 | G11 G14 | G19 G20 | G44.01 |
| `interfaces` | declarations | model | in-profile | in profile | S00 S01 | G11 G14 | G20 | G42 |
| `libraries` | declarations | model | in-profile | in profile | S00 S01 S03.03 | G11 G14 | G22.04 | G42.04 G44.02 |
| `modifierPlaceholder` | declarations | model | in-profile | in profile | S03.02 | G11 | G19 | G36.01 |
| `modifiers` | declarations | model | in-profile | in profile | S03.02 | G11 G14 | G19 | G36.01 G37 |
| `operatorAliases` | declarations | model | in-profile | in profile | S01 | G11 G13 G14 | G16 G20 | G25 G37 |
| `overrideDeclarations` | declarations | model | in-profile | in profile | S01 | G11 G14 | G20 | G37 |
| `publicGetters` | declarations | model | in-profile | in profile | S01 S03.03 | G13 G14 | G20 | G40 G41 |
| `receiveFunction` | declarations | model | in-profile | in profile | S03.03 S04.04 | G11 G14 | G20 | G40 |
| `sourceUnits` | declarations | model | in-profile | in profile | S00 | G11 G12 | G23 | G44 |
| `stateMutability` | declarations | model | in-profile | in profile | S01 S03.03 | G11 G13 | G20 G22 | G40 G42 |
| `stateVariables` | declarations | model | in-profile | in profile | S01 S04.01 | G09 G11 | G18.02 | G27 G44.01 |
| `structDeclarations` | declarations | model | in-profile | in profile | S00 S01 | G09 | G18 | G27.01 G32 |
| `usingFor` | declarations | model | in-profile | in profile | S01 | G11 G14 | G20 | G37 |
| `valueTypeDeclarations` | declarations | model | in-profile | in profile | S00 S01 | G09 G13 | G16 | G25 |
| `visibility` | declarations | model | in-profile | in profile | S01 | G11 G14 | G20 | G40 |
| `addressBalance` | environment | abstract | in-profile | in profile (abstraction) | S04.02 S04.03 | G10 G13 | G23 | G31 G43 |
| `blockTimestamp` | environment | abstract | in-profile | in profile (abstraction) | S04.02 | G10 G13 | G23 | G31 G46.04 |
| `msgSender` | environment | abstract | in-profile | in profile (abstraction) | S04.02 | G10 G13 | G23 | G31 G46.04 |
| `msgValue` | environment | abstract | in-profile | in profile (abstraction) | S04.02 | G10 G13 | G23 | G31 G43 |
| `thisAddress` | environment | abstract | in-profile | in profile (abstraction) | S04.02 | G10 G13 | G23 | G31 G46.04 |
| `arithmetic` | expressions | model | in-profile | in profile | S02 | G10 G13 | G16 | G25 |
| `assignment` | expressions | model | in-profile | in profile | S02 | G10 G13 | G17 | G26 G28 G34 |
| `bitwise` | expressions | model | in-profile | in profile | S02 | G10 G13 | G16 | G25 |
| `callOptions` | expressions | model | in-profile | in profile | S02 S03.03 | G10 G15 | G22 | G42 G43 G44.03 |
| `comparisons` | expressions | model | in-profile | in profile | S02 | G10 G13 | G16 | G25 |
| `compoundAssignment` | expressions | model | in-profile | in profile | S02 | G10 G13 | G17 | G26 G28 |
| `conditional` | expressions | model | in-profile | in profile | S02 | G10 G13 | G17 | G26 |
| `deleteExpression` | expressions | model | in-profile | in profile | S02 S04.01 | G10 G13 | G18.05 | G28 G30 G34 |
| `explicitConversions` | expressions | model | in-profile | in profile | S01 S02 | G10 G13 | G16 G18.05 | G25 G35 |
| `functionCalls` | expressions | model | in-profile | in profile | S02 S03.03 | G10 G13 | G20 | G37 G42 |
| `implicitConversions` | expressions | model | in-profile | in profile | S01 | G13 | G16 G18.05 | G25 G35 |
| `increments` | expressions | model | in-profile | in profile | S02 | G10 G13 | G17 | G26 G28 |
| `indexAccess` | expressions | model | in-profile | in profile | S02 | G10 G13 | G17 G18 | G26 G28 G34 |
| `inlineArrays` | expressions | model | in-profile | in profile | S02 | G10 G13 | G18.03 | G33 |
| `memberAccess` | expressions | model | in-profile | in profile | S02 | G10 G13 | G17 G18 | G26 G28 G34 |
| `metaTypeExpression` | expressions | model | in-profile | in profile | S01 | G10 G13 | G23 | G31 |
| `namedArguments` | expressions | model | in-profile | in profile | S02 | G10 G13 | G20 | G37 |
| `names` | expressions | model | in-profile | in profile | S01 S02 | G10 G12 | G16 G17 | G26 |
| `newMemory` | expressions | model | in-profile | in profile | S02 S04.01 | G10 G13 | G18.03 | G33 |
| `parentheses` | expressions | model | in-profile | in profile | S00 S02 | G10 | G16 | G26 |
| `rangeAccess` | expressions | model | in-profile | in profile | S02 | G10 G13 | G18.04 G21 | G35.03 |
| `shifts` | expressions | model | in-profile | in profile | S02 | G10 G13 | G16 | G25 |
| `shortCircuit` | expressions | model | in-profile | in profile | S02 | G10 | G17 | G26 |
| `structConstruction` | expressions | model | in-profile | in profile | S02 | G10 G13 | G18.03 | G33 |
| `tupleExpressions` | expressions | model | in-profile | in profile | S02 | G10 G13 | G17 | G26 |
| `unaryArithmetic` | expressions | model | in-profile | in profile | S02 | G10 G13 | G16 | G25 |
| `addressLiterals` | lexical | model | in-profile | in profile | S00 | G08 | G16 | G25 |
| `booleanLiterals` | lexical | model | in-profile | in profile | S00 | G08 | G16 | G25 |
| `comments` | lexical | model | in-profile | in profile | S00 | G08 | — | — |
| `etherUnits` | lexical | model | in-profile | in profile | S00 | G08 | G16 | G25 |
| `hexLiterals` | lexical | model | in-profile | in profile | S00 S02 | G08 | G18.03 | G33 |
| `identifiers` | lexical | model | in-profile | in profile | S00 S01 | G08 G12 | G16 G17 | G26 |
| `numericLiterals` | lexical | model | in-profile | in profile | S00 | G08 | G16 | G25 |
| `pragmaAbicoder` | lexical | model | in-profile | in profile | S00 S04.02 | G08 G12 | G21 | G40 G41 |
| `pragmaOther` | lexical | model | in-profile | in profile | S00 | G08 G12 | G15 | G54 |
| `pragmaVersion` | lexical | model | in-profile | in profile | S00 | G08 G12 | G15 | G54 |
| `stringLiterals` | lexical | model | in-profile | in profile | S00 S02 | G08 | G18.03 | G33 |
| `timeUnits` | lexical | model | in-profile | in profile | S00 | G08 | G16 | G25 |
| `unicodeLiterals` | lexical | model | in-profile | in profile | S00 S02 | G08 | G18.03 | G33 |
| `creationCode` | metadata | model | in-profile | in profile | S04.02 | G13 | G23 | G44.02 |
| `errorEventSelector` | metadata | model | in-profile | in profile | S01 S04.02 | G13 | G23 | G31 |
| `functionAddress` | metadata | model | in-profile | in profile | S04.03 | G13 | G22.04 | G42.05 |
| `functionSelector` | metadata | model | in-profile | in profile | S01 S04.02 | G13 | G23 | G31 G40 |
| `interfaceId` | metadata | model | in-profile | in profile | S01 | G13 | G23 | G31 |
| `runtimeCode` | metadata | model | in-profile | in profile | S04.02 | G13 | G23 | G44.02 |
| `typeBounds` | metadata | model | in-profile | in profile | S01 | G13 | G16 | G25 |
| `typeName` | metadata | model | in-profile | in profile | S01 | G13 | G23 | G31 |
| `abiEntryValidation` | semantics | abstract | in-profile | in profile (abstraction) | S04.02 | G13 | G21 | G40 |
| `checkedArithmetic` | semantics | model | in-profile | in profile | S02 | G13 | G16 | G25 |
| `constructorLifetime` | semantics | abstract | in-profile | in profile (abstraction) | S04.04 | G14 | G22.03 | G44 G50.01 |
| `defaultInitialization` | semantics | model | in-profile | in profile | S02 S04.01 | G13 | G18 | G30 G33 |
| `evaluationOrder` | semantics | model | in-profile | in profile | S02 S03 | G13 | G16 G17 | G26 |
| `exactConstants` | semantics | model | in-profile | in profile | S01 | G13 | G16 | G25 |
| `featureDetection` | semantics | model | in-profile | in profile | S05 | G15 | G15 | G48 |
| `nonpayableEntry` | semantics | model | in-profile | in profile | S04.04 | G13 | G22.05 | G40 G43 |
| `panicCodes` | semantics | model | in-profile | in profile | S04.02 | G13 | G21 | G38 |
| `referenceCopyRules` | semantics | model | in-profile | in profile | S04.01 | G13 | G18.05 | G29 G35 |
| `revertPayloads` | semantics | model | in-profile | in profile | S04.02 | G13 | G21 | G38 G41 |
| `rollback` | semantics | model | in-profile | in profile | S03.04 S04.03 | G13 | G21 G22 | G38 G39 G47 |
| `staticCallRestriction` | semantics | abstract | in-profile | in profile (abstraction) | S03.03 S04.03 | G13 | G22 | G42.02 G42.05 |
| `termination` | semantics | model | in-profile | in profile | S03.04 | G13 | G19 | G36.03 G37.02 G49.03 |
| `typeValidation` | semantics | model | in-profile | in profile | S01 | G13 | G15 | G48 |
| `uncheckedArithmetic` | semantics | model | in-profile | in profile | S02 | G13 | G16 | G25 |
| `worldAssumptions` | semantics | abstract | in-profile | in profile (abstraction) | S04.03 | G13 | G22 | G47 |
| `blocks` | statements | model | in-profile | in profile | S03.01 | G11 | G19 | G36.01 |
| `breakStatement` | statements | model | in-profile | in profile | S03.01 | G11 | G19 | G36.01 |
| `canonicalRethrow` | statements | abstract | in-profile | in profile (abstraction) | S03.01 S04.02 | G11 G15 | G21 | G38 |
| `catchClauses` | statements | model | in-profile | in profile | S03.03 S04.02 | G11 | G21 | G38 G41 |
| `continueStatement` | statements | model | in-profile | in profile | S03.01 | G11 | G19 | G36.01 |
| `doWhileStatement` | statements | model | in-profile | in profile | S03.01 | G11 | G19 | G36 |
| `emitStatement` | statements | model | in-profile | in profile | S03.01 S04.02 | G11 | G23 | G31 |
| `expressionStatements` | statements | model | in-profile | in profile | S03.01 | G11 | G17 | G26 |
| `forStatement` | statements | model | in-profile | in profile | S03.01 | G11 | G19 | G36 |
| `ifStatement` | statements | model | in-profile | in profile | S03.01 | G11 | G19 | G36.01 |
| `returnStatement` | statements | model | in-profile | in profile | S03.01 | G11 | G19 | G36.01 G37 |
| `revertStatement` | statements | model | in-profile | in profile | S03.01 S04.02 | G11 | G21 | G38 |
| `tryStatement` | statements | abstract | in-profile | in profile (abstraction) | S03.03 S04.03 | G11 | G21 G22 | G38 G42 |
| `uncheckedBlock` | statements | model | in-profile | in profile | S02 S03.01 | G11 | G16 | G25 |
| `variableDeclarations` | statements | model | in-profile | in profile | S03.01 | G11 G13 | G17 G19 | G26 |
| `whileStatement` | statements | model | in-profile | in profile | S03.01 | G11 | G19 | G36 |
| `arrayLength` | storage | model | in-profile | in profile | S04.01 | G10 G13 | G18 | G28 G34 |
| `arrayPop` | storage | model | in-profile | in profile | S04.01 | G10 G13 | G18.02 | G30 |
| `arrayPush` | storage | model | in-profile | in profile | S04.01 | G10 G13 | G18.02 | G30 |
| `arrayPushReference` | storage | model | in-profile | in profile | S04.01 | G10 G13 | G18.02 | G30 |
| `danglingReferences` | storage | model | in-profile | in profile | S04.01 | G13 | G18.05 | G28 G30 |
| `deleteMappingTails` | storage | model | in-profile | in profile | S04.01 | G13 | G18.05 | G29 G30 |
| `logicalStorageBase` | storage | model | in-profile | in profile | S04.01 | G09 G13 | G18.02 | G27.05 |
| `memoryAliasing` | storage | model | in-profile | in profile | S04.01 | G13 | G18.03 | G34 |
| `storageAliasing` | storage | model | in-profile | in profile | S04.01 | G13 | G18.02 | G28 |
| `storageCopy` | storage | model | in-profile | in profile | S04.01 | G13 | G18.05 | G29 |
| `transientState` | storage | model | in-profile | in profile | S04.03 | G09 G13 | G23 | G39 G46.03 |
| `addressTypes` | types | model | in-profile | in profile | S00 S01 | G09 G13 | G16 | G25 G42 |
| `boolType` | types | model | in-profile | in profile | S00 S01 | G09 G13 | G16 | G25 |
| `calldataLocation` | types | model | in-profile | in profile | S01 S04.01 | G09 G13 | G18.04 | G35.03 G40 G46.02 |
| `dynamicArrays` | types | model | in-profile | in profile | S00 S01 S04.01 | G09 G13 | G18 | G27.03 G32 |
| `dynamicBytesType` | types | model | in-profile | in profile | S00 S01 S04.01 | G09 G13 | G18 | G27.03 G32 |
| `enumTypes` | types | model | in-profile | in profile | S00 S01 | G09 G13 | G16 | G25 |
| `externalFunctionTypes` | types | abstract | in-profile | in profile (abstraction) | S00 S01 S04.03 | G09 G13 | G20 G22.04 | G42.05 |
| `fixedArrays` | types | model | in-profile | in profile | S00 S01 S04.01 | G09 G13 | G18 | G27.03 G32 |
| `fixedBytesTypes` | types | model | in-profile | in profile | S00 S01 | G09 G13 | G16 | G25 |
| `integerTypes` | types | model | in-profile | in profile | S00 S01 | G09 G13 | G16 | G25 |
| `internalFunctionTypes` | types | model | in-profile | in profile | S00 S01 | G09 G13 | G20 | G37.03 |
| `mappings` | types | model | in-profile | in profile | S00 S01 S04.01 | G09 G13 | G18.02 | G27.02 |
| `memoryLocation` | types | model | in-profile | in profile | S01 S04.01 | G09 G13 | G18.03 | G32 G34 |
| `recursiveTypes` | types | model | in-profile | in profile | S00 S01 S04.01 | G09 G13 | G18.01 | G27.04 G35.05 |
| `storageLocation` | types | model | in-profile | in profile | S01 S04.01 | G09 G13 | G18.02 | G27 G28 |
| `stringType` | types | model | in-profile | in profile | S00 S01 S04.01 | G09 G13 | G18 | G27.03 G32 |
| `structTypes` | types | model | in-profile | in profile | S00 S01 S04.01 | G09 G13 | G18 | G27.01 G32 |
| `tupleTypes` | types | model | in-profile | in profile | S00 S01 | G09 G13 | G17 | G26 |
| `valueTypes` | types | model | in-profile | in profile | S00 S01 | G09 G13 | G16 | G25 |
| `blobhashBuiltin` | environment | exclude | unresolved | C: a builtin, not a field; not named before 419f8a4 | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockBasefee` | environment | exclude | unresolved | B: `block.basefee` | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockBlobbasefee` | environment | exclude | unresolved | B-: generic block-field clause | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockChainid` | environment | exclude | unresolved | B-: generic block-field clause | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockCoinbase` | environment | exclude | unresolved | B-: "block and transaction fields other than those the model reads … ( … )" | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockDifficulty` | environment | exclude | unresolved | B-: generic block-field clause | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockGaslimit` | environment | exclude | unresolved | B-: generic block-field clause | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockNumber` | environment | exclude | unresolved | B: `block.number` | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockPrevrandao` | environment | exclude | unresolved | B-: generic block-field clause | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockSlotnum` | environment | exclude | unresolved | B-: generic block-field clause (Amsterdam-gated; no pinned EVM target accepts it) | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `blockhashBuiltin` | environment | exclude | unresolved | C: a builtin, not a field; not named before 419f8a4 | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `txGasprice` | environment | exclude | unresolved | B-: generic block/transaction-field clause | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `txOrigin` | environment | exclude | unresolved | B: `tx.origin` | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `addressCode` | excluded | exclude | unresolved | B: `address.code`, `extcodesize` | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `addressCodehash` | excluded | exclude | unresolved | C: not named before 419f8a4 | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `create2Salt` | excluded | exclude | unresolved | B: `create2` salts | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `delegatecall` | excluded | exclude | unresolved | C: not named before 419f8a4 | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `eventLog` | excluded | exclude | unresolved | B: the log is dropped; argument effects are kept | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `gasOption` | excluded | exclude | unresolved | B-: gas stipends beyond `transfer`/`send` (the `{gas:}` option is not named) | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `gasleft` | excluded | exclude | unresolved | B: `gasleft()` | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `inlineAssembly` | excluded | exclude | unresolved | B: inline assembly other than a canonical whole-byte-buffer rethrow | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `lowLevelCall` | excluded | exclude | unresolved | B: low-level `call(data)` with arbitrary bytes | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `lowLevelStaticcall` | excluded | exclude | unresolved | C: not named before 419f8a4 | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `machineResources` | excluded | exclude | unresolved | B-: compiler-verification.md: "no gas, no stack limit" (a model property, not a profile decision) | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `memoryLayout` | excluded | exclude | unresolved | C: not named before 419f8a4 | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `rawCalldata` | excluded | exclude | unresolved | B: raw calldata (`msg.data`, `msg.sig`) | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `rawReturndata` | excluded | exclude | unresolved | B: raw returndata | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `selfdestruct` | excluded | exclude | unresolved | B: `selfdestruct` | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `storageLayout` | excluded | exclude | unresolved | B-: storage layout (slot numbers, packing); `layout at` not named | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `transientLayout` | excluded | exclude | unresolved | C: not named before 419f8a4 | S00 G15 (precise refusal; observation side: G01/G06) | | | |
| `fixedPoint` | upstream | upstream | upstream-rejected | upstream pin | S00 G08 G11 G15 (precise rejection as invalid/removed) | | | |
| `invalidLexemes` | upstream | upstream | upstream-rejected | upstream pin | S00 G08 G11 G15 (precise rejection as invalid/removed) | | | |
| `invalidModifierBody` | upstream | upstream | upstream-rejected | upstream pin | S00 G08 G11 G15 (precise rejection as invalid/removed) | | | |
| `removedAliases` | upstream | upstream | upstream-rejected | upstream pin | S00 G08 G11 G15 (precise rejection as invalid/removed) | | | |
| `removedGenericSolidity` | upstream | upstream | upstream-rejected | upstream pin | S00 G08 G11 G15 (precise rejection as invalid/removed) | | | |
| `removedUnits` | upstream | upstream | upstream-rejected | upstream pin | S00 G08 G11 G15 (precise rejection as invalid/removed) | | | |
| `reservedKeywords` | upstream | upstream | upstream-rejected | upstream pin | S00 G08 G11 G15 (precise rejection as invalid/removed) | | | |
| `unsignedRightShift` | upstream | upstream | upstream-rejected | upstream pin | S00 G08 G11 G15 (precise rejection as invalid/removed) | | | |

### Upstream symbols by kind

- **parserRules** — in-profile (68): `block`, `booleanLiteral`, `breakStatement`, `callArgumentList`, `catchClause`, `constantVariableDeclaration`, `constructorDefinition`, `continueStatement`, `contractBodyElement`, `dataLocation`, `doWhileStatement`, `emitStatement`, `enumDefinition`, `errorDefinition`, `errorParameter`, `expression`, `expressionStatement`, `forStatement`, `functionDefinition`, `functionTypeName`, `hexStringLiteral`, `identifier`, `identifierPath`, `ifStatement`, `importAliases`, `importDirective`, `inheritanceSpecifier`, `inheritanceSpecifierList`, `inlineArrayExpression`, `interfaceDefinition`, `libraryDefinition`, `literal`, `mappingKeyType`, `mappingType`, `modifierInvocation`, `namedArgument`, `numberLiteral`, `overrideSpecifier`, `parameterDeclaration`, `parameterList`, `path`, `pragmaDirective`, `receiveFunctionDefinition`, `returnStatement`, `revertStatement`, `simpleStatement`, `sourceUnit`, `stateMutability`, `stateVariableDeclaration`, `statement`, `stringLiteral`, `structDefinition`, `structMember`, `symbolAliases`, `tryStatement`, `tupleExpression`, `uncheckedBlock`, `unicodeStringLiteral`, `userDefinableOperator`, `userDefinedValueTypeDefinition`, `usingAliases`, `usingDirective`, `variableDeclaration`, `variableDeclarationList`, `variableDeclarationStatement`, `variableDeclarationTuple`, `visibility`, `whileStatement`; combination-unresolved (6): `assemblyFlags`, `assemblyStatement`, `contractDefinition`, `eventDefinition`, `eventParameter`, `fallbackFunctionDefinition`; combination-upstream (5): `assignOp`, `elementaryTypeName`, `literalWithSubDenomination`, `modifierDefinition`, `typeName`; unresolved (14): `yulAssignment`, `yulBlock`, `yulBoolean`, `yulExpression`, `yulForStatement`, `yulFunctionCall`, `yulFunctionDefinition`, `yulIfStatement`, `yulLiteral`, `yulPath`, `yulStatement`, `yulSwitchCase`, `yulSwitchStatement`, `yulVariableDeclaration`
- **expressionAlternatives** — in-profile (23): `AddSubOperation`, `AndOperation`, `Assignment`, `BitAndOperation`, `BitOrOperation`, `BitXorOperation`, `Conditional`, `EqualityComparison`, `ExpOperation`, `FunctionCall`, `IndexAccess`, `IndexRangeAccess`, `InlineArray`, `MemberAccess`, `MetaType`, `MulDivModOperation`, `OrOperation`, `OrderComparison`, `PayableConversion`, `PrimaryExpression`, `Tuple`, `UnaryPrefixOperation`, `UnarySuffixOperation`; combination-unresolved (2): `FunctionCallOptions`, `NewExpr`; combination-upstream (1): `ShiftOperation`
- **lexerRules** — in-profile (108): `Add`, `And`, `As`, `AssignSar`, `AssignShl`, `BitAnd`, `BitNot`, `BitOr`, `BitXor`, `Break`, `COMMENT`, `Calldata`, `Catch`, `Colon`, `Conditional`, `Constant`, `Constructor`, `Continue`, `Dec`, `DecimalDigits`, `DecimalNumber`, `Delete`, `Div`, `Do`, `DoubleArrow`, `DoubleQuote`, `DoubleQuotedPrintable`, `DoubleQuotedStringCharacter`, `DoubleQuotedUnicodeStringCharacter`, `Else`, `Emit`, `EmptyStringLiteral`, `Enum`, `Equal`, `Error`, `EscapeSequence`, `EvenHexDigits`, `Exp`, `False`, `For`, `From`, `Function`, `Global`, `GreaterThan`, `GreaterThanOrEqual`, `Hex`, `HexCharacter`, `HexDigits`, `HexNumber`, `HexString`, `Identifier`, `IdentifierPart`, `IdentifierStart`, `If`, `Immutable`, `Import`, `Inc`, `Interface`, `Internal`, `Is`, `LINE_COMMENT`, `LessThan`, `LessThanOrEqual`, `Library`, `Mapping`, `Memory`, `Mod`, `Modifier`, `Mul`, `New`, `NonEmptyStringLiteral`, `Not`, `NotEqual`, `Or`, `Override`, `Period`, `Pragma`, `PragmaCOMMENT`, `PragmaLINE_COMMENT`, `PragmaSemicolon`, `PragmaToken`, `PragmaWS`, `Private`, `Public`, `Pure`, `Receive`, `Return`, `Revert`, `Sar`, `Shl`, `SingleQuote`, `SingleQuotedPrintable`, `SingleQuotedStringCharacter`, `SingleQuotedUnicodeStringCharacter`, `Storage`, `Struct`, `Sub`, `Transient`, `True`, `Try`, `Type`, `Unchecked`, `Unicode`, `UnicodeStringLiteral`, `Using`, `View`, `WS`, `While`; combination-unresolved (17): `Abstract`, `Anonymous`, `At`, `Comma`, `Contract`, `Event`, `External`, `Fallback`, `Indexed`, `LBrace`, `LParen`, `Layout`, `RBrace`, `RParen`, `Returns`, `Semicolon`, `Virtual`; combination-upstream (22): `Address`, `Assign`, `AssignAdd`, `AssignBitAnd`, `AssignBitOr`, `AssignBitXor`, `AssignDiv`, `AssignMod`, `AssignMul`, `AssignSub`, `Bool`, `Bytes`, `Fixed`, `FixedBytes`, `LBrack`, `Payable`, `RBrack`, `SignedIntegerType`, `String`, `SubDenomination`, `Ufixed`, `UnsignedIntegerType`; unresolved (42): `Assembly`, `AssemblyBlockCOMMENT`, `AssemblyBlockComma`, `AssemblyBlockLINE_COMMENT`, `AssemblyBlockLParen`, `AssemblyBlockRParen`, `AssemblyBlockWS`, `AssemblyDialect`, `AssemblyFlagString`, `AssemblyLBrace`, `YulArrow`, `YulAssign`, `YulBreak`, `YulCOMMENT`, `YulCase`, `YulComma`, `YulContinue`, `YulDecimalNumber`, `YulDefault`, `YulEVMBuiltin`, `YulFalse`, `YulFor`, `YulFunction`, `YulHex`, `YulHexNumber`, `YulHexStringLiteral`, `YulIdentifier`, `YulIdentifierPart`, `YulIdentifierStart`, `YulIf`, `YulLBrace`, `YulLINE_COMMENT`, `YulLParen`, `YulLeave`, `YulLet`, `YulPeriod`, `YulRBrace`, `YulRParen`, `YulStringLiteral`, `YulSwitch`, `YulTrue`, `YulWS`; upstream-rejected (6): `AssignShr`, `DecimalNumberFollowedByIdentifier`, `OctalNumber`, `ReservedKeywords`, `RightArrow`, `Shr`
- **astClasses** — in-profile (62): `ASTNode`, `ArrayTypeName`, `Assignment`, `BinaryOperation`, `Block`, `Break`, `BreakableStatement`, `CallableDeclaration`, `Conditional`, `Continue`, `ContractDefinition`, `Declaration`, `Documented`, `ElementaryTypeNameExpression`, `EmitStatement`, `EnumDefinition`, `EnumValue`, `ErrorDefinition`, `EventDefinition`, `Expression`, `ExpressionStatement`, `ForStatement`, `FunctionCall`, `FunctionDefinition`, `FunctionTypeName`, `Identifier`, `IdentifierPath`, `IfStatement`, `ImplementationOptional`, `ImportDirective`, `IndexAccess`, `IndexRangeAccess`, `InheritanceSpecifier`, `MagicVariableDeclaration`, `Mapping`, `MemberAccess`, `ModifierInvocation`, `NewExpression`, `OverrideSpecifier`, `ParameterList`, `PragmaDirective`, `PrimaryExpression`, `Return`, `RevertStatement`, `Scopable`, `ScopeOpener`, `SourceUnit`, `Statement`, `StructDefinition`, `StructurallyDocumented`, `StructuredDocumentation`, `TryCatchClause`, `TryStatement`, `TupleExpression`, `UnaryOperation`, `UserDefinedTypeName`, `UserDefinedValueTypeDefinition`, `UsingForDirective`, `VariableDeclaration`, `VariableDeclarationStatement`, `VariableScope`, `WhileStatement`; combination-unresolved (3): `FunctionCallOptions`, `InlineAssembly`, `StorageLayoutSpecifier`; combination-upstream (5): `ElementaryTypeName`, `Literal`, `ModifierDefinition`, `PlaceholderStatement`, `TypeName`; upstream-rejected (1): `Throw`
- **functionKinds** — in-profile (31): `ABIDecode`, `ABIEncode`, `ABIEncodeCall`, `ABIEncodePacked`, `ABIEncodeWithSelector`, `ABIEncodeWithSignature`, `AddMod`, `ArrayPop`, `ArrayPush`, `Assert`, `BytesConcat`, `Declaration`, `DelegateCall`, `ECRecover`, `ERC7201`, `Error`, `External`, `Internal`, `KECCAK256`, `MetaType`, `MulMod`, `ObjectCreation`, `RIPEMD160`, `Require`, `Revert`, `SHA256`, `Send`, `StringConcat`, `Transfer`, `Unwrap`, `Wrap`; combination-unresolved (3): `BareCall`, `Creation`, `Event`; combination-upstream (1): `SetValue`; unresolved (7): `BareDelegateCall`, `BareStaticCall`, `BlobHash`, `BlockHash`, `GasLeft`, `Selfdestruct`, `SetGas`; upstream-rejected (1): `BareCallCode`
- **globalNames** — in-profile (14): `abi`, `addmod`, `assert`, `ecrecover`, `erc7201`, `keccak256`, `mulmod`, `require`, `revert`, `ripemd160`, `sha256`, `super`, `this`, `type`; combination-unresolved (2): `block`, `msg`; unresolved (5): `blobhash`, `blockhash`, `gasleft`, `selfdestruct`, `tx`; upstream-rejected (3): `now`, `sha3`, `suicide`
- **yulBuiltins** — unresolved (81): `add`, `addmod`, `address`, `and`, `balance`, `basefee`, `blobbasefee`, `blobhash`, `blockhash`, `byte`, `call`, `callcode`, `calldatacopy`, `calldataload`, `calldatasize`, `caller`, `callvalue`, `chainid`, `clz`, `coinbase`, `create`, `create2`, `delegatecall`, `difficulty`, `div`, `eq`, `exp`, `extcodecopy`, `extcodehash`, `extcodesize`, `gas`, `gaslimit`, `gasprice`, `gt`, `invalid`, `iszero`, `keccak256`, `log0`, `log1`, `log2`, `log3`, `log4`, `lt`, `mcopy`, `mload`, `mod`, `msize`, `mstore`, `mstore8`, `mul`, `mulmod`, `not`, `number`, `or`, `origin`, `pop`, `prevrandao`, `return`, `returndatacopy`, `returndatasize`, `revert`, `sar`, `sdiv`, `selfbalance`, `selfdestruct`, `sgt`, `shl`, `shr`, `signextend`, `sload`, `slotnum`, `slt`, `smod`, `sstore`, `staticcall`, `stop`, `sub`, `timestamp`, `tload`, `tstore`, `xor`
- **compilerTokens** — in-profile (95): `Add`, `And`, `As`, `AssignSar`, `AssignShl`, `BitAnd`, `BitNot`, `BitOr`, `BitXor`, `Break`, `BytesM`, `CallData`, `Catch`, `Colon`, `CommentLiteral`, `Conditional`, `Constant`, `Constructor`, `Continue`, `Dec`, `Delete`, `Div`, `Do`, `DoubleArrow`, `EOS`, `Else`, `Emit`, `Enum`, `Equal`, `Exp`, `FalseLiteral`, `For`, `Function`, `GreaterThan`, `GreaterThanOrEqual`, `Hex`, `HexStringLiteral`, `Identifier`, `If`, `Immutable`, `Import`, `Inc`, `Int`, `IntM`, `Interface`, `Internal`, `Is`, `LessThan`, `LessThanOrEqual`, `Library`, `Mapping`, `Memory`, `Mod`, `Modifier`, `Mul`, `New`, `Not`, `NotEqual`, `Number`, `Or`, `Override`, `Period`, `Pragma`, `Private`, `Public`, `Pure`, `Receive`, `Return`, `SAR`, `SHL`, `Storage`, `StringLiteral`, `Struct`, `Sub`, `SubDay`, `SubEther`, `SubGwei`, `SubHour`, `SubMinute`, `SubSecond`, `SubWeek`, `SubWei`, `TrueLiteral`, `Try`, `Type`, `TypesEnd`, `UInt`, `UIntM`, `Unchecked`, `Unicode`, `UnicodeStringLiteral`, `Using`, `View`, `While`, `Whitespace`; combination-unresolved (15): `Abstract`, `Anonymous`, `Comma`, `Contract`, `Event`, `External`, `Fallback`, `Indexed`, `LBrace`, `LParen`, `RBrace`, `RParen`, `Returns`, `Semicolon`, `Virtual`; combination-upstream (17): `Address`, `Assign`, `AssignAdd`, `AssignBitAnd`, `AssignBitOr`, `AssignBitXor`, `AssignDiv`, `AssignMod`, `AssignMul`, `AssignSub`, `Bool`, `Bytes`, `Fixed`, `LBrack`, `Payable`, `RBrack`, `String`; unresolved (3): `Assembly`, `AssemblyAssign`, `Leave`; upstream-rejected (40): `After`, `Alias`, `Apply`, `AssignShr`, `Auto`, `Byte`, `Case`, `CopyOf`, `Default`, `Define`, `Final`, `FixedMxN`, `Illegal`, `Implements`, `In`, `Inline`, `Let`, `Macro`, `Match`, `Mutable`, `NullLiteral`, `Of`, `Partial`, `Promise`, `Reference`, `Relocatable`, `RightArrow`, `SHR`, `Sealed`, `Sizeof`, `Static`, `SubYear`, `Supports`, `Switch`, `Throw`, `TypeOf`, `Typedef`, `UFixed`, `UFixedMxN`, `Var`
- **typeCategories** — in-profile (20): `Address`, `Array`, `ArraySlice`, `Bool`, `Contract`, `Enum`, `FixedBytes`, `Function`, `InaccessibleDynamic`, `Integer`, `Magic`, `Mapping`, `Modifier`, `Module`, `RationalNumber`, `StringLiteral`, `Struct`, `Tuple`, `TypeType`, `UserDefinedValueType`; upstream-rejected (1): `FixedPoint`
- **magicMembers** — in-profile (15): `ABI.decode`, `ABI.encode`, `ABI.encodeCall`, `ABI.encodePacked`, `ABI.encodeWithSelector`, `ABI.encodeWithSignature`, `Block.timestamp`, `Message.sender`, `Message.value`, `MetaType.creationCode`, `MetaType.interfaceId`, `MetaType.max`, `MetaType.min`, `MetaType.name`, `MetaType.runtimeCode`; unresolved (13): `Block.basefee`, `Block.blobbasefee`, `Block.chainid`, `Block.coinbase`, `Block.difficulty`, `Block.gaslimit`, `Block.number`, `Block.prevrandao`, `Block.slotnum`, `Message.data`, `Message.sig`, `Transaction.gasprice`, `Transaction.origin`; upstream-rejected (2): `Block.blockhash`, `Message.gas`
- **AddressTypeMembers** — in-profile (3): `balance`, `send`, `transfer`; combination-unresolved (1): `call`; unresolved (4): `code`, `codehash`, `delegatecall`, `staticcall`; upstream-rejected (1): `callcode`
- **FixedBytesTypeMembers** — in-profile (1): `length`
- **ArrayTypeMembers** — in-profile (3): `length`, `pop`, `push`
- **FunctionTypeMembers** — in-profile (2): `address`, `selector`; upstream-rejected (2): `gas`, `value`
- **TypeTypeMembers** — in-profile (3): `concat`, `unwrap`, `wrap`
- **nativeMemberOwners** — in-profile (7): `ArrayType`, `ContractType`, `FixedBytesType`, `MagicType`, `ModuleType`, `StructType`, `TypeType`; combination-unresolved (1): `AddressType`; combination-upstream (1): `FunctionType`

### Ledger combinations (symbols mapped to in-profile and non-profile rows)

| kind | symbol | in-profile IDs | other IDs |
|---|---|---|---|
| parserRules | `assemblyFlags` | canonicalRethrow | inlineAssembly |
| parserRules | `assemblyStatement` | canonicalRethrow | inlineAssembly |
| parserRules | `assignOp` | assignment, compoundAssignment | unsignedRightShift |
| parserRules | `contractDefinition` | contracts, inheritance, logicalStorageBase | storageLayout |
| parserRules | `elementaryTypeName` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| parserRules | `eventDefinition` | eventDeclarations | eventLog |
| parserRules | `eventParameter` | eventDeclarations | eventLog |
| parserRules | `fallbackFunctionDefinition` | fallbackFunction | rawCalldata, rawReturndata |
| parserRules | `literalWithSubDenomination` | etherUnits, timeUnits | removedUnits |
| parserRules | `modifierDefinition` | modifierPlaceholder, modifiers | invalidModifierBody |
| parserRules | `typeName` | addressTypes, dynamicArrays, dynamicBytesType, enumTypes, externalFunctionTypes, fixedArrays, fixedBytesTypes, integerTypes, internalFunctionTypes, mappings, stringType, structTypes, valueTypes | fixedPoint |
| expressionAlternatives | `FunctionCallOptions` | callOptions, valueOption | create2Salt, gasOption |
| expressionAlternatives | `NewExpr` | newContract, newMemory | create2Salt |
| expressionAlternatives | `ShiftOperation` | shifts | unsignedRightShift |
| lexerRules | `Abstract` | contracts, inheritance | storageLayout |
| lexerRules | `Address` | addressTypes, arithmetic, assignment, boolType, conditional, dynamicBytesType, fixedBytesTypes, functionCalls, integerTypes, shortCircuit, stringType | fixedPoint |
| lexerRules | `Anonymous` | eventDeclarations | eventLog |
| lexerRules | `Assign` | assignment, compoundAssignment, constants, immutables, stateVariables, transientState, tupleExpressions, variableDeclarations | unsignedRightShift |
| lexerRules | `AssignAdd` | assignment, compoundAssignment | unsignedRightShift |
| lexerRules | `AssignBitAnd` | assignment, compoundAssignment | unsignedRightShift |
| lexerRules | `AssignBitOr` | assignment, compoundAssignment | unsignedRightShift |
| lexerRules | `AssignBitXor` | assignment, compoundAssignment | unsignedRightShift |
| lexerRules | `AssignDiv` | assignment, compoundAssignment | unsignedRightShift |
| lexerRules | `AssignMod` | assignment, compoundAssignment | unsignedRightShift |
| lexerRules | `AssignMul` | assignment, compoundAssignment | unsignedRightShift |
| lexerRules | `AssignSub` | assignment, compoundAssignment | unsignedRightShift |
| lexerRules | `At` | contracts, identifiers, inheritance, logicalStorageBase, names | storageLayout |
| lexerRules | `Bool` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| lexerRules | `Bytes` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| lexerRules | `Comma` | arithmetic, assignment, calldataLocation, conditional, constructors, enumDeclarations, errorDeclarations, eventDeclarations, functionCalls, functions, imports, inheritance, inlineArrays, memoryLocation, namedArguments, operatorAliases, overrideDeclarations, shortCircuit, storageLocation, tupleExpressions, tupleTypes, usingFor, variableDeclarations | eventLog |
| lexerRules | `Contract` | contracts, inheritance | storageLayout |
| lexerRules | `Event` | eventDeclarations | eventLog |
| lexerRules | `External` | fallbackFunction, receiveFunction, visibility | rawCalldata, rawReturndata |
| lexerRules | `Fallback` | fallbackFunction, freeFunctions, functions | rawCalldata, rawReturndata |
| lexerRules | `Fixed` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| lexerRules | `FixedBytes` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| lexerRules | `Indexed` | eventDeclarations | eventLog |
| lexerRules | `LBrace` | arithmetic, assignment, blocks, conditional, contracts, enumDeclarations, functionCalls, imports, inheritance, interfaces, libraries, namedArguments, operatorAliases, shortCircuit, structDeclarations, usingFor | storageLayout |
| lexerRules | `LBrack` | addressTypes, arithmetic, assignment, conditional, dynamicArrays, dynamicBytesType, enumTypes, externalFunctionTypes, fixedArrays, fixedBytesTypes, functionCalls, inlineArrays, integerTypes, internalFunctionTypes, mappings, shortCircuit, stringType, structTypes, valueTypes | fixedPoint |
| lexerRules | `LParen` | arithmetic, assignment, catchClauses, conditional, constructors, creationTry, doWhileStatement, errorDeclarations, eventDeclarations, externalFunctionTypes, fallbackFunction, forStatement, freeFunctions, functionCalls, functions, ifStatement, internalFunctionTypes, mappings, modifierPlaceholder, modifiers, namedArguments, overrideDeclarations, receiveFunction, shortCircuit, tryStatement, tupleExpressions, variableDeclarations, whileStatement | eventLog, rawCalldata, rawReturndata |
| lexerRules | `Layout` | contracts, identifiers, inheritance, logicalStorageBase, names | storageLayout |
| lexerRules | `Payable` | addressTypes, arithmetic, assignment, boolType, conditional, constructors, dynamicBytesType, fixedBytesTypes, functionCalls, integerTypes, receiveFunction, shortCircuit, stateMutability, stringType | fixedPoint |
| lexerRules | `RBrace` | arithmetic, assignment, blocks, conditional, contracts, enumDeclarations, functionCalls, imports, inheritance, interfaces, libraries, namedArguments, operatorAliases, shortCircuit, structDeclarations, usingFor | storageLayout |
| lexerRules | `RBrack` | addressTypes, arithmetic, assignment, conditional, dynamicArrays, dynamicBytesType, enumTypes, externalFunctionTypes, fixedArrays, fixedBytesTypes, functionCalls, inlineArrays, integerTypes, internalFunctionTypes, mappings, shortCircuit, stringType, structTypes, valueTypes | fixedPoint |
| lexerRules | `RParen` | arithmetic, assignment, catchClauses, conditional, constructors, creationTry, doWhileStatement, errorDeclarations, eventDeclarations, externalFunctionTypes, fallbackFunction, forStatement, freeFunctions, functionCalls, functions, ifStatement, internalFunctionTypes, mappings, modifierPlaceholder, modifiers, namedArguments, overrideDeclarations, receiveFunction, shortCircuit, tryStatement, tupleExpressions, variableDeclarations, whileStatement | eventLog, rawCalldata, rawReturndata |
| lexerRules | `Returns` | creationTry, externalFunctionTypes, fallbackFunction, freeFunctions, functions, internalFunctionTypes, tryStatement | rawCalldata, rawReturndata |
| lexerRules | `Semicolon` | breakStatement, constants, continueStatement, doWhileStatement, emitStatement, errorDeclarations, eventDeclarations, expressionStatements, fallbackFunction, forStatement, freeFunctions, functions, immutables, imports, modifierPlaceholder, modifiers, operatorAliases, receiveFunction, returnStatement, revertStatement, stateVariables, structDeclarations, transientState, tupleExpressions, usingFor, valueTypeDeclarations, variableDeclarations | eventLog, rawCalldata, rawReturndata |
| lexerRules | `SignedIntegerType` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| lexerRules | `String` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| lexerRules | `SubDenomination` | etherUnits, timeUnits | removedUnits |
| lexerRules | `Ufixed` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| lexerRules | `UnsignedIntegerType` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| lexerRules | `Virtual` | fallbackFunction, freeFunctions, functions, modifierPlaceholder, modifiers, receiveFunction | rawCalldata, rawReturndata |
| astClasses | `ElementaryTypeName` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| astClasses | `FunctionCallOptions` | callOptions, valueOption | create2Salt, gasOption |
| astClasses | `InlineAssembly` | canonicalRethrow | inlineAssembly |
| astClasses | `Literal` | addressLiterals, booleanLiterals, etherUnits, hexLiterals, numericLiterals, stringLiterals, timeUnits, unicodeLiterals | removedUnits |
| astClasses | `ModifierDefinition` | modifiers | invalidModifierBody |
| astClasses | `PlaceholderStatement` | modifierPlaceholder | invalidModifierBody |
| astClasses | `StorageLayoutSpecifier` | logicalStorageBase | storageLayout |
| astClasses | `TypeName` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| functionKinds | `BareCall` | emptyDataValueCall | lowLevelCall |
| functionKinds | `Creation` | creationTry, newContract | create2Salt |
| functionKinds | `Event` | emitStatement | eventLog |
| functionKinds | `SetValue` | valueOption | removedAliases |
| globalNames | `block` | blockTimestamp | blockBasefee, blockBlobbasefee, blockChainid, blockCoinbase, blockDifficulty, blockGaslimit, blockNumber, blockPrevrandao, blockSlotnum |
| globalNames | `msg` | msgSender, msgValue | rawCalldata |
| compilerTokens | `Abstract` | contracts, inheritance | storageLayout |
| compilerTokens | `Address` | addressTypes, arithmetic, assignment, boolType, conditional, dynamicBytesType, fixedBytesTypes, functionCalls, integerTypes, shortCircuit, stringType | fixedPoint |
| compilerTokens | `Anonymous` | eventDeclarations | eventLog |
| compilerTokens | `Assign` | assignment, compoundAssignment, constants, immutables, stateVariables, transientState, tupleExpressions, variableDeclarations | unsignedRightShift |
| compilerTokens | `AssignAdd` | assignment, compoundAssignment | unsignedRightShift |
| compilerTokens | `AssignBitAnd` | assignment, compoundAssignment | unsignedRightShift |
| compilerTokens | `AssignBitOr` | assignment, compoundAssignment | unsignedRightShift |
| compilerTokens | `AssignBitXor` | assignment, compoundAssignment | unsignedRightShift |
| compilerTokens | `AssignDiv` | assignment, compoundAssignment | unsignedRightShift |
| compilerTokens | `AssignMod` | assignment, compoundAssignment | unsignedRightShift |
| compilerTokens | `AssignMul` | assignment, compoundAssignment | unsignedRightShift |
| compilerTokens | `AssignSub` | assignment, compoundAssignment | unsignedRightShift |
| compilerTokens | `Bool` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| compilerTokens | `Bytes` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| compilerTokens | `Comma` | arithmetic, assignment, calldataLocation, conditional, constructors, enumDeclarations, errorDeclarations, eventDeclarations, functionCalls, functions, imports, inheritance, inlineArrays, memoryLocation, namedArguments, operatorAliases, overrideDeclarations, shortCircuit, storageLocation, tupleExpressions, tupleTypes, usingFor, variableDeclarations | eventLog |
| compilerTokens | `Contract` | contracts, inheritance | storageLayout |
| compilerTokens | `Event` | eventDeclarations | eventLog |
| compilerTokens | `External` | fallbackFunction, receiveFunction, visibility | rawCalldata, rawReturndata |
| compilerTokens | `Fallback` | fallbackFunction, freeFunctions, functions | rawCalldata, rawReturndata |
| compilerTokens | `Fixed` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| compilerTokens | `Indexed` | eventDeclarations | eventLog |
| compilerTokens | `LBrace` | arithmetic, assignment, blocks, conditional, contracts, enumDeclarations, functionCalls, imports, inheritance, interfaces, libraries, namedArguments, operatorAliases, shortCircuit, structDeclarations, usingFor | storageLayout |
| compilerTokens | `LBrack` | addressTypes, arithmetic, assignment, conditional, dynamicArrays, dynamicBytesType, enumTypes, externalFunctionTypes, fixedArrays, fixedBytesTypes, functionCalls, inlineArrays, integerTypes, internalFunctionTypes, mappings, shortCircuit, stringType, structTypes, valueTypes | fixedPoint |
| compilerTokens | `LParen` | arithmetic, assignment, catchClauses, conditional, constructors, creationTry, doWhileStatement, errorDeclarations, eventDeclarations, externalFunctionTypes, fallbackFunction, forStatement, freeFunctions, functionCalls, functions, ifStatement, internalFunctionTypes, mappings, modifierPlaceholder, modifiers, namedArguments, overrideDeclarations, receiveFunction, shortCircuit, tryStatement, tupleExpressions, variableDeclarations, whileStatement | eventLog, rawCalldata, rawReturndata |
| compilerTokens | `Payable` | addressTypes, arithmetic, assignment, boolType, conditional, constructors, dynamicBytesType, fixedBytesTypes, functionCalls, integerTypes, receiveFunction, shortCircuit, stateMutability, stringType | fixedPoint |
| compilerTokens | `RBrace` | arithmetic, assignment, blocks, conditional, contracts, enumDeclarations, functionCalls, imports, inheritance, interfaces, libraries, namedArguments, operatorAliases, shortCircuit, structDeclarations, usingFor | storageLayout |
| compilerTokens | `RBrack` | addressTypes, arithmetic, assignment, conditional, dynamicArrays, dynamicBytesType, enumTypes, externalFunctionTypes, fixedArrays, fixedBytesTypes, functionCalls, inlineArrays, integerTypes, internalFunctionTypes, mappings, shortCircuit, stringType, structTypes, valueTypes | fixedPoint |
| compilerTokens | `RParen` | arithmetic, assignment, catchClauses, conditional, constructors, creationTry, doWhileStatement, errorDeclarations, eventDeclarations, externalFunctionTypes, fallbackFunction, forStatement, freeFunctions, functionCalls, functions, ifStatement, internalFunctionTypes, mappings, modifierPlaceholder, modifiers, namedArguments, overrideDeclarations, receiveFunction, shortCircuit, tryStatement, tupleExpressions, variableDeclarations, whileStatement | eventLog, rawCalldata, rawReturndata |
| compilerTokens | `Returns` | creationTry, externalFunctionTypes, fallbackFunction, freeFunctions, functions, internalFunctionTypes, tryStatement | rawCalldata, rawReturndata |
| compilerTokens | `Semicolon` | breakStatement, constants, continueStatement, doWhileStatement, emitStatement, errorDeclarations, eventDeclarations, expressionStatements, fallbackFunction, forStatement, freeFunctions, functions, immutables, imports, modifierPlaceholder, modifiers, operatorAliases, receiveFunction, returnStatement, revertStatement, stateVariables, structDeclarations, transientState, tupleExpressions, usingFor, valueTypeDeclarations, variableDeclarations | eventLog, rawCalldata, rawReturndata |
| compilerTokens | `String` | addressTypes, boolType, dynamicBytesType, fixedBytesTypes, integerTypes, stringType | fixedPoint |
| compilerTokens | `Virtual` | fallbackFunction, freeFunctions, functions, modifierPlaceholder, modifiers, receiveFunction | rawCalldata, rawReturndata |
| AddressTypeMembers | `call` | emptyDataValueCall | lowLevelCall |
| nativeMemberOwners | `AddressType` | addressBalance, sendTransfer | addressCode, addressCodehash, lowLevelCall, delegatecall, lowLevelStaticcall |
| nativeMemberOwners | `FunctionType` | functionSelector, functionAddress, errorEventSelector | removedAliases |

### Named feature combinations

| construct | in-profile IDs | unresolved IDs | owners |
|---|---|---|---|
| `f{value:v,gas:g}(…)` | callOptions, valueOption | gasOption | G15 G22 G43 |
| `new C{salt:s,value:v}(…)` | callOptions, newContract, valueOption | create2Salt | G15 G22.03 G44.03 |
| byte-oriented `fallback(bytes calldata) returns (bytes memory)` | fallbackFunction | rawCalldata, rawReturndata | G15 G20 G40 |
| `emit E(args)` under a log-observing property | emitStatement, eventDeclarations | eventLog | G15 G23 G31 |
| `assembly { revert(add(d,32), mload(d)) }` vs any other assembly | canonicalRethrow | inlineAssembly | G15 G21 G38 |
| `(bool ok,) = a.call{value:v}("")` vs `a.call(data)` | emptyDataValueCall, valueOption | lowLevelCall, rawReturndata | G15 G22 G43 |
| literal `layout at` base vs physical layout | logicalStorageBase | storageLayout | G09 G15 G27.05 |
| `T transient x` vs physical transient slots | transientState | transientLayout | G15 G23 G39 |
| loops/recursion vs gas/stack exhaustion | termination, recursiveCalls | machineResources | G01 G36.03 G37.02 G49.03 |
| `send`/`transfer` vs exact stipend | sendTransfer | gasOption, machineResources | G22 G43 |
| `type(C).creationCode`/`runtimeCode` vs `address.code` | creationCode, runtimeCode | addressCode, addressCodehash | G15 G44.02 |
| `block.timestamp` vs other `block.*`/`tx.*` members | blockTimestamp, msgSender, msgValue | blockNumber, txOrigin, txGasprice, blockCoinbase, blockChainid | G15 G23 |
| `view` external call vs low-level `staticcall` | staticCallRestriction, externalTypedCalls | lowLevelStaticcall | G15 G42 |
| linked library call vs `delegatecall` | externalLibraryCalls | delegatecall | G15 G42.04 |
<!-- END generated by scripts/roadmap-g00-scope.py -->

## Remaining child obligations

G00 itself is complete as an audit; the obligations it hands on:
- Q1–Q5 to the user. Until answered, G15/S00 keep all 30 exclusions refused
  and unresolved; G55 cannot close with an unresolved row.
- G01: settings and fork in the theorem contracts; static code constants.
- G03: extend this ledger through admission → lowering → backend → EVM →
  theorem, including the `combination-*` symbols and the 14 named
  combinations.
- G05: the provenance settings validator vs linked libraries; the 0.8.34
  fixture boundary.
- G06: choose and pin the EVM fork for the core machine; reconcile Cancun
  vector scripts and the bridge.
- Each owner group: the rows assigned in the table, at the current statuses
  (139 model/partial, 1 model/missing, 21 abstract/partial).

## Review

Pending.

## Handoff

- Base `127c2ee59de16971e45b08a2def54f4e5fae8e2a`; branch
  `cloud/roadmap-w0-20261029/g00-scope-freeze`.
- Checked: pins by `git grep`; exclusion history by `git log`/`git show` and
  PR #5 metadata; reconciliation by the script (`--check`: 0 errors); manifest
  consistency by `solidity-feature-audit.py --check`; cited paths and
  declarations by `git grep -n` at the base. No Lean file was added, so no
  Lean build was required.

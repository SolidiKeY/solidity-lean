# G06 — re-pin the hand-written EVM vectors from Cancun to Osaka

Roadmap group G06 ([coverage-plan.md](../coverage-plan.md), wave 0), child
task. The user pinned Osaka for the semantics and the compiled bytecode
([G00 Q3](../solidity-scope.md#user-decisions-2026-10-29)), with the EIP-170 and
EIP-3860 code-size limits idealized (G01 Q2, same table). This task moves the
hand-written `scripts/check-*.mjs` EVM vector checks from Cancun to Osaka. It
does not touch Lean, Bridge or `Solidity/Evm/**`; the Lean-side pins are listed
as [child obligations](#4-child-obligations-for-g06).

- **Base revision:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`. Every
  `file:line` below refers to that revision unless it says "at head".
- **Commits.** The measurement commit adds this document, the evidence
  directory [tests/upstream/g06-osaka-repin/](../../tests/upstream/g06-osaka-repin/)
  and the locked runner [scripts/evm-vectors/](../../scripts/evm-vectors/run.sh).
  The **last commit on the branch** switches the pins and nothing else, so the
  integrator can take or drop it on its own. Without it the scripts stay on
  Cancun and the runner still works.
- **Not changed:** historical evidence records stay Cancun
  (`tests/upstream/revert-power/compiler-evm.json`,
  `tests/upstream/revert-power/validation.json:310`,
  `tests/upstream/step08-transient-world/evm-observations.json`). The Osaka
  regeneration of the two pinned outputs is stored beside the other evidence,
  not over them, so `validation.json`'s `reportSha256` stays true. The same
  holds for `tests/upstream/revert-power/compiler-evm-initial.json`. After the
  pin commit, three historical records hold the base SHA-256 of a script they
  ran: `tests/upstream/revert-power/validation.json:398`
  (`check-self-power-data.mjs`), `tests/upstream/step08-transient-world/report.json:31`
  (`check-transient-world-vectors.mjs`) and `tests/upstream/group01/validation.json:66`
  (`check-modifier-frames.mjs`). Nothing verifies those hashes. They stay records
  of the base scripts.

## 1. Setup on the VM

No network block was hit. Every dependency came through the agent proxy:

- solc from `raw.githubusercontent.com/ethereum/solc-bin/gh-pages/bin/`, as in
  [solidity-upstream-tests.md](../solidity-upstream-tests.md#reproduce). SHA-256 of
  `soljson-v0.8.38+commit.1835d247.js` is `6c74ffba…2d390` and of
  `soljson-v0.8.34+commit.80d5c536.js` is `c8649f8d…cfd11d8`. Both equal the pins
  the scripts assert.
- The external modules at the versions named in `scripts/check-abi-vectors.mjs:4`
  (EthereumJS `vm`/`common`/`util` 10.1.3, `ethers` 6.17.0), plus `tx` 10.1.3,
  which the two transaction-based scripts load (`check-transient-vectors.mjs:27`,
  `check-transient-world-vectors.mjs:20`). `evm` 10.1.3 is pinned too, as the
  version `vm` runs on. Before this task these
  scripts had no lockfile (G00 [pin disagreement 5](roadmap-g00-scope.md#pin-disagreements)).
  [scripts/evm-vectors/package.json](../../scripts/evm-vectors/package.json) now
  pins them exactly, with a `package-lock.json`:

```sh
npm ci --ignore-scripts --prefix scripts/evm-vectors
scripts/evm-vectors/run.sh /path/soljson-v0.8.38+commit.1835d247.js \
  /path/soljson-v0.8.34+commit.80d5c536.js OUT_DIR
```

`run.sh` runs the 12 scripts as 16 invocations (`check-public-getters`,
`check-call-exception-vectors`, `check-transient-vectors` and
`check-source-admission` take one compiler each and run once per pin;
`check-abi-hex-call` takes both). It prints one `PASS`/`FAIL` line per
invocation and `N/16 checks passed`. It exits 0 only if all pass. Each run
takes about 75 s on 4 cores.

## 2. Measurements

Three configurations ran on the same modules and compilers:

| Run | VM `Hardfork` | solc `evmVersion` | Result |
|---|---|---|---|
| Baseline | Cancun | `cancun` | **16/16 pass** ([cancun.txt](../../tests/upstream/g06-osaka-repin/cancun.txt)) |
| VM only (diagnostic) | Osaka | `cancun` | **13/16 pass** with the scripts unmodified; 16/16 once the EIP-7825 fix below is applied |
| Target | Osaka | `osaka` | **16/16 pass** ([osaka.txt](../../tests/upstream/g06-osaka-repin/osaka.txt)) |

Per invocation, identical on both forks:

| Check | Executions / observations | Compiler rejections |
|---|---|---|
| `check-abi-vectors` (0.8.38) | 31 | 5 |
| `check-recursive-types` (0.8.38) | 20 | 7 |
| `check-self-power-data` (0.8.38) | 82 exact-byte observations | — |
| `check-modifier-frames` (0.8.38) | 40 (20 per pipeline) | — |
| `check-operator-aliases` (0.8.38) | 38 + 2 metadata fixtures | 8 |
| `check-slice-copies` (0.8.38) | 18 | 3 per pipeline |
| `check-public-getters` (0.8.38, 0.8.34) | 62 each | 7 each |
| `check-call-exception-vectors` (0.8.38, 0.8.34) | 88 each | — |
| `check-transient-vectors` (0.8.38, 0.8.34) | 18 each | 12 each |
| `check-source-admission` (0.8.38, 0.8.34) | 22 each | 6 sources, 4 rejected + 3 accepted gates, each |
| `check-transient-world-vectors` (0.8.38) | 11 transactions per pipeline | — |
| `check-abi-hex-call` (0.8.38 + 0.8.34) | 36 | 40 |

**Differing vectors: none.** Every script compares against fixed expected
values, so a pass on both forks means every vector returned the same
observation. For the two scripts with a pinned output, the Osaka output
([compiler-evm-osaka.json](../../tests/upstream/g06-osaka-repin/compiler-evm-osaka.json),
[evm-observations-osaka.json](../../tests/upstream/g06-osaka-repin/evm-observations-osaka.json))
differs from the committed Cancun record only in the `evmVersion` field.
All 82, and 2 × 11, return bytes and exception kinds are equal. The Cancun runs
reproduce both committed records byte for byte.

**Cancun → Osaka changes the scripts had to absorb:**

| Change | EIP / fork | Effect here |
|---|---|---|
| Transaction gas cap 2^24 | EIP-7825 (Osaka) | `check-transient-vectors.mjs:55` and `check-transient-world-vectors.mjs:46` built signed legacy transactions with `gasLimit:30000000n`. Under Osaka, `createLegacyTx` throws `Transaction gas limit 30000000 exceeds the maximum allowed by EIP-7825 (16777216)` before any execution (3 invocations). The pin commit sets `16777216n`. With that limit the Cancun run passes and reproduces the committed record, so the change does not depend on the fork. No vector depends on gas: none asserts gas, and none runs out of it. |
| `runCode`/`runCall` message gas | — | The other 10 scripts call `vm.evm.runCode`/`runCall` with `gasLimit:30000000n`. These are message calls, not transactions, so EIP-7825 does not apply. They are left unchanged. |
| `CLZ` opcode (0x1e) | EIP-7939 (Osaka) | solc 0.8.38 emits no CLZ in any of the 97 compiled objects (counted at instruction positions, PUSH data skipped). |
| ModExp repricing / bounds, P-256 precompile | EIP-7883, EIP-7823, EIP-7951 (Osaka) | No script calls ModExp or P-256. Three precompiles are called, and none of them changed in Prague or Osaka: `ecrecover` (`tests/abi-0.8.38/Features.sol:47`, via `check-abi-vectors.mjs:90,96,97`), and `sha256` and `ripemd160` (`tests/solc/SliceCopies.sol:47-48`, via `check-slice-copies.mjs:44`). |
| BLS12-381 precompiles, EIP-7702 code delegation, calldata floor cost, historical block hashes in state | EIP-2537, EIP-7702, EIP-7623, EIP-2935 (Prague) | Not exercised: no BLS precompile calls, no type-4 transactions and no `blockhash`. Neither script that sends transactions asserts gas. |
| Contract and initcode size caps | EIP-170, EIP-3860 | Not idealized in these scripts (same as at the base). The largest runtime object is 9,484 bytes (cap 24,576). The largest creation object is 11,971 bytes (cap 49,152). No vector comes near either cap. |

**Compiled bytecode.** A `--require` preload intercepted every
`solidity_compile` call: 43 compiles, 97 `evm.bytecode`/`evm.deployedBytecode`
objects. It compared them between `evmVersion:'cancun'` and `'osaka'`
([bytecode-comparison.json](../../tests/upstream/g06-osaka-repin/bytecode-comparison.json)).
After the trailing CBOR metadata is stripped from deployed objects, 51 objects
are byte-identical. The other 46 differ only inside embedded CBOR metadata
sections: those of creation code and of child contracts' code. A metadata
section's IPFS hash covers the settings, including `evmVersion`. There
are 0 instruction differences. The preload itself was a scratch tool and is
not committed; the JSON records the method.

The pin commit's diff, by `file:line` at base:

- `Hardfork.Cancun` → `Hardfork.Osaka`: `check-abi-hex-call.mjs:64`,
  `check-abi-vectors.mjs:44`, `check-call-exception-vectors.mjs:49`,
  `check-modifier-frames.mjs:34`, `check-operator-aliases.mjs:41`,
  `check-public-getters.mjs:57`, `check-recursive-types.mjs:50,78`,
  `check-self-power-data.mjs:50`, `check-slice-copies.mjs:40`,
  `check-source-admission.mjs:47`, `check-transient-vectors.mjs:44`,
  `check-transient-world-vectors.mjs:33`.
- `evmVersion` `'cancun'` → `'osaka'` at the settings lines G00 lists
  (`check-abi-vectors.mjs:39`, `check-call-exception-vectors.mjs:37`,
  `check-modifier-frames.mjs:27`, `check-recursive-types.mjs:21`,
  `check-slice-copies.mjs:28`) and `check-abi-hex-call.mjs:49`,
  `check-operator-aliases.mjs:35`, `check-public-getters.mjs:37`,
  `check-self-power-data.mjs:38`, `check-source-admission.mjs:30,78`,
  `check-transient-vectors.mjs:35`, `check-transient-world-vectors.mjs:27`.
- Printed labels: `check-call-exception-vectors.mjs:92` and the
  `check-abi-hex-call.mjs:5` docstring now say Osaka.
- EIP-7825 gas limit: `check-transient-vectors.mjs:55` and
  `check-transient-world-vectors.mjs:46`, each with a one-line comment.

After the pin commit, `grep -rn -i cancun scripts/check-*.mjs` finds nothing.
This resolves G00 pin disagreement 2 for the vector scripts only.

## 3. Lanes whose gates must re-run

The Codex lanes' gate definitions are not in this repository, so this list is
by feature area plus the gates that are recorded here. If a lane gate runs
any `check-*.mjs` against the Cancun record, it must re-run after the pin
commit. Expected outputs are unchanged, except that `evmVersion` reads `osaka`.
Supplied `node_modules` must be EthereumJS 10.x, which has `Hardfork.Osaka`.

| Gate user | Scripts |
|---|---|
| Cloud integration post-build gate (`tests/upstream/cloud-integration-20261028/post-build-command.sh.txt`, phases `panic-evm`, `transient-evm`) | `check-self-power-data`, `check-transient-world-vectors` |
| revert-outcome-specs (revert data, panics) | `check-self-power-data`, `check-call-exception-vectors` |
| readonly-external (static calls, static creation refusal) | `check-call-exception-vectors`, `check-transient-world-vectors` |
| abi-lazy-calldata (ABI, calldata copies) | `check-abi-vectors`, `check-abi-hex-call`, `check-slice-copies`, `check-public-getters` |
| function-ref-args (function-type arguments) | `check-abi-vectors` (function-type ABI case) |
| memory-* (copies, reference arrays/structs, internal calls) | `check-recursive-types`, `check-slice-copies`, `check-modifier-frames` |
| evm-* (`Solidity/Evm` machine) | none of these scripts; the generated differential and replay were Osaka already |

Historical group validations that cite these scripts
(`tests/upstream/group01/validation.json` and
`tests/upstream/revert-power/validation.json`, both naming Cancun, and
`tests/upstream/group10-validation.json`) remain records of their own runs.
They are not re-run.

## 4. Child obligations for G06

These are Lean-side or other-owner pins that this task may not edit:

1. **Bridge EVM schedule.** `Bridge/vendor/EvmYul/Wheels.lean:148`
   `def TargetSchedule := "Cancun"`. This is the vendored EVMYulLean, and
   moving it to Osaka is a Bridge change (G06).
2. **Hash-pinned AST fixtures compiled with `evmVersion: cancun`.**
   `tests/solc/CallExceptions.ast.json` (imported at
   `Solidity/Examples/Tactics/CallExceptions.lean:17`, `hash 0x13163372312c84bc`),
   `tests/solc/SelfPowerData.legacy.ast.json` / `.viaIR.ast.json`
   (`Solidity/Examples/Tactics/SelfPowerData.lean:12,14`), and
   `tests/solc/TransientFactory.ast.json` / `.viaIR.ast.json`
   (`Solidity/Examples/Tactics/TransientWorldSource.lean:12,14,191,193`).
   To regenerate them with `--evm-version osaka`
   (`docs/feature-work/calls-exceptions.md:76` shows the command), the
   `solc_import`/`solc_world_factory` hashes in those Lean files must change.
   The ASTs record settings, not bytecode, so the only expected change is the
   settings field.
3. **Text that describes these scripts as Cancun.** These lines are owned by
   other groups' documents and are left for the integrator:
   `docs/feature-work/abi-hashes.md:95`,
   `docs/feature-work/transient-storage.md:95,389`,
   `docs/feature-work/source-admission.md:111`,
   `docs/solidity-upstream-tests.md:225`, the AST regeneration command's
   `--evm-version cancun` (`docs/feature-work/calls-exceptions.md:76`, which
   changes together with item 2), and the source comment
   `tests/solc/TransientStorage.sol:4`. G00's pin disagreement 2 and its
   follow-ups (`docs/feature-work/roadmap-g00-scope.md:96–102,336,784`) are owned
   by g00-manifest-rev.
4. **Core machine fork.** `docs/feature-work/roadmap-g00-scope.md:784` asks G06
   to "pin the EVM fork for the core machine". The core `Solidity/Evm` machine
   records no fork (same document, lines 102–103). `Solidity/Evm/**` belongs to
   the open evm-*/memory-* lanes, so this stays a G06 obligation.
5. **`evm-reference` module versions.** `scripts/evm-reference/package.json:8-9`
   still pins `@ethereumjs/common`/`util` 10.1.2, while `evm-vectors` pins 10.1.3.
   That package is already on Osaka and is not part of this task. That half of
   G00 disagreement 5 remains open.
6. **Code-size idealization in the vector scripts.** It is not encoded (see
   the table above). Add it only if a vector ever approaches 24,576 / 49,152
   bytes, as `scripts/evm-reference/replay.mjs:54` already does.

## 5. Gates

All results are at head. No Lean file was touched, so no Lean build or Lean
diagnostics were needed.

- `scripts/evm-vectors/run.sh` at base pins (Cancun): `16/16 checks passed`.
- `scripts/evm-vectors/run.sh` with the pin commit (Osaka): `16/16 checks passed`.
- `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`,
  `bash scripts/check-trust.sh`: see the handoff.
- `bash scripts/check-doc-paths.sh`: 46 missing references, unchanged from the base.

Elapsed time is about 75 s per vector run. Peak memory was not measured
(`/usr/bin/time` is absent), and nothing was built.

## Review

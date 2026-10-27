# Upstream Solidity tests

The complete `test/` tree from Solidity **v0.8.38**, commit
`1835d247de183f23e7b0e2bc4a50732af525b77c`, is stored in
`tests/upstream/solidity-0.8.38.tar.gz`. This matches the language inventory's
pin. The archive also includes Solidity's license and the complete schema
submodule at `937e3484cb4cf408a4e808d62f34285a71fece80`.
`tests/upstream/snapshot.json` records all 11,622 regular files, their sizes,
SHA-256 hashes, repository revisions and the archive hash. Upstream inputs
and expectations are preserved without editing. Keeping them compressed
avoids adding thousands of unrelated source files to normal repository scans.

## Separate result lists

The recorded run is in `tests/upstream/results/`:

It is a historical baseline on top of base commit `cadb628c`, with the added
adapter, as recorded in `validation.json`. The exact model source hash is
in `summary.json`.
Integrating later `master` changes does not rewrite that evidence. Re-run the
adapter against a newer source tree to obtain updated compatibility counts.

| File | Meaning |
| --- | --- |
| `working.json`, `working.txt` | Fixtures whose adapted expectations actually matched. |
| `broken.json`, `broken.txt` | Observed frontend import/call gaps or mismatched expectations, with reasons and available evidence. |
| `blocked.json`, `blocked.txt` | Fixtures requiring an unimplemented adapter, host/configuration, or more execution resources. These are not passing or demonstrated semantic bugs. |
| `summary.json` | Counts, compiler/source hashes, model hash, execution scope and completion flag. |
| `results.json` | Combined fixture verdicts and run provenance. |
| `file-coverage.json` | Every archived file, including native C++ suites, extensionless command-line assets, harnesses and support files. Unrun native assets are explicitly recorded. |
| `retries/*.json` | Complete isolated retry reports, including their distinct timeout/batch settings; the combined report retains their hashes and paths. |

Counts are **fixture/reference files**, not individual C++ tests or assertions.
The main verdict lists cover `.sol`, `.yul`, `.json`, `.stack`, `.ssa`, `.asm`
and `.asmjson` inputs. The exhaustive file ledger accounts for everything
else. A file's presence in the archive is not evidence it ran.

Two different checks have different meanings:

* `compiler-diagnostics` compares syntax-test diagnostics with the exact
  upstream expectations: diagnostic kind, number, order, source name,
  byte offsets and complete message. Expected compiler rejections count
  as working when their diagnostics match. This runs the SHA-pinned **solc
  reference**; it does not demonstrate Lean frontend or interpreter coverage.
* `lean-runtime` imports the contract through the repository's modern source
  admission and typed `solc_import`, then compares supported scalar runtime
  vectors with the typed Lean interpreter. Calls retain state in order,
  constructors/initializers run, failed calls roll back, and return values
  are compared as ABI words. Default/explicit `compileViaYul: also` fixtures
  must match in both legacy and via-IR source evaluation modes. `true` or
  `false` selects its requested single mode. The combined verdict retains
  each mode's observations and gaps.

Runtime results are observations, not universal correctness proofs. They do
not exercise generated solc EVM/SSA code, the repository's EVM compiler, gas
costs or the upstream C++ EVM host. Unsupported gas/log/host observations
remain blocked. The Group 10 adapter additionally replays canonical-prefix typed ABI
aggregates/bytes and v2 primitive decoder checks from raw calldata words,
retaining exact encoded returns. Actual declaration types must agree with the
compiler ABI. Aggregate/function inputs must have an exact canonical prefix; trailing bytes
remain recorded and are unreachable under the raw-data/assembly/host exclusions.
ABI v1 raw inputs require this prefix check even for primitive parameters; an
eager v2 rejection cannot certify a v1 failure. Malformed/lazy layouts, nominal enum ranges,
physical assembly layouts and unimplemented wrapper types remain blocked.
Failure payloads use supported native word/string/hex formatting and compare
complete retained revert bytes, including constructors. The external-entry
observer retains source failure bytes without self-call environment rewriting;
ABI preparation/probes/serialization keep their ordinary failure policy. Empty failure means
empty bytes; a generic panic cannot certify a concrete ABI panic code and
remains blocked. Ordinary-call lowering can abstract data away, so a payload
mismatch is an adapter/model observation, not an upstream EVM bug.
See [ABI M3](feature-work/abi-hashes.md#m3-upstream-group-10-exact-retained-revert-data-2026-10-26)
for the staged evidence and exact limits. Loop fuel remains 1,000 per loop;
exhaustion or a process timeout is blocked, never a matching expected failure.
Unsupported compiler configurations and EVM-version constraints are likewise
explicit. Other upstream families (SMT checker, Yul optimizer, AST/NatSpec
goldens, command-line and native unit tests) are preserved and inventoried but
need their own adapters. A whole-suite `complete` flag means every selected
fixture has a verdict, including blocked cases; it does not mean all suites ran.

## Reproduce

Use Lean 4.24.0 from `lean-toolchain`, Node, Python 3 and `tar`.
No dependency is added to the core Lake package. In the configured cloud
workspace, first source `/workspace/.setup/activate.sh`.

```sh
# Verify and extract all files into the ignored .lake/upstream/solidity/.
node scripts/solidity-upstream.mjs verify

# Download the exact external reference compiler if it is not already present.
curl -fL \
  https://raw.githubusercontent.com/ethereum/solc-bin/gh-pages/bin/soljson-v0.8.38+commit.1835d247.js \
  -o /tmp/soljson-v0.8.38+commit.1835d247.js

# The runner checks the compiler's SHA-256 and full version before using it.
node scripts/solidity-upstream.mjs run \
  --compiler /tmp/soljson-v0.8.38+commit.1835d247.js

# Focused rerun (keep its result directory separate from the complete report).
node scripts/solidity-upstream.mjs run \
  --compiler /tmp/soljson-v0.8.38+commit.1835d247.js \
  --filter semanticTests/arithmetics --out .lake/upstream/arithmetic-results

node --test --test-isolation=none scripts/solidity-upstream.test.mjs
lake --no-build lean tests/upstream/Replay.lean -- --tstack=131072
```

The runner builds `Solidity.Tools.Upstream` once. Lean runs in batches of 16
mode-specific imports with a 120-second process limit. Results are checkpointed
after each fixture/mode and saved after each batch. `--timeout-ms` and
`--batch-size` adjust those limits. `--resume` reuses completed file verdicts
only when compiler, archive, runner, model and configuration hashes match.
No source changes or test expectation changes are needed to rerun failures.
Exit 0 requires no broken/blocked fixtures; 1 records an incomplete-compatible
suite; 2 indicates an invocation, integrity or initial build error.

If a batch times out, completed mode checkpoints survive, but later fixtures
in that process may not have started. Retry an interrupted fixture with its
entire snapshot path as `--filter`, `--batch-size 1`, and a separate `--out`.
After the full run finishes, merge the isolated reports with:

```sh
node scripts/merge-solidity-upstream-retries.mjs \
  tests/upstream/results /path/to/isolated-retry-results
```

The merger requires identical compiler, snapshot, runner, model and execution
scope. It retains conclusive mode observations, refuses contradictory verdicts,
stores each retry's original report, and records its SHA-256 and configuration.
This prevents an expensive earlier fixture from concealing the results of
otherwise runnable tests.

To recreate the snapshot from Git, initialize the schema submodule and run:

```sh
git -C /path/to/solidity checkout 1835d247de183f23e7b0e2bc4a50732af525b77c
git -C /path/to/solidity submodule update --init test/ethdebugSchemaTests/ethdebug-format
python3 scripts/snapshot-solidity-upstream.py /path/to/solidity
```

## Verification and review

The parser/vector regressions check fixture boundaries, preamble offsets,
exact diagnostics, pipeline defaults, malformed calldata, signed ABI words,
unsupported observations and exhaustive partitioning. The Lean replay
regressions check deployment initializers, stateful sequencing, rollback,
real mismatches and inconclusive fuel/panic outcomes.

The milestone's independent read-only finder and skeptic reviews identified
the implicit `compileViaYul: also` default, native files outside fixture lists,
the schema gitlink, raw-comment context matching, constructor failure behavior
and shared temporary paths. The runner now checks required interpreter modes,
records every archived file, vendors the pinned submodule, scans the AST for
host-dependent behavior, blocks calls after failed deployment, and isolates
each run's temporary inputs/checkpoints.

The retry merger received its own finder/skeptic review. Retry reports are
content-addressed so repeated retries cannot overwrite evidence used by an
earlier mode. A regression merges two partial retries of one fixture and
requires both original reports to survive. All 14 JavaScript regression tests
and the five Lean replay checks pass.

The completed corpus partition and the two observed via-IR modifier return
differences are recorded in [the corpus summary](../tests/upstream/README.md).
The archived source and expectation bytes were independently checked against
all 11,622 pinned Git blobs. Snapshot regeneration reproduces the archive and
manifest byte for byte. Module reachability and core/frontend layering checks
pass. The documentation-path check still reports its 13 pre-existing missing
references outside these additions.
The new observational `evalExpr` site is recorded in the trust inventory.
The trust scanner still reports the same 25 inventory mismatches as the
original checkout; comparing the complete finding lists confirms no new drift.
The theorem-dependency audit passes for 468 headline theorems. The broader
`lake build Solidity` cold build was stopped after 45 minutes at 614/618
targets, while checking the existing `Examples/Decision.lean`; no build
errors had been reported. Its result is inconclusive. The new upstream module
and all replay checks completed successfully. Exact check outcomes are in
`tests/upstream/results/validation.json`.

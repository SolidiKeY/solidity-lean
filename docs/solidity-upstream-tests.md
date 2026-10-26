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

The recorded run is in `tests/upstream/results/` (counts and the observed
via-IR modifier differences: [the corpus summary](../tests/upstream/README.md)).
It is a baseline of base commit `cadb628c`; the model source hash is in
`summary.json`. Re-run the adapter to measure a newer model.

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
costs or the upstream C++ EVM host. Unsupported gas/log/revert-data checks,
aggregate/dynamic/bytes ABI inputs, noncanonical calldata, external host
behavior and source imports remain blocked rather than being dropped.
Only empty-data function failures are currently replayed; the model's generic
panic cannot certify an expected ABI panic code. Loop fuel is 1,000 per loop;
exhaustion or a process timeout is blocked, never a matching expected failure.
Unsupported compiler configurations and EVM-version constraints are likewise
explicit. Other upstream families (SMT checker, Yul optimizer, AST/NatSpec
goldens, command-line and native unit tests) are preserved and inventoried but
need their own adapters. A whole-suite `complete` flag means every selected
fixture has a verdict, including blocked cases; it does not mean all suites ran.

## Reproduce

Use Lean 4.24.0 from `lean-toolchain`, Node, Python 3 and `tar`.
No dependency is added to the core Lake package.

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

## Tests

`node --test --test-isolation=none scripts/solidity-upstream.test.mjs` covers
fixture boundaries, preamble offsets, exact diagnostics, pipeline defaults
(an omitted `compileViaYul` means `also`), malformed calldata, signed ABI
words, the exhaustive partition and retry merging; `tests/upstream/Replay.lean`
covers deployment initializers, stateful sequencing, rollback, real
mismatches and inconclusive fuel/panic outcomes. The new `evalExpr` site of
`Tools/Upstream.lean` is in the trust inventory.

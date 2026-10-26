# Solidity v0.8.38 test corpus

All 11,622 pinned upstream test/schema/license files are preserved in
`solidity-0.8.38.tar.gz`; `snapshot.json` records their provenance and hashes.
Run `node scripts/solidity-upstream.mjs verify` from the repository root to
extract them into `.lake/upstream/solidity/`.

The recorded run on top of base commit `cadb628c`, with the added adapter,
classifies 9,660 fixture/reference files. The report retains that model's source hash and
validation evidence; later changes on `master` may change individual results.
Run the adapter again to measure a newer model.

| Check | Working | Broken | Blocked |
| --- | ---: | ---: | ---: |
| Lean functional runtime vectors | 229 | 308 | 1,164 |
| Pinned solc syntax diagnostics | 3,478 | 0 | 64 |
| Other fixture/reference families | 0 | 0 | 4,417 |
| Total | 3,707 | 308 | 5,645 |

The two working columns measure different things: solc diagnostics are
reference-compiler checks, not Lean interpreter coverage. Runtime verdicts
cover the supported functional observations in every required legacy/via-IR
source evaluation mode. They do not test generated EVM/SSA code or gas.

* [Working fixtures](results/working.txt)
* [Broken fixtures](results/broken.txt)
* [Blocked fixtures](results/blocked.txt)
* [Complete machine-readable results](results/results.json)
* [Every preserved file, including unrun native suites and support assets](results/file-coverage.json)
* [Summary and run provenance](results/summary.json)
* [Validation outcomes and existing repository audit failures](results/validation.json)

Of the 308 broken runtime fixtures, 306 expose frontend import/call gaps.
Two show return-value differences in via-IR modifiers:

| Upstream semantic fixture | Expected | Lean observed |
| --- | --- | --- |
| `modifiers/function_modifier_loop_viair.sol`, `f()` | `1` | `10` |
| `modifiers/function_modifier_multi_invocation_viair.sol`, `f(true)` | `1` | `2` |

Blocked cases include unsupported harnesses/configurations and execution
limits; they are not passing tests or demonstrated semantic defects. Native
C++ files may contain many tests and are preserved in the exhaustive file
ledger rather than counted as individual cases here. All source files and
upstream expectations remain unchanged.

The run includes 26 isolated retry reports for fixtures interrupted behind
expensive earlier cases. Their original metadata and content hashes are
retained in `results/retries/` and referenced by the combined report.

The runner's 14 JavaScript tests, five Lean replay checks and the 468-theorem
axiom audit pass. The broader cold Lean build was stopped after 45 minutes
at 614/618 targets in existing decision examples, so that check is inconclusive.
The existing 25 trust-inventory mismatches and 13 missing documentation
references are recorded separately; this change adds no new trust findings.

See [the runner documentation](../../docs/solidity-upstream-tests.md) for
commands, exact scope, limitations and validation details.

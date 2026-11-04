# Fresh Dafny / Solidity Lean stdio baseline

Recorded 2026-11-03T23:16:38.244Z. Full parity is **not established**.

54 sequential isolated server launches: 45 measured trials, 9 warmups, 0 broken launches and 0 timeouts in the selected datasets. Exploratory failed probes are retained separately in JSON.

Dafny 4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2; Node v24.19.0; CPU quota 400000 100000; memory limit 17179869184 bytes; one Lean thread selected. No editor executable ran.

## Paired language-service results

Five measured trials per target/worker setting; one excluded warmup each. Values are median / nearest-rank p95 milliseconds.

| Target | Workers | Launch → initialize | Launch → document symbols | Hover | Member completion | Eight concurrent hovers |
|---|---:|---:|---:|---:|---:|---:|
| dafny | 1 | 837.6 / 870.4 | 1087.1 / 1111.4 | 18.7 / 23.3 | 35.4 / 44.8 | 12.1 / 44.7 |
| local | 1 | 76.6 / 83.0 | 452.3 / 511.2 | 10.2 / 20.4 | 23.9 / 24.8 | 78.8 / 80.2 |
| dafny | 2 | 815.9 / 863.2 | 1049.9 / 1134.2 | 18.6 / 21.7 | 31.7 / 60.8 | 9.1 / 12.0 |
| local | 2 | 72.0 / 74.0 | 446.2 / 478.4 | 9.2 / 12.5 | 24.4 / 29.2 | 69.4 / 78.1 |
| dafny | 4 | 854.0 / 864.2 | 1120.0 / 1134.3 | 20.2 / 23.3 | 39.1 / 55.3 | 10.7 / 12.3 |
| local | 4 | 81.1 / 110.1 | 468.0 / 611.9 | 9.8 / 12.6 | 25.2 / 31.7 | 83.4 / 100.5 |

Document-symbol availability includes initial frontend loading; initialization alone does not establish useful feedback. Standard deviations, min/max, resource statistics and every native response remain in JSON. Requested proof-worker counts do not make this language-service workload parallel.

Both targets passed actual declaration/reference ranges, rename edits, supported member completion, opening-parenthesis signatures, symbols, meaningful hover, concurrent requests, rapid symbol edits and graceful lifecycle checks. Dafny returned no second-argument signature and lost member completion after a full replacement with incomplete code; the local server handled both. These are explicit partial observations, not hidden normalization. Formatter checks remain partial.

The local eight-concurrent-hover median is 78.8 ms versus Dafny’s 12.1 ms at one worker. A separate post-run microprofile measured synchronous backend-generation fingerprinting at 9.7 ms median / 12.2 ms p95 over 20 samples after three warmups. Every local language request calls analyze → refresh → fingerprint, so repeated synchronous freshness checks plausibly explain much of this serialization. This is an investigated unresolved responsiveness difference, not an isolated causal measurement; no cache-safety check was weakened.

## Reference-only verification and scaling

| Dafny workers | Initial median / p95 ms | Incremental median / p95 ms | Two-file median / p95 ms | Initial speedup | Max CPU-active Z3 in initial phase |
|---:|---:|---:|---:|---:|---:|
| 1 | 611.1 / 616.0 | 313.0 / 317.5 | 309.5 / 311.1 | 1.000× | 1 |
| 2 | 611.4 / 708.2 | 208.7 / 209.4 | 310.8 / 314.6 | 0.999× | 2 |
| 4 | 608.3 / 621.3 | 208.7 / 214.8 | 313.8 / 315.9 | 1.005× | 4 |

Real Dafny/Z3 verifies eight constant-return methods using explicit native symbol requests with automatic verification disabled. False postconditions, incremental checks, versioned stale diagnostics and concurrent files pass. The initial-phase samples establish interval CPU activity in distinct Z3 processes, while this tiny workload shows almost no initial end-to-end scaling. They do not establish representative throughput or exact simultaneous execution.

## Blocked and unexamined

- **VS Code API/DOM/accessibility/renderer validation:** Official VS Code download https://update.code.visualstudio.com/1.108.0/linux-x64/stable returned HTTP 403 under the enforced network policy.
- **Fresh local proof/performance comparison:** Repository heavy-build instructions require a systemd scope. systemd-run --user failed because no user bus exists; no fresh local backend build or local verification run was substituted.

Local proof latency/scaling and all new UI measurements remain unexamined. Earlier paired editor/proof baselines describe older implementations. The manual CI workflow can build the current backend and run either editor or stdio comparisons on a provisioned host.

## Validation and audit

117 Node tests passed, two real-backend suites skipped, zero failed. The 93-feature inventory and independent 99-file / 609-registration ledger match the pinned sources. No feature is classified complete. Read-only finder and skeptic findings and their repairs are recorded in [the harness guide](../../docs/dafny-editor-parity.md#harness-integrity-and-stdio-comparison-2026-11-03).

## Evidence and limits

The [machine-readable baseline](stdio-baseline.json) persists per-trial native responses, metrics, resource phases, failure rates, feature evidence, source hashes and excluded probes. Raw JSON-RPC/events/process samples remain under the referenced `.cache/editor-parity/` paths; archive those directories to retain full raw traces outside this workspace.

- Stdio measurements do not measure extension activation, VS Code APIs or renderer responsiveness. Changed editor scenarios have not been executed here.
- Language-service fixtures are not verified; full proof scope runs explicit per-symbol requests on eight constant-return obligations.
- Dafny/Z3 and the local Lean verifier have different resource-limit meanings; no solver-speed ratio is claimed.
- Five repetitions provide descriptive median, nearest-rank p95 and variability, not a stable tail-latency estimate.
- Process-cold startup retains OS caches. Startup through initialize can precede useful language-service availability.
- Formatting proves invocation/response shape only. No capability is classified complete by these runs.
- Full stdio scope lacks cancellation, restart, counterexamples, settings transitions, complex proofs and large-project/contention tests.
- CPU overlap is interval-level evidence, not proof of simultaneous instructions; short solver jobs may be missed.

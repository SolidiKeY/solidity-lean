# Measured editor baseline

Recorded 2026-10-31T14:47:11.110Z. Full parity is **not established**.

46 isolated editor launches; 35 measured trials; 11 warmups; 0 broken launches.

| Dataset | Target | Workers requested | Cache requested | n | Initial median / p95 ms | Incremental median / p95 ms |
|---|---|---:|---|---:|---:|---:|
| full-measured-20261031 | dafny | 1 | none | 1 | 1051.8 / 1051.8 | 260.8 / 260.8 |
| full-measured-20261031 | local | 1 | none | 1 | 5375.9 / 5375.9 | 6432.7 / 6432.7 |
| scaling-measured-20261031 | dafny | 1 | none | 3 | 1129.9 / 1137.0 | 245.8 / 252.8 |
| scaling-measured-20261031 | local | 1 | none | 3 | 5869.7 / 6299.4 | 6550.2 / 6855.3 |
| scaling-measured-20261031 | dafny | 2 | none | 3 | 1150.6 / 1154.8 | 252.2 / 263.7 |
| scaling-measured-20261031 | local | 2 | none | 3 | 5559.6 / 6023.6 | 6589.2 / 6636.3 |
| scaling-measured-20261031 | dafny | 4 | none | 3 | 1034.6 / 1043.8 | 247.1 / 269.4 |
| scaling-measured-20261031 | local | 4 | none | 3 | 5702.0 / 5729.1 | 6368.9 / 6537.8 |
| caching-retry-20261031 | dafny | 1 | basic | 3 | 1140.5 / 1158.3 | 239.8 / 245.6 |
| caching-retry-20261031 | local | 1 | basic | 3 | 6063.0 / 6170.8 | 6593.6 / 6831.4 |
| profile-control-20261031 | dafny | 1 | none | 3 | 1157.7 / 1158.9 | 249.6 / 287.2 |
| profile-control-20261031 | local | 1 | none | 3 | 5631.1 / 5763.1 | 6371.1 / 6744.8 |
| observer-control-20261031 | dafny | 1 | none | 3 | 1152.3 / 1166.0 | 258.1 / 262.5 |

| Dataset | Workers requested | Cache requested | Local / Dafny initial latency | Local / Dafny incremental latency |
|---|---:|---|---:|---:|
| scaling-measured-20261031 | 1 | none | 5.19× | 26.65× |
| scaling-measured-20261031 | 2 | none | 4.83× | 26.12× |
| scaling-measured-20261031 | 4 | none | 5.51× | 25.77× |
| caching-retry-20261031 | 1 | basic | 5.32× | 27.50× |
| profile-control-20261031 | 1 | none | 4.86× | 25.53× |

Ratios include frontend and process architecture differences. They do not compare pure solver execution speed.

## Observed process overlap

| Target | Workers | Cache | Maximum CPU-active Z3 processes | Maximum CPU-active Lean processes |
|---|---:|---|---:|---:|
| dafny | 1 | none | 4 | 0 |
| local | 1 | none | 0 | 2 |
| dafny | 2 | none | 6 | 0 |
| local | 2 | none | 0 | 2 |
| dafny | 4 | none | 11 | 0 |
| local | 4 | none | 0 | 2 |
| dafny | 1 | basic | 4 | 0 |
| local | 1 | basic | 0 | 2 |

These counts cover the complete scenario suite, including concurrent files and cancellation. They show CPU activity within sampling intervals, not exact simultaneous instructions or isolated phase throughput.

## Scope and interpretation

- The paired workloads use 4 constant-return functions; the incremental case adds one function.
- Fresh process/profile startup and live-server incremental verification are separate. OS caches were not flushed.
- The local backend does not apply worker/cache settings. Its repeated configurations are controls, not local scaling.
- Solver overlap is derived from distinct process CPU deltas, not task counts or async calls.
- Dafny owns a Boogie engine per project; Boogie 3.5.5 applies VcsCores using a per-engine semaphore. Requested workers are not a global server-wide solver cap.
- Cancellation remains acknowledgement-only; complex proofs, renderer paint latency and single-declaration assertion-split scaling remain unexamined.
- Three measurement repetitions give descriptive medians and nearest-rank p95, not a stable tail-latency estimate.

## Artifacts

- .cache/editor-parity/full-measured-20261031/report.json: completed-with-gaps; source hashes, exact configuration and raw trial references are retained in the JSON baseline.
- .cache/editor-parity/scaling-measured-20261031/report.json: completed-with-gaps; source hashes, exact configuration and raw trial references are retained in the JSON baseline.
- .cache/editor-parity/caching-retry-20261031/report.json: completed-with-gaps; source hashes, exact configuration and raw trial references are retained in the JSON baseline.
- .cache/editor-parity/profile-control-20261031/report.json: completed-with-gaps; source hashes, exact configuration and raw trial references are retained in the JSON baseline.
- .cache/editor-parity/observer-control-20261031/report.json: completed-with-gaps; source hashes, exact configuration and raw trial references are retained in the JSON baseline.
- Invalidated .cache/editor-parity/caching-measured-20261031/report.json: 6 failed starts across 8 attempts. Pre-fix editor IPC path exceeded the Unix socket-path limit. Excluded from performance estimates and rerun with short temporary editor state.

The [machine-readable baseline](baseline.json) retains individual timings, dispersion, timeout rates, resource activity, scenario classifications, protocol summaries and feature evidence. Raw traces and renderer artifacts are referenced under `.cache/editor-parity/`; rerun the [harness](../../docs/dafny-editor-parity.md) when those workspace artifacts are unavailable.

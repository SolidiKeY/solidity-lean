# Measured editor baseline

Recorded 2026-10-31T21:28:22.856Z. Full parity is **not established**.

20 isolated editor launches; 16 measured trials; 4 warmups; 0 broken launches.

| Dataset | Target | Workers requested | Cache requested | n | Initial median / p95 ms | Incremental median / p95 ms |
|---|---|---:|---|---:|---:|---:|
| compiler-project-full-final | dafny | 1 | none | 1 | 1124.6 / 1124.6 | 239.1 / 239.1 |
| compiler-project-full-final | local | 1 | none | 1 | 7001.9 / 7001.9 | 4856.2 / 4856.2 |
| compiler-project-full-final | dafny | 2 | none | 1 | 1140.2 / 1140.2 | 239.9 / 239.9 |
| compiler-project-full-final | local | 2 | none | 1 | 6724.9 / 6724.9 | 3308.0 / 3308.0 |
| compiler-project-measured-final | dafny | 1 | none | 3 | 1181.7 / 1190.5 | 245.5 / 262.0 |
| compiler-project-measured-final | local | 1 | none | 3 | 6354.9 / 6528.6 | 5070.3 / 5137.8 |
| compiler-project-measured-final | dafny | 2 | none | 3 | 1074.7 / 1147.9 | 264.2 / 266.9 |
| compiler-project-measured-final | local | 2 | none | 3 | 6466.8 / 7918.7 | 3513.8 / 3598.1 |

| Dataset | Target | Workers | Exact-snapshot cache median / p95 ms | Two-file median / p95 ms |
|---|---|---:|---:|---:|
| compiler-project-full-final | dafny | 1 | unmeasured | 426.0 / 426.0 |
| compiler-project-full-final | local | 1 | 130.1 / 130.1 | 8786.8 / 8786.8 |
| compiler-project-full-final | dafny | 2 | unmeasured | 434.0 / 434.0 |
| compiler-project-full-final | local | 2 | 166.9 / 166.9 | 6839.8 / 6839.8 |
| compiler-project-measured-final | dafny | 1 | unmeasured | 325.9 / 327.7 |
| compiler-project-measured-final | local | 1 | 132.5 / 184.0 | 8397.8 / 8429.2 |
| compiler-project-measured-final | dafny | 2 | unmeasured | 346.0 / 360.7 |
| compiler-project-measured-final | local | 2 | 170.1 / 171.4 | 5327.3 / 6342.5 |

| Dataset | Workers requested | Cache requested | Local / Dafny initial latency | Local / Dafny incremental latency |
|---|---:|---|---:|---:|
| compiler-project-measured-final | 1 | none | 5.38× | 20.65× |
| compiler-project-measured-final | 2 | none | 6.02× | 13.30× |

Ratios include frontend and process architecture differences. They do not compare pure solver execution speed.

## Observed process overlap

| Target | Workers | Cache | Maximum CPU-active Z3 processes | Maximum CPU-active Lean processes |
|---|---:|---|---:|---:|
| dafny | 1 | none | 3 | 0 |
| local | 1 | none | 0 | 2 |
| dafny | 2 | none | 6 | 0 |
| local | 2 | none | 0 | 4 |

These counts cover the complete scenario suite, including concurrent files and cancellation. They show CPU activity within sampling intervals, not exact simultaneous instructions or isolated phase throughput.

## Scope and interpretation

- The paired workloads use 4 constant-return functions; the incremental case adds one function.
- Fresh process/profile startup and live-server incremental verification are separate. OS caches were not flushed.
- The local LSP bounds concurrent functions and files with 1–4 workers. Assertions within one function remain serial. Exact-snapshot cache hits and changed-buffer checks are separate; Dafny cache policies have no equivalent local selector.
- Solver overlap is derived from distinct process CPU deltas, not task counts or async calls. A native Lean LSP can include server and file-worker processes; CPU-active Lean processes are not a proof-worker count.
- Dafny owns a Boogie engine per project; Boogie 3.5.5 applies VcsCores using a per-engine semaphore. Requested workers are not a global server-wide solver cap.
- The editor cancellation metric measures acknowledgement; separate real LSP tests check worker termination. Complex proofs, renderer paint latency and single-declaration assertion-split scaling remain unexamined.
- Three measurement repetitions give descriptive medians and nearest-rank p95, not a stable tail-latency estimate.

## Artifacts

- .cache/editor-parity/compiler-project-full-final/report.json: completed-with-gaps; source hashes, exact configuration and raw trial references are retained in the JSON baseline.
- .cache/editor-parity/compiler-project-measured-final/report.json: completed-with-gaps; source hashes, exact configuration and raw trial references are retained in the JSON baseline.

The [machine-readable baseline](compiler-project-baseline.json) retains individual timings, dispersion, timeout rates, resource activity, scenario classifications, protocol summaries and feature evidence. Raw traces and renderer artifacts are referenced under `.cache/editor-parity/`; rerun the [harness](../../docs/dafny-editor-parity.md) when those workspace artifacts are unavailable.

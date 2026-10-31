# Measured editor baseline

Recorded 2026-10-31T18:37:35.999Z. Full parity is **not established**.

18 isolated editor launches; 14 measured trials; 4 warmups; 0 broken launches.

| Dataset | Target | Workers requested | Cache requested | n | Initial median / p95 ms | Incremental median / p95 ms |
|---|---|---:|---|---:|---:|---:|
| lsp-integrated-full | dafny | 1 | none | 1 | 1038.5 / 1038.5 | 239.4 / 239.4 |
| lsp-integrated-full | local | 1 | none | 1 | 6053.7 / 6053.7 | 4918.7 / 4918.7 |
| lsp-integrated-measured | dafny | 1 | none | 3 | 1143.5 / 1162.7 | 246.9 / 248.5 |
| lsp-integrated-measured | local | 1 | none | 3 | 6127.1 / 7947.6 | 5174.7 / 5196.7 |
| lsp-integrated-measured | dafny | 2 | none | 3 | 1150.1 / 1174.1 | 149.4 / 244.8 |
| lsp-integrated-measured | local | 2 | none | 3 | 6345.2 / 6428.4 | 5377.3 / 5467.0 |

| Dataset | Target | Workers | Exact-snapshot cache median / p95 ms | Two-file median / p95 ms |
|---|---|---:|---:|---:|
| lsp-integrated-full | dafny | 1 | unmeasured | 540.5 / 540.5 |
| lsp-integrated-full | local | 1 | 103.9 / 103.9 | 8889.8 / 8889.8 |
| lsp-integrated-measured | dafny | 1 | unmeasured | 317.9 / 325.9 |
| lsp-integrated-measured | local | 1 | 100.2 / 118.6 | 8638.1 / 8674.4 |
| lsp-integrated-measured | dafny | 2 | unmeasured | 314.0 / 320.5 |
| lsp-integrated-measured | local | 2 | 108.6 / 128.0 | 6633.5 / 7101.9 |

| Dataset | Workers requested | Cache requested | Local / Dafny initial latency | Local / Dafny incremental latency |
|---|---:|---|---:|---:|
| lsp-integrated-measured | 1 | none | 5.36× | 20.96× |
| lsp-integrated-measured | 2 | none | 5.52× | 35.99× |

Ratios include frontend and process architecture differences. They do not compare pure solver execution speed.

## Observed process overlap

| Target | Workers | Cache | Maximum CPU-active Z3 processes | Maximum CPU-active Lean processes |
|---|---:|---|---:|---:|
| dafny | 1 | none | 5 | 0 |
| local | 1 | none | 0 | 2 |
| dafny | 2 | none | 6 | 0 |
| local | 2 | none | 0 | 3 |

These counts cover the complete scenario suite, including concurrent files and cancellation. They show CPU activity within sampling intervals, not exact simultaneous instructions or isolated phase throughput.

## Scope and interpretation

- The paired workloads use 4 constant-return functions; the incremental case adds one function.
- Fresh process/profile startup and live-server incremental verification are separate. OS caches were not flushed.
- The local LSP bounds concurrent files with 1–4 workers. Within-file proofs remain serial. Exact-snapshot cache hits and changed-buffer checks are separate; Dafny cache policies have no equivalent local selector.
- Solver overlap is derived from distinct process CPU deltas, not task counts or async calls. A native Lean LSP can include server and file-worker processes; CPU-active Lean processes are not a proof-worker count.
- Dafny owns a Boogie engine per project; Boogie 3.5.5 applies VcsCores using a per-engine semaphore. Requested workers are not a global server-wide solver cap.
- The editor cancellation metric measures acknowledgement; separate real LSP tests check worker termination. Complex proofs, renderer paint latency and single-declaration assertion-split scaling remain unexamined.
- Three measurement repetitions give descriptive medians and nearest-rank p95, not a stable tail-latency estimate.

## Artifacts

- .cache/editor-parity/lsp-integrated-full/report.json: completed-with-gaps; source hashes, exact configuration and raw trial references are retained in the JSON baseline.
- .cache/editor-parity/lsp-integrated-measured/report.json: completed-with-gaps; source hashes, exact configuration and raw trial references are retained in the JSON baseline.

The [machine-readable baseline](lsp-baseline.json) retains individual timings, dispersion, timeout rates, resource activity, scenario classifications, protocol summaries and feature evidence. Raw traces and renderer artifacts are referenced under `.cache/editor-parity/`; rerun the [harness](../../docs/dafny-editor-parity.md) when those workspace artifacts are unavailable.

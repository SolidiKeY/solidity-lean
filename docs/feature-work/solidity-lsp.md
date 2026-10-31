# Persistent Solidity language server

The extension now keeps a Solidity LSP and bounded Lean proof workers running.
It verifies versioned, unsaved buffers through the pinned compiler frontend and
existing kernel-checked proof commands. No core Lean semantics changed.

`vscode/src/rpc.cjs` owns byte framing and full-duplex JSON-RPC. The server owns
buffer versions, compiler diagnostics, analysis, proof scheduling, exact-snapshot
cache entries and dependency generations. Each proof worker keeps one generated
Lean document open, retaining its imported environment between versions. Compiler
analysis runs separately so editor queries need not wait for proof completion.
Workers are bounded to 1–4 concurrent files; each document's contracts and
obligations remain serial. Cancellation kills active worker trees; replacements
start lazily. Restart and configuration changes clear sessions and caches.

Completion, definitions, references, symbols, signatures, highlights and rename
use compiler declaration identities. Incomplete code gets lexical completion.
Rename refuses collisions and NatSpec references requiring manual updates. The
extension provides syntax, proof gutters, status, diagnostics, Testing and hover.
Source hashes, compiler pins, import-gap messages and certified witness validation
remain enforced. Generated checkpoint files are unique to task and contract;
rows must belong to that contract's declaration lineage.

Cache entries require identical URI, source bytes, selection, proof options and
backend generation. Sources, compiler pins and artifact identities invalidate
both reports and live Lean sessions. The cache reuses already checked reports;
changed source still requires Lean checking. It is not assertion-level caching.

Receiver-type completion, formatting, code actions, workspace symbols, project
includes, per-assertion scheduling, full refactoring and Dafny protocol equivalence
remain open. The [88-feature inventory](../dafny-editor-features.json) keeps these
limits visible. The [extension guide](../../vscode/README.md) documents operation
and [comparison guide](../dafny-editor-parity.md) documents measurement scope.

## Review and validation

The required read-only finder and skeptic reviews identified cancelled-promise
reuse, stale same-version status, late build callbacks, unversioned rename,
qualified identifier ranges, default compiler invalidation, hidden native import
warnings and cross-contract checkpoint reuse. These were fixed, with focused
regressions and real compiler/Lean tests. The final pass also caught native Lean restart initialization, compiler warnings
on cache hits, selected-function sibling diagnostics, closed-document startup,
and overlapping parent/child qualified-name edits. These were fixed and both
reviewers confirmed the changes. Neither reviewer used the Lean server.

The real stdio tests check unsaved proofs without disk mutation, exact cache
hits, same-process Lean reuse for changed source, actual language services,
compiler errors, certified refutations, stale-result suppression, cancellation
quiescence, two bounded concurrent workers and distinct multi-contract identities.

Final validation after integrating master at `4165de13` passed 89 offline tests,
11 real stdio LSP tests, and 35 native VS Code host checks. The real-backend suite
is intentionally skipped in the offline command and run separately. The current
Lean API built all 263 targets. Its sampled process-tree peak RSS was 3,629,551,616
bytes under a 4 GiB guard and 12 GiB available-memory reserve; the user systemd
service is unavailable in this environment. An earlier integration test reached
its setup deadline while rebuilding changed upstream dependencies; that run was
stopped, the API built separately, and the final checks rerun with built artifacts.
The [validation record](../../tests/editor-parity/lsp-validation.json) includes
commands, exact source hashes and the native host's check list.

## Measured editor results

The [current measured report](../../tests/editor-parity/lsp-baseline.md) retains
18 isolated launches: two full functional runs and sixteen benchmark launches
(including four warmups). No launch or scenario was broken. Each worker setting
has three measured repetitions on the same VS Code 1.108.0, Dafny 4.11.0 and
Lean 4.24.0 installation, with four constant-return functions and one Lean thread.
These small samples describe this workload, not stable tail latency or general
proof performance. Full parity remains unestablished.

With one local worker, median initial verification was 6.13 s; adding a fifth
function took 5.17 s; an unchanged-snapshot cache hit took 100 ms. Dafny's matching
initial and incremental medians were 1.14 s and 247 ms. The current changed-buffer
path therefore remains about 21 times slower on this shared fragment. The older
CLI baseline's incremental median was 6.55 s, but it is a separate historical
measurement, not a controlled paired regression experiment.

Raw LSP evidence shows the same native Lean PID and increasing document version
between changed snapshots. Warm compiler analysis took tens of milliseconds;
proof construction still consumed roughly a second per function and reran the
whole file. Persistent sessions remove repeated startup and enable language
services; they do not supply declaration-level proof reuse or parallelism.
Two-file local median latency decreased from 8.64 s with one worker to 6.63 s
with two. That result concerns concurrent files, not within-file scaling.
Exact-cache latency and changed-source verification must remain separate.

The 88-feature audit now contains 23 partial, 34 missing and 31 unexamined
capabilities, with no unsupported complete claims. The real call-site scenario
checks local completion, definition, references, signature help and rename;
cross-language equivalence and the remaining inventory gaps stay explicit.

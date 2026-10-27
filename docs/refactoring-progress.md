# Architectural refactoring progress

## Current state

The two selected representation changes are implemented and verified. The
upstream pull was merged in `dc044e71`, preserving its enum/UDVT getter support.

| Change | Commit | Structural guarantee |
|---|---|---|
| Getter plans | `2669fa75` | Each input keeps its binding, type, source key and ABI type together; each result keeps its binding/type/expression together. A completed plan requires a first result. |
| Compiler provenance | `82f67125` | Historical versus analysed compilation is one mode; pipeline, settings, historical-fixture flag and effective coder are derived observations. |
| Final verification record | `ffa05eb2` | Library, TestSuite and frozen sort checks passed after restoring the normal build configuration. |

## Decisions and limits

Getter traversal uses `GetterPath`; completion produces `GetterPlan` with
`first` and `rest`. `params`, `sourceParams`, `abiParams` and `rets` are
projections, and `returnText` renders scalar or tuple returns without `head!`.
The source refuses a getter with no returned members, including a struct whose
only members are omitted arrays/mappings. Bounds guards, generated-name
freshness, named mapping arguments and source ABI identities are preserved.

`Compilation.historical` carries no recorded pipeline/settings;
`Compilation.analysed pipeline settings` carries the selected analysis input.
Historical v1 has an unknown effective coder. Analysed legacy compilation uses
the requested coder; via-IR uses v2 even if v1 was requested. Settings text is
still validated by `Source.read`: manually constructing a provenance record
is not a compiler-validation certificate.

No interpreter, taclet or proof-rule changes, dependencies, axioms or heartbeat
increases were needed. The two code areas received read-only finder and skeptic
reviews without remaining confirmed defects. Relevant Git history did not show
that these representations were introduced for checking speed; changing frontend
modules still invalidates their consumers.

## Validation

Recorded on 2026-10-27; job counts describe that verification snapshot.
The full-build snapshot is recorded in `ffa05eb2`. The subsequent documentation
refresh regenerated advisory feature metadata and checked that file alone;
it did not rerun the full library or TestSuite build.

| Check | Result |
|---|---|
| Changed Lean files | Per-file error diagnostics passed. |
| Direct getter-plan regression | Mapping metadata, scalar/tuple order, omitted fields, mixed array/mapping traversal and omission-only refusal passed (`scripts/getter-plans.test.mjs`). |
| Provenance regression | Historical v1/v2, analysed legacy/via-IR, settings preservation and malformed/downgraded metadata refusals passed (`scripts/source-provenance.test.mjs`). |
| Existing getter regressions | Success/false-assertion and reference-return refusal tests passed. |
| `./run-lean.sh` | Exit 0: 684 library jobs, 259 TestSuite jobs and the frozen sort check. Includes public-getter proofs and source-admission report quotation checks. |
| Frozen sort check | 377 taclets; all 131 read-bearing annotations match. |
| Layer check | 152 core modules; none reaches the elaborator. |
| Frozen TestSuite static audit | 564 selected functions: 552 derived, 11 refuted, one excluded, no pending. The scoped table itself contains 563 obligations. |

Use `tests/migration/solkey/keyext.solidity.examples` for the static TestSuite
audit and its `solidityProgramRules.key` for `SOLKEY_RULES`; the sibling checkout
has drifted from this fixture. These passing checks are not a theorem of
compiler/extractor equivalence. Source refusals and unsupported boundaries remain.

The local documentation audit after integrating cloud task 10 checked links,
heading anchors and Lean-file citations across all 72 tracked Markdown files
without findings. The feature
manifest, generated report and Lean catalog pass the generation-consistency
check; the catalog's per-file error diagnostics also pass. Five stale `missing`
assessments now describe bounded partial support with evidence; ordinary
recursive-source support remains missing. Feature scopes and admission policy
were not changed.
Read-only finder and skeptic reviews confirmed those bounded assessments and
corrected operator wording to distinguish symbols from unary/binary signatures.

At documentation-refresh snapshot `b5e6438d`, the whole-repository prose
checker reported seven missing references:
six in an archived validation JSON record and one upstream Mathlib citation in
a Lean source comment. These are outside the current Markdown documents and
were not rewritten to alter historical evidence.

## Resource bounds and resuming work

Acquire `/tmp/solidity-lean-feature-groups-20261025/writer.lock` before writes or
Lean checks, then reread Git status. Preserve unrelated work. Keep heavy checks
sequential and use a hard systemd scope (`MemoryMax=12G`, `MemorySwapMax=0`) plus
an available-memory guard with a 12 GiB reserve. Do not terminate other sessions'
workers. Keep at most four LSP files open.

Use `LEAN_NUM_THREADS=1` and explicit `-j1` for large fresh proof checks; the
environment variable alone started an additional Lean thread in the measured
probe. A session-specific alternate TOML can add `-j1` to library `weakLeanArgs`
without changing the tracked lakefile. Remove the temporary file after checking.
Do not confuse virtual address reservations for thread stacks with resident RAM.
The existing OpenLoops proof passed under the 12 GiB cap at 9.32 GiB aggregate
RSS; this does not establish that a clean rebuild fits 10 GiB.

Keep private artifact caches on disk under `.lake/refactor-cache`, not on the
RAM-backed `/tmp` filesystem. A private cache repaired reported fetches whose
object files were absent. Resource guards stopped earlier attempts when other
jobs filled RAM/swap; the completed proof artifacts were reused after headroom
returned. No resource stop was counted as a passing check.

Rebuild `Solidity.Frontend.Testing` before JavaScript regressions using
`build:false`. Sandbox Node child-process EPERM calls for the same bounded host
check, not changed verdicts. No verification for these two refactors is pending.

## Remaining candidate

The lower-priority candidate is a dedicated parameter/result signature for
finite-dispatch candidates in `Frontend/SolcJson/Contract.lean`. It would remove
`asExternal`'s impossible scalar case. Keep `Ty` parsing at the external boundary
and migrate `candidate`, `getterCandidate` and `inspectCall` together if pursued.
Preserve unknown/reference candidates, source/native distinctions, alias checks
and the restricted zero-argument internal memory-byte return.

This is future work, not an unfinished part of either completed increment.
Validate any such change with `scripts/finite-dispatch.test.mjs` and
`scripts/getter-dispatch.test.mjs` against rebuilt frontend artifacts; do not add
another representation unless its simplification justifies those migration risks.

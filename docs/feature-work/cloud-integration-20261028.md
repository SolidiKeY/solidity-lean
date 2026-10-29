# Feature-cloud integration, 2026-10-28

Eight finished workstreams are combined on `master`, from common base
`f4dee4a29c2e208b36db4a4161a4723c735cd775`. Each was retrieved as a Git bundle,
checked against its reported clean committed head and SHA-256, and imported
with its complete history. In particular, the final baseline export alone
would have omitted earlier baseline commits.

| Workstream | Collected head | Integrated scope |
|---|---|---|
| Source units | `178d0d4b` | Compilation-unit provenance, imports/remappings, scoped names/errors, and the validated callback proof replay repair. |
| Aggregate expressions | `a958a747` | Fresh deep copies of fixed primitive rows in calldata slices, inline projections, width and evaluation-order controls. |
| Panic payloads | `968c7f35` | Checked unsigned self-frame power failure data and ordering controls, with preserved historical failed attempts. |
| Contract world | `dcbf1d40` | Creation-catch operations and execution/reachability certificates for explicit factory/library wrappers. |
| Transient composition | `d6bed189` | Typed outer transaction composition, reset/rollback laws, and closed transient factory targets. |
| Quantified diamonds | `60ebe532` | Scalar quantified loop invariant preservation under variant snapshots, rule correspondence, soundness and source examples. |
| Generated differential tests | `e4681d99` | Two-root uint256 cases in ten families, with the recorded 640 real EVM comparisons kept separate from kernel proofs. |
| Baseline and attribution | `0211be73` | Full historical corpus, attribution, bounded cache/native diagnostics, and the value-entry supplement. |

The entrypoints VM remains active on its separate proof-performance repair.
Its original 300-second full aggregate getter gate has not passed; its branch
is excluded from this integration. The two-hour monitor continues that task.
The SolKey re-pin was cancelled and is excluded. The integration pin remains
`473da8944ca7329e6b76819863591407db26e7ec`.

## Conflict resolution and review

Root import conflicts retain every module from both branches. Documentation
append conflicts retain both scoped handoffs, and the module map retains both
the world certificates and expanded transient composition entry. The source-unit
and slice body-reader changes, and the slice and power evaluation-order changes,
merged together. Generated feature files were checked against the combined
manifest rather than selecting one branch's generated output.

Independent read-only finder and skeptic reviews inspected all eight merged
areas without Lean or server calls. Confirmed findings and fixes:

- The reusable baseline provenance checks now require the current compilation-unit
  adapter hash and include that adapter in the exact-base Git guard. Missing,
  stale and changed adapter controls are tested.
- Historical attribution and reader-only matrices now replay against small,
  hash-checked capsules of their original source/document inputs. Existing
  observations, reports and hashes remain unchanged; they are not fresh evidence
  about this merged model.
- Native cache tests read their authenticated committed evidence archive, rather
  than requiring ignored cloud work files. Archived log paths are checked against
  their recorded cloud root, independently of the verifier's checkout path.
  Reproduction compares every original observation; the repaired executing
  generator records its current source hash separately from the historical one.
- `LoopInvariantWk` is registered as a core proof module in the layer checker.
- The documented generated-test command explicitly sets its pinned compiler path.

The callback theorem's statement, expected verdicts, feature exclusions and proof
budgets remain unchanged. The generalized loop rule retains its quantified
invariant and has its matching soundness proof. Features remain partial: the quantified lane proves two source
obligations per pipeline and leaves six pending, world wrappers do not admit
general source-world execution, and the baseline's 9,660-fixture counts describe
the original snapshot rather than a new full corpus run after integration.

## Combined verification

The combined Lean gate passed: **698 default jobs**, **262 TestSuite jobs**, and
the frozen sort comparison (**377 taclets / 131 read-bearing / 131 covered**).
The generated executable passed its 60-job build. Final per-file checking and
rehashing confirmed the normalized loop fixture and all current default/suite
artifacts. The affected frontend/compiler/EVM replay also passed:

- 49 baseline Python integrity/provenance tests.
- 46 frontend Node tests, with no failure or skipped case; this includes the
  transient tests that initially refused the still-stale Testing dependency.
- 21 compiler/EVM reference tests and 640/640 generated comparisons, with zero
  mismatch or blocked variant on the committed integration.
- 32 slice, 82 panic-payload and 22 transient-world EVM observations, plus the
  slice admission check. These observations remain separate from kernel proofs.

The [combined validation record](../../tests/upstream/cloud-integration-20261028/validation.json)
contains exact collected heads, commands, source/settings fingerprints, resource
counters, original/current generator identities, reviews and log hashes. Logs and
the generated report are losslessly gzip-compressed beside it; the record includes
both compressed and uncompressed hashes. Earlier stale-dependency and launcher
failures remain separately identified and are not counted as passing checks.

The build uses Lean 4.24.0, `LEAN_NUM_THREADS=1`, explicit
`-j1` compiler settings, a 12 GiB/no-swap systemd scope and a 12 GiB available-host
reserve. The temporary Lake file changes worker settings only. An initial LSP
request started automatic dependency setup outside this scope; that request's
process tree was stopped and is not counted as a passing gate. The passing
combined run recorded 11.69 GiB sampled peak aggregate RSS; the cgroup high-water mark
reached its 12 GiB cap with reclaim events, zero OOM/kills and zero swap.
The frontend/reference replay recorded 2.15 GiB sampled aggregate RSS and a
3.72 GiB cgroup high-water mark. An unnecessary temporary executable stack flag
was removed; all three CLI roots were checked directly at their original default
stack before final cache confirmation. Library proof/stack settings were unchanged.

Local logs are under `.lake/cloud-integration-20261028/`. The standard orphan
scanner also sees 33 preexisting ignored scratch modules; an exact allowlist
of those files leaves no other orphan. The documentation scanner reports 46
missing references: the prior external/historical citations plus verbatim copies
of those diagnostics in newly collected evidence. New integration prose adds
no missing Lean-file reference. Raw diagnostic logs retain their original
whitespace and hashes.

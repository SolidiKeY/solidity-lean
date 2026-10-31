# V17 whole-pipeline validation preparation

Task: `solidity-v12-v17-20261031/v17-validation-release`.
Assigned base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Repository: `/workspace/solidity-lean`; branch:
`codex/solidity-v12-v17-20261031/v17-validation-release`.
The starting checkout was clean on `work`, exactly at the base. The assigned
branch was created there; no existing worker branch was fetched or integrated.

**Lane status: blocked, preparation only.** No new Lean declaration, theorem,
axiom, representation, semantics, profile, assertion, verdict or proof budget
is changed. Every output deliberately retains `releaseClosed: false`.
Successful report accounting means consistency of supplied claims and retained
bytes. It cannot authenticate a producer, inspect a theorem's meaning, or prove
that a named premise was actually discharged in the kernel.

## Queue and ownership

| Work item | State and precise remaining obligation |
|---|---|
| G52 | Partial preparation: a same-revision retained-report consumer checks the existing generated runner's four pipeline/optimizer settings, ten grammar families, deployment, ABI return/revert bytes, initial/final state, raw storage and rollback observations. It invokes the published generator and comparator; it never replaces either. Actual fresh same-revision execution is pending. Callbacks and wider combinations are unsupported by that published grammar and remain open, not excluded. |
| G53 | Partial preparation: snapshot/verify binds exact revision, corpus verdict table, SolKey pin, TestSuite report, runner inputs and actual Lean/Lake binary hashes/versions. Bounded read-only strict/parity probes retain discrepancies. Actual integrated re-pin/migration/strict correspondence and suite closure remain with their owners. No pin or Derived file is edited. |
| G54.01 | Pending: clean default/compiler/frontend proof targets with serial workers, actual resource measurements, and same-revision clean/cache provenance. The inherited cache is unverified, not a clean build. |
| G54.02 | Pending: same-revision full suite/corpus kernel closure, unchanged process budgets including the configured 300s automation bound. No whole-suite build has been claimed. |
| G54.03 | Pending until .01/.02 pass: scoped headline axiom checks, trust, joint public kernel imports, executable artifacts, clean/cache equivalence. Textual inventory and a trust probe are preparation only. No duplicate build/cache export. |
| G55 | Blocked: final independent evidence audit waits for actual integrated V11→V12→V13→V14→V15→V16 proofs and all G/S child gates. G03 currently supplies 118 work packages, 175 feature rows, 41 combinations, 98 symbol combinations and 25 decisions: 457 accounting requirements. None is silently marked discharged. |
| Backfill A | Implemented preparation: revision-bound nonempty log/checksum aggregation; corrupt/missing logs, false pass/exit labels, wrong revisions, duplicate records, mislabeled known commands and path escapes are rejected. Missing/failed gates remain incomplete. Full runtime/clean/cache provenance and combined release audit remain pending. |
| Backfill B | Implemented preparation: ledger-bound all-row inventory; explicit theorem kind, module, axiom list, observations and acyclic named premise accounting; lexical core public-import inventory reuses the existing repository script. Missing rows, wrong revisions, contradictory/parameterized-only claims, unmatched observations, cycles and unapproved axioms fail. Kernel extraction of exact theorem types/axioms and Bridge/joint import closure remain pending. |

Reserved prerequisites are read only: Source/admission (S00–S05), lowering
(G16–G23 and V07–V11), G24 foundation, storage/layout/hash, scalar,
environment, failure, creation, assembler/control, precompiles, stipend,
fixed point, existing EVM/Bridge workers, copy recovery, generated-differential
and SolKey re-pin/TestSuite repairs. Their component documents distinguish
local component theorems from missing parent composition. This lane makes no
replacement theorem, new final premise, or inferred preservation claim.
No scope decision is requested; integration is the coordinator's prerequisite.

Proposed ledger reconciliation: retain G52, G53, G54.01/.02/.03 and G55 open;
attach these preparation controls without changing any feature verdict.
The full 457-row pending accounting inventory is exported in the handoff.
Specific exercised observation anchors include `returnStatement`,
`revertBuiltin`, `requireBuiltin`, `assertBuiltin`, `tryStatement`,
`constructors`, `creationCode`, `runtimeCode`; tests add no coverage claim.

## Runtime and bounds

Read AGENTS, module map, documentation index, intrinsic Gate G0, parallelism,
contributing, local lean-verify, matching typing/derivation/soundness conventions,
G01 contracts, G03 ledger, G04 restrictions, G06 pin, G02 measurements, actual
scope/decision tables, and the reserved component documents before consumers.
The repository writer lock is
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`.

Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Lake: 5.0.0-src+797c613 (Lean 4.24.0).
VM cgroup: 17,179,869,184 bytes; host swap: 0. Initial disk available: 30 GiB.
No Lean MCP is exposed by the attached tool inventory; no Lean file is edited.
No Lean server or concurrent heavy check is started.

The system/user systemd scope attempts fail (PID 1 is not systemd, user bus
absent). The supported Docker fallback was verified with Debian bookworm-slim
image digest `sha256:99c0b25c46d0214d5a2091092e7908907dcaecd6a962cde0ac700acee222b6f3`.
The actual child reports `memory.max=12884901888`, `memory.swap.max=0`.
One CPU, `LEAN_NUM_THREADS=1`, a temporary alternate TOML adding Lean `-j1`
without changing tracked lakefile settings, network disabled, writer lock held.
The temporary config was removed after the run. No proof budget increased.

Command: `lake -f roadmap-v17-runtime.lakefile.toml build Solidity.KeySort`.
Outcome: exit 0, `Build completed successfully (2 jobs).`
Cgroup peak: 25,579,520 bytes. This is a warm runtime/toolchain check only.
`RUNTIME_GATE_PASS` applies to that check; it says nothing about G54 closure.
Raw output: `/workspace/scratch/v17-evidence/keysort.log`.

## Reproduction and evidence contracts

From a clean committed checkout with the actual Lean/Lake binaries on PATH:

```sh
python3 scripts/roadmap-v17-evidence.py snapshot
python3 scripts/roadmap-v17-evidence.py verify-snapshot --report /absolute/snapshot.json
python3 scripts/roadmap-v17-evidence.py inventory
python3 scripts/roadmap-v17-evidence.py aggregate --report /absolute/gates.json --evidence-root /absolute/logs
python3 scripts/roadmap-v17-evidence.py closure --report /absolute/closure-claims.json
python3 scripts/roadmap-v17-evidence.py differential --report /absolute/generated-report.json
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/roadmap-v17 -v
```

JSON duplicate keys are rejected. Gate records require schema/revision, stable
ID, argv command, exact exit/status, relative log path and SHA256. Closure
records require canonical ledger hash, exact lexical core import list, every
ledger-derived row, theorem names/modules/kinds/axioms/premises/observations.
A missing record never becomes a pass. Theorems are producer claims until actual
kernel gates and independent evidence audits verify them. No automatic path
from `accountingComplete` to release closure exists.

The differential consumer requires the exact current executable/input hashes,
regenerates the existing enumeration (60s published generator bound), and calls
the existing `compare` export. The thin adapter separately checks retained
observation schemas and compiler input/settings hashes; these are serialization
checks, not duplicate source/EVM semantics. Use a capped runtime to consume a
fresh report. Node dependencies come from the existing lockfile, installed
with `npm ci --ignore-scripts --no-audit --no-fund`; no dependency enters Lean.
The historical 640-agreement fixture is used only as an inhabited parser/
comparator test. Its revision is `016184b5564044d22d1d387dfb88d1209d8ea190`,
so it is rejected as present-revision evidence. The current `solcases` binary
is absent and the installed 0.8.34 compiler is not the pinned 0.8.38 witness.
Fresh differential execution is therefore pending; no wrong compiler is run.

`roadmap-v17-probe.py` acquires the repository writer lock internally and runs only existing read-only lightweight checks plus the
new lexical import inventory, serially, with a 60s host bound. It requires a
clean commit and a new external output directory, records external SolKey and
checker hashes, raw exits, elapsed time and sampled aggregate process-group RSS.
A nonzero probe remains a failure even when inherited. It does not invoke Lean,
repair a pin, or assert a full corpus/suite proof. Raw checker failures and an
explicitly separate exact-base docs no-new comparison are retained externally.

## Independent preparation reviews

Separate read-only finder and skeptic agents reviewed the actual files without
Lean/server/build/test calls. Confirmed findings and fixes:

- Observation presence alone admitted malformed or contradictory agreement:
  now check object shapes and reuse the published comparator; mutation controls
  corrupt ABI bytes, rollback words, initial observations, settings and nulls.
- Missing operation families and enumeration identity: require all ten families,
  every settings pair, exact generated enumeration and source/input hashes.
- Unclosed theorem inventory ignored by completeness: any unclosed theorem
  prevents complete accounting; regression includes an extra conditional entry.
- Missing import accounting: use the repository's exported import graph and
  check exact public lexical inventory plus every claimed theorem's module.
- Declared toolchain alone was insufficient: bind actual binary bytes/versions.
- A probe reporting a changed checkout could still be aggregated: explicitly reject it, hold the writer lock through all probes, and double-check snapshot cleanliness.
- Retained host metrics and exception consistency now have explicit checks.
- Known gate labels accepted arbitrary argv: check canonical command mappings;
  unregistered gate labels remain producer claims, documented as such.

The checkpoint includes no headline kernel theorem; theorem names/premises added:
none. Exact types and scoped axiom output for all final integrated headline
proofs remain an open G55 obligation. Synthetic acyclic premise controls and
historical external observations are never counted as those proofs.

## Preparation checkpoint handoff

The separate finder and skeptic re-reviewed the actual final preparation diff,
including hypotheses/non-vacuity, ownership and handoff; neither found a
remaining blocker to this preparation checkpoint. This is not G55's final
integrated review. All confirmed findings above were fixed.

Validation: 36 Python unit/control tests pass (including actual Node comparator
mutations). `git diff --cached --check` passes. The full docs path checker exits
1 with 46 findings, retained in `docs-head-initial.log`; an exact-base
source-only worktree reproduces the identical raw output in `docs-base.log`.
The separate byte-for-byte no-new-findings comparison passes. No Lean imports
were changed; per-file diagnostics are inapplicable. Heavy full, clean, suite,
corpus and Bridge checks remain pending, not waived by these controls.

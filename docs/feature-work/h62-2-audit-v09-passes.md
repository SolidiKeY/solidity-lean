# H62 item 2: V09 empty-statement audit

Status: blocked, full assignment unfinished. This checkpoint supplies a source
census and reproduction tooling; it proves no simultaneous premise witness.

## Frozen scope and setup

Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-h62-2-20261106/audit-v09-passes`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The initial clean `work` branch was preserved. The exact base and remote master
were fetched; the base is an ancestor of fetched master
`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`. The assigned branch was created
at the exact base. No producer interface, module map, root, pin, toolchain file
or original proof was edited. No push, merge, PR or pre-gate was attempted.
The final committed head is recorded in the off-git `handoff.json`.

The supplied coordinator inputs at `/workspace/h62-coordinator-inputs` all
match their `sha256.json`. No get_goal or Lean MCP tool was exposed; optional
get_goal inspection absence is not a blocker under the coordinator instruction.
The existing goal was not replaced or reset.

## Checkpoints and remaining obligations

| Checkpoint | State | Evidence / remaining work |
|---|---|---|
| 1: exact inventory and owner, global/per-input distinction | partial | Frozen source census: 179 files, 1,259 theorem/lemma declarations, each once. Elaborated signatures, implicit variables and complete global/per-input premise classification remain pending. |
| 2: simultaneous witness for every statement | blocked | Zero verified. All 1,259 source rows explicitly uncovered until semantic classification; no independently inhabited assumptions are counted as a simultaneous witness. |
| 3: supported-program totality, negative controls and observation boundary | blocked | No new totality/success or reject-all/always-revert exclusion theorem checked. Public failure, gas and fork boundaries remain pending. |
| 4: Lean witness verification and statement-fidelity census | blocked | Only source-span fidelity checked. No elaborated fidelity, axiom audit or full final validation claimed. |

The map expands to 43 named files and 136 additional controls/pin wildcard
files. There are 1,069 public/protected declarations and 190 private declarations.
Private and hypothesis-free candidates are retained conservatively; classification
has not yet established the interface-theorem denominator. Each row records
its fully qualified source name, exact source signature span, source/signature
SHA256, location, visibility and area owner. Section variables and options are
recoverable from the frozen file prefix; these are not elaborated signatures.
The owner is the assigned V09 area owner, not a fresh per-file writer claim.
The source census cannot certify feasibility or detect all semantic vacuity.
No theorem has been adjudicated weakened or vacuous by this checkpoint.

In-scope additions:

- `scripts/h62/item2/audit-v09-passes/census.py`: deterministic frozen census;
  bulk JSON remains off git and refuses changed frozen files.
- `scripts/h62/item2/audit-v09-passes/check_closure.py`: fallback serial
  dependency baseline with frozen source verification and isolated cache.
- `tests/h62/item2/audit-v09-passes/test_census.py`: meaningful scanner
  acceptance including the nine review-discovered top-level-let regressions.

There are zero new Lean declarations/helpers, zero new axioms, zero new sorry,
zero trust shortcuts and no proof-budget changes. No registration fragment is
needed yet because no Lean module has been added.

## Dependency ticket B-MIGRATION-SYNTAX-RAW

Owner/relay destination: coordinator's Syntax migration producer; V09 area
producer is an affected consumer. This ticket is saved for coordinator retrieval;
no relay.sh is available in this checkout and no delivery acknowledgement is
claimed. No out-of-scope repair was attempted.

Official pinned archive: `lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual executable versions:

- Lean 4.35.0, release, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Lake 5.0.0-src+eb6cafb (Lean 4.35.0).

Unchanged `Solidity/Syntax/Raw.lean`, source SHA256
`7c137f7e8e4c70f4868dc41a437687ab42e2d63e887cdde3ba3ccd1ea764b76f`,
fails the first audit import's dependency closure with five errors:

| Line | Decisive error |
|---|---|
| 597 | `f.drop 1` is String.Slice, but HashKind.ofName? expects String |
| 650 | String.Slice.toList is unavailable |
| 665 | dropped/sliced rest is passed to splitTopCommas expecting String |
| 682 | partially applied c.endsWith has the wrong predicate type |
| 684 | String.dropRight is unavailable |

ESCALATE: action Solidity.Syntax.Raw v4.35 migration dependency; unchanged frozen source fails at lines 597/650/665/682/684 before Solidity.Backend.Passes.value_success_tail can be imported; options: (1) Syntax migration owner supplies an approved compatibility overlay preserving frozen statements for isolated validation, or (2) coordinator supplies an explicitly authorized migrated base and a statement-equivalence reconciliation plan while retaining this frozen audit census. No premise/exclusion change is requested.

Resume requires an owner-approved route to check the unchanged interfaces on
the common pinned toolchain. Merely reverting this worker to v4.24 would violate
the latest coordinator instruction. This lane cannot edit Syntax/Raw or the
tracked toolchain. All four original checkpoints remain obligations after repair.

## Commands and gates

Run from the repository. Paths below are absolute off-git VM evidence paths.
The corrected baseline report records complete argv, source hashes, outcomes
and per-file wall times. Its cache is separate from the old v4.24 cache.

| Command | Outcome | Evidence |
|---|---|---|
| `git fetch --no-tags origin master c6f550e281a7e5affa9a99bc2cdaed556dec00e4` and ancestry check | pass | setup.json |
| coordinator input SHA256 checks and official archive SHA256 | pass | setup.json, toolchain archive, coordinator-inputs/ |
| `python3 tests/h62/item2/audit-v09-passes/test_census.py` | pass: 5 tests | census-acceptance.log |
| `python3 scripts/h62/item2/audit-v09-passes/census.py --output /workspace/h62-audit-v09-passes-evidence/census` | pass: 179 files/1,259 rows, zero verified witnesses | census/census.json, census/census.sha256 |
| repeat census into census-repeat and byte comparison | recorded in acceptance-gates.json | deterministic-repeat log |
| `PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-v09-passes/check_closure.py --toolchain /workspace/h62-audit-v09-passes-evidence/toolchain/lean-4.35.0-linux --output /workspace/h62-audit-v09-passes-evidence/baseline-confirmed Solidity.Backend.Passes.ValueCertificate` | fail: dependency, exit 1 | baseline-confirmed/report.json and Solidity.Syntax.Raw.log |
| `lean -j1 --tstack=131072 -o <isolated output> Solidity/KeySort.lean` | pass: exit 0, 1.606 seconds in corrected run | baseline-confirmed/report.json |
| `bash scripts/check-doc-paths.sh` | pass: all references resolve; 115 repository-wide ambiguity warnings | doc-paths.log |
| `git diff --cached --check` | pass | diff-check.log |
| full affected builds, witnesses, success controls, axiom checks, `./run-lean.sh` | pending, blocked by dependency migration | B-MIGRATION-SYNTAX-RAW |

The corrected run also passes AST (8.233 seconds) and SpecSyntax (2.414 seconds);
Raw fails in 4.415 seconds. No resource stop was counted as a proof failure or
pass. The runner holds writer.lock, rereads status, verifies sources under the
lock, runs one child with LEAN_NUM_THREADS=1 and explicit -j1, uses a 12GiB
address-space cap and a 4GiB effective available-memory guard that includes
finite cgroup ancestor limits/current usage. Swap is absent. Initial effective
headroom was about 12.218GiB. No systemd-run was used.

No Lean refactor occurred and no passing audit baseline exists, so there is no
valid before/after proof-performance delta. The earlier baseline report is
retained as superseded review history; use baseline-confirmed for the corrected
resource/provenance guard. No RUNTIME_GATE_PASS or final acceptance is claimed.
Python acceptance and source hashes are external checks, not Lean kernel proofs.

## Independent read-only reviews

Finder and skeptic used no Lean server, ran no Lean and made no edits. Both
found nine truncated signatures caused by top-level let assignments; the scanner
was fixed and all nine full conclusions now reach their actual proof delimiters.
Both confirmed the 179-file expansion and 1,259-declaration census. Finder
identified pre-lock source verification; skeptic additionally identified a host-only
memory guard. Both were fixed. Final independent rechecks report no unresolved
finding in the narrow census/baseline artifact review. The Raw failure's source
hash and migration-error provenance were independently confirmed. These reviews
do not stand in for the required later proof milestones. See reviews.json.

## Handoff and export

Evidence directory: `/workspace/h62-audit-v09-passes-evidence`.
Original patch: `/workspace/h62-audit-v09-passes-evidence/original.patch`.
Machine-readable handoff: `/workspace/h62-audit-v09-passes-evidence/handoff.json`.
Human handoff: `/workspace/h62-audit-v09-passes-evidence/handoff.md`.
Checksum manifest: `/workspace/h62-audit-v09-passes-evidence/SHA256SUMS`.
The checksum manifest covers deliverables, logs, census outputs and source
archive; the toolchain archive is pinned separately in the same manifest.
The deterministic census generator is committed; its 1.4MB bulk output is not.
The coordinator can retrieve this committed partial checkpoint from this VM.
No fresh goal or replacement thread was launched. Resume the existing goal and
branch after the owner dependency is resolved; do not mark the queue complete.

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
| 1: exact inventory and owner, global/per-input distinction | partial | Frozen source census: 179 files, 1,259 theorem/lemma declarations, each once. Source premise roles are now recorded for all rows; elaborated signatures, actual implicit inclusion and semantic global/per-input classification remain pending. |
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

Owner/relay destination: `solidity-h62-6-20261106/migrate-syntax`; V09 area
producer is an affected consumer. Coordinator H70 reports host-journal relay delivery acceptance.
Delivery establishes neither owner agreement nor validation. relay.sh is host-only and is not a VM installation task.
No out-of-scope repair was attempted. Wait for the owner before elaborated
witnesses, supported-success controls and affected gates.

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

## H70 continuation: source premises and owners

The coordinator authorized continued source classification on the same frozen
1,259-row inventory while the Syntax migration owner repairs the dependency.
No migration branch was merged or fetched into this lane, and no new Lean check
was attempted during this source-only continuation.

`premises.py` creates one additive row for every existing census row, joined by
path, fully qualified name and both frozen hashes. It extracts all 1,327
source-written telescope groups, plus 427 available section-variable groups
counted across rows. Each group records its exact source text, type annotation,
source-role candidate and absolute frozen-file span. Names/implicit inclusion
still require Lean. All 1,259 witness statuses remain uncovered and every
binder's inhabitation remains unproved.

| Source classification | Count / meaning |
|---|---|
| Global program certificates | 115 source telescope groups; selected supported expressions/programs, not certified feasible runs |
| Global operator certificates, fragment laws, return-form laws | 2 / 3 / 2 groups; none shown inhabited here |
| Per-input admission, representation, reached-transport | 16 / 31 / 15 groups |
| Per-input representation/allocation and stack-capacity packages | 10 / 3 groups; a structure in Type may still encode per-input capacity |
| Quantified conditional laws | 3 groups; allocation/execution occurrences retained separately |
| Execution/evaluation/verdict constraints | 68 groups; source-versus-target layer left unresolved |
| Other logical/resource constraints | 91 groups; semantic scope unresolved |
| Macro return types | 27 rows contain type_of%; expansion can reveal further inputs |
| No source-written telescope groups | 820 rows; this does not mean hypothesis-free after elaboration |

Seventy rows have source global-certificate/law roles; 124 have a per-input role
including data such as states/maps; 52 have both. These are source triage counts,
not a denominator of inhabited public interfaces. The remaining source-role
categories describe data, scalar parameters, range/support and observation
constraints. All counts and the 27 definition-family references are in
`source-premises/premises.json`. Family references do not resolve every
unqualified identifier to its elaborated declaration.

Concrete distinctions retained:

- value_success_tail requires its selected CompiledVal, the same StateRepr
  and successful source evaluation together, with shared parameters.
- compilation_mapped_reflect_success requires selected Compilation artifacts,
  actual Input, a reached link and actual target success together. A certificate
  or conditional link alone does not supply that successful execution.
- RuntimeReturnCapture.capture keeps selected producer, global alias law,
  physical admission, actual call success, reached evaluation and room together.
- BinaryInvocation and ClosedInvocation package stackBound for the selected
  tail. They are per-input capacity certificates even though defined as structures.

The source classifier preserves the whole return type. In particular it flags
27 type_of% cases and the leading-forall result of ShortCircuitBoundary.execution;
it does not mistake result quantification or conditional laws for absent premises.
No source classification is accepted as a simultaneous witness or as evidence
that a premise is inhabited.

New commands (source-only, no Lean):

- `python3 scripts/h62/item2/audit-v09-passes/premises.py --output /workspace/h62-audit-v09-passes-evidence/source-premises`
- `PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item2/audit-v09-passes/test_premises.py`

The seven new acceptance tests verify nested/implicit binders, scoped-variable
lifetimes, assignment-token decoys, quantified budgets, source/target ambiguity,
all frozen telescopes and the generated 1,259-row hash join with absolute spans
and unproved statuses. Bulk classification remains off git. Original census
bytes and frozen signatures remain unchanged.

Independent finder/skeptic reviews found and corrected three issues: target
runs mislabeled as source; ambiguous span-coordinate bases; and :=/=> mistaken
for logical equality. Quantified allocation laws now keep their law role and
occurrence tags. Final outcomes are saved in reviews-h70.json. Required Lean
witness, totality, negative-control, fidelity and full gates remain pending on
B-MIGRATION-SYNTAX-RAW; there is no new runtime or proof-performance pass.

## H70 requester disposition: residual source constraints

The remaining 91 generic logical/resource groups now have a lexical refinement:
22 numeric ranges, 19 frame/arena bounds, 11 static fragment/operator conditions,
9 nonzero conditions, 6 stack-capacity bounds, 6 fragment identities,
5 short-circuit selections, 4 compiler-acceptance equations, 4 environment reads,
2 code decompositions, and one each of initial-stack observation, target-memory
observation and word range. These 13 forms partition all 91 groups; they do not
prove consistency, feasibility or implicit inclusion.

All 27 macro return rows now retain a lexical callee token, its exact token span
and the separate macro-start offset in the preserved return type. Namespace/type
resolution and callee-owner attribution remain pending. In particular a
compiler-acceptance equation is a premise to witness, not evidence that the
selected compiler succeeded on a supported program.

Evidence: source-premises-disposition/premises.json. The original census is
unchanged. All 14 Python acceptance tests pass. Independent finder and skeptic
reviews confirmed the partition and macro token census. Finder identified an
ambiguous macro/token offset; separately named macro/token coordinates and a
substring regression correct it. No Lean was run during this disposition.
All four original checkpoints remain unfinished. Wait for
solidity-h62-6-20261106/migrate-syntax on Solidity/Syntax/Raw.lean lines
597/650/665/682/684 before value_success_tail proof imports. Host relay journals
establish delivery acceptance only; owner agreement and validation are unproved.

## Held partial Raw prerequisite and source return frontiers

Coordinator reports migration-owner head
72441d298484976c48dd14b4e095c9149b852025 and partial Raw source commit
074e62c1840dd2d7ab19c95ca5d437ebfe57dbb8, reported source SHA256
a463aa0f978da5d5bae6ba5cffdfa95861a495a8d69942502b706b7b157ec506.
Reported host patch SHA256 is
34fc66ea93a8a2c956ebb51f225b03593109239c5b46631aaa28bfb24efb2a9a.
The host receipt path is not locally available. These are reported hashes,
not locally verified artifact hashes. No patch was applied or migration commit
merged. The frozen local Raw source remains unchanged.

Thirty reported axiom-growth entries require root review. The coordinator
explicitly grants no trust acceptance or lifting of holds. Keep
B-MIGRATION-SYNTAX-RAW open and record B-RAW-TRUST-REVIEW as an unresolved
root-review dependency; do not retry value_success_tail imports on this basis.
Receipt details are saved in owner-prerequisite-receipt.json off git.

Remaining source review now records outer return frontiers for every row:
102 existential results, 27 macro-expansion cases, one universal result,
four remaining let-prefixed results after macro classification, and 1,125 other results. Macro occurrence takes
precedence over outer syntax, including a let-prefixed macro result. Existential witnesses are
outputs, not new premises. A universal result requires binder-inclusion review;
it is not evidence of a global inhabited premise. Other results do not establish
absence of hypotheses. Macro expansion, let reduction, actual implicit inclusion
and simultaneous feasibility remain unverified. This adds no theorem or premise.
All four original checkpoints remain unfinished; no Lean run is authorized by
the partial receipt. Source-only acceptance and independent review evidence are
saved with the return-frontier checkpoint.

## Human H82 retirement: stopped handoff

Implementation is stopped, not complete. Handoff to
solidity-inline-assembly5-20261031/vy3-compilation takes effect only after the
final stopped/head acknowledgement. Original assignment, original goal context,
work/backfill queues, exact scope and all remaining work/waits are committed
under tests/h62/item2/audit-v09-passes/handoff/. No in-flight source-reading work
created uncommitted proof changes. No H71 push permission is available, so no
push was performed. No new proof implementation is authorized on this worker.

PAUSED was requested by the human. The exposed goal tool supports only complete
or blocked and cannot express PAUSED; prior calls also lacked trusted CCA goal
context. No substitute completion/reset/new goal is attempted. This precise
limitation is saved in retirement-state.json; the worker stops regardless.
The successor must retrieve the original scope and waits before integrating.

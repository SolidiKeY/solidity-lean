# H62 item 2: V09 empty-statement audit

H145 evidence location: lane receipts, transition records, checksum/resource
records and validation reports formerly stored below the audit test directory
are preserved in the private coordination repository, commit
`f347f97aa7aec79c74e006efaf0508cd077a569c`, under
`evidence/solidity-inline-assembly5-20261031/vy3-compilation/evidence-archive.tar.gz`.
Historical references below to those evidence JSON files refer to that archive.
The code branch retains the Lean modules, checker-read witness maps, portable
fixture/materialization inputs and acceptance code. Frozen registrations,
expected assertions and external materialization requirements are unchanged.
The archive preserves fresh records; it does not reconstruct the still-missing
historical VM evidence.

Status: partial; full assignment unfinished. The selected frozen census contains
179 files and1259 rows. Last recorded selected coverage is538 rows;721 remain
open. These historical counts do not replace missing evidence recovery or fresh
full kernel acceptance. Counts include checked reuse of original control proofs.
The19 earlier supplemental instances and4 unselected ClosedValues instances do not reduce this count.
Earlier subtraction counts are withdrawn; see Coverage membership correction.
Supplemental proof validity and resolved private identities are retained.

## External selected-heap fixture availability

[SelectedHeapBoundaryWitness.lean](../../tests/h62/item2/audit-v09-passes/selected-heap-artifacts.json)
is an H44 bulk artifact, deliberately absent
from a clean checkout. Historical references below name this external fixture,
not a published in-tree Lean module. Its intended materialization target is

```text
tests/h62/item2/audit-v09-passes/SelectedHeapBoundaryWitness.lean
```

The tracked [artifact manifest](../../tests/h62/item2/audit-v09-passes/selected-heap-artifacts.json)
records its exact bytes/hash and those of the companion ledger. The
[verification/materialization tool](../../scripts/h62/item2/audit-v09-passes/selected_heap_artifacts.py)
is in-tree. See [H44 selected-heap bulk split](#h44-selected-heap-bulk-split)
for staging, mandatory external acceptance and the unchanged Lean gate.
No missing file should be reconstructed from the compact source inventory.

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

## Scalar-passes successor adoption

The successor verified all five committed handoff-document SHA256 values from
final audit head `521196a3a78cd6cce22a7f14dd4364493b16cdbc` against the
coordinator receipt, then merged that stopped member head on its existing
branch. The recorded original assignment is a thread transcription; matching
the handoff hashes does not establish launcher rendered-prompt byte equality.
The portable evidence archive and prior runtime results have not been locally
verified by the successor.

The existing source acceptance suite was rerun after adoption: all 15 tests
passed. This verifies the frozen 179-file/1259-declaration source census and
its source-classification controls, not Lean elaboration, premise feasibility,
witness coverage, supported-success totality or timing acceptance. All four
checkpoints remain unfinished. Raw migration and reported axiom-growth review
holds remain in force; the failed runtime baseline was not rerun unchanged.
No original producer, frozen statement, proof budget or trust policy changed.

## Frozen source axiom-report accounting

`axiom_reports.py` inventories report commands over the same frozen
179-file/1259-declaration census. It records exact source spans and recognizes
only directly enclosing single-command `#guard_msgs` forms. At the original
pin it finds 458 `#print axioms` commands: 434 directly guarded and 24 bare or
using unrecognized guard syntax. These command counts are not theorem
coverage: command targets remain unresolved and actual axiom sets are not
inferred. In particular, bare output is not an enforced axiom pin.

Five new source tests guard against fake commands in comments/strings, guards
covering more than one command, intervening commands, incorrect source spans,
and loss of the recognized options/comment form. The full source suite passed
20 tests. No Lean declaration, witness, axiom set, statement, budget or producer
changed. All original proof/totality/fidelity checkpoints remain open.

Current prerequisite routing is `solidity-h62-6-20261106/migrate-root-gate`
for Raw compatibility and reported migration axiom-growth review, and
`solidity-parallel-20261103/memory-copies` for Physical.ByteWorld realization.
No unaccepted overlay was merged and no known timing STOP was rerun.

## Outer return-input source accounting

The premise classifier now records recognized outer forall binder prefixes
and arrow domains with exact spans in the unchanged return type. Arrow domains
may be data rather than proof premises. Parenthesized outer forms can be
examined, but existential outputs, unreduced lets/macros, nested top-level
quantifiers and iff-precedence forms remain explicit barriers. The unprocessed
remainder stays visible; no-input output never proves absence of hypotheses.
Implicit inclusion, resolved identities and simultaneous witnesses remain
pending Lean and statement review.

At the frozen pin the declaration join still contains exactly 1259 rows; one
recognized prefix is exposed: `∀ tail,` in
`Solidity.Backend.Passes.ShortCircuitBoundary.execution`. It is a source
quantifier, not an inhabited premise or success witness. Seven new tests name
the hidden-return-input regression and check exact spans, data domains,
existential/let/macro barriers, nested quantifiers, iff precedence, parentheses,
ASCII notation and comment masking. All 27 source tests passed. No Lean code,
existing signature, axiom set or proof budget changed; all proof checkpoints
remain unfinished.

## Joint Boundary fixture

`tests/h62/item2/audit-v09-passes/BoundaryJointWitness.lean` constructs one
simultaneous premise tuple for the four public theorems in the frozen
`Backend/Passes/Boundary.lean`: exact, success, reflected success and revert
transport. The same checked compilation, populated input state/machine/base,
no-payment proof, successful source output and target result occur together.
The interface remains byte-identical to c6f550e281a7e5affa9a99bc2cdaed556dec00e4;
`boundary-witness-map.json` records its four frozen signatures and proof join.
The new concrete fixture is additive and was not present at that pin.

A general successful-run lemma excludes revert and fault, instantiated on this
supported input. This is four inhabited premise bundles, not an elaborated
1259-row census, general compiler totality, gas/fork adequacy or whole-audit
completion; 1255 declaration rows remain uncovered by this fixture. Guarded
Lean 4.24.0 checking passed with existing standard axiom dependencies. The editor
attempt was interrupted during dependency setup under the serial worker lock;
it is not a passing diagnostic. The explicit validated import-map kernel check
is retained separately. V4.35 migration and full acceptance remain open.

The same additive audit fixture now also publicly selects a non-paying reverting
program on that populated input. `Reverting.joint_failure` supplies actual G24
Input, source revert and target revert jointly; `transported_failure` instantiates
the unchanged `compilation_revert_iff`. A universal target-machine control refuses
forged successful observations. This is an additional failure instance of one of
the four already mapped declarations, not a fifth covered row. Coarse revert
transport does not establish revert payload, gas, fork, divergence or full audit
adequacy. The prior editor dependency-lock failure is not rerun unchanged; guarded
serial kernel checks use the retained validated import map.

The parameterized `GuardFailure` family adds checked false-require and
false-assert instances on the same populated input. Both have joint Input,
no-payment, actual source-failure alternatives and target revert. The panic
case proves the original `asserts = true` guard rather than erasing it. A
source-distinction control proves panic and revert differ despite equal coarse
target observations. These remain instances of the same already mapped
`compilation_revert_iff`, not additional covered declarations. Error bytes,
gas, fork, divergence and the other1255 declaration rows remain open.

## Saved-tail joint fixture

`StackJointWitness.lean` supplies the joint hypotheses of the three public
frozen Stack declarations on a concrete checked core store, universally in
the saved tail. Actual Input, no-payment and source success hold together;
target success preserves the exact arbitrary tail and full branch-specific Rep.
A general run/stack discrimination lemma rejects a forged machine returning
any unequal tail. `stack-witness-map.json` pins the unchanged Stack interface
and exact source signatures. Three private Stack helpers remain uncovered.

This adds three disjoint declaration instances to the four Boundary instances:
current combined coverage is seven of1259 source-census rows, with1252 remaining.
Earlier four/1255 counts above describe their earlier checkpoint. This does not
elaborate the full census or cover other compilation branches, resource/fork/gas,
native adequacy or whole-lane acceptance. The failed initial unqualified Instr
check is retained; the corrected Evm.Instr proof and standard-only axiom guards
are checked with the validated original4.24 import map.

## Reached core links and intentional resource refusal

`CoreBoundaryJointWitness.lean` supplies concrete premise instances for all five
public frozen CoreBoundary declarations. It projects an actual reached Rep and
selected map, builds the checked empty-suffix certificate with the same bound,
and applies the mapped link to the actual successful prefix to obtain suffix
Input. No core relation is upgraded into heap ownership.

The fifth instance, `core_input_refused`, is intentional negative evidence:
its certificate and over-limit premise hold together, and Input is refused.
It is not a witness for an impossible Input-plus-over-limit conjunction.
Combined mapping now contains12 disjoint frozen declaration rows:11 concrete
reached instances and one intentional negative premise bundle;1247 remain
uncovered. The unchanged CoreBoundary source was checked into an evidence-local
artifact using the existing validated original4.24 dependency map; provenance
and artifact hash are retained off Git. Full elaborated census, other branches,
resource adequacy and all original whole-lane gates remain open.

## Private Stack source-signature premises

`PrivateStackPremiseWitness.lean` constructs the three private helper premise
bundles on the same empty object heap, actual state/machine/base, frame8 and
nonzero cursor16. Both allocator inputs admit positive cost1; zero-cost branches
are proved separately. Full object StateRepr is constructed directly, not
upgraded from a weaker array/core relation. All relations transport arbitrary
tails; a general full-word-cost refusal guards the strict capacity condition.

The private originals stay private and unchanged. Their exact frozen source
signatures and lexical identities are joined in `private-stack-witness-map.json`;
no mangled private kernel name is resolved or invoked. These are independently
checked instances of their premise types, not new calls to the private theorems.
Combined source-row mapping is now15 of1259, with1244 uncovered, including one
previous intentional negative and three source-accounted private identities.
Full elaborated identity accounting and other heaps/branches remain open.

## Correlated sequencing fixture

`SequenceJointWitness.lean` witnesses the four public frozen Sequence
declarations using the same actual checked store and checked empty suffix.
Their Input link, both no-payment facts and both successful source runs hold
together. The intrinsic joined source run, emitted concatenation, exact stack
and both original Rep observations are retained. Actual program/code
association and refusal of a forged reverting joined outcome are checked.
The revert equivalence is instantiated on success, not claimed as a new
failing-alternative witness. Nonempty suffixes and other compiler branches
remain open.

Combined mapping now has19 disjoint source-census rows,1240 uncovered, retaining
one intentional negative and three source-accounted private premise instances.
This remains concrete source-signature accounting, not a complete elaborated
identity census or general sequencing/resource/native/gas/fork adequacy.

Review found a legacy census extraction defect for equation-style
`typed_sequencing_assoc`: its raw signature/span includes equation bodies and
the next declaration. The Sequence map preserves those frozen census fields
with an explicit limit and independently pins the clean source telescope/span.
Its witness reference is `typed_association`, the exact program equality. This
fix does not repair or certify the global signature extractor; full statement
fidelity accounting remains unfinished.

## Resolved private Stack kernel identities

The actual imported environment exposes all three names beneath
`_private.Solidity.Backend.Passes.Stack`, numeric Name component0, then
`Solidity.Backend.Passes`. `PrivateStackKernelIdentityChecks.lean` constructs
that numeric component explicitly and anonymously checks each actual constant
against its original source premise/conclusion types. Each constant's actual
transitive axiom set is guarded as propext/Quot.sound. Original visibility and
statements stay unchanged; no public theorem aliases are introduced.

The private map now records exact kernel names and component kinds as well as
source signatures. This resolves the three previously source-only identities,
without adding rows to the19 mapped declarations or reducing the1240 uncovered
rows. Earlier unresolved/source-only descriptions above are checkpoint history.
Full elaborated census and the equation-style global extraction defect remain
open. Failed print-prefix/numeric-identifier/reserved-word diagnostic attempts
are retained separately from the passing checks.

## Coverage membership correction

A frozen-selection reconciliation exposed an error in the earlier coverage
counts: Boundary, Stack, CoreBoundary and Sequence are not members of the
179-file module-map/wildcard selection underlying the1259-row census. Their19
checked premise instances are supplemental interface work explicitly requested
in later queue relays, not19 covered original census rows. The original1259
rows therefore remain uncovered by these fixtures. Earlier subtraction counts
(1255/1252/1247/1244/1240 remaining) are withdrawn. The supplemental proofs and
three resolved private identities remain valid, with their existing limits.
Each map now records exact frozen-selection membership separately.

The supplemental header recognizer leaves the legacy census untouched. At the
original selection it recognizes1259 source headers with no changed boundaries;
the known equation-style over-extraction occurs in supplemental Sequence.
This result is source accounting only, not an elaborated census or proof.

## First selected-census HeapBoundary instance

The H44 external SelectedHeapBoundaryWitness.lean fixture (see availability
and materialization instructions above) witnesses the selected frozen
`Solidity.Backend.Passes.objects_memory_link` declaration. Membership is checked
against the actual179-file/1259-row selection before counting it. Checked
object/memory nil-program certificates, capacity and nonallocation align with
the constructed object state. Actual prefix success yields a selected output
map; the original link is applied to that run/map to obtain real suffix Input
and successful concatenation with the original memory-branch Rep.

This is one selected row with an empty-program/empty-heap instance, leaving1258
selected rows uncovered by the fixtures. It is not public root branch selection
(which is not a premise of this theorem), allocating/nonempty-program or broad
compiler adequacy. The earlier19 supplemental rows remain separate and do not
reduce the selected count. Exact fixture module names and matching evidence-local
artifact provenance are retained; no artifact rekey or cache freshness claim.

The existing selected fixture now has one branch-parameterized Family for
reference-arrays/object/construction prefixes and a checked memory suffix. It
instantiates existing generic checked compilers, MappedBoundaryLink and
compilation_mapped_success; no new per-case modules or interface copies.
Actual Input is retained per branch, and the generic success theorem exercises
all three links with both selected output maps and exact returned stack.
This adds only referenceArrays_memory_link and construction_memory_link; the
existing objects_memory_link is not counted twice. Selected coverage is now3
rows with1256 remaining, separate from19 supplemental rows. Empty/nonallocating
programs and empty heaps only; full allocation/other branch adequacy stays open.

The same fixture now also has a two-selector OwnedFamily for object/construction
prefixes and reference-array/object suffixes. Each combination applies its
original generic link and generic mapped sequencing with actual full Input,
prefix/output maps, successful concatenation and exact stack. No new per-case
module, representation or production interface is introduced. This adds four
distinct selected rows, bringing selected instances to7 with1252 remaining.
The19 supplemental rows remain separate. The eighth HeapBoundary row,
construction_budgeted_link, is explicitly not covered; empty/nonallocating
instances do not stand in for its allocating adequacy.

## Positive construction sum-budget instance

The existing fixture's Budgeted namespace instantiates construction_budgeted_link
with two nonempty programs, each allocating a one-element uint array at cost2.
The same actual cursor16 object allocator supplies the universally quantified
combined budget4 and prefix Input, alongside both successful source runs.
Generic mapped sequencing exercises the link and retains both output relations.
Generic allocator-growth laws prove the actual successful final machine has
cursor20. No zero-cost suffix substitutes for this positive suffix.

Direct interpreter normalization hit the unchanged200000-heartbeat limit.
The accepted proof instead uses existing growth laws, with no budget increase;
failed diagnostics remain retained. An extra exact source object-count draft
was not proved or retained. This is one flat-array pair from an empty initial
heap, not general allocation/physical-byte/native/resource adequacy.
All eight selected HeapBoundary declarations now have concrete premise instances;
1251 selected census rows remain uncovered. Earlier19 supplemental rows are
still separate, and full elaborated census/whole-lane acceptance remain open.

## Actual memory compiler composition and reindexing

The same fixture now instantiates six selected ReindexedMemory declarations
and two selected MemoryCompilerSequence declarations. Both allocating stages
are accepted by Memory.compileProg itself; actual legacy Input, positive cost2
each, sum budget4 and both source runs align. Generic mapped sequencing retains
real output maps and target concatenation. memory_compile_join constructs an
accepted joined compiler result with exactly the component code/fragment, and
memory_compile_single_block constructs the accepted wrapper with unchanged code.
Reindexing uses genuine reflexive fragment equality and actual accepted/run
data; no distinct-layout equality or ownership upgrade is asserted.

The ledger records per-row source paths and additional interface hashes rather
than treating every row as HeapBoundary. Actual selected coverage is16 distinct
rows,1243 remain;19 supplemental rows remain excluded. These are narrow concrete
premise instances, not full elaborated census, arbitrary composition/resource
adequacy, Source/physical/native closure or whole-lane acceptance.

## Joint value success, ordering and reached failure

The same fixture instantiates the five selected ValueCertificate/ValueSequence
declarations through their existing generic APIs. A single typed selector table
produces actual checked five/seven literals and checked unsigned underflow.
All source outcomes and full represented Input hold on the same state. Generic
value/pair adapters retain arbitrary saved tails, exact successful machine
observations and the actual first success before second revert, without a
post-failure machine claim. Concrete pair order is seven above five; reversed
order and always-reverting behavior are refused semantically.

Both original interfaces were checked unchanged under exact module names, with
matching source/setup/artifact provenance. This adds five distinct selected rows:
21 selected instances,1238 uncovered,19 supplemental excluded. These are narrow
wide-uint pure-expression instances, not all shapes/widths or general compiler
totality, stateful effects, gas/fork/native or whole-lane adequacy. No new per-case
module/production interface or expression AST was introduced.

## One canonical allocation pair for every saved tail

The same generic fixture now instantiates the selected compilation_pair_shared
interface on its actual cost2+2 allocation pair. Actual Input, empty initial
stack, correlated link, both no-payment facts and both source successes hold
jointly. The original generic interface chooses one canonical intermediate/final
machine and pair of maps; every saved tail uses those same observations. Both
branch-specific Inputs, both stage runs, concatenation and both output relations
remain available. No new producer or interface is introduced.

The unchanged MappedTail/TripleSequence dependencies were checked for this
consumer; those checks are not additional selected witnesses. This adds one
selected member:22 instances,1237 uncovered,19 supplemental excluded. Arbitrary
model-tail transport does not establish native stack/gas/resource bounds or
physical byte-world adequacy, and full elaborated census/whole-lane gates remain
open. The larger scalar invocation/capacity adapter cases remain uncovered.

## Concrete scalar adapter capacity and failure instances

The existing fixture instantiates all nine selected StatefulValues declarations
through the published generic APIs. Literal operands five/seven feed actual
wrapping-add and uint-to-int cast certificates and accepted whole-value compilers.
A BinaryInvocation and unary stackBound premise are checked for empty saved
lists; tail preservation is not substituted for these capacity premises.
Explicit joint bundles cover checked underflow, left/right eager failures, and
a false Boolean short circuit whose untaken right expression actually reverts.
The generic source/component/whole-code observations remain distinct.

These are literal-operand instances of state-dependent-capable interfaces, not
state-dependent memory-load coverage or all operations/widths. Model capacity
evidence is not native/gas/fork/resource adequacy. The frozen selected ledger
now has31 distinct instances,1228 uncovered;19 supplemental rows stay separate.

All41 source dependencies outside the previous validated map were checked
serially. PowerBounds took250.57seconds and is explicitly reported above60s;
its existing generated threshold proofs and budgets were unchanged, with no
resource stop. Dependency checks are not additional witness rows or a full
build/timing acceptance claim. Exact module/source/setup/artifact provenance is
retained off Git. Existing ByteWorld and Raw producer waits remain unchanged.

### P20 V2 control layer repair

Moved the unchanged P20 V2 regression declarations to
`tests/h62/item2/audit-v09-passes/P20InterfaceV2Controls.lean`; the core module
retains an interface-only compatibility import. Five audit witnesses now import
the actual test module. Fresh serial kernel checks passed for the relocated
controls (4.68s) and all five consumers (5.30s, 3.52s, 2.94s, 3.57s, 1.75s),
with the old core control artifact excluded from the consumer import maps.
Finder and skeptic identified the stale test imports and confirmed their repair.
`node scripts/check-layers.mjs` still exits 1 for the 12 previously reported
master edges; the added P20 edge is absent. This is a baseline-relative repair,
not a global layer-gate pass. No control statement or proof changed.

### Closed-value generic application validation

The external fixture namespace `Solidity.Backend.Passes.AuditSelectedHeap.ClosedApplication`
instantiates existing
ClosedValues application, prefix capacity, byte roundtrip and represented-word
APIs with the actual literal-5 certificate, empty saved stack, real capacity
and the existing full represented symbolic input. The prefix split is only
the empty entry prefix, not an interior-prefix maximum. Byte decoding is not
native execution. The selected count stays 31 (1228 open), with 19 supplemental
rows separate, until exact frozen signature/ledger reconciliation. All six
new definitions have exact axiom guards; no axiom growth or interface copies.
Independent read-only finder and skeptic found no semantic defect and requested
these guards. Failed draft syntax/Fin-constructor diagnostics are retained off
Git; they are not passing proof evidence. Full gates/timing holds remain open.

### ClosedValues frozen selection reconciliation

The frozen ClosedValues source is byte-identical, but its four theorem rows
are absent from the original module-map selection. They discharge zero selected
rows. The ledger explicitly separates these four new supplemental instances
from the prior 19 supplemental rows; selected coverage stays 31/1259,1228 open.
A regression recomputes actual frozen membership and rejects counting these
names as selected. The joint premise bundle is kernel checked with an exact
standard-axiom guard; the generic byte theorem needs only its actual certificate,
while application and entry-prefix safety retain actual capacity and StateRepr.
No full elaborated census or original-row completion is inferred.

### Selected populated-memory sequence frontier

All 13 frozen ValueSequenceControls theorem rows are retained explicitly as
uncovered: four explicit-tail rows, one private range/representation helper,
and eight without explicit source binders. Exact membership and signature
hashes are independently reconciled by a regression. Empty tails and n=5 are
proposed tuples, not checked witnesses. The actual populated-memory fixture,
its import closure, private kernel identity and axiom checks remain required;
literal-only instances cannot discharge them. No implicit premise feasibility
or proof acceptance is inferred. Selected31/1228open remains unchanged.

### Populated-memory selected controls checked

The actual ValueSequenceControls import closure is now serially checked (12
missing modules, each below6s) with source/setup/artifact receipts. The fixture
jointly supplies StateRepr1/0/4, actual dynamic memory reads7/4 and an inhabited
tail. Twelve public selected declarations are checked reuse of the unchanged
original concrete proofs, with arbitrary-tail APIs retained. They are not new
independent compiler proofs. Thirteen exact axiom guards passed in16.63s;
emitted_prefix uses propext/Quot.sound, the others standard-three. The ambiguous
machine draft failure is retained; finalfixture references are fully qualified.
Private literal_word remains uncovered pending originalkernelidentity mapping.
The selected ledger now43/1259 (1216open); prior19 and4ClosedValues supplemental
stay separate. unchanged_memory observes its selectedcell vector only; byteworld,
native/resources, generalallocation and fulltotality remain open. Sourcecategory
counts are lexical and do not establish implicitpremise classification.

### Original private populated-word helper resolved

The numeric kernel identity for ValueSequenceControls.literal_word is now
checked by anonymous applications against its full unchanged n/hn/implicitword/hr
telescope and a concrete n5 joint range/representation instance. No public alias
or original private source edit is introduced. private_word_joint uses propext;
the original private constant uses propext/Quot.sound, both exactly guarded.
The wrong indexValue namespace draft is retained as failure evidence. All13
ValueSequenceControls selected rows now have concrete instances (12 checked
publicproof reuses and one originalprivate instance). Selected44/1259,1215open;
prior19 and4supplemental remain separate. No generalwidth/resource/native/full
elaborated census or full-lane completion follows.

### Captured local stability instances

All eight frozen selected CapturedValueStability theorems now have concrete
instances using the existing generic interface: actual represented local5,
accepted local-read compilation, captured-local extension, accepted update7,
and accepted checked-underflow expressions in original and extended contexts.
The same joint bundle supplies full StateRepr1/1/8, capacity1+2≤8 and both
success/failure outcomes. Immediate failure chooses the distinct failed capture
expression; later failure chooses the failed update. These are distinct tuples,
not simultaneous success and failure of one expression. Original execution
retains captured5 while updating the old local7, with shared words before all
tails and accepted mapped readback. Failure retains only its successful prefix,
never a post-revert machine. Fifteen exact axiom guards cover certificates,
capacity, joint premises and adapters; original source freshly checked3.82s.
Wrongcellnamespace draft retained. Selected52/1259,1207open; prior19 and4
supplemental remain separate. This uint-local instance is not general capture,
physicalByteWorld/native/resource or full-lane adequacy.

### Fresh scalar/reference context controls

Fifteen exact frozen selected ValueContextControls rows are now checked reuse
of original concrete control proofs. The joint tuple uses the same populated
source/machine/base at StateRepr1/0/4 and StateRepr1/0/6, actual oldlocal0 and
arrayread7, and an inhabited saved tail. Original arbitrary-tail types and
successful fresh-declaration prefixes are retained. Wrong unshifted indices
remain distinguishable (0vs11,7vs4), actual core refusal is preserved, and
reached failures have no post-revert machine. Ordered memory vectors observe
only their original listed cells. All16reports are exactly guarded; core refusal
and recognizer equality use standardtwo, othersstandardthree. Three source modules
freshlychecked2.91/1.75/2.35s, draftadaptercheckPASS21.00s. Selected67/1259,
1192open; prior19+4supplemental separate. No independentnewcompilerproof,
generalcontext, wholeworld/native/resource or full-lane completion claim.

### Typed bitwise receiving controls

Nine of ten frozen selected BitwiseValueContextControls rows have checked
reuse instances. The joint supplies actual StateRepr1/1/64 clean runtime5/3,
Supported And/Or/Xor and inhabitedtail; inhabited is concretely And. Existing
and/or/xor result/frame vectors, wrong-result/tailcorruption, dirty256 refusal
at8bits and signed refusal remain unchanged. Ten reports exactly guarded,
signedrefusal standardtwo, othersstandardthree. Five fresh sourcechecks passed,
draftadaptercheck21.75s. Source_result remains explicitly uncovered: its actual
Source.Env/Glob/Fr/fuel/St tuple is not supplied by receiving-context inputs;
it remains independent owned work. Generic ValueContext and ValueContextCode
are absent from the frozen selection and have not been counted. Selected76,
1183open; prior19+4supplemental separate. No Sourceadmission/native/resource,
generalbitwise or full-lane adequacy claim from these receiving controls.

### Bitwise Source-result tuple

The remaining original selected source_result row now has an independent actual
Source.Env/Program/Glob/Fr/St.init tuple, with joint pipeline/checked/state/n0/
SupportedAnd witnesses. No target StateRepr substitutes for Source premises.
The original evaluator theorem is applied with arbitrary pipeline, checkedmode,
fueloffset and Supportedoperator; concrete cleanuint8 operands5/3 yield fuel3
success, while the existing evalE_two theorem yields fuel2 timeout on the same
locals/state. Four exact standardthree axiom guards. The fixed zero hash and
precompile parameters are merely inhabited witness data, not realhash/fork/native
adequacy. The optional Source.SemanticsExamples fresh check failed at the existing
STy.implicit mismatch (7.90s); no failed artifact or theorem from it supplies this
witness. Direct Source constructors bypass that unrelated module. Failed record
syntax draft retained. Selected77/1259,1182open; prior19+4supplemental separate.
Full source dependency migration, elaboratedcensus, affected/final/editor/timing
and whole-lane gates remain open; this is not Sourcewholeprogram admission.

### Stateful populated-memory scalar controls

Fifteen original selected StatefulValueControls rows now have checked reuse
instances, with full represented populated memory, actual source reads7/4,
saved99 and real binaryheight3/unaryheight2 stack bounds. Checked arithmetic
retains separate test/body capacities and actual original guarded outcomes.
The same numeric/symbolic distinction, actual byte encodings, nonempty symbolic
load despite empty cast component, captured-state result change, listed memory
cells and not_closed refutation remain unchanged. not_closed is an intentional
negative conclusion (two actual states yield3vs4), not a premise demanding the
forbidden closed certificate. No literal substitution, contradictory premise
or new per-shape interface is introduced. Sixteen standardthree reports exactly
guarded; two fresh sourcechecks1.86/2.09s, draftkernel24.90s. Selected92/1259,
1167open; prior19+4supplemental separate. This is original concrete-proof reuse,
not generaloperator/byteworld/native/resource or whole-lane adequacy.

### Signed/bool closed-value selected controls

Nine original selected ClosedValueControls rows now have checked reuse
instances, separate from the four unselected ClosedValues supplemental rows.
The signed and bool applications consume actual ClosedInvocation structures
for savedFin99; their true height1 stack bounds hold on the same populated
StateRepr1/0/4 fixture. Original reference-prefix, selected memory vector,
byte-encoding, noncanonicalbool2, stack1024 refusal and rawPOP tail corruption
controls remain unchanged. No arbitrary-tail lemma substitutes for capacity,
and negative conclusions are not assumptions of forbidden witnesses. Twelve
exact reports guarded: noncanonicalbool propext-only, othersstandardthree.
FreshcontrolsourcePASS1.83s, draftkernelPASS26.50s. Selected101/1259,1158open;
prior19+4supplemental separate. No generalclosedoperator/native/resource,
wholememory, fetchedexecution or whole-lane adequacy claim.

### Capture effects and original private source steps

Twenty-one original frozen selected CaptureControls rows now have concrete
instances:18public proof reuses and3private kernel constants resolved by numeric
names and anonymous exact-statement applications. No public aliases/private
source edits. The actual populated fixture jointly supplies frame4/frame6
representations and sourcecapture old7→new8, preserving original fresh reach,
alias/context extension, shared canonical full-tail output and wrong-order/
recapture/POP controls. Private alias_source/value_source/bad_after are checked
against their original concrete statements. Effect-before-failure inspects only
the successful prefix; the complete failed run remains coarse revert, with no
post-revert machine. Listed vectors are not whole-memory/native observations.
22exactstandardthree axiom guards; freshmodule5.74s, draftkernel33.16s. These
are checkpoint timings, not paired performance acceptance. Selected122/1259,
1137open; prior19+4supplemental remain separate. Original whole-lane/fullcensus,
physicalByteWorld/resource/native and final gate obligations remain open.
## Imported member receipt: explicit reactivation and published re-baseline, 2026-11-07

The following incoming member receipt is retained as provenance. Its v4.35
overlay/runtime status is separate from the VY3 original-toolchain checkpoints
above; neither receipt clears the other queue, gate or trust hold.

## Explicit reactivation and published re-baseline, 2026-11-07

The coordinator's new user instruction explicitly reactivates this lane after
its recorded retirement. The existing VM/branch/goal are preserved; no goal was
created/reset. Published master 5da4771e63a4278ed53932ac39a032e3d7aea6ed contains
retirement head 521196a3a78cd6cce22a7f14dd4364493b16cdbc. The clean lane was
fast-forwarded to that exact published head, preserving earlier local merges.
The ownership snapshot remains dated; no new per-file producer claim is inferred.
All new writes remain in the original additive audit scope.

Every frozen census file (179) is byte-identical to the original c6f550e2 base;
all 1,259 source signatures retain their original identity. The local Raw source
is also unchanged, and tracked lean-toolchain still names v4.24.0. The supplied
fleet instruction still pins the verified official v4.35.0 release. Therefore
no v4.24 cache is reused, and the known failing Raw import is not retried.
B-MIGRATION-SYNTAX-RAW and B-RAW-TRUST-REVIEW remain waits. A touched gate/review
reported for the published merge is not a new Lean witness or trust disposition.

Independent backfill now maps all 27 macro-return rows to source dependency
candidates. macro_dependencies.py checks that each selected frozen callee is in
the caller's frozen import closure, captures its complete source signature,
source-written telescope and available section-variable groups. All 27 current
callee signatures and section-context texts match their frozen counterparts.
The 44 available section groups retain exact frozen source spans. Namespace,
macro application typing and actual implicit inclusion remain pending Lean.

The callee telescope is reference evidence only. Applied macro arguments may
already discharge inputs; no callee hypothesis is added to any caller and no
witness is counted. All 27 caller_new_premises lists are empty. All rows remain
uncovered. PrimitivePackets dependency ownership is explicitly unconfirmed;
V09 dependency ownership is an area candidate, not a per-file agreement.

Independent read-only finder/skeptic review found an inherited owner-label bug
and a missing callee-context field. Both were fixed, with regressions. Final
reviews report no remaining concrete finding and used no Lean/server or writes.
Source acceptance now covers 18 tests, including exact macro-row coverage,
source signature/context spans, import reachability and no-extra-premise/owner
controls. Evidence is under rebaseline-20261107/; original retirement exports
remain preserved. No Lean declaration, axiom, sorry, budget or interface changed.

All four original checkpoints remain unfinished. The next independent source
item is an applied-argument ledger for these 27 macro cases; resolved types and
simultaneous witnesses still wait on the same runtime/trust dependencies. This
checkpoint does not complete the work/backfill queue or authorize scope takeover.

### Allocating selected-map composition controls

Thirteen original frozen selected AllocatingControls rows now have checked
reuse instances. The joint supplies actual StateRepr1/1/6, StructAllocator
cursor16, exact allocating-prefix cost5, strict16+5<W and an inhabited initial
machine. Original coupled intermediate/final maps, full mapped outputs,
five-cell growth, populated second allocation preserving both old array IDs,
cursor23, bootstrap and reached failure remain exact. stale_map_impossible is
an intentional negative conclusion about the reached heap under the oldzero
map, not an assumed impossible representation. No post-revert machine or
symbolic-to-ByteWorld/native/resource inference. Fourteen standardthree reports
exactly guarded; freshsource2.65s, draftkernel32.33s. Selected135/1259,1124open;
prior19+4supplemental separate. Checkpointtimings are not pairedperformance or
whole-lane acceptance; original final/fullcensus/gate obligations remain open.

Master7683091e7 adoption also brought an incoming member reactivation receipt.
The audit-document conflict was resolved by preserving both complete histories;
its v4.35 receipt remains separate provenance. Own-scope whitespace checks and
unmerged-path checks pass. Whole cached whitespace check reports incoming
migrate-optimizer retirement artifact whitespace; those archived bytes are
unchanged from published master and are preserved, not edited as lane work.

### Three-stage canonical map and tail controls

Twenty original frozen selected TripleControls rows now have concrete
instances:11public proof reuses and9exact private cell lemma checks. The joint
retains actual frame7 StateRepr/StructAllocator cursor16/cost5 and source capture/
observe transitions. Original shared_resources chooses three maps and canonical
machines before all tails, retains both code associations, all three full mapped
outputs, old-reference identities and growth5. Nine anonymous private checks
apply both original numeric-name observer and exact lemma; the observer is not
an extra census row, and no private source/public alias is changed. Exact21
axiom reports guarded (same standardthree set, observed order pinned). Source
freshcheck4.15s, draftkernel37.86s. Listed cell vectors and stale-map negatives
are not whole-memory/ByteWorld/native/resource/general allocation adequacy.
Selected155/1259,1104open; prior19+4supplemental separate. Fullcensus/lane and
paired performance acceptance remain open.

The first triple axiom-pin run failed because short-name prefix replacement
nested cell1/cell2 guards inside cell17/cell20 blocks. Finder/skeptic identified
the layout defect; rebuilding the nine blocks by complete names restores one
matching guard per report. The failed38.75s log is retained and is not a pass.
No original theorem application, statement, premise or axiom set was changed.

### Fresh-state source and target reachability steps

Fourteen original frozen selected ReachabilityControls rows now have concrete
instances:3public proof reuses and11exact private step checks. Actual joint
input combines full populated StateRepr1/0/4 with the original builder run from
State.init to the same typed state. Anonymous private checks retain complete
source/target propositions, genuine heap growth for two allocations, population,
alias/rebinding/finalscalar steps and full-record arbitrary-tail write/read runs.
No type_of self-check replaces a stated proposition; helper definitions are not
extra theorem rows and no private source/public alias is changed. Fifteenexact
standardthree reports guarded with observed order. Freshmodule2.31s, draftkernel
41.80s. Intrinsic fixture reachability is not independent Source-session,
deployed constructor, ByteWorld/native/resource or general reachability adequacy.
Selected169/1259,1090open; prior19+4supplemental separate. Fullcensus/lane,
pairedperformance and original final gates remain open.

### Real failing RHS and primitive-pair expression controls

Seven original frozen selected ExpressionControls rows now have checked
reuse instances. The joint supplies actual populated StateReprframes4/6,
actual badTest source revert and successful distinct skipped AND/OR/conditional
expressions, plus an inhabited tail. Original full-record arbitrary-tail runs,
selected RHS failures and eager-order failure remain exact. The actual two-local
primitive capture program retains7/9 after aliased write12, with the original
checkedPair.Agrees certificate; this is not a new general tuple lowering layer.
Conditional-top and captured-cell values are their selected projections only.
Eight exact standardthree axiom reports guarded. Freshmodule2.96s,draft43.12s.
Selected176/1259,1083open; prior19+4supplemental separate. No contradictory
same-expression premises, post-revert state, native/resource/generalfunction
frame or full-lane claim. Pairedperformance/fullcensus/finalgates remain open.

### Correlated core/memory links and separated fresh frames

Ten original frozen selected LinkedControls rows now have concrete instances:
9public proof reuses and1exact private forall-id base-bound check, without a
public alias or original source edit. The joint uses actual frames4/6 and
separate true-assert success, false-assert panic and independent right-stage
revert, plus id0 and emptytail witnesses. Both original prefix and suffix Rep
clauses remain; freshvalue11 is below occupied header16 and frame17 is correctly
denied, not assumed as a premise. Coarse internal panic/revert is not equality
of public ABI observations. Eleven exact reports guarded: privatebound axiomfree,
frame17negative standardtwo, remainingstandardthree. Freshmodule1.46s; firstdraft
FAIL44.21s on new existential-grouping syntax, fixedjointPASS45.04s. Rawfailure
retained and not a proof pass. Selected186/1259,1073open; prior19+4supplemental
separate. No post-revert state, native/resource/general-frame or full-lane claim;
pairedperformance/fullcensus/finalgates remain open.

### Accepted stages and actual mixed-root refusal

Fifteen original frozen selected Controls rows now have checked reuse
instances. The joint supplies actual populated StateRepr, separate core-assert
and memory Inputs, actual write/read source success and machine/tail data.
Actual recognizer acceptance, nonempty stages, result5 and local rejection of
empty/revert-all substitutes coexist with original mixed whole-program R01
refusal. No accepted-stage result is promoted to acceptance of that root entry
or G01 session/totality. Original wrong-order, POP corruption, fragment cherry-
picking and association controls remain exact. Sixteen standardthree reports
guarded; freshsource2.04s,draftkernel47.22s. Selected201/1259,1058open; prior19+4
supplemental separate. No ABI/native/resource/generalcompiler or full-lane
adequacy follows; pairedperformance/fullcensus/finalgates remain open.

### Runtime reference selection and wrong-order control

Six original frozen selected ReferenceControls rows now have checked reuse
instances. The joint supplies both actual represented bool states/targets at
frame6 and inhabited bool/tail data. One original compiled runtime conditional
selects source reference/value1/4 versus0/7 and target pointers20/16; this is not
two compile-time branch copies. The wrong-order program reads old7 before
rebinding. Original certificate remains parameterized by bool and tail, and
fresh reachability is preserved. Seven exact standardthree reports guarded;
freshsource2.09s,draftkernel53.03s. Selected207/1259,1052open; prior19+4supplemental
separate. Intrinsic conditional reassignment is not Source ternary, general
tuple/function-reference, deployed/native/resource or whole-lane adequacy.
Pairedperformance/fullcensus/finalgates and producer waits remain open.

### Memory scope exit and real slot reuse

Eighteen original frozen selected MemoryScopeControls rows now have checked
reuse instances, all retaining their arbitrary pipeline/machine/tail parameters.
The joint uses actual AssignmentMultiplicationControls StateRepr1/1/64, accepted
body Input and prefix source success. Eight source modules passed fresh serial
checks, including the published V09 assignment/generic modules and scope module.
Actual scope exit drops two source locals while retaining code/selected maps;
next declaration reuses slot4, wrong context writes6, and private word255 at5
is not cleared. Original source/target reached reverts remain separate, with no
post-revert machine. Nineteen exact axiom reports guarded; draftkernel52.80s.
Selected225/1259,1034open; prior19+4supplemental separate. No scrubbing, SourceABI,
ByteWorld/native/resource/general scope or full-lane adequacy is inferred.
Checkpointtimings are not pairedperformance acceptance; all original final
proof/census/gate obligations and producer waits remain open.

### H44 selected-heap bulk split

The exact held checkpoint at `2e1dd272c6d89d5883956791a26315bf0a67bc0b`
is retained outside Git. On the producing VM its artifact root is
`/workspace/vy3-evidence/h44-selected-heap-20261107`; this is an export location,
not a path expected on consumer machines. The tracked artifact manifest linked
above contains relative artifact names, byte sizes and SHA-256 hashes. This
historical checkpoint contains 225 selected rows (1,034 then open); later
increments below account separately for subsequent progress. The unfinished
joined-memory draft is preserved separately and adds no accepted rows.

Obtain both unchanged manifest-listed files through the approved artifact
channel and stage them together in a local directory. Set `VY3_AUDIT_ARTIFACTS`
to that directory, or use the checkout-relative default
`.audit-artifacts/selected-heap`. Run:

```sh
python3 scripts/h62/item2/audit-v09-passes/selected_heap_artifacts.py
python3 scripts/h62/item2/audit-v09-passes/selected_heap_artifacts.py --acceptance
```

The first command checks both files' sizes and hashes. The second is mandatory
full accounting acceptance: it runs portable source tests and the original
external-ledger assertions. Missing or changed artifacts fail this gate;
portable source tests alone do not establish external witness acceptance.

For the unchanged Lean per-file gate, run the verifier with `--materialize`
under the repository writer lock, then run the original
`gate.sh per-file tests/h62/item2/audit-v09-passes/SelectedHeapBoundaryWitness.lean`
with the existing serial/resource wrapper and frozen toolchain. This temporarily
creates the absent target from verified bytes and refuses to overwrite different
local work. Keep materialized bulk untracked and do not commit it. Relocation
changes no theorem, gate, budget or acceptance claim. Consumers must stage the
external artifacts before attempting this validation.

### Small joined-memory public certificate witness

`JoinedMemoryWitness.lean` instantiates the existing public whole-memory admission certificates. One concrete tuple jointly satisfies the initial state relation, both success/failure allocation inputs, total cost 9 and an inhabited tail. The original success statement chooses the same final map before every caller tail; the original reached-failure statement reverts without asserting an output map. These are model compiler certificates, not native ByteWorld or full Source/G24 production.

`joined-memory-witness-map.json` records the two exact frozen signatures, independently checked against the frozen selected census and disjoint from the 225-row external checkpoint. Aggregate coverage is 227 of 1,259 selected rows, with 1,032 open. The prior 19 supplemental rows and four unselected ClosedValues rows stay separate. The generated bulk fixture remains external under H44; no new per-case interface or Artifact structure was introduced.

### Public joined-allocation controls

`JoinedAllocationWitness.lean` checks eight unchanged public `MemoryJoinedAllocation.Controls` statements, including actual compile acceptance, one final machine before all tails, complete cell observations, wrong-cursor/reference refusals, stale-map impossibility and the observable effect of an extra POP on a saved tail. The joint tuple supplies the original prefix Input, total allocation cost 9 and an inhabited concrete machine; `reached_joint` retains the full original correlated middle machine/map and every-tail suffix Input/allocation budget.

The compact eight-row ledger is checked against frozen signatures and disjoint from both prior checkpoints. Selected aggregate coverage is now 235 of 1,259, leaving 1,024 open. The sixteen private cell proofs are listed explicitly as uncovered; no kernel-identity coverage is inferred from public reuse. Supplemental/unselected counts remain unchanged. No native ByteWorld, matching emission or full Source/G24 adequacy is claimed.

### Private joined-allocation kernel identities

The existing `JoinedAllocationWitness.lean` now resolves each of the sixteen original private cell theorems and private `readCell` through their actual module-qualified kernel names. Anonymous checks retain each complete original closed cell signature; one shared loop checks the original declarations' transitive axiom sets. No private theorem is re-exported or replaced by a fresh decision proof. The original Input/cost/machine joint and correlated reached-stage certificate remain in the same module.

This resolves the preceding checkpoint's sixteen private exclusions, raising selected aggregate coverage to 251 of 1,259 (1,008 open). The compact metadata stores exact frozen signature hashes and kernel-name provenance. The original public eight, prior joined-memory two and external held225 are disjoint; supplemental/unselected counts stay separate. Model cell observations establish no native ByteWorld/emission or full-lane acceptance.

### Joined allocation-cost controls

The existing allocation witness module now exercises all ten public and eight private frozen `MemoryJoinCost.Controls` rows. Public instances retain actual prefix/suffix admission, total cost 9 rather than 5, reached correlated allocation input, complete prefix observations, source revert, skipped suffix cost and actual every-tail target revert. Private checks use the original mangled kernel identities and complete closed cell types, with one guarded axiom loop. Existing concrete prefix Input/cost/machine and reached-stage witnesses are reused.

The compact ledger is checked against every selected row of this frozen file, with no overlap against the prior 251. Aggregate coverage is 269 of 1,259 selected rows, leaving 990 open; supplemental/unselected counts remain separate. These model cost and failure controls establish no native gas, ByteWorld realization/emission, physical resource or full Source/G24 adequacy. H44 bulk remains outside Git.

### Joined frame admission and refusal

The existing allocation witness now checks all ten unchanged `MemoryJoinFrame.Controls` selected rows. Its new joint tuple supplies the actual initial state representation, total allocation budget and an inhabited real joined compiler result for the universally quantified undersized-frame control. Full original types retain public admission, mapped boundary link, shared final machine/map before every tail, cursor 25, scoped maximum/slot reuse, and unreachable-allocation frame retention/refusal. `unreachable_other_fields` keeps the other premises inhabited while the static capacity check intentionally fails; this is not a claim that all public compiler premises are jointly impossible.

The generalized frozen-file regression verifies exact hashes, complete file membership and disjointness across both cost and frame families. Aggregate selected coverage is 279 of 1,259, leaving 980 open; supplemental/unselected counts stay separate. Source frame and model allocation/revert facts establish no native gas, physical ByteWorld/emission or full Source/G24 adequacy. H44 bulk remains external.

### Public triple-admission witnesses

The existing allocation witness now exercises thirteen unchanged selected `MemoryTripleAdmission.Controls` public statements. A concrete joint supplies the actual seven-slot state representation, both success/failure allocation budgets, an actual whole compiled program and an inhabited caller tail. Original signatures retain source length/capture, public capture selection, total cost, stage maps/machines before every tail, full cell observation, wrong-old-length and insufficient-third-frame refusals, and reached third-stage failure.

The seventeen private cell rows remain explicitly uncovered. Frozen-file accounting checks the union of covered and uncovered rows and preserves disjointness with the prior 279. Aggregate selected coverage is 292 of 1,259, leaving 967 open; supplemental and unselected rows remain separate. The generic `MemoryJoinFrame.lean` interface was inspected but is outside the original selected census and contributes zero rows. No native ByteWorld/emission, resource or full Source/G24 adequacy is inferred. H44 bulk remains external.

### Private triple-admission identities

The seventeen remaining original private `MemoryTripleAdmission.Controls.cell*` theorems are now checked anonymously at complete original closed types, using the actual private module names and original `readCell`. A shared guarded loop records each original declaration's transitive axioms; no private theorem is re-exported or replaced by a fresh decision proof. The existing joint representation/both budgets/actual whole program/tail remains in place.

This resolves the preceding seventeen private exclusions. All thirty selected rows in the frozen file are accounted for distinctly; aggregate coverage is 309 of 1,259 selected rows, leaving 950 open. Supplemental/unselected counts remain separate. Model cell observations do not establish native ByteWorld/emission, physical resources or full Source/G24/lane adequacy. H44 bulk remains external.

### Public memory-association observations

The existing allocation witness now reuses the two unchanged `MemoryAssociation.Controls` original theorems with the actual triple-admission joint. Both real public compiler selections retain one final machine and full selected map before every tail, including the same reached allocator growth and the third-frame refusal. The failure pair retains reached bounds failure for both associations without an output-map conclusion. No abstract per-case interface or copied Artifact structure is added.

Fresh generic-source and control checks precede witness checking. Exact frozen-file membership and disjoint accounting give 311 of 1,259 selected rows covered, with 948 open; supplemental/unselected counts remain separate. Model association transport does not establish native ByteWorld/emission, gas/session resources or full Source/G24/lane adequacy. H44 bulk remains external.

### Actual public memory-call witnesses

`MemoryCallWitness.lean` checks ten unchanged public `MemoryCallControls` statements at their original full types. One concrete joint supplies the actual allocation Input at frame 128, the push-free call, actual public compiler acceptance, all three source runs, and the genuine call-frame demand bound. The intrinsic program allocates an old array, calls a body returning a fresh object while rebinding a private parameter, then consumes both caller alias and escaped return. Public recognizer and frame/cost facts are retained; target whole-pipeline execution is not inferred from these source/admission witnesses.

Five private rows remain explicitly uncovered: `noRefs`, three source-success selectors and `source_get`. The empty-heap refutation is intentional negative evidence and is not counted as a jointly inhabited premise bundle. Exact frozen-file covered/uncovered union and disjoint accounting give 321 of 1,259 selected rows covered, leaving 938 open. Supplemental/unselected rows stay separate. Intrinsic expanded-memory-call admission establishes no independent Source lowering, external CALL/world, native ByteWorld/emission, gas/session-resource or full-lane adequacy. H44 bulk remains external.

### Private memory-call success and extraction

The three original private source-success selectors and generic `source_get` rule are now checked against their actual private kernel identities and complete original signatures. A concrete existential tuple uses the real nontrivial allocation state/program/output and proves `some output = (program.run state).toOption`, jointly inhabiting the extraction rule's hypothesis. The three actual source stages remain correlated by the previous joint. Original declarations' axiom sets are guarded; no private theorem is re-exported or replaced by a fresh decision proof.

The intentional `noRefs` empty-heap refutation remains explicitly uncovered and does not supply an inhabited-reference claim. Four distinct selected rows raise aggregate coverage to 325 of 1,259, leaving 934 open; supplemental/unselected counts stay separate. These source-success/extraction witnesses establish no target whole-pipeline, external CALL/world, independent Source lowering or native adequacy. H44 bulk remains external.

### Scoped memory-call model trace

The existing memory-call witness now checks eight unchanged `MemoryCallScopeBoundary.Controls` public rows. A concrete joint supplies actual allocation Input, scoped-call and suffix source successes and the real private call-frame demand bound. Original full types retain both source associations, correlated three-stage maps/machines before every tail, scope-output relation, reached suffix Input, zero suffix allocation cost and refusal of the smaller source-frame demand. The stage certificate is built from the existing call producer; this checkpoint asserts no new top-level `Compiler.compile` recognition for the scope wrapper.

Fresh serial checks cover the scope boundary, actual call application and original controls. One private `final_some` selector remains explicitly uncovered. Exact frozen membership and disjoint union accounting give 333 of 1,259 selected rows covered, leaving 926 open; supplemental/unselected counts stay separate. These intrinsic model traces establish no external CALL/world, native ByteWorld/emission, gas/session resource or independent Source/full-lane adequacy. H44 bulk remains external.

### Private scoped-call success identity

The remaining private scoped-call `final_some` selector is checked anonymously at its full original closed type, using its actual kernel name under `MemoryCallScopeControls.0` and the distinct source namespace `MemoryCallScopeBoundary.Controls`. Its transitive axioms are guarded against the observed report. No private theorem is re-exported or replaced by a new decision proof; the existing actual scoped source/Input joint is retained.

All nine selected rows in this frozen file are now accounted for. Aggregate coverage is 334 of 1,259 selected rows, leaving 925 open. The separate `MemoryCallControls.noRefs` intentional refutation remains uncovered; supplemental/unselected counts stay separate. This identity check adds no native, top-level scope-recognition or full-lane acceptance claim. H44 bulk remains external.

### Fresh returned-reference readback

The existing allocation witness now exercises all six unchanged `ReturnedMemoryCapture.Controls` selected statements. One joint supplies actual public selection, original compiler Input, a source-success output and the fresh reference's actual environment binding. The existing generic readback application is also checked, without counting its definition as a selected theorem. Original full observations distinguish the fresh selected pointer 21 from stale initial-map pointer 0 and detect saved-tail corruption.

Fresh serial checks cover the generic readback module and its original controls. Exact frozen whole-file membership and disjoint accounting give 340 of 1,259 selected rows covered, leaving 919 open; supplemental/unselected counts remain separate. The independently Source-dependent related-capture family is not substituted for this family, and known Source/example validation holds are not cleared or rerun unchanged. No native ByteWorld/emission, gas/resource or full Source/G24/lane adequacy is inferred. H44 bulk remains external.

### Intentional empty-heap refutation

The original private `MemoryCallControls.noRefs` declaration is now checked at its full `{R} (r : HRef initial.H R) : False` type through the actual kernel identity. The additive general lemma `noRefs_premises_impossible` proves that the reference premise is uninhabited for every reference type in that actual empty initial heap. Both reports use only `propext`. This certifies intentional negative evidence; it does not manufacture a simultaneous premise witness or identify a defect requiring theorem repair.

The ledger records this classification, original signature/kernel name and impossibility proof separately, with null joint witness and zero selected-witness credit. Its literal joint-witness obligation therefore stays in the open set. Coverage remains 340 of 1,259 selected rows, with 919 open; supplemental/unselected counts are unchanged. No original statement, definition, axiom set, exclusion or budget changed.

### Allocated-reference readback and full tail observation

The existing allocation witness now checks all five public and sixteen private selected `AllocatedReferenceRead.Controls` rows. It reuses the actual public-selection/Input/source/fresh-binding joint. Full original statements retain one reached final machine/map before every tail, fresh-reference read success, old-alias bounds failure, complete memory observations, and a corrupt suffix that leaves the top returned zero intact while deleting the caller's saved 99. Private cell checks resolve actual kernel identities at complete original closed types without re-exporting originals or adding decision-proof copies.

The original controls are freshly checked against the existing allocation dependencies. Whole-file frozen membership and disjoint accounting give 361 of 1,259 selected rows covered, with 898 open; supplemental/unselected rows stay separate, as does the zero-credit intentional refutation. Model memory/stack observations establish no native ByteWorld/emission, gas/resources or full Source/G24/lane adequacy. H44 bulk remains external.

### Portable source tests and mandatory H44 external acceptance

The clean-checkout source suite is `python3 -m unittest discover -s tests/h62/item2/audit-v09-passes -p 'test_*.py'`. It uses the compact, reviewable 225-row source registration inventory and unchanged frozen signatures, with no external fixture reads. This is source accounting, not evidence that the external Lean fixture has been checked.

The original nine detailed ledger assertions are retained unchanged in `selected_heap_external_checks.py`; an additional assertion equates its verified ledger with the portable source inventory. Full accounting acceptance remains required: stage the two unchanged bulk files in a directory, set `VY3_AUDIT_ARTIFACTS` to that directory, then run `python3 scripts/h62/item2/audit-v09-passes/selected_heap_artifacts.py --acceptance`. This verifies hashes, runs the entire portable suite and runs every external assertion. Missing, altered or escaping manifest paths fail; no assertion is skipped or replaced by the source inventory. The committed manifest contains only relative artifact names, sizes and SHA-256 hashes.

For the unchanged external Lean gate, use the same staged directory and run the verifier with `--materialize` under the writer lock, followed by the original resource-bounded `gate.sh per-file tests/h62/item2/audit-v09-passes/SelectedHeapBoundaryWitness.lean` on the frozen toolchain. Keep the materialized bulk untracked. The default staging location is `.audit-artifacts/selected-heap` relative to the checkout; no worker-specific absolute path is required. Scope questions and acceptance remain unchanged. No theorem, gate, budget or witness count is weakened.

### Reached positive-base allocation failure

`PositiveAllocationWitness.lean` exercises all ten unchanged selected `PositiveAllocationFailure.Controls` statements using the existing assignment and V3 bare-revert producer APIs. One concrete joint supplies actual representation and reached allocation capacity at cursor 64, body failure after allocation, an inhabited saved tail, and the distinct near-end stale/reached budget facts. At the same near-end header the stale one-word estimate fits while the actual three-word demand is refused. Original full types retain the successful assignment prefix and its saved-stack observation before the reached body reverts; no post-failure machine is invented.

Fourteen available dependencies were freshly checked serially, without changing their source or budgets. Exact frozen whole-file membership and disjoint accounting give 371 of 1,259 selected rows covered, with 888 open; supplemental/unselected rows and zero-credit intentional refutation stay separate. These positive-base model capacity and failure facts establish no native ByteWorld/emission, gas/session resources or full Source/G24/lane adequacy. H44 bulk remains external and portable source tests remain independent of it.

### Substantive admission joint and reached allocator preservation

The legacy `AuditJoinedAllocation.joint` constructor/cost tuple remains for compatibility. Its ledger references now use `joint_admission`, which checks actual whole public compiler selection, full original Input, reached cost and an actual successful source output together. The constructor self-equality is not used as evidence of admission. P20 compatibility documentation now names the in-tree controls after their integration, retaining its core-only import.

`PreservedAllocatorWitness.lean` checks nine public and one private unchanged selected controls. Its joint derives a genuinely inhabited mapped construction-prefix output from the existing shared execution certificate, together with original Input and actual suffix source success. Full original statements retain a nonidentity object mutation, both budgeted suffix interfaces, allocator preservation and growth to cursor 25, with stage maps chosen before every tail. No desired allocator preservation conclusion is assumed as a premise witness.

Seven available dependencies pass fresh serial checks. Frozen declaration visibility now drives private/public static classification instead of name patterns. Exact whole-file and disjoint accounting give 381 of 1,259 selected rows covered, leaving 878 open; supplemental/unselected counts and zero-credit intentional refutation stay separate. Native ByteWorld/emission, resources and full Source/G24/lane adequacy remain open. H44 bulk remains external and the portable-source/external-acceptance split remains mandatory.

### Construction/reference-array/memory boundary controls

`HeapBoundaryWitness.lean` checks eleven public and three private selected original controls with a joint actual construction Input and all three real source-stage successes. Original full types retain heap/allocator representation, reached links, both code associations, saved tails and the mutated answer 42. The original success statement selects maps per caller tail; no stronger uniform-map theorem is substituted. Actual private selector names and axiom sets are guarded with full module-qualified identities.

The original `noRefs` declaration and its general premise-impossibility consequence are checked separately, with null joint witness and zero selected credit. Shared refutation accounting now handles both empty-heap families generically. Whole-file covered/uncovered union and disjoint accounting give 395 of 1,259 selected rows covered, leaving 864 open; supplemental/unselected counts stay separate. Published master `7de6f66ad29488d70e3c31c6b2a4798b72a0a209` was adopted before this checkpoint. The root-gate documentation still leaves compatibility/API/axiom and consumer acceptance gaps open; its transport alone clears no wait. No native ByteWorld/emission, resources or full Source/G24/lane adequacy is inferred. H44 bulk remains external.

### Shrinking-frame call-prefix controls

`ReframedWitness.lean` checks all eleven unchanged selected `ReframedControls` statements. Its joint supplies the actual allocating/capturing call Input at frame 128, prefix and consumer source successes, the real prefix/suffix frame bounds and reached failing-suffix source. Full original types keep the prefix at its original frame while admitting the suffix at frame 5, retain frame-4 refusal, choose stage maps/machines before caller tails, and observe the full old/new-object/private-cell/alias/sentinel/cursor/tail vectors. Failure concludes revert after a real successful prefix without a post-failure machine or map.

Eight available dependencies pass fresh serial checks. Exact frozen whole-file membership and disjoint accounting give 406 of 1,259 selected rows covered, leaving 853 open; the private observer definition adds zero rows, and supplemental/unselected/intentional-refutation accounting stays separate. No ABI/function-reference producer, external CALL/world, native ByteWorld/emission, gas/session-resource or full Source/G24/lane adequacy is inferred. H44 bulk remains external and portable source checks remain independent of it.

### Reframed allocating-loop triple controls

`ReframedTripleWitness.lean` checks seven unchanged selected original controls across frames 128, 64 and 5. Its joint supplies actual preparation Input, all three source successes and an inhabited reached middle Input with three-word allocation capacity. The middle capacity is derived from the existing shared execution's checked `Room` and original positive cost proof; it is not assumed from the zero legacy metric. Original full statements retain the existential cost judgement, shared maps/machines before caller tails, both code associations, saturated-cursor refusal and complete ordered tail observations.

Twelve available dependencies pass fresh serial checks. The first witness check failed on ambiguous fixture aliases and is retained as failed, including recovery diagnostics; explicit concrete state qualification fixes the ambiguity, and only subsequent successful checks receive credit. Exact frozen whole-file membership and disjoint accounting give 413 of 1,259 selected rows covered, leaving 846 open. Private observer definitions add zero rows; supplemental/unselected/intentional-refutation accounting stays separate. No native ByteWorld/emission, gas/session resources or full Source/G24/lane adequacy is inferred. H44 bulk remains external.

### Source allocating-loop scope controls

`LoopScopeWitness.lean` checks seventeen unchanged public controls and the actual private generic extraction rule at its full original telescope. Its joint supplies actual preparation Input, public loop-scope recognition, the real allocating body success, wrapped source success, positive source cost 3 and the distinct zero legacy metric. The source iteration witness remains the original finite `TLoop` argument: one allocating/rebinding body sets the condition false, rather than target execution being substituted as source semantics. A concrete preparation equality inhabits the private extraction hypothesis.

Precise axiom reports include the full private kernel identity. Frozen whole-file visibility, signatures and disjoint accounting give 431 of 1,259 selected rows covered, leaving 828 open; supplemental/unselected/intentional-refutation accounting stays separate. The prior fresh source artifact is reused with recorded provenance; dependency kernel checking alone had received no row credit. No native ByteWorld/emission, gas/session resource or full Source/G24/lane adequacy is inferred. H44 bulk remains external and portable checks do not require it.


Loop-prefix checkpoint: eighteen original public `LoopPrefixControls` rows now
have exact frozen signature accounting and checked original-proof aliases in
`tests/h62/item2/audit-v09-passes/LoopPrefixWitness.lean`. The common witness
inhabits preparation Input and the reached failure/divergence Inputs at their
respective actual source states. The original prefix effect, unreachable
allocation cost, finite failing turn and nonterminating source proof remain
distinct; internal revert/fault observations establish neither public ABI bytes
nor native gas/resource adequacy. Private observer definitions receive no row
credit. Selected accounting is 449/1259, leaving 810 open; supplemental rows
remain separate. The memory-call intentional-refutation list again requires
exactly one entry, with its existing null joint and zero-credit checks retained.
Raw compatibility/axiom adjudication and checked ByteWorld realization with
matching actual emission provenance remain producer waits. Bulk check/resource
logs are external at `/workspace/vy3-evidence/loop-prefix-controls-20261107`.


Loop-call checkpoint: nine public original `LoopCallControls` rows are mapped
to exact frozen signatures in `loop-call-witness-map.json` and checked through
`LoopCallWitness.lean`. The common witness obtains both actual selected maps
from `LoopScopeTerminal.prefix_relations` and applies the original `receiving`
theorem to inhabit the call Input at the actual rebound loop state. Original
expanded frame, cost6, source success, whole-mixture recognizer refusal and
undersized-frame refusal remain distinct. Selected accounting is458/1259,
801open; supplemental rows stay separate. A draft using stack-replaced states
hit the unchanged heartbeat limit; using exact existing prefix relations
avoids that conversion without changing any statement or budget. Failed and
successful checks are retained outside Git at
`/workspace/vy3-evidence/loop-call-controls-20261107`. No native ByteWorld,
Source dispatch/admission or full-lane adequacy is claimed. Existing producer
waits, STOPs and full validation/timing obligations remain open.


Reframed loop-failure checkpoint: fifteen public original
`LoopReframedFailureControls` rows have exact frozen signature accounting and
checked aliases in `LoopReframedFailureWitness.lean`. Its joint uses the actual
shared prefix maps and original shrinking link to inhabit the failing suffix
Input at5; the same source guard succeeds before rebinding and reverts after it.
Wrong ordering, saved-tail corruption, insufficient frame and stale alias
refusal retain their original statements. Selected473/1259,786open; the three
private `guard_code`, `before_value` and `stale_pointer` helpers remain explicitly
uncovered. In particular the contradictory stale-pointer premises receive no
joint-witness credit. Supplemental counts stay separate. No native ByteWorld,
public ABI/gas or full Source/G24 adequacy is inferred. Resource logs, proof
checks and reviews are external at
`/workspace/vy3-evidence/loop-reframed-failure-20261107`. Existing producer waits,
STOPs, full affected/final validation and paired-timing obligations remain open.


Private reframed-loop checkpoint: exact kernel identities for `guard_code` and
`before_value` are now exercised through explicit unchanged types, including
the private `beforeValue` definition in the code-equality signature. Both
original helper theorems have no hypotheses; their common joint remains the
actual source/map/Input witness rather than an added feasibility assumption.
The two original kernel axiom reports and both alias reports are guarded;
ordered axiom lists are recorded separately. Selected475/1259,784open.
`stale_pointer` alone remains uncovered in this family; its contradictory
premises receive no positive witness credit. No private definition adds a row.
Logs and reviews: `/workspace/vy3-evidence/loop-reframed-private-20261107`.
Original production/acceptance obligations and producer waits remain open.


Stale-pointer refutation checkpoint: the exact private `stale_pointer` kernel
signature is checked unchanged. A general theorem proves its pointer-relation
and observed-pointer premises cannot jointly hold for any target machine.
Both original and derived theorem axiom reports are guarded. The compact map
records one intentional stale-pointer refutation, null joint witness and zero
selected witness credit; the row stays uncovered by an inhabited witness.
Selected475/1259 and784open are unchanged. This is negative consistency evidence,
not successful admission or native execution. Existing noRefs refutation checks
retain their exact empty-heap classification, axioms and cardinality checks.
Evidence: `/workspace/vy3-evidence/loop-stale-pointer-refutation-20261107`.
All original producer waits, proof budgets, STOPs and final obligations remain.


Public compiler-call-scope checkpoint: four original `CompilerCallScopeControls`
rows now have exact frozen signature accounting in `compiler-call-scope-witness-map.json`
and checked aliases in `CompilerCallScopeWitness.lean`. The joint retains the
actual public compiler selection and branch and derives its reached Input from
an actual allocation run and selected MappedOutput via the existing generic
boundary link. Full prefix/final stack-memory vectors, skipped-consumer refusal
and corrupted saved-tail refusal retain their original statements. The private
observer definition adds no selected row. Selected479/1259,780open; supplemental
rows stay separate. Evidence is external at
`/workspace/vy3-evidence/compiler-call-scope-20261107`. No native ByteWorld,
ABI/gas or full Source/G24 adequacy is inferred; original producer waits, STOPs
and full validation/timing obligations remain open.


Reference-call readback checkpoint: ten original `ReferenceCallReadbackControls`
rows now have exact frozen signatures and checked aliases in
`ReferenceCallReadbackWitness.lean`. The joint includes the actual tuple-reference
runtime Entry atframe64, lo/pointer16 andcursor20, NoAliasPromotion flags, source
call success/evaluated7, reached StateRepr/BaseExtends and suffixInput. The original
complete memory/tail/allocator observations, wrong recapture, body failure,
undersized entry and stale-map refusals retain their full statements. No private
selector, application or observer definition adds a row. Selected489/1259,770open;
supplemental counts stay separate. Evidence is external at
`/workspace/vy3-evidence/reference-call-readback-20261107`. This establishes no
native ByteWorld/emission, ABI/gas or full Source/G24 adequacy. Original producer
waits, STOPs and full validation/timing obligations remain open.


Authorized signed-bitwise transition intake: H71 routes MRS owner head
`abf726ff80b52c1e4bfd6e95dcea64cef1ee2830`, reporting H87/H96/H126 authorization
to replace `BitwiseValueContextControls.signed_refusal` with `signed_acceptance`.
The tracked `authorized-statement-transitions.json` preserves the exact frozen
old signature and records the proposed new identity separately. Fetched master
still has the historical negative; fetching the exact owner head returned
`upload-pack: not our ref`. No replacement signature or gate result is invented.
The reported ticket SHA is provenance, not a locally verified artifact hash.
Frozen registrations and every original external assertion remain unchanged;
source notes in both inventory and external checks point to this separate intake.
The historical negative is superseded only by the explicitly authorized live
acceptance transition, not silently re-proved, renamed or counted unchanged.
Adoption waits for exact replacement bytes/signature and owner validation.
Selected489/1259,770open remain unchanged; no acceptance credit is transferred.


Reference-call capture-failure checkpoint: six original
`ReferenceCallCaptureFailureControls` rows have exact frozen signature accounting
and checked aliases in `ReferenceCallCaptureFailureWitness.lean`. Its joint
retains actual Entry/frame64, lo/pointer16, cursor20 and NoAliasPromotion flags,
the successful tuple call and returned map, paid growth1 and footprint, followed
by captureInput at the failing alias read. The original all-tail source/target
revert transport, complete returned observations, nonzero free capture cell and
successful alternate local read retain their full types. No failure-output
machine or zero-initialization premise is added. Selected495/1259,764open;
application/selector definitions and supplemental rows add no credit. Seven
axiom reports are guarded. Evidence is external at
`/workspace/vy3-evidence/reference-call-capture-failure-20261107`. No native
ByteWorld/emission, ABI/gas or full Source/G24 adequacy is inferred. Existing
transition-intake/producer waits, STOPs and original acceptance obligations remain.


Runtime primitive-return capture checkpoint: ten original
`RuntimeReturnCaptureControls` rows have exact frozen signature accounting and
checked aliases in `RuntimeReturnCaptureWitness.lean`. The joint includes actual
positive/negative call members atframe16, lo/pointer8 andcursor10, alias flags,
source success/revert and evaluated7, then the real returned run, StateRepr,
BaseExtends and correlated captureInput. Original complete memory/stack success,
all-tail failure, wrong order/capture/tail and capacity refusal types remain
unchanged. No instantiated/application definition adds a selected row.
Selected505/1259,754open; supplemental counts stay separate. Eleven reports are
guarded: wrong_capture has no axioms; the other aliases and joint use the existing
standard set. Evidence: `/workspace/vy3-evidence/runtime-return-capture-20261107`.
No native ByteWorld/emission, ABI/gas or full Source/G24 adequacy is inferred.
Existing transition/producer waits, STOPs and final acceptance obligations remain.


Runtime void-capture checkpoint: eleven original `RuntimeVoidCaptureControls`
rows have exact frozen signature accounting and checked aliases in
`RuntimeVoidCaptureWitness.lean`. The joint retains actual success/failure
domains, Entry/frame16 lo/pointer8 cursor10, alias flags, source success/revert,
before7/after37 evaluation and the correlated returned run, StateRepr,
BaseExtends and captureInput. Original complete caller-alias/array payload,
cursor/protected-word and saved-tail observations, body failure, premature
capture, stale value and insufficient-frame refusal statements are unchanged.
No entry/instantiated/application definition adds a row. Selected516/1259,743open;
supplemental counts stay separate. Twelve reports are guarded, including the
axiom-free stale_capture_refused. Evidence is external at
`/workspace/vy3-evidence/runtime-void-capture-20261107`. No native ByteWorld,
ABI/gas or full Source/G24 adequacy is inferred. Existing transition/producer
waits, STOPs and original final acceptance obligations remain open.


Stateful capture checkpoint: six original `StatefulCaptureControls` rows have
exact frozen signature accounting and checked aliases in `StatefulCaptureWitness.lean`.
The joint retains initialInput and both actual source runs, obtains the reached
capture map from original execution and derives declarationInput through the
existing generic nonallocating memory link. No post-capture preservation equation
is assumed. The full local/alias/header/array observations with and without
capture retain their original statements; scalar numeric and symbolic expression
execution remain separate interfaces. Selected522/1259,737open; invocation and
observer definitions and supplemental rows add no credit. Seven axiom reports
are guarded. Evidence: `/workspace/vy3-evidence/stateful-capture-20261107`.
No native ByteWorld/emission, ABI/gas or full Source/G24 adequacy is inferred.
Existing transition/producer waits, STOPs and original final obligations remain.


Shift-capture target checkpoint: fifteen original `ShiftCaptureControls` target
and control rows have exact frozen signature accounting and checked aliases in
`ShiftCaptureWitness.lean`. Its general joint uses the existing generic
shift/capture application for both directions and all finite values/counts to
inhabit the actual represented state and whole captureInput. Original saturated
zero success, old-count clearing, full observations, wrong recapture/modulo/order
and insufficient-frame refusals retain their full statements. The public
`source_expression` row is explicitly uncovered pending its concrete Source
metadata/state/fuel tuple; target witnesses receive no Source credit. Census
accounting distinguishes uncovered public rows from private helpers.
Selected537/1259,722open; definitions/supplemental rows add no credit. Sixteen
reports are guarded, including axiom-free insufficient_frame. Evidence:
`/workspace/vy3-evidence/shift-capture-20261107`. No native ByteWorld/emission,
ABI/gas or full Source/G24 adequacy is inferred. Existing transition/producer
waits, STOPs and all original final acceptance obligations remain open.


Shift Source-expression checkpoint: the remaining original `source_expression`
row now has its exact original alias and a stronger correlated Source/target
joint. Shared `SourceExpressionContext.lean` instantiates original typed
Source.Program/Glob/Fr interfaces with Source.St.init and existing Roadmap fixed
parameters; no per-case metadata or interface family is copied. The tuple retains
every pipeline and caller checked flag, extra fuel, direction and finite operand.
Evaluation explicitly uses checked=false as the frozen theorem requires. Fuel2
times out, while extra+3 succeeds with the original Source encodings and unchanged
locals/state. The old target joint remains unchanged. Selected538/1259,721open;
context definitions and extra fuel controls add zero selected rows. Shared context
and all new proof axiom reports are guarded. No session/hash/native adequacy follows.
The attempted UnsignedCast.Controls fixture import failed at its explicit
sourceState construction (line42: incompatible Source.St/Cursor.empty under the
frozen artifact closure); that raw failure is retained, no production edit applied.
Evidence: `/workspace/vy3-evidence/shift-source-expression-20261107`.
All original transition/producer waits, STOPs and full acceptance obligations remain.


Authorized signed-bitwise transition reconciliation: published master now contains
the exact MRS owner commit `abf726ff80b52c1e4bfd6e95dcea64cef1ee2830`. Its parent
control file matches the frozen historical bytes; its current file matches the
owner's replacement bytes. The exact new `signed_acceptance` signature and source
hash are recorded in `authorized-statement-transitions.json`, with the prior
unavailable-object observation retained as history. The change from isNone to
isSome is explicit authorized acceptance, not an unchanged historical proof.
Frozen `signed_refusal` registrations, original external assertions and old
failures remain unchanged; no witness credit transfers. The owner also changes
Layout, SimLemmas and Bitwise.Selected, so local kernel/axiom and joint-witness
validation must use their matching updated import closure. Source-reported axiom
pins alone are not local kernel validation. Frozen coverage538/1259,721open is
unchanged. Exact-byte delivery wait is resolved; semantic/kernel adoption remains
pending. Evidence: `/workspace/vy3-evidence/signed-bitwise-transition-reconciliation-20261107`.


Matching master artifact closure follow-up: the coordinator identified qualified-units
commit 912456d61 and the published lake-cache release as the UnsignedCast closure.
The repository cache fetcher verified and restored that release in a private RAM
staging directory, using hard links to avoid a second artifact copy. Lean 4.24
serial checks passed KeySort (2.41s), the unchanged UnsignedCast controls (2.61s),
and the original signed-bitwise controls including their axiom guards (3.01s).
The cache identifies head 3da1da5b1e; checked source master was f5038bc02.
Initial missing-artifact, permission and resource-stopped probes remain raw
evidence and receive no passing credit. Generated native C was retained with
verified hashes in RAM and original-path symlinks to preserve disk headroom;
its relocation manifest is included in the evidence directory.
This resolves the local UnsignedCast closure ticket and signed-acceptance control
validation wait, without changing source or frozen historical accounting.
Broader acceptance joint coverage, native production, full affected checks and
paired timings remain open. Coverage stays 538/1259 selected, 721 open.
The unrelated RelatedMemoryCapture/Source.SemanticsExamples STOP remains in force.
Evidence: `/workspace/vy3-evidence/matched-master-cache-20261107`; comparison,
ticket resolution, raw logs, resource records and native-C relocation hashes
are retained there. The RAM artifacts are VM-local and are not portable Git data.


Original VY3 backfill A: `tests/h62/item2/audit-v09-passes/FrameAllocationCertificates.lean`
extends the existing generic Frame API with argument/result/local interval bounds,
three injectivity laws reusing label injectivity, and constructive coverage of
every position in the frame footprint. All arities, including empty regions,
and every base are retained. A nonzero-base combined argument/result/local
witness rejects the exclusive frame limit as a local. These are allocation
certificates only; runtime contents, calling convention and G24 simulation are
not inferred. No per-case interface or new production import was added.

Fresh official Lean4.24.0/Lake5.0.0-src+797c613 runtime was restored separately
from missing historical evidence. Serial Docker checks enforce12GiB/no swap
and4GiB headroom. Direct KeySort and the final companion kernel check passed
(1.409s for the latter), with guarded axiom reports: argument/result bounds
are axiom-free, other certificates use propext and Quot.sound. No runtime/full
acceptance marker is inferred from these focused checks.

The first inline draft kernel-checked but exceeded the10% timing threshold
(0.803s original,1.409s inline), so that workload remains a timing STOP. Proofs
were split and simplified; the original Allocation module is byte-unchanged.
Its restored check still measured1.208s, so the timing hold remains open; no
unchanged retry or performance acceptance is claimed. A first companion check
failed because its new axiom guards overstated the two optimized bounds' actual
dependencies; raw failure is retained and final guards reflect the axiom-free
proofs. Selected538/1259,721open remains unchanged. Evidence and timing/limits
are inventoried in `frame-allocation-evidence.json`; raw records remain at
`/workspace/vy3-allocation-evidence-20261107`. Historical `/workspace/vy3-evidence`
is still missing and has not been reconstructed.


Original VY3 backfill A scoped-slot/label extension reuses the same
`tests/h62/item2/audit-v09-passes/FrameAllocationCertificates.lean` companion.
`Slots.covers` constructs the newest-first index for every occupied position;
`Slots.fresh_above_old` proves fresh binders are above every old slot, complementing
the unchanged production extension law. Finite label bounds, constructive
coverage and separated-region disjointness are general in all bases/arities.
A nonzero-base joint witness preserves an old address under extension, places
a fresh binder above it and shows the actual collision from moving an adjacent
label region backward. These identities are not assembled byte offsets or
scanner-valid JUMPDEST certificates; runtime preservation remains separate.

The focused serial Lean4.24 kernel check passed in1.309s with no resource stop.
Label bounds/disjointness are axiom-free; the other additions use propext and
Quot.sound. The first run failed only the new combination witness's expected
axiom report; its actual standard dependencies are now pinned and raw failure
is retained. Production Allocation and all prior theorem statements are
unchanged; no new interface copy or import edge was added. Selected538/1259,
721open stays unchanged. Prior timing STOPs and full validation holds remain;
no unchanged STOP workload was retried. Raw resources/logs are off Git at
`/workspace/vy3-slot-label-evidence-20261107`, inventoried in
`slot-label-evidence.json`. Historical evidence remains missing.

The unchanged documentation checker reports one missing reference in the
base-identical generic-v08 feature document (ExecutionTransport citation).
No changed-file citation failed. The exact source hash and owner request are
retained in the external evidence's owner-ticket.json; the checker and other
owner's document remain unchanged. This is not a passing global doc gate.


Original VY3 backfill A numeric stack-slot extension:
`tests/h62/item2/audit-v09-passes/StackSlotCertificates.lean` derives the actual
exchange result from a prefix/selected-cell/tail split and uses the existing
readSlot/writeSlot API. For every accessible prefix and arbitrary full-width
words/tail, writes preserve all other cells and read-then-writeback is a genuine
identity execution. Separate read/write underflow laws reject the missing cell
at stack.length even when the Fin16 opcode index is valid. A nonzero-index
combination witness preserves the preceding cell and arbitrary caller tail.
No new instruction, interface structure or production-source edit was added.

All six original imports were cold kernel-checked serially into a private
off-Git artifact directory. The final companion check passed in1.205s with all
eight axiom guards: exchange prefix/end lemmas are axiom-free, others use
propext and Quot.sound. The first syntax failure (reserved prefix identifier)
and its failed-elaboration recovery placeholders are retained as failures only;
none contributes a proof or axiom acceptance claim. Records/resources/artifact
hashes are inventoried in `stack-slot-evidence.json` and retained at
`/workspace/vy3-stack-slot-evidence-20261107`. The12GiB/no-swap serial bound and
4GiB headroom remained satisfied. Numeric none is not an EVM exception theorem;
1024 capacity, gas/observations, Source/G24 and native production remain separate.
Selected538/1259,721open unchanged. All prior timing/trust holds and known
base-documentation failure remain open; no unchanged STOP workload was retried.
Historical off-Git evidence is still missing and has not been reconstructed.


Original VY3 backfill A capacity extension adds seven general certificates to
`tests/h62/item2/audit-v09-passes/StackSlotCertificates.lean`. Read and
read/writeback have the exact prefix condition0<=height and height+1<=1024.
A joint theorem combines actual identity execution with the existing height
checker on the same stack. Controls distinguish height-safe empty-stack
underflow from a successful mathematical identity at initial height1024 whose
DUP prefix reaches1025 and fails the capacity checker. A nonzero-slot concrete
witness satisfies both execution and capacity. No budget, instruction, Source
encoding, existing theorem statement or production definition changed.

The final serial Lean4.24 check passed in1.612s with all old and seven new axiom
guards. The additions use propext, Classical.choice and Quot.sound; no axiom
declaration or sorry was introduced. Reused private dependencies match their
previous cold-checked source/artifact hashes. The initial1.414s observation
exceeded the prior1.205s run by more than10%; proof-only trace simplification
reduced an intermediate run to1.312s, but the final guarded check measured1.612s.
That timing STOP is retained, not accepted or rerun unchanged. These are focused
observations, not full affected/final or native acceptance. Gas and Source/G24
observations remain separate. Selected538/1259,721open is unchanged. The H44
records are inventoried in `stack-capacity-evidence.json`, retained at
`/workspace/vy3-stack-capacity-evidence-20261107`. Historical evidence, prior
trust/timing holds and the known baseline documentation failure remain open.


Original VY3 backfill A arity-aware composition:
`tests/h62/item2/audit-v09-passes/SliceCapacityCertificates.lean` reuses
the existing generic stackBound_comp law from ClzBounds and Slice.comp. Its
main theorem derives actual intermediate/final vectors, execution of both
stages and their composition, capacity at the shifted entry height derived
from run_height, and bounded intermediate/final arities. A constructive
prefix theorem derives a successful bounded stack for every code decomposition;
no desired intermediate execution is assumed. General positive addition
preserves every caller tail with two spare words; a negative control succeeds
mathematically but rejects the1025-word peak before a1024-word final result.
The1024 limit and all original producer/interface definitions are unchanged.

The15-module import closure was validated with six exact previously checked
artifacts and nine fresh bounded cold checks. Allocation was unnecessarily
recompiled instead of reusing its artifact; this is retained as dependency
compilation, not timing credit or STOP clearance. The CLZ lowering check took
100.107s within bounds; no source repair or budget increase was made. Final
serial Lean4.24 companion check passed in1.307s with five axiom guards: generic
laws and overflow use propext/Quot.sound; the positive room arithmetic also
uses Classical.choice. No new axioms/sorry/interface copies or production edits.
Selected538/1259,721open unchanged. Prior slot timingSTOPs, full validation,
Source/native waits and known doc failure remain; the stopped slot companion
was not rerun. H44 records and import/artifact provenance are inventoried in
`slice-capacity-evidence.json`, retained at
`/workspace/vy3-slice-capacity-evidence-20261107`. Historical evidence is still
missing; these fresh checks do not reconstruct it or finish the lane.


Original VY3 backfill A emitted-reference extension:
`tests/h62/item2/audit-v09-passes/AssemblerReferenceCertificates.lean` reuses
actual assemble_eq/tagIndex uniqueness and both absolute/relative reference
certificates. Successful checked assembly supplies source-tag uniqueness; the
general pair theorem derives the two actual emitted pushes, the same unique
tag/JUMPDEST, absolute=base+relative, and scanner validity behind any correctly
sized encoded prefix and suffix. This is emitted-code closure, not the earlier
finite identity arithmetic or an actual jump-execution theorem.

A genuinely assembled three-item Fin1/Empty section at base16 derives its
output via the existing generic assembly-success theorem, and validates the
correct destination after16 STOP instructions. The raw relative word differs
from that target by16; it is not claimed universally to be an invalid offset
or never another JUMPDEST. The initial attempted direct20/4 reduction lacked
Decidable equality for Assembled and did not reduce the scanner; that draft
and failed recovery placeholders are retained as failures, not proof credit.
The final constructive proof uses no new equality instance or semantic table.

Serial Lean4.24 final check passed in1.306s with three guarded standard axiom
reports (propext,Classical.choice,Quot.sound), no resource stop or production
edit. Three private artifacts match prior cold-checked source/byte hashes.
Master was adopted by rebase; prior slot timingSTOPs were not rerun or cleared.
New focused duration is not paired/full timing acceptance. Selected538/1259,
721open unchanged. H44 logs/provenance are inventoried in
`assembler-reference-evidence.json`, retained at
`/workspace/vy3-assembler-reference-evidence-20261107`. Historical evidence,
known doc failure, native/Source waits and full validation remain open.


H145 migration preserves the nine archived evidence records byte-for-byte and
all checker-read fixtures in place. Only two module-docstring pointers changed
in Python; their executable ASTs are unchanged. The unchanged evidence and
private-path checks pass. The portable suite currently attempts41 tests and
reports four errors from the existing frozen/live bitwise statement drift;
the unmodified committed census source reproduces that same refusal. No missing
archived JSON is involved, no guard/expected assertion was changed and no
frozen inventory was repinned. This remains an open acceptance failure.


The emitted-reference companion now also proves stable-width relocation of
section-relative references using the existing relocated-offset and assembler
reference laws. Both checked assemblies and the stable-width premise are
retained. The actual emitted relative values stay equal; scanner validity uses
the new base plus that value. A leading-tag fixture proves successful assembly
uniformly at positive bases below256 and supplies a genuine delta15 witness
from base1to16. Its base0-to16 control refutes stable widths, not assembly
success. Existing emitted-reference statements and production definitions are
unchanged, with no new interface. Verification, provenance, the formatting-only
failed guard and retained timing hold are in the private H145 evidence directory
`evidence/solidity-inline-assembly5-20261031/vy3-compilation/vy3-relative-reference-publish-20261107/`.
This adds no selected-row credit and no jump-execution, Source/native or full
validation claim. All prior holds and historical-evidence waits remain open.


The generic linking companion
`tests/h62/item2/audit-v09-passes/LinkingCertificates.lean` connects existing
link_patch results to a specific original emitted pushTag: byte substitution
preserves that reference and its scanner-valid destination, leaves no unresolved
links, and makes another link pass inert. Existing resolved addresses remain
unchanged. A generic PUSH payload law derives scanner rejection of every
immediate byte from actual instruction boundaries, including arbitrary trailing
bytes and every valid width. The linked nonempty-placeholder fixture uses20
address bytes0x5b and proves both the real target valid and every payload byte
invalid behind every correctly placed prefix. No new linker/interface or
production definition was added. Private H145 proof/resource/provenance records
are under
`evidence/solidity-inline-assembly5-20261031/vy3-compilation/vy3-linking-reference-publish-20261107/`.
This is byte-emission/scanner backfill only, with no jump-execution, native,
Source/G24 or full validation claim, and no selected-row credit. Prior timing,
trust, census/documentation failures and missing-history waits remain open.

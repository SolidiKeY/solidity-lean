# H28 Main/scoped compiler non-vacuity

Status: **in progress; not full-assignment acceptance**.

## Identity and boundaries

- Frozen base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
- Branch: `codex/solidity-h28-sol-20261104/non-vacuity`.
- VM checkout: `/workspace/solidity-lean`.
- Writes stay in `Solidity/Assurance/NonVacuityH28/`,
  `tests/h28-sol/non-vacuity/`, and this document.
- The coordinator publication `b419c3cf4f642ae519b66bebc26cdf2f7cf93574`
  was fetched, and both its remote ancestry and the frozen base ancestry
  verified. No merge, rebase, reset, push or producer edits occurred.
- H16/H22/H21 freezes, statements, premises, observations, budgets and
  intrinsic types remain unchanged. Terra Selection/MemoryCopies/FunctionValues
  audits and G01–G55 producer repairs are excluded. Reading a checked contract's
  existing input does not constitute a producer audit or a new producer claim.

The local registration manifest is
`tests/h28-sol/non-vacuity/registration.json`. Generated roots, central module
maps and trust registries are reserved for integration and are untouched.

## Core-controls checkpoint

`Families.lean` constructs intrinsic local values and environments for every
context. `every_rule_inhabited` supplies an actual state, syntactic rule and the
`Premise.Sound` implication for any statement constructor. It does not supply
truth of each `Premise.fml` antecedent or say every statement succeeds.
`assertion_rule_semantics` separately supplies a true antecedent and applies it.
The explicit `require` programs are nonempty. Their source and target evaluators
are separate, with independent successful and reverting run equalities. A closed
contract/state/machine witness discharges fresh balance and address conditions.
`Main.compiler_correct`, `compiler_net` and core `compiler_checked` are applied to
jointly inhabited inputs. Always-revert code disagrees on the successful run.
Fully constructed pairs reject inconsistent funds, external/self ledger, oracle
and resource bounds; no inconsistent Sim is assumed as a positive witness.

`Calculus.lean` derives a successful nonempty assertion through the calculus and
applies the public soundness wrappers. It checks the actual false-annotated box
loop rule, proves the loop terminates, and rejects the rule's false entry
obligation. The clean-tail application uses actual initialized clean storage;
at the core checkpoint this did not test dirty-tail sensitivity; the expanded
TailSensitive module now supplies that control.

`Callbacks.lean` constructs successful resumed, deterministic-policy and reverting
payments. An initially true ledger invariant fails at payout. A consistent top
invariant permits a resumed state with a distinct ledger. No-callback uniqueness
excludes that resumed outcome. A payment-specific derivation actually applies
`Main.callback_soundness`, using the existing first-order top invariant.
These are abstract callback executions, not source-to-bytecode adequacy claims.

`Storage.lean` supplies arbitrary in-range uint writes, separate source/target
executions, an actual Main compiler application with initial Sim, and a changed
nonzero storage observation that cannot be erased.

`Signatures.lean` reports exact expanded types and axioms for all 21 Main wrappers,
their source originals, the calculus induction contract and all named local
witnesses. `Pins.lean` kernel-checks the core checkpoint's **105 exact measured axiom sets**; every
set is a subset of `propext`, `Classical.choice`, `Quot.sound`. Raw output and its
hash are retained in `axiom-pins.json` and the measurement log. In particular the
previously unpinned noCallback and cleanTail wrappers are included.

## Validation and resource evidence

Commands run through `tests/h28-sol/non-vacuity/run.py` hold the repository writer
lock and execute in the task-owned Docker container. Its enforced cgroup values
are 12 GiB memory and zero swap. The VM has 16 GiB and no swap. A VM guard
requires estimated available memory of at least 4 GiB. It discounts inactive
file cache after dirty/writeback pages and is bounded by host MemAvailable;
it is not a hard reservation of 4 GiB. Lean workers use explicit `-j1`; the environment sets
`LEAN_NUM_THREADS=1`. The scope-local Lake overlay is bound only inside Docker;
the tracked lakefile is unchanged. No heartbeat increase or trust shortcut was
introduced. No speed refactor occurred.

Actual versions: Lean **4.24.0**, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake **5.0.0-src+797c613**.
The source KeySort gate printed:

```text
KEYSORT_PASS: Solidity/KeySort.lean checked from source
```

This establishes the runtime gate only. It does not establish final acceptance.

Each saved `evidence/<tag>.json` contains the exact command, exit, elapsed time,
sampled aggregate RSS, cgroup peak memory and worker command snapshots. RSS is a
one-second sample, and sums shared pages across processes; it is not an exact
physical-memory peak. The first import record's `peak_aggregate_rss_bytes` has the
same sampled meaning. Cgroup memory is independently enforced. New records also
bind input and output SHA256 hashes. Early records remain historical evidence;
the combined checkpoint gate provides current source bindings.

| Evidence tag | Outcome |
|---|---|
| `imports-01` | PASS: 254 jobs, 588.523 s, sampled aggregate RSS 2,074,320,896 bytes |
| `keysort-01` | PASS: source KeySort and actual versions, 2.152 s |
| `families-diag-02` | PASS: per-file MCP diagnostics, zero errors |
| `callbacks-kernel-02` | PASS: actual payment/control module |
| `calculus-kernel-02` | PASS: derivations and false-loop control |
| `storage-kernel-04` | PASS: writes and Main compiler application |
| `signatures-kernel-01` | PASS: 105 measured signatures/axiom reports |
| `pins-kernel-02` | PASS: all 105 exact guarded sets, 60.834 s |
| `core-checkpoint-kernel-02` | PASS: all six current modules, exact source/log hashes, 60.779 s |

At the core checkpoint, structural inventory checking and seventeen accounting
mutation tests passed,
including omitted theorem/constructor/control, changed source/base, empty or
duplicated premise slices, co-omitted pin/signature names, fake evidence,
failed final gate, and a finder/skeptic identity collision within an area.
This external Python checker supplements Lean; it proves no semantic theorem.
`check.py --accept` intentionally fails until the remaining whole-scope ledger,
source-bound final gates and final independent reviews are complete.

Failures are retained. The first raw Families MCP report returned process exit 0
but `success:false` with errors; it is **not** a passing diagnostic gate. Earlier
MCP startup/import attempts failed or returned incomplete output. One retry
started overlapping setup builds; the task-owned container was stopped. A later
MCP diagnostic hung with idle workers and was stopped (exit 137). Kernel module
builds replaced that unreliable diagnostic path. Syntax/inference failures and
the first missing pin-module attempt remain in their original logs. None is
converted to a pass. The first commit whitespace check caught an extra blank
line at the end of Pins; it was removed and the current combined gate rerun.
Early exploratory startup attempts predate the evidence
runner and have no measured RSS/timing; they are not checkpoint gates.

## Reviews and full queue

Separate read-only `/root/finder` and `/root/skeptic` reviewed rules/calculus,
callbacks, compiler, and checker/evidence without using the Lean server. Confirmed
signature extraction, word-conversion, callback inference and checker accounting
findings were fixed. Both approve the current **core-controls checkpoint**.
Their dispositions and artifact hashes are in `checkpoint-reviews.json`.
This is not a final whole-assignment review.

| Frozen queue item | Current accounting |
|---|---|
| Main and source-original enumeration | 21 wrappers, exact source signatures/identities, delegated premises and 217 kernel pins; full premise disposition still open |
| Jointly inhabited executions/applications | Core/context, assertion, payment, arbitrary storage, live locals/environments, all11 checked-constructor contracts inhabited; operation-specific representation subfamilies remain open |
| Countercontrols | Always-revert, nonempty fragment, Sim/resource mismatches, false-loop entry, source panic/refusal/divergence, dirty-tail and pointer/storage/callback erasure controls checked; constructor-specific residuals stay explicit |
| Complete acceptance/reviews/seal | Structural checker and27 regressions pass;145 semantic dispositions,10 resource findings, failed required repository gate, final reviews and whole-assignment seal remain open |
| Assigned backfill | Additional arbitrary-contract/context/value families implemented; no producer audit or repair |

`inventory.json` enumerates all 36 Stmt, 2 Prog, 13 Premise, 28 Proves, 39 ProvesC,
41 ExecS, 4 ExecP constructors and all 11 Compilation branches. Generic open rows
are interim bookkeeping, not durable final findings or proof of theorem falsity.
They must receive precise witness or durable finding dispositions before full
acceptance. All selected theorem/premise statuses remain open until those
bindings are reviewed. No whole compiler correctness, external EVM adequacy,
physical bytecode correctness or source-producer completion is claimed.

## Artifacts and continuation

Repository-relative evidence directory: `tests/h28-sol/non-vacuity/evidence/`.
The immutable checkpoint patch/bundle/checksum manifest will be sealed beneath
`tests/h28-sol/non-vacuity/sealed/` after committing the reviewed checkpoint.
That checkpoint is partial progress on the active original goal. Continue the
remaining ledger and controls in this same VM and branch; do not reset the goal.

## Expanded joint-input checkpoint

The second checkpoint adds eleven proof modules, for seventeen locally
registered modules total. `Outcomes` independently evaluates source and target
panic, actual payment, refusal and divergence cases, then applies the existing
Main compiler contracts. `Locals`, `Fragile` and `Environments` construct live
value/storage-alias/fragile paths and nonzero sender/value/time/self fields.
`Preconditions` distinguishes an inhabited core Sim from rejected fragment and
live-pointer premises. `VacuityControls` rejects done(false), empty goal guards,
false callback derivations and expression nonrevert halts, and keeps exhausted
assumeFalse distinct from successful source execution.

`TailSensitive` uses the existing Tokens model: a clean initialized run succeeds,
whereas the same program panics from a reachable dirty tail. Removing the actual
clean-tail premise is refuted in the kernel.

`MemoryInputs` constructs the original Sim, reserved frame, allocator and cursor
capacity jointly, executes a real dynamic uint-array allocation and proves a
nonempty typed heap. `CheckedObjects` applies the construction contract and
extracts a represented live pointer above the frame. `CheckedFamilies` uses this
same allocated heap/machine/base to inhabit the eight remaining checked
constructors. Each client has an actual source run, target success and the
unchanged branch-specific output Rep. This gives contract inhabitation for all
eleven Compilation constructors. Target success for these heap clients is
derived from the public theorem plus independent source success; it is not a
separate reduction of all target instruction streams.

`MemoryControls` constructs a valid allocator at cursor W−1 and rejects a cost-2
allocation. It obtains an actual allocated pointer and rejects all-zero memory
erasure. The near-full allocator is itself inhabited; its capacity failure is
not an assumed inconsistent positive premise.

The eight additional clients use scalar require/declaration or memory rebind.
They do not exercise loop/call/copy producer operations. `resource-findings.json`
retains ten separately source-bound gaps: positive loop/scoped-loop demand,
positive calls/copy/copy-construction cost, positive copied extent, actual fixed
or reference-element arrays, distinct-object separation, structs and reference
fields. No exclusion or producer repair is inferred from those gaps.

All **217** named exact signatures/axiom sets are now measured; the Pins module
kernel-guards every measured set. `refresh-signatures.py` generates accounting
only, holds writer.lock, and rejects measurement log/source hash mismatches.
Independent checker recomputation and kernel guards provide separate checks.

The inventory includes complete constructor clauses, hashes and source lines.
It marks explicitly constructed derivations and execution constructors; the
remaining **145 semantic constructor obligations** stay open in
`open-premises.json`. Those rows do not imply theorem falsity. Some are
intentional impossible specializations, while others need actual continuation,
argument/frame, decode, invariant or callback inputs. Every such distinction
must receive its final disposition before whole-assignment acceptance.

Current checkpoint gates (commands, exits, timing, sampled aggregate RSS,
per-process child maximum RSS, OOM events and input/log hashes are in each JSON):

| Evidence | Decisive result |
|---|---|
| `signatures-expanded-02` | PASS, 217 kernel reports, 89.040 s |
| `pins-expanded-01` | PASS, 217 exact guarded sets, 90.065 s |
| `expanded-checkpoint-kernel-01` | PASS, all 17 current modules/source hashes; cached replay, 1.080 s |
| `memory-controls-kernel-02` | PASS, both inhabited countercontrols, 2.137 s |
| `keysort-04` | PASS, Lean 4.24.0 / Lake 5.0.0-src+797c613, KeySort source PASS, 2.202 s |
| `accounting-expanded-04` | PASS27 accounting regressions and structural checks; full acceptance remains intentionally FAIL |
| `full-repository-01` | FAIL exit 127: Node unavailable before layers/registration |
| `full-repository-02` | FAIL exit 1: both layer checks PASS; register --check lists 17 missing own imports |

Node v24.19.0 was supplied from the already installed local runtime to the
owned container after the first full-gate attempt. Its SHA256 is
`bc17c508ffeed0ec622934f9b7fa72f8e78da65350e63c3eceb56fa688aa5e12`.
No generated root was edited or hidden. Full gate resolution remains an
integration/layout obligation: the task mandates a local manifest and prohibits
these root writes, while the repository gate requires generated imports.
The root failure is not a passing full build or RUNTIME_GATE_PASS claim.

Other failed proof attempts, memory-guard stops and incomplete diagnostics remain
in immutable raw evidence. The independent Fragile target reduction was stopped
by the earlier conservative memory guard; only its theorem-derived joint target
success is accepted. The old guard counted reclaimable cache against headroom;
current records use the explicitly described working-set estimate. No OOM event
occurred on the accepted expanded gates. Child rusage maximum RSS is per process,
not an aggregate; cgroup peak is the container lifetime, not a per-command peak.
An initial host-side accounting test attempt hit the read-only sandbox creating
temporary fixtures; the authorized bounded-runtime runs provide the saved tests.

Full queue remains active: finish precise semantic constructor and delegated
premise dispositions, resolve the required repository gate without prohibited
writes or masking, run final source-bound validation, obtain final independent
reviews and seal the whole assignment. This checkpoint is partial progress, not
completion. No goal was created, reset or marked complete; get_goal remains
unavailable in the actual tool list.

## Private harness and complete contract ledger

Current Lean sources are under
`tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/`.
Their logical module names remain `Solidity.Assurance.NonVacuityH28.*`.
Only owned files moved; shared roots and maps were not edited. The unchanged
registration check now passes. The historical root failures above remain valid
records of the earlier layout, rather than current blockers.

`kernel.py` prepends a private olean directory, mirrors baseline namespace entries
as explicit symlinks, excludes stale owned modules, and checks actual `--deps`
resolution for each own import. Every Lean process receives `-j1` and
`--tstack=131072`. Cache fingerprints cover own sources and recursive own
artifacts, not the entire baseline artifact graph. Final validation therefore
requires `--all --fresh` after the baseline build. The earlier MCP startup/hang
failures and lack of a Lake target for the private source root remain concrete
limitations; these private files use the bounded per-file kernel harness.

The matched layout check used the same 217 guards, byte-identical inputs,
precompiled imports and fresh source checking without olean output:
87.059 seconds before, 84.040 after. This satisfied the 10% slowdown limit.
`layout-source-preservation.json` and `layout-performance.json` retain the
identities and measurements. Later larger reports check additional obligations;
they are not matched speed comparisons.

New queried witnesses include:

- `Originals`: actual `Stmt.Sound`, `Proves.sound_of`, first-order/no-transfer
  invariant inputs and direct callback formula applications; explicit rejection
  of an always-empty recognizer using a nonempty accepted program.
- `ScalarPremises`: changed Bool update with actual landing, both require guards,
  true box-revert premise, and a hidden Bool binder valid for every initial value.
- `CallbackFrames`: all six ExecF constructors, including nonempty resumed,
  halted and violated payment sequences, and actual local pop/drop frames.
- `AllocatorGrowth`: both legacy and object positive-cost allocator contracts,
  queried with cursor256 and cost2, producing cursor258.
- `HeapQueries`: actual allocator preservation, live old-reference base extension,
  concrete header/element cells, and the one-object separation-domain limitation.
  `primitive_source_observations` combines successful source evaluation with
  expected heap length1, a live pointer, array length1 and zero element.
  `primitive_source_eq` alone is only a transport lemma, not the witness.
- `PrimitiveFamilies`: every value of all three primitive types, separate source
  and target evaluations, queried representation fields and signed−1 controls.
- `JointWorld`: the same funded entry inhabits Sim, deterministic source/target
  payment, callback and noCallback executions. Compiler observations retain−5;
  the callback resumption retains its distinct−7 ledger.
- `LoopContracts`: actual reached zero Demand/Cost for the nonallocating clients.
  Positive allocating loop demand remains an explicit field finding.
- `LogicalGates`: queried transfer/callback/admission/modalFree/boxOnly selectors,
  universal-binder rejection of an existential reading, and distinct typed-run
  versus ordinary-update halt predicates.

The ledger now enumerates169 exact constructor clauses: Stmt36, Prog2,
Premise13, Proves28, ProvesC39, ExecS41, ExecP4 and ExecF6. It records32
constructed constructor instances/families and137 durable constructive-coverage
findings. A witnessed constructor is an inhabited instance/family, not coverage
of every parameter or helper branch. The full statement dispatch/helper analysis
and remaining parameter requirements are retained separately.

`public-contracts.json` expands137 delegated predicates, gates and checked-result
schemas with exact pinned sources, fields, constructors and kernel identities.
Ten leaf contracts remain durable-open; inhabited whole-state relations do not
supply nonexistent fixed/reference-array/struct object arguments. Typed immutable
certificate data, evaluator/observer functions and explicit budget functions are
identified endpoints; no producer, selector, source-to-bytecode or physical
adequacy audit is claimed. All source-original and delegated identities are
included in the414-name kernel signature/axiom report.

The frozen assignment permits an explicit witness OR a durable open finding.
The checker accounts for those separately. Main wrappers, all11 Compilation
constructors and mandatory controls still require actual kernel witnesses.
A finding preserves its exact missing constructive obligation and does not
assert theorem falsity, introduce an exclusion or change a premise. Final review
records must bind the exact proof/accounting input snapshot. Final acceptance
also requires committed input bytes, frozen tracked contents and exact-head
gates; the ledger alone cannot produce a passing result.

## Remaining required validation

Full repository attempts03 and04 stopped at the4GiB VM headroom guard, rather
than a proof error. Attempt03 reached a Yul shifts module; attempt04 passed the
large PowerBounds module and reached frozen Source/Horizon. Their failed exits,
resource samples and missing final child-rusage records remain explicit.

Read-only POSIX_FADV_DONTNEED reclaimed disposable Lake cache pages without
changing or deleting files: about5.7GB in the first cache and2GB in the legacy
cache. The runner now covers both cache locations, retains pre/post samples,
and stops immediately on a pre-reclamation sample below4GiB. Hard12GiB memory,
zero swap and the4GiB headroom requirement are unchanged. Its matched no-trigger
Pins regression was79 seconds versus84 seconds; actual reclamation costs are
recorded separately and are not inferred from that no-trigger timing.

Finish current axiom guards, accounting regressions and independent reviews;
run a fresh private-module gate and the required unchanged full repository gate,
including the coordination toolkit checks. Freeze the reviewed source/accounting
commit before exact-head final gates, and put final evidence under the ignored,
sealed artifact tree so an evidence-only commit cannot invalidate the gate head.
Whole-assignment acceptance and its final seal remain pending.

Checkpoint validation: all414 exact axiom guards pass (pins-contracts-03). The
statement helper ledger now covers all36 Stmt constructors, including the
unconstructed complex-assert capture case. Queue accounting is marked complete
under the explicit witness-or-durable-finding policy; this does not mark the
persistent goal or the required exact-head final gates complete.

## Serial runtime correction checkpoint

The frozen corpus generator uses Promise.all to launch Lean probes. The owned
Lake shim now serializes its exact no-build probe prefix with flock, creates
the ignored lock parent on a cold checkout, and forwards explicit -j1 after
the caller separator. Producer sources, gate scripts and proof budgets are
unchanged. Sampling recognizes plain/relative/absolute Lean argv0; the runner
stops and the checker rejects recorded multiworker evidence. Sampling alone
cannot establish absence of brief overlap; flock enforces probe serialization.
Two actual OS/parser smoke tests passed (no Lean output mocked), and the full
accounting checkpoint passed37 tests. Finder and skeptic reviewed this change
read-only without a Lean server.

The long full preparation attempt stopped after8970.736 seconds at the4GiB
headroom guard in frozen Examples/DecisionHashesChecks.lean, at progress3150/3474.
It is failed preparation evidence under sealed/final-v1, not final acceptance.
The runtime changed during that run and therefore requires a new frozen head.
No proof error was reported and no baseline repair is made here.

Post-stop retained generated pages explained4.5GB of VM usage. Read-only
POSIX_FADV_DONTNEED on26011 regular .lake/build artifacts took0.828 seconds,
with no error or inode/size/mtime/ctime change. Same-command/source414-Pins
checks passed at101.365 seconds before and100.243 seconds after (ratio<1.1).
The runner now includes this checkout's generated build pages in its existing
advice policy, skipping symlinks/opening read-only with O_NOFOLLOW. The12GiB
cap, zero swap, pre-advice4GiB stop and30-second cooldown remain unchanged.
A final exact-head full retry is justified by this measured cache recovery;
no threshold, exclusion, premise or theorem is weakened.

## Shared pin-registration dependency

At runtime checkpoint49af79545eaef77678e7c6d32041c278a311ece4 the unchanged
full toolkit build passed3672 jobs, including TestSuite; after recovering the
authentic adjacent SolKey pin, every full-gate stage passed except axiom-pins.
The axiom gate reports0 errors and414 unrecorded H28 pin entries. It hardcodes
scripts/g07-axiom-pins.json and has no local-manifest option. H28 explicitly
forbids H21 shared-registry/trust-inventory writes, so that file is unchanged.
No pin is hidden, gate changed, or inventory overlaid to manufacture a pass.

pin-proposal contains a source-bound414-entry local delta, the preserved6343-entry
registry plus proposed additions, and an unapplied registration patch. Its
read-only comparison reports0 errors/0 notes against the candidate only; this
is not a passing global gate. The separately labeled authorized-exception.patch
also proposes the corresponding single-path allowance in the owned checker.
Neither proposal is applied. Q-H28-PINS records the two explicit dispositions:
keep scope and hand off blocked for central integration, or authorize that exact
exception before any shared write. Kernel/private validation and a sealed
blocked handoff are still required; no RUNTIME_GATE_PASS is claimed.

## Published master adoption, 2026-11-05

The coordinator explicitly authorized adopting8495f1deb0a95dd6b9301822d8649ab76b217681.
Merge9121caa3685b18df08ff7b40a7ce73beb87cbc1a preserves the prior owned head
ffd09ef2d49fd7bd71d585e66fc78e3bc81ecf83 and its sealed blocked handoff. All63
source files referenced by theorem, delegated predicate and resource inventories
are byte-identical to original base6f3eedf0. Original source hashes/signatures,
premises, exclusions and proof budgets remain pinned. The checker separately
audits original worker history and worker changes relative to the authorized
published baseline; it does not count published producer changes as worker edits.
The38th accounting control rejects a substituted adoption anchor. Shared g07
registration and H35 receiving-route authority are not inferred from publication.
Fresh VM validation and current cache status remain required.

### Adopted-head checkpoint handoff (partial)

Committed proof/accounting head `38885cd4efe1d37889b2f7109d28eb8239f27718`
passed KeySort (Lean4.24.0/Lake5.0.0-src+797c613), all26 fresh private modules
including414 signature/axiom guards (child220.4707s; runner221.4058s), and38
external accounting controls. The unchanged full gate ran766.8858s child
(767.4584s runner):10 stages passed, including run-lean699s/3923jobs,
TestSuite/corpus/strict automatic; only axiom-pins failed with0errors and414
unrecorded records. Actual host acceptance rejected only the nonzero full gate
and its nonzero-rusage condition; tracked checkout was clean.

Both independent read-only finder/skeptic passed all4areas against snapshot
`2af1cd784c534f38c5abb66c056f541131d3b06009d855d148f4b22b53163e2a`; neither
used Lean/server. The regenerated7546+414 registration candidate and exact
two-file exception remain UNAPPLIED. Scope authority is still pending.

H35 shipping failed again: normal command exit2/master-only guard; documented
nonmaster dry-run exit1/missing coordinator poll-state. Actual26fresh oleans
and manifest were archived, extracted and27file hashes verified; archive
SHA256 `e1b93df34205f3cedb60cef5d3bf7505f1d2169e41a0bab7e5a0339d0e02191f`.
Remote receipt remains null. The incoming coordinator-cache notice supplies
no outbound receipt or worker routing. Checkpoints remain partial; no
RUNTIME_GATE_PASS or goal completion is claimed.

Exact commands, exits/times/RSS, per-area reviews, source identities and the two
unanswered stable scope questions are committed in
`tests/h28-sol/non-vacuity/adoption-checkpoint-handoff.json`; raw immutable
command outputs are under its absolute VM evidence path. This records the
measured head explicitly. Final exact-head gates will be rerun after this
handoff commit; historical results do not certify a different head.

### Follow-on published master f77cf60d (partial handoff)

The user explicitly authorized adopting `f77cf60d3cea8f7f1db8db29cc027532b0cd3fce`.
Merge `da9d39bad42f9e0fd996866bf0cde5caa32fe2ef` preserves owned head
`66b9d11f3a614fb626df318334ae8ecdc099e1a8`; remote ancestry from8495 and6f3
was verified. All63 frozen inputs remain byte-identical to original6f3 and
no upstream change touches owned paths. All26 Lean witnesses, exact theorem
signatures, premises, exclusions and budgets remain unchanged. No new producer
interface is needed for this non-vacuity queue. Upstream deferred/semantic
extensions are adoption only, not additional audited scope.

The checker now retains the exact historical8495 adoption and audits three
worker ranges:6f3→ffd09ef2,8495→66b9d11f,f77cf60d→HEAD. This preserves the
previous ownership boundary without reclassifying upstream changes as worker
edits. A39th negative test rejects missing adoption history. A new unapplied
414-pin proposal must preserve the exact f77c registry; older candidates/seals
remain historical and are not overwritten. Shared-registry authority and H35
outgoing transport/receipt remain unresolved; no authorization inferred from
publication or incoming-cache notices. Fresh final-head gates and separate
read-only finder/skeptic reviews follow this checkpoint. No done or
RUNTIME_GATE_PASS claim. The prior committed handoff and sealed66b9 packet
retain all previous measured commands and proof-versus-external-test boundaries.

Follow-on preparation gates passed in the existing12GiB/no-swap/-j1 runtime:
39 accounting tests and structural/negative-acceptance controls; read-only
proposal generation preserves7590 existing entries, adds414 and compares with
0errors/0notes (8004 total). Commands/exits/times/RSS and exact measured merge
head are committed in `tests/h28-sol/non-vacuity/follow-on-preparation.json`;
raw outputs are committed in its evidence directory. Finder and skeptic each
passed all4source areas read-only/noLean-server. The new two-file exception
patch remains UNAPPLIED, with no additional path allowed in the real checker.
Final-head gates, actual outgoing shipment attempt and sealed handoff follow;
the prior full-gate/H35 blockers are retained, not waived.

### 0840Z integration and H41 (partial handoff)

User-authorized master9584f9e7df09f638d9e0cb8930501d1660aa4b2f was fetched
and ancestry verified fromf77 and6f3. Merge74a46841faa1b645e820363a8322ba47b1e25e86
preserves owned502cf541; all63 frozen input files and26ownedLean modules
remain byte-identical, with no upstream-owned-path collision. No integrated
producer fragment is reimplemented or added to this audit's scope.

Exact two-entry adoption history plus current adoption now generate four
worker-scope audits:6f3→ffd,8495→66b9,f77→502cf541,9584→HEAD. Fixed history
and ancestry guards remain; new controls reject mutated historical merge
and VM shipping policy, bringing external test count to41. No protected
write-path allowance or theorem/premise/exclusion/budget change.

H41 supersedes the earlier worker-shipping question: never run ship-cache.sh
on the VM. Prepare verified packs with absolute path and SHA for coordinator
pull. `prepare-cache.py` now durably packages only the actual26fresh private
oleans plus manifest, binds exact head/source/dependency/toolchain identities
and verifies extracted payload hashes; output is restricted to owned sealed
directories. Null external receipt means transfer unobserved, not failure
to execute a prohibited VM command. No coordinator receipt is invented.
Shared registries remain generated and outside worker writes; the exact414
generated delta is delivered for central integration. The required full gate
still needs actual verification; no done or RUNTIME_GATE_PASS claim.

Preparation gates:41external tests/structural controls pass; read-only pin
proposal preserves7925records plus414=8339, compare0errors/0notes. Exact
commands, measured merge head, exits/times/RSS are committed in
`tests/h28-sol/non-vacuity/integration9584-preparation.json` with raw evidence.
Separate finder/skeptic source reviews passed all4areas read-only/noLean.
The packer additionally requires exact--all--fresh and observed KeySort
version evidence, avoiding a hardcoded version claim. Committed final-source
snapshot and actual fresh VM gates/verified pull pack follow. The old
shipping scope question is retired; central generated registration remains
an integration dependency, with no new exception request.

### 1200Z published integration (partial handoff)

Published b86ae4568cef6d6226f4d170360bbb089debe3fb was fetched and remote/base
ancestry verified. Mergee98f9b2b7834ee37019e4eac2d81ba187c61a86b preserves
owned d952505990a00083f379d6221b729b37ffec6838. All63 frozen inputs and26
ownedLean files remain byte-identical; no upstream-owned-path collision.
Selected Main/scoped APIs need no repair or new producer implementation.
Published horizon/representation/world/physical limitations are not treated
as whole-lane correctness or added H28 audit scope.

The fixed adoption history now retains8495,f77,9584 plus currentb86, producing
five exact worker-scope audits. Existing41controls cover missing/mutated
history, current-anchor tampering and H41 policy. No theorem, premise,
exclusion, observation, heartbeat, trust-policy or protected-path change.
H41 remains verified pack/path/SHA for coordinator pull; no VM shipping.
Shared registries remain generated centrally; a fresh exact414record delta
is delivered without shared writes or exception request. Fresh exact-head
VM gates, independent reviews and sealed pull handoff follow; no done or
RUNTIME_GATE_PASS claim for the whole goal. Earlier seals remain immutable.

Preparation evidence:41controls/structural/negativeacceptance testsPASS;
generated proposal preserves7990records plus414=8404, compare0errors/0notes.
Exact commands, exits/times/RSS and measuredmergehead are committed in
`tests/h28-sol/non-vacuity/integrationb86a-preparation.json` with raw outputs.
Separate read-only finder/skeptic passed all4sourceareas. No proof/helper
changes beyond exactadoption accounting. Finalcommitted snapshot, actual
freshVM gates and verifiedH41pullpack follow; centralregistration remains
pending, without sharedwrites or an exceptionrequest.

### 1422Z published integration (partial handoff)

Published8bf8321873befa3f35ca31e97e5339a1baee93e6 was fetched and remote/base
ancestry verified. Merge1d064c778d182600ea13d7e18cc0885c27222c92 preserves
ownedb42be661791d54378c5268a3ae6dad2081c2862d. All63 frozen input files and26
ownedLean modules remain byte-identical; no upstream-owned-path collision.
Existing selectedMain/scoped contracts need no producer repair or duplicate
implementation. Published bounded/world/physical/source limitations remain
with their owners; none are inferred discharged by this adoption.

Exact historical/current adoption now yields six worker-scope audits. Existing
41controls retain history/current-anchor/H41 guards; no new sharedwritepath,
theorem/premise/exclusion/observation/budget/trust change. H41 remains verified
pack/path/SHA for coordinator pull, noVMshipping. Generated414pin delta is
left for central integration without worker sharedwrites/exceptionrequest.
Fresh exact-head VM gates, independent reviews and sealed handoff follow.
No whole-goal done or RUNTIME_GATE_PASS claim; prior seals remain immutable.

Preparation gates passed: all 41 controls, structural inventory and negative
acceptance tests; the generated proposal preserves 8,059 records and adds
414 (8,473 total), with zero comparison errors or notes. Exact commands,
exits, times, RSS and the measured merge head are committed in
`tests/h28-sol/non-vacuity/integration8bf8-preparation.json` and raw evidence.
Separate read-only finder and skeptic reviews passed all four source areas.
Final gates will run on the committed snapshot. Central registration remains
pending; no shared write or scope exception is requested.

### Published source-copy rebase and inhabited loop backfill

The coordinator published H28 by source copy at
`de1d76d922d7ff42d3a07bc020b740f8ec9f0105`, within requested master
`e6849d3bdf516099d20c33d3581d523449764018`. The assigned branch was rebased
onto that exact master before this checkpoint; the old owned head
`8f6e7e626cd5d2b6b444616a5a17294ff29cc605` and working changes were preserved.
All 54 retained reviewed inputs are byte-identical between those immutable
old/published trees. The sole pruned reviewed input, `public-contracts.json`,
is restored byte-for-byte. The small pruned rusage fixture used by existing
resource negative controls is also restored exactly. Bulk pruned evidence is
preserved in the local immutable pre-rebase archive, rather than reintroduced
into tracked master. Historical writer audits still end at the retained old
head; published-copy ancestry and the new owned delta are checked separately.
This records the actual source-copy delivery and does not assert that the old
worker commits became ancestors of published master.

Seventeen additive universal loop lemmas inhabit existing Main/scoped compiler
contracts with an actually constructed one-object live heap. Twelve cover a
nonempty false-condition loop, including a body that would revert if entered;
source execution, independent compiled target execution, zero demand/cost and
the actual `Main.compiler_checked` application are supplied. Five complement
these with a true-condition loop that enters the same reverting body: source
and independent EVM evaluation revert, the reached demand branch exists, and
the complete compiler Input is constructively inhabited. This is one attempted
body execution and zero completed successful turns. Universality over contracts
and annotations is retained; it does not establish annotation validity.

No completed allocating turn, positive allocating capacity, arbitrary compiled
body acceptance, arbitrary termination, callback-loop semantics or LoopScopes
finding is promoted. Existing 137-contract classifications, 169 constructor
clauses, ten delegated leaf gaps and ten resource findings remain unchanged.
There are 431 exact signature/axiom entries in 26 private modules. Direct measurement shows that none of the original 414 pins are centrally
registered in the adopted master; all 431 require coordinator-owned
registration. No shared registry or producer implementation is changed here.
The external controls include explicit rejection of completed-turn promotion
and changed published-copy anchors. Fresh exact-head runtime gates and cache
packing follow this committed checkpoint; pending/failed gates remain explicit.
H41 requires a verified local pack with path and SHA for coordinator pull;
no VM `ship-cache.sh` invocation or remote-transfer receipt is claimed.

Preparation handoff: bounded per-file loop proof, all 431 measured signatures,
all 431 exact axiom guards and 45 external controls pass. Exact commands,
exits, timing, child RSS and headroom are in `backfill-preparation.json` and
its immutable raw evidence. The unapplied proposal preserves 8,120 registered
entries and adds exactly 431 owned pins; 65 upstream-only unregistered pins
remain unchanged and byte-verified against adopted master. The repository
gate is not bypassed. Failed draft checks and the two rejected proposal-count
assumptions remain explicitly failed evidence. Final committed-head gates,
independent reviews and cache/seal evidence are recorded in the local
`sealed/loop-backfill-e684-<head>` handoff after this commit.

### Human H82 retirement and H44 packaging split

Implementation remains stopped; the accepted successor is `solidity-v12-v17-20261031/v17-validation-release`. The reviewable retirement increment keeps the complete original rendered prompt, original work/backfill queue and human-readable handoff under `tests/h28-sol/non-vacuity/retirement-h82/`. `BULK-MANIFEST.json` authenticates an off-git archive of every original retirement file, including the full scope/open-queue data, drafts, unfinished patch and evidence records. The held head remains preserved on a backup ref and its earlier immutable seal. No theorem, gate, budget, scope or live implementation changes. The PAUSED tool transition was rejected by its enum; human STOP remains binding. No applicable H71 push grant was available, so no push occurs. The coordinator/successor integrates the split head after review.

The assurance successor also retains its earlier preservation records and `H44-OFF-TREE.json`; the published archive manifest is additive provenance. This merge does not certify archive availability on the successor VM, accept unfinished drafts or close any original obligation.

### H107 headline witness CI safety net

The library CI job now runs `kernel.py --all --fresh` with serial threads after
cache restoration. It elaborates every private H28 witness module, including
Families' actual Main.compiler_correct, compiler_net and compiler_checked
applications. Any dependency or elaboration failure fails the step. Witnesses
and check.py are unchanged. Finder and skeptic accepted the wiring read-only.
V2 headlines are not present in the inspected tree; include their witness
applications when V14 publishes them, without dropping existing coverage.

Local validation subsequently passed at reviewed CI commit
`e04e0b8e6cc8b15a28d51922a697112e6d19ee6c`: all 26 modules freshly elaborated
in the coordinator-authorized owned worktree `/workspace/v17-witness`, using
serial Lean and the unchanged 12 GiB address-space cap. All witness source
hashes match the original checkout. Earlier prerequisite/permission failures
remain preserved. The master-cache seed fell back after temporary staging
reached its reserve; the successful build used existing artifacts through an
owned cache view at `/tmp/v17-witness-owned/cache`, with new outputs in owned
temporary storage. The original root-owned build tree was not repaired.

The coordinator-published lane branch was verified at that same reviewed CI
commit. Workflow dispatch no longer waits on a VM token: the coordinator will
dispatch the published branch and return its run URL. That reference remains
pending. The H107 evidence manifest pins successful and failed raw logs off git.
This suite pass does not close the whole non-vacuity or V17 release assignment.

### H121: inhabited H98 V2 headlines and actual checked-entry success

`Solidity/Backend/Payments/EntrySuccess.lean` adds
`Evm.Compiler.compile_core_some` and `Evm.Compiler.compile_core_success`.
These concern the actual `Evm.Compiler.compile`, not an arbitrary result:
every existing core-fragment certificate produces a compilation result, and
the original simulation, stack-room and successful typed-run premises yield
successful emitted-code execution, protected stack and final representation.
The proof reuses `Payments.compile_success`; no frozen definition or statement
changes, new admission predicates or assumed preservation are introduced.
This is success on the stated supported core domain, not all-source compiler
totality, physical EVM adequacy or precompile/gas/fork agreement.

`tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/FamiliesV2.lean`
reuses the existing nonempty require family and jointly constructed simulation.
It directly applies `Main.compiler_checked_v2` in `checked_v2_family` and
`Main.compiler_correct_v2` in `correct_v2_success`. `actual_entry_success`
applies the actual compiler theorem over arbitrary contracts and fresh balances;
`closed_actual_entry_success` provides a closed successful instance with no
caller feasibility premise. All six new declarations have exact standard-axiom
pins. The existing H107 all-module CI step discovers this new witness module;
`check.py`, the original families and H98 interfaces remain unchanged.

The production theorem is the reusable OBL-SUCCESS artifact for the
precompile-agreement consumer. That consumer must still audit its own original
statements and failure/gas/fork obligations; no downstream acceptance or whole
lane completion follows from this additive checkpoint.

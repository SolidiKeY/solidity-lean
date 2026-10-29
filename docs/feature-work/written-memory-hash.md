# Written-memory/hash composition

The ORIGINAL `gapWrittenMemory` is now refuted by `decideHash` and
`decideGoal`, with a kernel-checked dispatched verdict and an actual
`State.init` countermodel. Its formula and `inTarget` certificate are
unchanged. This supersedes partial checkpoint `b813cbf98d86`, which is
preserved in history and in the external checkpoint exports.

Coverage is explicit: two fresh `uint[]` memory arrays, `s[0] = 1`, then
equality of their hashes, under either modality and any of the three
non-recovery kinds. Binder names are parameters. The producer refuses other
syntax, including a changed index/value/type, self-equality, recovery, and
an extra scope. This is an exact syntax-schema refuter, not a general
negative-array input-certificate extractor or full decision completeness.
No target, exclusion, waiver, callback/profile policy, or `DecisionTheorem`
was narrowed or weakened. All six original gap statements/certificates
remain; only this pin's observation improves with proof-backed evidence.

## Proof and integration

[HashWrittenInput.lean](../../Solidity/Calculus/HashWrittenInput.lean)
factors the original proved helpers below `Decision`, preserving their
names. Normalized byte equality is equal lengths plus bounded pointwise
byte equality. Actual successful heap writes preserve every untouched
byte. `hashEq_iff_input` and `hashEq_afterT_iff` use only the formula-local
finite premise; converse congruence excludes recovery, while forward input
congruence remains valid for every kind. Failure/exhaustion semantics stay
unchanged.

The continuation adds `hashFree_update_of_landing`, which constructs the
update's finite premise from its unique actual landing when the updater has
no hashes. `refutes_update_input` transfers a realized unequal-input
counterexample through either modality. `AllocCounterexample` is the
minimal scoped realization interface: an actual typed object plus a body
counterexample under that body's own premise at the allocated/pushed state.
`refutes_alloc` composes it through each fresh binder without borrowing an
outer premise.

[HashWrittenRealize.lean](../../Solidity/Calculus/HashWrittenRealize.lean)
constructs actual fresh arrays `[1]` and `[2]`. The write to the first array
is in bounds and has an actual typed landing. The existing checked family
supplies the two real distinct hash outputs and the landing's finite
premise; no global injectivity or collision-freedom hypothesis appears.
Nested allocation certificates then refute the original closed formula.
The universal allocation domain remains all typed objects; the one-word
family objects are existential counterexample witnesses only.
This concrete realization makes the original pin independent of the general
`gapMemInnerNeg` reduction. The referenced `0590c505` object is not available
in this checkout; no other VM's unmerged work was copied or contacted.

`body?` and `extract?` return intrinsic formula equality certificates.
Their tactic `cases` definitions elaborate to the required recursors;
existing certified `Tm.beqR` checks every write/hash term and sort. No untyped
syntax/state/witness or indexed-family match is introduced. `refutation?`
tries only the three non-recovery kinds. `Decision.tryWritten`, placed last
in `hashTries`, returns the actual certified countermodel and retains all
earlier decisions and ordering.

[HashWritten.lean](../../Solidity/Calculus/HashWritten.lean) retains the
original closed `HashInputReduction` interface and exact composition with
hoist 1024, `mxTop` and `decideMem`. Its refutation adapter still requires the
original finite premise at the returned prestate. General negative-array
input extraction through this cut remains open; the new original-pin verdict
comes from the explicit realized syntax certificate, not from claiming that
broader extraction exists.

## Observations and kernel boundary

[DecisionWrittenMemory.lean](../../Solidity/Examples/DecisionWrittenMemory.lean)
retains the full ordered 18-path matrix: memory; three single-kind paths;
six ordered two-kind paths; six ordered three-kind paths; hash; goal.

| Fixture | Baseline | Continuation |
|---|---|---|
| Original written-memory pin | unknown in all 18 paths; inTarget true | first 16 unchanged unknown; hash/goal refuted at preheap length 0; inTarget true |
| Written self-hash box | unknown in all 18 paths | unchanged; existing certified positive cut still proves it |
| Input self box | mem/goal proved; other 16 unknown | unchanged |
| Input diamond | mem/goal refuted at preheap length 0; other 16 unknown | unchanged |

Exactly 70 of 72 original observations are unchanged; only the original
hash/goal observations improve. The six kind/modality variants retain 108
ordered observations, with hash/goal refuted for each. Direct-stage refusal
controls cover self, recovery, index, value, type and extra scope. Existing
controls retain actual non-idempotent writes/aliases, modulo-equivalent
bytes, unequal tails/lengths, real family hash separation, invalid recovery
inputs, zero-length box/diamond failures and an unset local.

`original_refuted` proves the original statement has a countermodel.
`original_kernel_verdict` evaluates its actual dispatched refutation in the
kernel; `original_realized_covered` checks certificate coverage. All new
headline audits use only `propext`, `Classical.choice`, `Quot.sound`;
`hashInput_write_index` uses only `propext`. Exact audit outputs are guarded.
No new axiom or admitted proof is present. This is intrinsic-model/kernel
and compiled Lean evidence. No new Solidity-source/compiler/EVM conformance
or language-support result is inferred from it. All hash semantics and
language inventory support classifications remain unchanged.

## Runtime, failures and recovery

The retained checkout is `/workspace/solidity-lean`, branch
`codex/next10-written-memory-hash`, origin
`https://github.com/SolidiKeY/solidity-lean.git`, based on published master
`f4dee4a29c2e208b36db4a4161a4723c735cd775`. Startup/reconnect verified the
retained `b813cbf98d866dafbecfbe5e434df7cb6d40ea46`, ancestry, Bash, Lean
4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`) and Lake
`5.0.0-src+797c613`. Saved setup/user files are preserved; its thread default
is overridden with `LEAN_NUM_THREADS=1` and explicit Lean `-j1` in a temporary
Lake configuration. `-DElab.async=false` is the existing scheduling repair;
no proof/fuel/node/test budget changes.

Writes/checks use the documented writer lock. One heavy check runs at a time
in the same VM under verified `memory.max=12884901888`,
`memory.swap.max=0`, beneath the 16 GiB parent. Caches stay on disk. VM
headroom uses parent limit minus current plus inactive file cache and checks
host available RAM; the unchanged stop threshold is 1 GiB. Exact cgroup
peaks include all charged processes/cache in the group. No cold-build-fit
claim is made from retained-cache confirmations.

The continuation KeySort runtime gate passed before edits: exit 0, two
jobs, 24,879,104-byte peak. The unchanged original checkpoint baseline and
its original failed full-run/headroom stop, distinct Derived17 serialization
repair and passing warm confirmation remain in the preserved checkpoint
handoff/archive. No old failed or stopped check is relabeled a pass.

MCP automatic `lake setup-file` initially lost the alternate Lake config.
Only the affected task container was stopped (exit 137); this was not an OOM
or a pass. The repaired launcher uses `lake env` and an explicit `LAKE`
wrapper; process evidence verifies `-j1` and serialized elaboration on the
child compiler. The executor briefly became unavailable while that repaired
check ran. The SAME saved VM/branch and running container were recovered,
without a duplicate check, new VM, clone or replacement branch. The outer
monitor was lost; a recovery monitor covered the later window. CSV epochs
record the gap, so uninterrupted headroom coverage is not claimed for this
attempt. Its recovered actual peak was 6,461,456,384 bytes, no OOM. It exited
1 after ten partial diagnostic polls; doc-comment attachment and audit line
wrapping errors were repaired. That attempt is not a pass.

Future MCP setup calls forbid automatic builds (`--no-build --no-cache`),
with imports prebuilt separately. The new durable build runner keeps its
headroom guard inside the bounded container, so loss of an outer tool
session does not stop monitoring.

## Validation and review

Final changed-file diagnostics so far pass: input helpers, producer,
Decision, cut adapters, expanded fixture and original Decision source.
The original source check passed in 592 seconds, sampled peak
6,266,277,888 bytes and minimum available headroom 4,790,579,200 bytes; exact
final peak is retained in its log. Hash fixture dependencies passed in
276 seconds (`DecisionHashes` 275 seconds, matching baseline), exact peak
7,148,191,744 bytes and minimum headroom 4,092,399,616 bytes. Expanded
fixture diagnostics passed in 17 seconds with no errors/warnings.

The assignment target build passed all 313 jobs in 14 seconds, exact peak
247,640,064 bytes. `./run-lean.sh` passed in 100.034 seconds with exact group
peak 1,064,669,184 bytes and minimum available headroom 9,878,556,672 bytes:
default library 689 jobs; complete SolkeyTestSuite 259 jobs; native checker
377 taclets, 131 read-bearing annotations, all matched. No OOM or guard stop.
This is a current-tree confirmation with retained checked caches, not a cold
build or fresh timing claim for cached modules. The root import file's final
per-file diagnostic also passed.

Inventory regeneration/check passed with unchanged 212 features (151 model,
23 abstract, 30 excluded, 8 upstream) and 783 upstream symbols; generated
files/support classifications have no diff. Orphans: 704 reachable, zero
orphans/not-allowed. Layers: 152 core modules, zero elaborator reachability.
Strict automation: 491 automatic, 61 existing step budgets, zero manual,
11 refuted, zero pending. Trust: 718 sources, 240 inventoried sites, zero
findings. These required gates passed both the quick and final bundles.

The unchanged 300-second timing policy passed against the current full log
(zero newly timed TestSuite modules: checked cache) and the retained actual
26-module profile (maximum 173 seconds). Historical successful per-module
timings are not relabeled fresh runs; the old stopped full attempt remains
a failure. Isolated OpenLoops and Derived17 confirmations reused checked
artifacts and passed in about two seconds each; no new proof timings are
claimed for them. The prepared full-suite serialization script was not
needed or executed because those dependency graphs were unchanged.

An ADDITIONAL global `check-doc-paths.sh` audit failed with 20 missing foreign
file references in unchanged `Solidity/Eqns.lean` and historical group03/group10
validation JSON. A read-only reproduction against published baseline `f4dee4a`
finds exactly the same 20 failures, all citing files byte-identical, and zero
new missing references. The task document's four file links resolve. The
checker/exclusions and historical artifacts were not modified. The final
bundle's aggregate exit is therefore 1 solely for that additional baseline
failure; it is not counted as a passing bundle or hidden by the passing
required gates. The global audit remains open outside this patch.

Read-only finder and skeptic have reviewed the input/update/allocation
semantics and producer/dispatcher without Lean server, builds or edits.
Neither found a semantic false accept. Confirmed stale descriptions, the
missing adapter module docstring and additional refusal controls were fixed.
Their scope limitation is retained above: exact schema realization closes
this pin, without general negative-array extraction. Both rechecked the final
source/evidence and found no semantic defect or evidence overclaim. The
skeptic's cumulative-import count correction (four imports, not the two
continuation additions alone) was applied. Final metrics/documentation review
is recorded in the external review record.

## Shared edits and artifacts

Shared changes are narrow: the Decision import and last certified hash
stage; four cumulative root imports (two at the b813 checkpoint and two in
this continuation); the original proof-backed verdict pin;
module-map/correspondence/M7 owning links. New implementation stays in
`HashWrittenInput`/`HashWrittenRealize`; the existing adapter and task fixture
are updated in this lane. No other gap source, target/waiver tail, setup/user
configuration, repository script, hash semantics or external VM/monitor was
modified. The inventory is regenerated with its audit script, without hand
editing generated files or inflating support.

Evidence is under `/workspace/next10-written-memory-hash-evidence`, including
full ordered observations, source preservation, recovery/process traces,
commands/exit codes/timings/peaks and reviews. Original b813 exports are
preserved separately in `/workspace/next10-written-memory-hash-checkpoint-b813`.
Final cumulative patch, handoff, archive and SHA256 manifest are refreshed
at `/workspace/next10-written-memory-hash.{patch,sha256}`,
`/workspace/next10-written-memory-hash-handoff.md` and
`/workspace/next10-written-memory-hash-evidence.tar.gz` after final checks.
The temporary `lakefile.next10.toml` is exported inside the evidence directory
and removed from the checkout before commit. To reproduce, copy it back,
activate the saved setup, override `LEAN_NUM_THREADS=1`, and use the retained
bounded runners; explicit `-j1` belongs to Lean, not Lake build flags. No
tracked setup/user configuration is changed. No push, merge or cherry-pick
is performed.

## Complete-delivery fact-type follow-up (2026-10-29)

The retained whole-delivery finder finding names eight missing fact types:
`hp` and `he` in `HashWrittenInput`, `ea`, `ep`, `ea'` and `eb` in
`HashWrittenRealize`, and `hw` and `h` in `DecisionWrittenMemory`.
All eight annotations are already present in integration snapshot `67576ad8`;
this follow-up preserves them rather than replaying the source assignment.

Auditing the complete candidate against delivery base
`f4dee4a29c2e208b36db4a4161a4723c735cd775` found one additional newly added
untyped fact, `hIu` in `Calculus/TermSize.lean`. It now spells out the exact
inequality supplied by `invFml_size`, before the existing simplification.
The proof term and all subsequent proof steps are unchanged. The final
comment-aware audit covers 165 newly added `have` facts across 67 changed
Lean files and finds no remaining missing fact types. Its result is retained
in `/tmp/written-memory-hash-type-audit.json`.

Complete per-file MCP diagnostics (`interactive=false`) for the only Lean
file edited in this follow-up, `TermSize`, report no errors or warnings,
no failed dependencies and no pending elaboration. The results are retained
in `/tmp/written-memory-hash-type-diagnostics.json`. These focused results
do not complete earlier pending diagnostics or replace the coordinator's
combined validation. The existing pending `DecisionKInt` check recorded in
the memory-negative-block milestone remains pending here.

Local read-only finder and skeptic passes checked the cumulative fact-type
audit and the annotation against its helper's signature. No further finding
or semantic decision remains in this repair. Whitespace and actual
conflict-marker checks pass. This follow-up changes only a fact annotation
and this record; semantics, observations, target predicates, invariants and
budgets are preserved. No full build, index write, commit, push, source VM,
skill or monitor modification is performed. Independent review and combined
gates remain with the coordinator.
